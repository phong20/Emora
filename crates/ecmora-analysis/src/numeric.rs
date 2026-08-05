use super::*;

impl Lowerer {
    pub(super) fn record_abstract_instruction(&mut self, instruction: &Instruction) {
        let value = match instruction {
            Instruction::ConstUndefined { result } => {
                Some((*result, AbstractValue::from_value(Value::Undefined)))
            }
            Instruction::ConstNull { result } => {
                Some((*result, AbstractValue::from_value(Value::Null)))
            }
            Instruction::ConstNumber { result, value } => {
                Some((*result, AbstractValue::from_value(Value::Number(*value))))
            }
            Instruction::ConstBool { result, value } => {
                Some((*result, AbstractValue::from_value(Value::Bool(*value))))
            }
            Instruction::ConstString { result, value } => Some((
                *result,
                AbstractValue::from_value(Value::String(value.clone())),
            )),
            Instruction::Parameter {
                result, value_type, ..
            }
            | Instruction::Capture {
                result, value_type, ..
            }
            | Instruction::CellGet {
                result, value_type, ..
            }
            | Instruction::ObjectGet {
                result, value_type, ..
            } => Some((*result, AbstractValue::from_type(*value_type, None))),
            Instruction::ToNumber { result, .. }
            | Instruction::UnaryNumber { result, .. }
            | Instruction::BinaryNumber { result, .. } => {
                Some((*result, AbstractValue::from_type(ValueType::Number, None)))
            }
            Instruction::ToBoolean { result, .. }
            | Instruction::UnaryBool { result, .. }
            | Instruction::CompareNumber { result, .. }
            | Instruction::CompareString { result, .. }
            | Instruction::CompareObject { result, .. }
            | Instruction::ObjectDelete { result, .. } => {
                Some((*result, AbstractValue::from_type(ValueType::Bool, None)))
            }
            Instruction::TypeOfDynamic { result, .. } => {
                Some((*result, AbstractValue::from_type(ValueType::String, None)))
            }
            Instruction::Phi {
                result,
                value_type,
                incoming,
            } => {
                let mut values = incoming
                    .iter()
                    .filter_map(|(_, value)| self.abstract_values.get(value).cloned());
                let value = values
                    .next()
                    .map(|first| values.fold(first, AbstractValue::join));
                Some((
                    *result,
                    value.unwrap_or_else(|| AbstractValue::from_type(*value_type, None)),
                ))
            }
            Instruction::ObjectNew { result }
            | Instruction::ObjectNewWithPrototype { result, .. }
            | Instruction::ObjectGetPrototype { result, .. } => {
                Some((*result, AbstractValue::from_type(ValueType::Object, None)))
            }
            Instruction::ClosureNew { result, .. } => {
                Some((*result, AbstractValue::from_type(ValueType::Callable, None)))
            }
            Instruction::CallDirect {
                result,
                return_type,
                ..
            }
            | Instruction::CallIndirect {
                result,
                return_type,
                ..
            } => Some((*result, AbstractValue::from_type(*return_type, None))),
            Instruction::PromiseResolved { result, .. }
            | Instruction::PromiseRejected { result, .. }
            | Instruction::PromisePending { result }
            | Instruction::PromiseThen { result, .. } => {
                Some((*result, AbstractValue::from_type(ValueType::Promise, None)))
            }
            Instruction::CellNew { result, .. } => {
                Some((*result, AbstractValue::from_type(ValueType::Cell, None)))
            }
            _ => None,
        };
        if let Some((result, value)) = value {
            self.abstract_values.insert(result, value);
        }
    }

    pub(super) fn abstract_value_for_expression(&self, expression: &Expression) -> AbstractValue {
        let mut bindings = HashMap::new();
        for scope in &self.scopes {
            for (name, binding) in scope {
                if !binding.initialized {
                    continue;
                }
                let value = self
                    .abstract_values
                    .get(&binding.value_id)
                    .cloned()
                    .unwrap_or_else(|| {
                        AbstractValue::from_type(binding.value_type, binding.value.clone())
                    });
                bindings.insert(name.clone(), value);
            }
        }
        abstract_value::evaluate(expression, &bindings)
    }

    pub(super) fn coerce_to_number(
        &mut self,
        expression: &Expression,
        value: (ValueId, ValueType, Option<Value>),
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        if value.1 == ValueType::Number {
            return Ok(value);
        }
        if let Some(known) = value.2 {
            let number = ecmora_value::to_number_checked(&known)?;
            return Ok(self.emit_value(Value::Number(number)));
        }
        let abstract_value = self.abstract_value_for_expression(expression);
        if abstract_value.may_be_bigint() {
            bail!("BigInt arithmetic uses compatibility numeric tower")
        }
        if !abstract_value.numeric_coercion_safe() {
            bail!(
                "dynamic ToNumber may observe object/Proxy coercion; \
                 use compatibility runtime"
            )
        }
        let result = self.new_value();
        self.emit(Instruction::ToNumber {
            result,
            operand: value.0,
            operand_type: value.1,
        });
        Ok((result, ValueType::Number, None))
    }

    pub(super) fn can_lower_number_arithmetic(
        &self,
        left: &Expression,
        operator: BinaryOperator,
        right: &Expression,
    ) -> bool {
        let left = self.abstract_value_for_expression(left);
        let right = self.abstract_value_for_expression(right);
        if left.may_be_bigint() || right.may_be_bigint() {
            return false;
        }
        if operator == BinaryOperator::Add && (left.may_be_string() || right.may_be_string()) {
            return false;
        }
        left.numeric_coercion_safe() && right.numeric_coercion_safe()
    }

    pub(super) fn lower_number_arithmetic(
        &mut self,
        left_expression: &Expression,
        operator: BinaryOperator,
        right_expression: &Expression,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        let left = self.lower_expression(left_expression)?;
        let left = self.coerce_to_number(left_expression, left)?;
        let right = self.lower_expression(right_expression)?;
        let right = self.coerce_to_number(right_expression, right)?;
        let operator = number_operator(operator)
            .ok_or_else(|| anyhow::anyhow!("operator không phải Number arithmetic"))?;
        let result = self.new_value();
        self.emit(Instruction::BinaryNumber {
            result,
            operator,
            left: left.0,
            right: right.0,
        });
        let known = match (left.2, right.2) {
            (Some(left), Some(right)) => Some(ecmora_value::binary(
                to_sem_binary(operator_to_hir(operator)),
                left,
                right,
            )?),
            _ => None,
        };
        Ok((result, ValueType::Number, known))
    }

    pub(super) fn lower_number_unary(
        &mut self,
        operator: UnaryOperator,
        argument: &Expression,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        let abstract_value = self.abstract_value_for_expression(argument);
        if abstract_value.may_be_bigint() {
            bail!("BigInt unary arithmetic uses compatibility numeric tower")
        }
        let operand = self.lower_expression(argument)?;
        let operand = self.coerce_to_number(argument, operand)?;
        let result = self.new_value();
        self.emit(Instruction::UnaryNumber {
            result,
            operator: match operator {
                UnaryOperator::Plus => UnaryNumberOperator::Plus,
                UnaryOperator::Minus => UnaryNumberOperator::Minus,
                UnaryOperator::BitwiseNot => UnaryNumberOperator::BitwiseNot,
                _ => unreachable!(),
            },
            operand: operand.0,
        });
        let known = operand
            .2
            .map(|value| ecmora_value::unary_checked(to_sem_unary(operator), value))
            .transpose()?;
        Ok((result, ValueType::Number, known))
    }
}

fn operator_to_hir(operator: BinaryNumberOperator) -> BinaryOperator {
    match operator {
        BinaryNumberOperator::Add => BinaryOperator::Add,
        BinaryNumberOperator::Subtract => BinaryOperator::Subtract,
        BinaryNumberOperator::Multiply => BinaryOperator::Multiply,
        BinaryNumberOperator::Divide => BinaryOperator::Divide,
        BinaryNumberOperator::Remainder => BinaryOperator::Remainder,
        BinaryNumberOperator::Exponential => BinaryOperator::Exponential,
        BinaryNumberOperator::ShiftLeft => BinaryOperator::ShiftLeft,
        BinaryNumberOperator::ShiftRight => BinaryOperator::ShiftRight,
        BinaryNumberOperator::ShiftRightZeroFill => BinaryOperator::ShiftRightZeroFill,
        BinaryNumberOperator::BitwiseOr => BinaryOperator::BitwiseOr,
        BinaryNumberOperator::BitwiseXor => BinaryOperator::BitwiseXor,
        BinaryNumberOperator::BitwiseAnd => BinaryOperator::BitwiseAnd,
    }
}
