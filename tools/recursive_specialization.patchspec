#!/usr/bin/env python3
from pathlib import Path

def replace_once(path: str, old: str, new: str) -> None:
    file = Path(path)
    text = file.read_text(encoding="utf-8")
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{path}: expected exactly one match, found {count}\n--- OLD ---\n{old[:500]}")
    file.write_text(text.replace(old, new, 1), encoding="utf-8")

analysis = "crates/ecmora-analysis/src/lib.rs"

replace_once(
    analysis,
    "use std::collections::{HashMap, HashSet};",
    """use std::{
    collections::{HashMap, HashSet, hash_map::DefaultHasher},
    hash::{Hash, Hasher},
};""",
)

replace_once(
    analysis,
    "    inline_callables: HashMap<String, HirFunction>,",
    "    inline_callables: HashMap<String, ClosureBinding>,",
)

replace_once(
    analysis,
    """    specializations: HashMap<String, (String, ValueType)>,
    active_specializations: HashMap<String, ActiveSpecialization>,""",
    """    specializations: HashMap<String, (String, ValueType)>,
    active_specializations: HashMap<String, ActiveSpecialization>,
    specialization_counts: HashMap<String, usize>,
    expected_type_hint: Option<ValueType>,
    function_return_hint: Option<ValueType>,
    function_arity: Option<usize>,""",
)

replace_once(
    analysis,
    """                let value = match expression {
                    Some(expression) => self.lower_expression(expression)?,
                    None => self.emit_value(Value::Undefined),
                };
                self.return_types.push(value.1);
                self.set_terminator(Terminator::ReturnValue {
                    value: value.0,
                    value_type: value.1,
                });
                Ok(())""",
    """                let return_hint = self.function_return_hint;
                let value = match expression {
                    Some(expression) => {
                        self.lower_expression_with_hint(expression, return_hint)?
                    }
                    None => self.emit_value(Value::Undefined),
                };
                self.return_types.push(value.1);
                if let Some(tail_call) = self.take_direct_tail_call(value.0) {
                    self.set_terminator(tail_call);
                } else {
                    self.set_terminator(Terminator::ReturnValue {
                        value: value.0,
                        value_type: value.1,
                    });
                }
                Ok(())""",
)

replace_once(
    analysis,
    """    fn lower_expression(
        &mut self,
        expression: &Expression,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {""",
    """    fn lower_expression_with_hint(
        &mut self,
        expression: &Expression,
        expected: Option<ValueType>,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {
        let previous = self.expected_type_hint;
        self.expected_type_hint = expected;
        let result = self.lower_expression(expression);
        self.expected_type_hint = previous;
        result
    }

    fn expression_type_hint(&self, expression: &Expression) -> Option<ValueType> {
        let mut bindings = HashMap::new();
        for scope in &self.scopes {
            for (name, binding) in scope {
                if binding.initialized {
                    bindings.insert(name.clone(), binding.value_type);
                }
            }
        }
        infer_expression_type_hint(expression, &bindings, None)
    }

    fn take_direct_tail_call(&mut self, result: ValueId) -> Option<Terminator> {
        let is_tail_call = matches!(
            self.blocks[self.current].instructions.last(),
            Some(Instruction::CallDirect {
                result: call_result,
                ..
            }) if *call_result == result
        );
        if !is_tail_call {
            return None;
        }
        let expected_arity = self.function_arity?;
        let argument_count = match self.blocks[self.current].instructions.last() {
            Some(Instruction::CallDirect { arguments, .. }) => arguments.len(),
            _ => return None,
        };
        if argument_count != expected_arity {
            return None;
        }
        let Instruction::CallDirect {
            function,
            arguments,
            argument_types,
            ..
        } = self.blocks[self.current]
            .instructions
            .pop()
            .expect("tail call instruction disappeared")
        else {
            unreachable!()
        };
        Some(Terminator::TailCallDirect {
            function,
            arguments,
            argument_types,
        })
    }

    fn lower_expression(
        &mut self,
        expression: &Expression,
    ) -> Result<(ValueId, ValueType, Option<Value>)> {""",
)

replace_once(
    analysis,
    """            ExpressionKind::Binary {
                left,
                operator,
                right,
            } => {
                let left = self.lower_expression(left)?;
                if *operator == BinaryOperator::InstanceOf {""",
    """            ExpressionKind::Binary {
                left,
                operator,
                right,
            } => {
                let numeric_context = matches!(
                    operator,
                    BinaryOperator::Subtract
                        | BinaryOperator::Multiply
                        | BinaryOperator::Divide
                        | BinaryOperator::Remainder
                        | BinaryOperator::Exponential
                        | BinaryOperator::ShiftLeft
                        | BinaryOperator::ShiftRight
                        | BinaryOperator::ShiftRightZeroFill
                        | BinaryOperator::BitwiseOr
                        | BinaryOperator::BitwiseXor
                        | BinaryOperator::BitwiseAnd
                );
                let right_hint = self.expression_type_hint(right);
                let left_hint = if numeric_context
                    || (*operator == BinaryOperator::Add
                        && right_hint == Some(ValueType::Number))
                {
                    Some(ValueType::Number)
                } else {
                    None
                };
                let left = self.lower_expression_with_hint(left, left_hint)?;
                if *operator == BinaryOperator::InstanceOf {""",
)

replace_once(
    analysis,
    """                let right = self.lower_expression(right)?;
                let known = match (left.2.clone(), right.2.clone()) {""",
    """                let right_hint = if numeric_context
                    || (*operator == BinaryOperator::Add
                        && left.1 == ValueType::Number)
                {
                    Some(ValueType::Number)
                } else {
                    None
                };
                let right = self.lower_expression_with_hint(right, right_hint)?;
                let known = match (left.2.clone(), right.2.clone()) {""",
)

replace_once(
    analysis,
    """    fn lower_inline_call(
        &mut self,
        name: &str,
        function: &HirFunction,""",
    """    fn resolve_callback_argument(
        &mut self,
        argument: &Expression,
    ) -> Option<ClosureBinding> {
        match &argument.kind {
            ExpressionKind::Function(function) => {
                let captures = self.capture_environment_for(function);
                Some(ClosureBinding {
                    function: function.clone(),
                    captures,
                })
            }
            ExpressionKind::Global(name) => {
                if let Some(callback) = self.inline_callables.get(name).cloned() {
                    Some(callback)
                } else if let Some(callback) = self.closure_callables.get(name).cloned() {
                    Some(callback)
                } else if let Some(function) = self.function_defs.get(name).cloned() {
                    let captures = self.capture_environment_for(&function);
                    Some(ClosureBinding { function, captures })
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn lower_inline_call(
        &mut self,
        name: &str,
        function: &HirFunction,""",
)

old_loop = """        let mut call_arguments = Vec::new();
        let mut parameters = Vec::new();
        let mut callbacks = HashMap::new();
        let mut parameter_type_hints = HashMap::new();
        for (parameter, argument) in function.parameters.iter().zip(arguments) {
            if let ExpressionKind::Function(callback) = &argument.kind {
                parameter_type_hints.insert(
                    parameter.clone(),
                    ValueType::Callable,
                );

                callbacks.insert(
                    parameter.clone(),
                    callback.clone(),
                );
            } else {
                let value = self.lower_expression(argument)?;

                parameter_type_hints.insert(
                    parameter.clone(),
                    value.1,
                );

                parameters.push((
                    parameter.clone(),
                    value.1,
                ));

                call_arguments.push(value);
            }
        }"""
new_loop = """        let mut call_arguments = Vec::new();
        let mut parameters = Vec::new();
        let mut callbacks = HashMap::new();
        let mut parameter_type_hints = HashMap::new();
        for (parameter, argument) in function.parameters.iter().zip(arguments) {
            if let Some(callback) = self.resolve_callback_argument(argument) {
                parameter_type_hints.insert(parameter.clone(), ValueType::Callable);
                callbacks.insert(parameter.clone(), callback);
            } else {
                let value = self.lower_expression(argument)?;
                parameter_type_hints.insert(parameter.clone(), value.1);
                parameters.push((parameter.clone(), value.1));
                call_arguments.push(value);
            }
        }"""
replace_once(analysis, old_loop, new_loop)

replace_once(
    analysis,
    """        let specialization_key = format!(
            "{}::{:?}::{capture_signature:?}",
            name,
            parameters
                .iter()
                .map(|(_, value_type)| *value_type)
                .collect::<Vec<_>>(),
        );""",
    """        let mut callback_order = callbacks.keys().cloned().collect::<Vec<_>>();
        callback_order.sort();

        let callback_signature = callback_order
            .iter()
            .map(|parameter| {
                (
                    parameter.as_str(),
                    callback_specialization_fingerprint(&callbacks[parameter]),
                )
            })
            .collect::<Vec<_>>();

        let mut specialization_captures = captures.to_vec();
        for parameter in &callback_order {
            specialization_captures.extend(callbacks[parameter].captures.iter().cloned());
        }

        let return_seed = self.expected_type_hint.unwrap_or(ValueType::Dynamic);
        let specialization_key = format!(
            "{}::{:?}::{capture_signature:?}::{callback_signature:?}::{return_seed:?}",
            name,
            parameters
                .iter()
                .map(|(_, value_type)| *value_type)
                .collect::<Vec<_>>(),
        );""",
)

replace_once(
    analysis,
    """        if let Some(active) = self
            .active_specializations
            .get(&specialization_key)
            .cloned()
        {
            if !callbacks.is_empty() {
                bail!(
                    "recursive function `{name}` với devirtualized callback \\
                    chưa được hỗ trợ"
                )
            }

            return Ok(self.emit_specialization_call(
                &active.function_name,
                active.return_type,
                &call_arguments,
                captures,
            ));
        }""",
    """        if let Some(active) = self
            .active_specializations
            .get(&specialization_key)
            .cloned()
        {
            return Ok(self.emit_specialization_call(
                &active.function_name,
                active.return_type,
                &call_arguments,
                &specialization_captures,
            ));
        }""",
)

replace_once(
    analysis,
    """        // Giữ chính sách cache cũ. Function có captures vẫn được predeclare cho
        // recursion, nhưng chưa cache lâu dài sau khi lower xong.
        let cacheable = callbacks.is_empty() && captures.is_empty();""",
    """        // Captures are ABI slots and callback bodies are part of the key, so
        // these specializations are reusable across closure instances.
        let cacheable = true;""",
)

replace_once(
    analysis,
    """        let declared_return_type = infer_function_return_type(
            function,
            &parameter_type_hints,
            captures,
        );

        let specialization_id = self.next_function;""",
    """        let inferred_return_type = infer_function_return_type(
            function,
            &parameter_type_hints,
            captures,
        );
        let declared_return_type = if inferred_return_type == ValueType::Dynamic {
            self.expected_type_hint.unwrap_or(ValueType::Dynamic)
        } else {
            inferred_return_type
        };

        const MAX_SPECIALIZATIONS_PER_FUNCTION: usize = 64;
        let specialization_count = self
            .specialization_counts
            .entry(name.to_owned())
            .or_default();
        if *specialization_count >= MAX_SPECIALIZATIONS_PER_FUNCTION {
            bail!(
                "function `{name}` vượt quá {MAX_SPECIALIZATIONS_PER_FUNCTION} native specializations;                  recursion/callback types không hội tụ"
            )
        }
        *specialization_count += 1;

        let specialization_id = self.next_function;""",
)

replace_once(
    analysis,
    """                return Ok(self.emit_specialization_call(
                    &function_name,
                    return_type,
                    &call_arguments,
                    captures,
                ));""",
    """                return Ok(self.emit_specialization_call(
                    &function_name,
                    return_type,
                    &call_arguments,
                    &specialization_captures,
                ));""",
)

replace_once(
    analysis,
    """        Ok(self.emit_specialization_call(
            &function_name,
            return_type,
            &call_arguments,
            captures,
        ))""",
    """        Ok(self.emit_specialization_call(
            &function_name,
            return_type,
            &call_arguments,
            &specialization_captures,
        ))""",
)

replace_once(
    analysis,
    "            inline_callables: callbacks,",
    "            inline_callables: HashMap::new(),",
)

replace_once(
    analysis,
    """        let mut ir_captures = Vec::with_capacity(captures.len());
        for (index, capture) in captures.iter().enumerate() {
            let value = child.new_value();
            child.emit(Instruction::Capture {
                result: value,
                index: index as u32,
                value_type: ValueType::Cell,
            });
            ir_captures.push(Parameter {
                name: capture.name.clone(),
                value,
                value_type: ValueType::Cell,
            });
            child.scopes[0].insert(
                capture.name.clone(),
                Binding {
                    kind: capture.kind,
                    initialized: true,
                    value_id: value,
                    value_type: capture.value_type,
                    value: None,
                    cell: Some(value),
                },
            );
        }""",
    """        let mut ir_captures = Vec::with_capacity(specialization_captures.len());
        for (index, capture) in specialization_captures.iter().enumerate() {
            let value = child.new_value();
            child.emit(Instruction::Capture {
                result: value,
                index: index as u32,
                value_type: ValueType::Cell,
            });
            ir_captures.push(Parameter {
                name: if index < captures.len() {
                    capture.name.clone()
                } else {
                    format!("@callback.capture.{index}.{}", capture.name)
                },
                value,
                value_type: ValueType::Cell,
            });
            if index < captures.len() {
                child.scopes[0].insert(
                    capture.name.clone(),
                    Binding {
                        kind: capture.kind,
                        initialized: true,
                        value_id: value,
                        value_type: capture.value_type,
                        value: None,
                        cell: Some(value),
                    },
                );
            }
        }

        let mut callback_capture_offset = captures.len();
        for parameter in &callback_order {
            let callback = callbacks[parameter].clone();
            let remapped_captures = callback
                .captures
                .iter()
                .enumerate()
                .map(|(index, capture)| CapturedBinding {
                    name: capture.name.clone(),
                    kind: capture.kind,
                    cell: ir_captures[callback_capture_offset + index].value,
                    value_type: capture.value_type,
                })
                .collect::<Vec<_>>();
            callback_capture_offset += callback.captures.len();
            child.inline_callables.insert(
                parameter.clone(),
                ClosureBinding {
                    function: callback.function,
                    captures: remapped_captures,
                },
            );
        }""",
)

replace_once(
    analysis,
    """            specializations: self.specializations.clone(),
            active_specializations: self.active_specializations.clone(),
            ..Default::default()""",
    """            specializations: self.specializations.clone(),
            active_specializations: self.active_specializations.clone(),
            specialization_counts: self.specialization_counts.clone(),
            function_return_hint: Some(declared_return_type),
            function_arity: Some(parameters.len()),
            ..Default::default()""",
)

replace_once(
    analysis,
    """        self.next_function = child.next_function;
        self.specializations = child.specializations;
        self.active_specializations.remove(&specialization_key);""",
    """        self.next_function = child.next_function;
        self.specializations = child.specializations;
        self.specialization_counts = child.specialization_counts;
        self.active_specializations.remove(&specialization_key);""",
)

replace_once(
    analysis,
    """            if let Some(function) = self.inline_callables.get(name).cloned() {
                if function.r#async {
                    return self.lower_async_call(name, &function, arguments);
                }

                return self.lower_inline_call(
                    name,
                    &function,
                    arguments,
                    None,
                );
            }""",
    """            if let Some(callback) = self.inline_callables.get(name).cloned() {
                if callback.function.r#async {
                    return self.lower_async_call(name, &callback.function, arguments);
                }

                return self.lower_inline_call(
                    name,
                    &callback.function,
                    arguments,
                    Some(&callback.captures),
                );
            }""",
)

replace_once(
    analysis,
    """fn sanitize_function_name(name: &str) -> String {""",
    """fn callback_specialization_fingerprint(callback: &ClosureBinding) -> u64 {
    let mut hasher = DefaultHasher::new();
    format!("{:?}", callback.function).hash(&mut hasher);
    for capture in &callback.captures {
        capture.name.hash(&mut hasher);
        capture.value_type.hash(&mut hasher);
    }
    hasher.finish()
}

fn sanitize_function_name(name: &str) -> String {""",
)

ir = "crates/ecmora-ir/src/lib.rs"

replace_once(
    ir,
    """    ReturnValue {
        value: ValueId,
        value_type: ValueType,
    },
    Unreachable,""",
    """    ReturnValue {
        value: ValueId,
        value_type: ValueType,
    },
    TailCallDirect {
        function: String,
        arguments: Vec<ValueId>,
        argument_types: Vec<ValueType>,
    },
    Unreachable,""",
)

replace_once(
    ir,
    """                Terminator::ReturnValue { value, value_type } => {
                    require_type(&types, *value, *value_type)?;
                    if function.return_type != Some(*value_type)
                        && function.return_type != Some(ValueType::Dynamic)
                    {
                        bail!("return type không khớp function `{}`", function.name)
                    }
                }
                Terminator::Unreachable => {}""",
    """                Terminator::ReturnValue { value, value_type } => {
                    require_type(&types, *value, *value_type)?;
                    if function.return_type != Some(*value_type)
                        && function.return_type != Some(ValueType::Dynamic)
                    {
                        bail!("return type không khớp function `{}`", function.name)
                    }
                }
                Terminator::TailCallDirect {
                    function: callee,
                    arguments,
                    argument_types,
                } => {
                    verify_call_arguments(&types, arguments, argument_types)?;
                    let target = program
                        .functions
                        .iter()
                        .find(|candidate| candidate.name == *callee)
                        .ok_or_else(|| anyhow::anyhow!("unknown direct tail callee `{callee}`"))?;
                    if target.parameters.len() != arguments.len() {
                        bail!("direct tail call `{callee}` sai target arity")
                    }
                    if function.parameters.len() != arguments.len() {
                        bail!("direct tail call `{callee}` không thể tái sử dụng argv")
                    }
                    if function.return_type != Some(ValueType::Dynamic)
                        && function.return_type != target.return_type
                    {
                        bail!("direct tail call `{callee}` sai return type")
                    }
                }
                Terminator::Unreachable => {}""",
)

replace_once(
    ir,
    """            Terminator::ReturnI32(_)
            | Terminator::ReturnValue { .. }
            | Terminator::Unreachable => Vec::new(),""",
    """            Terminator::ReturnI32(_)
            | Terminator::ReturnValue { .. }
            | Terminator::TailCallDirect { .. }
            | Terminator::Unreachable => Vec::new(),""",
)

replace_once(
    ir,
    """                Terminator::ReturnValue { value, value_type } => {
                    writeln!(&mut output, "    ret {:?} %v{}", value_type, value.0).unwrap()
                }
                Terminator::Unreachable => writeln!(&mut output, "    unreachable").unwrap(),""",
    """                Terminator::ReturnValue { value, value_type } => {
                    writeln!(&mut output, "    ret {:?} %v{}", value_type, value.0).unwrap()
                }
                Terminator::TailCallDirect {
                    function,
                    arguments,
                    ..
                } => {
                    let arguments = arguments
                        .iter()
                        .map(|value| format!("%v{}", value.0))
                        .collect::<Vec<_>>()
                        .join(", ");
                    writeln!(&mut output, "    tail_call @{}({})", function, arguments).unwrap()
                }
                Terminator::Unreachable => writeln!(&mut output, "    unreachable").unwrap(),""",
)

codegen = "crates/ecmora-codegen-llvm/src/lib.rs"

replace_once(
    codegen,
    """    let dynamic_print = module.add_function(
        "ecmora_print_dynamic",
        context
            .void_type()
            .fn_type(&[i8_type.into(), i64_type.into()], false),
        None,
    );""",
    """    let dynamic_print = module.add_function(
        "ecmora_print_dynamic",
        context
            .void_type()
            .fn_type(&[i8_type.into(), i64_type.into()], false),
        None,
    );
    let recursion_enter = module.add_function(
        "ecmora_recursion_enter",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), i32_type.into()], false),
        None,
    );
    let recursion_leave = module.add_function(
        "ecmora_recursion_leave",
        context.void_type().fn_type(&[], false),
        None,
    );""",
)

replace_once(
    codegen,
    """    for (index, block) in function.blocks.iter().enumerate() {
        builder.position_at_end(llvm_blocks[index]);
        for instruction in &block.instructions {
            match instruction {""",
    """    for (index, block) in function.blocks.iter().enumerate() {
        builder.position_at_end(llvm_blocks[index]);
        if index == 0 && function.return_type.is_some() {
            let function_name = builder.build_global_string_ptr(
                &function.name,
                &format!(".recursion.name.{}", function.name),
            )?;
            builder.build_call(
                recursion_enter,
                &[
                    function_name.as_pointer_value().into(),
                    i32_type.const_int(512, false).into(),
                ],
                "recursion.enter",
            )?;
        }
        for instruction in &block.instructions {
            match instruction {""",
)

replace_once(
    codegen,
    """            Terminator::ReturnValue { value, value_type } => {
                let value = values
                    .get(value)
                    .copied()
                    .context("thiếu return SSA value")?;""",
    """            Terminator::ReturnValue { value, value_type } => {
                builder.build_call(recursion_leave, &[], "recursion.leave")?;
                let value = values
                    .get(value)
                    .copied()
                    .context("thiếu return SSA value")?;""",
)

replace_once(
    codegen,
    """            Terminator::Unreachable => {
                builder.build_unreachable()?;
            }""",
    """            Terminator::TailCallDirect {
                function,
                arguments,
                argument_types,
            } => {
                let target = llvm_functions
                    .get(function)
                    .copied()
                    .with_context(|| format!("unknown direct tail callee `{function}`"))?;
                let argv = main
                    .get_nth_param(2)
                    .context("JavaScript function thiếu argv cho tail call")?
                    .into_pointer_value();
                for (index, (argument, value_type)) in
                    arguments.iter().zip(argument_types).enumerate()
                {
                    let value = values
                        .get(argument)
                        .copied()
                        .context("thiếu tail-call argument SSA")?;
                    let dynamic = to_dynamic(
                        &builder,
                        value,
                        *value_type,
                        i8_type,
                        i64_type,
                        dynamic_type,
                    )?;
                    let slot = unsafe {
                        builder.build_gep(
                            dynamic_type,
                            argv,
                            &[i32_type.const_int(index as u64, false)],
                            "tail.argv.slot",
                        )?
                    };
                    builder.build_store(slot, dynamic)?;
                }
                let out = main
                    .get_nth_param(3)
                    .context("JavaScript function thiếu return out pointer")?
                    .into_pointer_value();
                builder.build_call(recursion_leave, &[], "recursion.leave.tail")?;
                let tail_call = builder.build_call(
                    target,
                    &[
                        ptr_type.const_null().into(),
                        i32_type.const_int(arguments.len() as u64, false).into(),
                        argv.into(),
                        out.into(),
                    ],
                    "tail.call.direct",
                )?;
                tail_call.set_tail_call(true);
                builder.build_return(None)?;
            }
            Terminator::Unreachable => {
                builder.build_unreachable()?;
            }""",
)

runtime = "crates/ecmora-runtime/native/object_runtime.c"
replace_once(
    runtime,
    """static EcmoraPromiseJob *microtask_head = NULL;
static EcmoraPromiseJob *microtask_tail = NULL;""",
    """static EcmoraPromiseJob *microtask_head = NULL;
static EcmoraPromiseJob *microtask_tail = NULL;

#if defined(_MSC_VER)
__declspec(thread) static uint32_t ecmora_recursion_depth = 0;
#else
static _Thread_local uint32_t ecmora_recursion_depth = 0;
#endif

void ecmora_recursion_enter(const char *function_name, uint32_t limit) {
    if (ecmora_recursion_depth >= limit) {
        fprintf(
            stderr,
            "Ecmora RangeError: maximum native recursion depth (%u) exceeded in %s\\n",
            limit,
            function_name == NULL ? "<anonymous>" : function_name
        );
        fflush(stderr);
        abort();
    }
    ecmora_recursion_depth += 1;
}

void ecmora_recursion_leave(void) {
    if (ecmora_recursion_depth != 0) {
        ecmora_recursion_depth -= 1;
    }
}""",
)
