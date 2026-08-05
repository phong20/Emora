use anyhow::{Result, anyhow, bail};
use ecmora_hir::{
    ArrayElement, AssignmentOperator, AssignmentTarget, BinaryOperator, Expression, ExpressionKind,
    ForInit, Function as HirFunction, LogicalOperator, MemberProperty, ObjectEntry, Program,
    Statement, StatementKind, UnaryOperator, UpdateOperator, VariableKind,
};
use ecmora_value::{BinaryOperator as SemBinary, RealmId, Value};

mod async_generator;
use async_generator::{GeneratorResumeAction, direct_yield};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet, VecDeque},
    rc::Rc,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PromiseRejectionOperation {
    Reject,
    Handle,
}

#[derive(Debug, Clone)]
pub struct PromiseRejectionEvent {
    pub promise: u64,
    pub reason: Value,
    pub operation: PromiseRejectionOperation,
    pub realm: RealmId,
}

pub type PromiseRejectionTracker = fn(&PromiseRejectionEvent) -> Result<()>;

#[derive(Clone, Copy)]
pub struct HostHooks {
    pub promise_rejection_tracker: PromiseRejectionTracker,
}

impl Default for HostHooks {
    fn default() -> Self {
        Self {
            promise_rejection_tracker: default_promise_rejection_tracker,
        }
    }
}

fn default_promise_rejection_tracker(event: &PromiseRejectionEvent) -> Result<()> {
    if event.operation == PromiseRejectionOperation::Reject {
        bail!(
            "unhandled promise rejection: {}",
            ecmora_value::to_string(&event.reason)
        )
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq)]
enum Completion {
    Normal,
    Break,
    Continue,
    Return(Value),
    Throw(Value),
}

#[derive(Debug, Clone)]
enum RuntimeValue {
    Js,
    Console,
    ConsoleLog,
    NumberConstructor,
    BigIntConstructor,
    StringConstructor,
    BooleanConstructor,
    ObjectConstructor,
    ObjectCreate,
    ObjectSetPrototypeOf,
    ObjectGetPrototypeOf,
    ProxyConstructor,
    PromiseConstructor(String),
    PromiseResolve(String),
    PromiseReject(String),
    PromiseThen(u64),
    PromiseCatch(u64),
    PromiseFinally(u64),
    Function(u64),
    FunctionWithThis(u64, Value),
    ClassConstructor(String),
    AsyncGeneratorNext(u64),
    AsyncGeneratorReturn(u64),
    AsyncGeneratorThrow(u64),
}

#[derive(Debug, Clone)]
struct Binding {
    kind: VariableKind,
    initialized: bool,
    value: Value,
}

type BindingRef = Rc<RefCell<Binding>>;
type Scope = HashMap<String, BindingRef>;

#[derive(Debug, Clone)]
enum FunctionKind {
    User(HirFunction),
    Resolve(u64),
    Reject(u64),
    AsyncResume { task: u64, rejected: bool },
    FinallyPreserve { original: Value, rejected: bool },
    Noop,
}

#[derive(Debug, Clone)]
struct FunctionObject {
    kind: FunctionKind,
    closure: Vec<Scope>,
    #[allow(dead_code)]
    realm: RealmId,
}

#[derive(Debug, Clone)]
enum PromiseState {
    Pending,
    Fulfilled(Value),
    Rejected(Value),
}

#[derive(Debug, Clone)]
struct PromiseReaction {
    fulfilled: Option<u64>,
    rejected: Option<u64>,
    next: u64,
    finally: bool,
}

#[derive(Debug, Clone)]
struct PromiseObject {
    state: PromiseState,
    reactions: Vec<PromiseReaction>,
    handled: bool,
    reported_unhandled: bool,
    constructor: String,
    realm: RealmId,
    object: Value,
}

#[derive(Debug, Clone)]
struct PromiseJob {
    reaction: PromiseReaction,
    settled: PromiseState,
}

#[derive(Debug, Clone)]
enum AsyncResumeAction {
    Discard,
    Initialize(String),
    Return,
}

#[derive(Debug, Clone)]
struct AsyncTask {
    statements: Vec<Statement>,
    next_statement: usize,
    scopes: Vec<Scope>,
    strict: bool,
    promise: u64,
    action: AsyncResumeAction,
}

#[derive(Debug, Clone)]
struct AsyncGeneratorRuntime {
    object: Value,
    statements: Vec<Statement>,
    next_statement: usize,
    scopes: Vec<Scope>,
    strict: bool,
    resume_action: Option<GeneratorResumeAction>,
    completed: bool,
}

#[derive(Default)]
struct Machine {
    functions: Vec<FunctionObject>,
    promises: Vec<PromiseObject>,
    jobs: VecDeque<PromiseJob>,
    async_tasks: Vec<Option<AsyncTask>>,
    promise_subclasses: HashMap<String, ecmora_hir::PromiseSubclass>,
    class_constructors: HashMap<String, Value>,
    async_generators: Vec<Option<AsyncGeneratorRuntime>>,
    current_realm: RealmId,
    host_hooks: HostHooks,
    host_events: VecDeque<PromiseRejectionEvent>,
    proxy_depth: usize,
}

fn binding(kind: VariableKind, initialized: bool, value: Value) -> BindingRef {
    Rc::new(RefCell::new(Binding {
        kind,
        initialized,
        value,
    }))
}

enum CallOutcome {
    Value(Value),
    Throw(Value),
}

impl Machine {
    fn register_function(&mut self, function: HirFunction, closure: Vec<Scope>) -> u64 {
        let id = self.functions.len() as u64;
        self.functions.push(FunctionObject {
            kind: FunctionKind::User(function),
            closure,
            realm: self.current_realm,
        });
        id
    }

    fn register_native_function(&mut self, kind: FunctionKind) -> u64 {
        let id = self.functions.len() as u64;
        self.functions.push(FunctionObject {
            kind,
            closure: Vec::new(),
            realm: self.current_realm,
        });
        id
    }

    fn promise_object_view(&self, value: &Value) -> Option<Value> {
        let Value::Promise(id) = value else {
            return None;
        };
        self.promises
            .get(*id as usize)
            .map(|promise| promise.object.clone())
    }

    fn class_name_from_value(&self, value: &Value) -> Option<String> {
        ecmora_value::class_constructor_slots(value).map(|slots| slots.name)
    }

    fn class_prototype(&self, name: &str) -> Option<ecmora_value::ObjectRef> {
        self.class_constructors
            .get(name)
            .and_then(ecmora_value::class_constructor_slots)
            .map(|slots| slots.prototype)
    }

    fn is_promise_subclass(&self, name: &str) -> bool {
        let mut current = name;
        loop {
            if current == "Promise" {
                return true;
            }
            let Some(parent) = self
                .promise_subclasses
                .get(current)
                .map(|class| class.parent.as_str())
            else {
                return false;
            };
            current = parent;
        }
    }

    fn predeclare_promise_subclasses(
        &mut self,
        subclasses: &[ecmora_hir::PromiseSubclass],
        scopes: &mut [Scope],
    ) -> Result<()> {
        let scope = scopes
            .first_mut()
            .ok_or_else(|| anyhow!("thiếu global scope"))?;
        for subclass in subclasses {
            if scope.contains_key(&subclass.name) {
                bail!("class `{}` được khai báo trùng", subclass.name)
            }
            scope.insert(
                subclass.name.clone(),
                binding(VariableKind::Const, false, Value::Undefined),
            );
        }
        Ok(())
    }

    fn install_promise_subclasses(
        &mut self,
        subclasses: &[ecmora_hir::PromiseSubclass],
        scopes: &mut Vec<Scope>,
    ) -> Result<()> {
        for subclass in subclasses {
            if self.class_constructors.contains_key(&subclass.name) {
                bail!("class `{}` được khai báo trùng", subclass.name)
            }
            if subclass.parent != "Promise"
                && !self.class_constructors.contains_key(&subclass.parent)
            {
                bail!(
                    "parent class `{}` của `{}` chưa được khởi tạo",
                    subclass.parent,
                    subclass.name
                )
            }

            let parent_constructor = self.class_constructors.get(&subclass.parent).cloned();
            let parent_prototype = parent_constructor
                .as_ref()
                .and_then(ecmora_value::class_constructor_slots)
                .map(|slots| slots.prototype);
            let prototype_value =
                ecmora_value::object_with_prototype_in_realm(parent_prototype, self.current_realm);
            let Value::Object(prototype) = &prototype_value else {
                unreachable!()
            };
            let constructor_value = ecmora_value::class_constructor_object(
                subclass.name.clone(),
                Some(subclass.parent.clone()),
                None,
                prototype.clone(),
                self.current_realm,
            );
            if let Some(Value::Object(parent)) = parent_constructor.as_ref() {
                ecmora_value::set_prototype(&constructor_value, Some(parent.clone()))?;
            }
            ecmora_value::set_property(
                &constructor_value,
                "name".to_owned(),
                Value::String(subclass.name.clone()),
            )?;
            ecmora_value::set_property(
                &constructor_value,
                "prototype".to_owned(),
                prototype_value.clone(),
            )?;
            ecmora_value::set_property(
                &prototype_value,
                "constructor".to_owned(),
                constructor_value.clone(),
            )?;

            let class_binding = scopes[0]
                .get(&subclass.name)
                .cloned()
                .ok_or_else(|| anyhow!("class binding `{}` chưa được predeclare", subclass.name))?;
            {
                let mut class_binding = class_binding.borrow_mut();
                class_binding.initialized = true;
                class_binding.value = constructor_value.clone();
            }
            self.class_constructors
                .insert(subclass.name.clone(), constructor_value.clone());

            let constructor_id = if let Some(constructor) = &subclass.constructor {
                Some(self.register_function(constructor.clone(), scopes.clone()))
            } else {
                None
            };

            for method in &subclass.methods {
                let super_base = if method.r#static {
                    parent_constructor.clone().unwrap_or(Value::Undefined)
                } else {
                    self.class_prototype(&subclass.parent)
                        .map(Value::Object)
                        .unwrap_or(Value::Null)
                };
                let mut closure = scopes.clone();
                let mut home_scope = HashMap::new();
                home_scope.insert(
                    "@super_base".to_owned(),
                    binding(VariableKind::Const, true, super_base),
                );
                closure.push(home_scope);
                let function = self.register_function(method.function.clone(), closure);
                let target = if method.r#static {
                    &constructor_value
                } else {
                    &prototype_value
                };
                match method.kind {
                    ecmora_hir::ClassMethodKind::Method => {
                        ecmora_value::set_property(
                            target,
                            method.key.clone(),
                            Value::Function(function),
                        )?;
                    }
                    ecmora_hir::ClassMethodKind::Get => {
                        ecmora_value::define_accessor(
                            target,
                            method.key.clone(),
                            Some(function),
                            None,
                        )?;
                    }
                    ecmora_hir::ClassMethodKind::Set => {
                        ecmora_value::define_accessor(
                            target,
                            method.key.clone(),
                            None,
                            Some(function),
                        )?;
                    }
                }
            }

            ecmora_value::set_object_kind(
                &constructor_value,
                ecmora_value::ObjectKind::ClassConstructor(ecmora_value::ClassConstructorSlots {
                    name: subclass.name.clone(),
                    parent: Some(subclass.parent.clone()),
                    realm: self.current_realm,
                    constructor: constructor_id,
                    prototype: prototype.clone(),
                }),
            )?;
        }
        Ok(())
    }

    fn new_promise_capability(&mut self, constructor: &str) -> Result<u64> {
        let promise = self.new_promise_with_constructor(constructor);
        let executor = self.register_native_function(FunctionKind::Noop);
        if let Some(override_value) = self.run_promise_constructor(
            constructor,
            promise,
            vec![Value::Function(executor)],
            true,
        )? {
            if override_value != Value::Promise(promise) {
                bail!(
                    "Promise capability constructor `{constructor}` returned \
                     a different object"
                )
            }
        }
        Ok(promise)
    }

    fn initialize_intrinsic_promise(
        &mut self,
        promise: u64,
        arguments: Vec<Value>,
        strict: bool,
    ) -> Result<()> {
        let Some(Value::Function(executor)) = arguments.first() else {
            bail!("Promise executor phải là function")
        };
        let resolve = self.register_native_function(FunctionKind::Resolve(promise));
        let reject = self.register_native_function(FunctionKind::Reject(promise));
        match self.call_function(
            *executor,
            vec![Value::Function(resolve), Value::Function(reject)],
            strict,
        )? {
            CallOutcome::Value(_) => {}
            CallOutcome::Throw(reason) => {
                self.settle(promise, PromiseState::Rejected(reason));
            }
        }
        Ok(())
    }

    fn run_promise_constructor(
        &mut self,
        constructor: &str,
        promise: u64,
        arguments: Vec<Value>,
        strict: bool,
    ) -> Result<Option<Value>> {
        if constructor == "Promise" {
            self.initialize_intrinsic_promise(promise, arguments, strict)?;
            return Ok(None);
        }
        let class = self
            .promise_subclasses
            .get(constructor)
            .cloned()
            .ok_or_else(|| anyhow!("Promise subclass `{constructor}` không tồn tại"))?;
        let Some(constructor_value) = self.class_constructors.get(constructor).cloned() else {
            bail!("class constructor object `{constructor}` chưa được cài đặt")
        };
        let constructor_id = ecmora_value::class_constructor_slots(&constructor_value)
            .and_then(|slots| slots.constructor);

        let Some(constructor_id) = constructor_id else {
            return self.run_promise_constructor(&class.parent, promise, arguments, strict);
        };

        let super_called = binding(VariableKind::Let, true, Value::Bool(false));
        let this_binding = binding(VariableKind::Const, true, Value::Promise(promise));
        let mut extra = HashMap::new();
        extra.insert("@this".to_owned(), this_binding.clone());
        extra.insert(
            "@derived_promise_id".to_owned(),
            binding(VariableKind::Const, true, Value::Number(promise as f64)),
        );
        extra.insert(
            "@super_constructor".to_owned(),
            binding(
                VariableKind::Const,
                true,
                Value::String(class.parent.clone()),
            ),
        );
        extra.insert("@derived_super_called".to_owned(), super_called.clone());
        extra.insert(
            "@super_base".to_owned(),
            binding(
                VariableKind::Const,
                true,
                self.class_prototype(&class.parent)
                    .map(Value::Object)
                    .unwrap_or(Value::Null),
            ),
        );

        let outcome = self.call_function_with_bindings(
            constructor_id,
            Value::Promise(promise),
            arguments,
            strict,
            Some(extra),
        )?;
        match outcome {
            CallOutcome::Throw(reason) => {
                bail!(
                    "constructor `{constructor}` threw {}",
                    ecmora_value::to_string(&reason)
                )
            }
            CallOutcome::Value(value) if ecmora_value::is_object_like(&value) => Ok(Some(value)),
            CallOutcome::Value(Value::Undefined)
                if matches!(&super_called.borrow().value, Value::Bool(true)) =>
            {
                let this_value = this_binding.borrow().value.clone();
                if this_value == Value::Promise(promise) {
                    Ok(None)
                } else {
                    Ok(Some(this_value))
                }
            }
            CallOutcome::Value(Value::Undefined) => {
                bail!(
                    "derived constructor `{constructor}` phải gọi super()                      hoặc return object"
                )
            }
            CallOutcome::Value(_) => {
                bail!("derived constructor chỉ được return object hoặc undefined")
            }
        }
    }

    fn iterator_result(&mut self, value: Value, done: bool) -> Result<Value> {
        let result = ecmora_value::object_with_prototype_in_realm(None, self.current_realm);
        ecmora_value::set_property(&result, "value".to_owned(), value)?;
        ecmora_value::set_property(&result, "done".to_owned(), Value::Bool(done))?;
        Ok(result)
    }

    fn create_async_generator(
        &mut self,
        definition: HirFunction,
        mut scopes: Vec<Scope>,
        strict: bool,
    ) -> Result<Value> {
        predeclare(&definition.body, &mut scopes, self)?;
        let id = self.async_generators.len() as u64;
        let object = ecmora_value::async_generator_object(id, self.current_realm);
        self.async_generators.push(Some(AsyncGeneratorRuntime {
            object: object.clone(),
            statements: definition.body,
            next_statement: 0,
            scopes,
            strict,
            resume_action: None,
            completed: false,
        }));
        Ok(object)
    }

    fn enqueue_async_generator(
        &mut self,
        id: u64,
        completion: ecmora_value::GeneratorCompletion,
    ) -> Result<Value> {
        let promise = self.new_promise();
        let object = self
            .async_generators
            .get(id as usize)
            .and_then(Option::as_ref)
            .map(|generator| generator.object.clone())
            .ok_or_else(|| anyhow!("async generator handle không hợp lệ"))?;
        ecmora_value::async_generator_enqueue(
            &object,
            ecmora_value::AsyncGeneratorRequest {
                completion,
                capability: promise,
            },
        )?;
        self.resume_async_generator(id)?;
        Ok(Value::Promise(promise))
    }

    fn resume_async_generator(&mut self, id: u64) -> Result<()> {
        let Some(mut generator) = self
            .async_generators
            .get_mut(id as usize)
            .and_then(Option::take)
        else {
            return Ok(());
        };
        let Some(request) = ecmora_value::async_generator_dequeue(&generator.object)? else {
            self.async_generators[id as usize] = Some(generator);
            return Ok(());
        };

        if generator.completed {
            match request.completion {
                ecmora_value::GeneratorCompletion::Throw(reason) => {
                    self.settle(request.capability, PromiseState::Rejected(reason));
                }
                ecmora_value::GeneratorCompletion::Normal(_) => {
                    let result = self.iterator_result(Value::Undefined, true)?;
                    self.settle(request.capability, PromiseState::Fulfilled(result));
                }
                ecmora_value::GeneratorCompletion::Return(value) => {
                    let result = self.iterator_result(value, true)?;
                    self.settle(request.capability, PromiseState::Fulfilled(result));
                }
            }
            self.async_generators[id as usize] = Some(generator);
            return Ok(());
        }

        match request.completion {
            ecmora_value::GeneratorCompletion::Throw(reason) => {
                generator.completed = true;
                ecmora_value::set_async_generator_state(
                    &generator.object,
                    ecmora_value::AsyncGeneratorState::Completed,
                )?;
                self.settle(request.capability, PromiseState::Rejected(reason));
                self.async_generators[id as usize] = Some(generator);
                return Ok(());
            }
            ecmora_value::GeneratorCompletion::Return(value) => {
                generator.completed = true;
                ecmora_value::set_async_generator_state(
                    &generator.object,
                    ecmora_value::AsyncGeneratorState::Completed,
                )?;
                let result = self.iterator_result(value, true)?;
                self.settle(request.capability, PromiseState::Fulfilled(result));
                self.async_generators[id as usize] = Some(generator);
                return Ok(());
            }
            ecmora_value::GeneratorCompletion::Normal(input) => {
                if let Some(action) = generator.resume_action.take() {
                    match action {
                        GeneratorResumeAction::Discard => {}
                        GeneratorResumeAction::Initialize(name) => {
                            let binding =
                                find_binding(&generator.scopes, &name).ok_or_else(|| {
                                    anyhow!("generator binding `{name}` không tồn tại")
                                })?;
                            let mut binding = binding.borrow_mut();
                            binding.initialized = true;
                            binding.value = input;
                        }
                        GeneratorResumeAction::Assign(target) => {
                            write_target(
                                &target,
                                input,
                                &mut generator.scopes,
                                generator.strict,
                                self,
                            )?;
                        }
                        GeneratorResumeAction::Return => {
                            generator.completed = true;
                            ecmora_value::set_async_generator_state(
                                &generator.object,
                                ecmora_value::AsyncGeneratorState::Completed,
                            )?;
                            let result = self.iterator_result(input, true)?;
                            self.settle(request.capability, PromiseState::Fulfilled(result));
                            self.async_generators[id as usize] = Some(generator);
                            return Ok(());
                        }
                    }
                }
            }
        }

        ecmora_value::set_async_generator_state(
            &generator.object,
            ecmora_value::AsyncGeneratorState::Executing,
        )?;
        while generator.next_statement < generator.statements.len() {
            let index = generator.next_statement;
            let statement = generator.statements[index].clone();
            if let Some((argument, action)) = direct_yield(&statement)? {
                let value = match argument {
                    Some(argument) => evaluate_expression(
                        &argument,
                        &mut generator.scopes,
                        generator.strict,
                        self,
                    )?,
                    None => Value::Undefined,
                };
                generator.next_statement += 1;
                generator.resume_action = Some(action);
                ecmora_value::set_async_generator_state(
                    &generator.object,
                    ecmora_value::AsyncGeneratorState::SuspendedYield,
                )?;
                let result = self.iterator_result(value, false)?;
                self.settle(request.capability, PromiseState::Fulfilled(result));
                self.async_generators[id as usize] = Some(generator);
                return Ok(());
            }

            generator.next_statement += 1;
            match execute_statement(&statement, &mut generator.scopes, generator.strict, self)? {
                Completion::Normal => {}
                Completion::Return(value) => {
                    generator.completed = true;
                    ecmora_value::set_async_generator_state(
                        &generator.object,
                        ecmora_value::AsyncGeneratorState::Completed,
                    )?;
                    let result = self.iterator_result(value, true)?;
                    self.settle(request.capability, PromiseState::Fulfilled(result));
                    self.async_generators[id as usize] = Some(generator);
                    return Ok(());
                }
                Completion::Throw(reason) => {
                    generator.completed = true;
                    ecmora_value::set_async_generator_state(
                        &generator.object,
                        ecmora_value::AsyncGeneratorState::Completed,
                    )?;
                    self.settle(request.capability, PromiseState::Rejected(reason));
                    self.async_generators[id as usize] = Some(generator);
                    return Ok(());
                }
                Completion::Break | Completion::Continue => {
                    bail!(
                        "break/continue vượt generator top-level; \
                         yield trong CFG cần continuation lowering"
                    )
                }
            }
        }

        generator.completed = true;
        ecmora_value::set_async_generator_state(
            &generator.object,
            ecmora_value::AsyncGeneratorState::Completed,
        )?;
        let result = self.iterator_result(Value::Undefined, true)?;
        self.settle(request.capability, PromiseState::Fulfilled(result));
        self.async_generators[id as usize] = Some(generator);
        Ok(())
    }

    fn is_primitive_value(value: &Value) -> bool {
        matches!(
            value,
            Value::Undefined
                | Value::Null
                | Value::Number(_)
                | Value::BigInt(_)
                | Value::Bool(_)
                | Value::String(_)
        )
    }

    fn call_coercion_method(
        &mut self,
        receiver: &Value,
        method: Value,
        arguments: Vec<Value>,
        strict: bool,
    ) -> Result<Option<Value>> {
        let Value::Function(method) = method else {
            return Ok(None);
        };
        match self.call_function_with_this(method, receiver.clone(), arguments, strict)? {
            CallOutcome::Value(value) if Self::is_primitive_value(&value) => Ok(Some(value)),
            CallOutcome::Value(_) => Ok(None),
            CallOutcome::Throw(reason) => {
                bail!(
                    "primitive coercion threw {}",
                    ecmora_value::to_string(&reason)
                )
            }
        }
    }

    fn to_primitive_value(&mut self, value: Value, hint: &str, strict: bool) -> Result<Value> {
        if Self::is_primitive_value(&value) {
            return Ok(value);
        }

        let exotic = self.get_property_value(&value, "@@toPrimitive", value.clone(), strict)?;
        if !matches!(exotic, Value::Undefined) {
            let Some(result) = self.call_coercion_method(
                &value,
                exotic,
                vec![Value::String(hint.to_owned())],
                strict,
            )?
            else {
                bail!("@@toPrimitive phải callable và trả primitive")
            };
            return Ok(result);
        }

        let order = if hint == "string" {
            ["toString", "valueOf"]
        } else {
            ["valueOf", "toString"]
        };
        let mut attempted_callable = false;
        for method in order {
            let method_value = self.get_property_value(&value, method, value.clone(), strict)?;
            attempted_callable |= matches!(&method_value, Value::Function(_));
            if let Some(result) =
                self.call_coercion_method(&value, method_value, Vec::new(), strict)?
            {
                return Ok(result);
            }
        }
        if attempted_callable {
            bail!("không thể convert object sang primitive")
        }

        if matches!(&value, Value::Array(_)) {
            return Ok(Value::String(ecmora_value::to_string(&value)));
        }
        if matches!(&value, Value::Object(_)) {
            return Ok(Value::String("[object Object]".to_owned()));
        }
        if matches!(&value, Value::Function(_)) {
            return Ok(Value::String("function () { [native code] }".to_owned()));
        }
        if matches!(&value, Value::Promise(_)) {
            return Ok(Value::String("[object Promise]".to_owned()));
        }
        Ok(value)
    }

    fn to_number_value(&mut self, value: Value, strict: bool) -> Result<f64> {
        let primitive = self.to_primitive_value(value, "number", strict)?;
        ecmora_value::to_number_checked(&primitive)
    }

    fn explicit_number_value(&mut self, value: Value, strict: bool) -> Result<f64> {
        let primitive = self.to_primitive_value(value, "number", strict)?;
        ecmora_value::explicit_number(&primitive)
    }

    fn to_numeric_value(&mut self, value: Value, strict: bool) -> Result<Value> {
        let primitive = self.to_primitive_value(value, "number", strict)?;
        Ok(match ecmora_value::to_numeric_primitive(&primitive)? {
            ecmora_value::Numeric::Number(value) => Value::Number(value),
            ecmora_value::Numeric::BigInt(value) => Value::BigInt(value),
        })
    }

    fn to_string_value(&mut self, value: Value, strict: bool) -> Result<String> {
        let primitive = self.to_primitive_value(value, "string", strict)?;
        Ok(ecmora_value::to_string(&primitive))
    }

    fn bigint_value(&mut self, value: Value, strict: bool) -> Result<Value> {
        let primitive = self.to_primitive_value(value, "number", strict)?;
        Ok(Value::BigInt(ecmora_value::bigint_from_primitive(
            &primitive,
        )?))
    }

    fn unary_value(
        &mut self,
        operator: UnaryOperator,
        value: Value,
        strict: bool,
    ) -> Result<Value> {
        if operator == UnaryOperator::Not {
            return Ok(Value::Bool(!ecmora_value::to_boolean(&value)));
        }
        let numeric = self.to_numeric_value(value, strict)?;
        ecmora_value::unary_checked(to_sem_unary(operator), numeric)
    }

    fn binary_value(
        &mut self,
        operator: BinaryOperator,
        left: Value,
        right: Value,
        strict: bool,
    ) -> Result<Value> {
        use BinaryOperator as Op;

        if matches!(
            operator,
            Op::StrictEqual | Op::StrictNotEqual | Op::In | Op::InstanceOf
        ) {
            return ecmora_value::binary(to_sem_binary(operator), left, right);
        }

        if matches!(operator, Op::Equal | Op::NotEqual) {
            let left_object = !Self::is_primitive_value(&left);
            let right_object = !Self::is_primitive_value(&right);
            let left = if left_object && !right_object {
                self.to_primitive_value(left, "default", strict)?
            } else {
                left
            };
            let right = if right_object && !left_object {
                self.to_primitive_value(right, "default", strict)?
            } else {
                right
            };
            return ecmora_value::binary(to_sem_binary(operator), left, right);
        }

        if matches!(
            operator,
            Op::LessThan | Op::LessEqual | Op::GreaterThan | Op::GreaterEqual
        ) {
            let left = self.to_primitive_value(left, "number", strict)?;
            let right = self.to_primitive_value(right, "number", strict)?;
            return ecmora_value::binary(to_sem_binary(operator), left, right);
        }

        if operator == Op::Add {
            let left = self.to_primitive_value(left, "default", strict)?;
            let right = self.to_primitive_value(right, "default", strict)?;
            return ecmora_value::binary(to_sem_binary(operator), left, right);
        }

        let left = self.to_numeric_value(left, strict)?;
        let right = self.to_numeric_value(right, strict)?;
        ecmora_value::binary(to_sem_binary(operator), left, right)
    }

    fn proxy_trap(&mut self, handler: &Value, name: &str, strict: bool) -> Result<Option<u64>> {
        let trap = self.get_property_value(handler, name, handler.clone(), strict)?;
        match trap {
            Value::Undefined => Ok(None),
            Value::Function(id) => Ok(Some(id)),
            _ => bail!("Proxy `{name}` trap phải là callable hoặc undefined"),
        }
    }

    fn call_proxy_trap(
        &mut self,
        trap: u64,
        handler: Value,
        arguments: Vec<Value>,
        strict: bool,
    ) -> Result<Value> {
        match self.call_function_with_this(trap, handler, arguments, strict)? {
            CallOutcome::Value(value) => Ok(value),
            CallOutcome::Throw(reason) => {
                bail!("Proxy trap threw {}", ecmora_value::to_string(&reason))
            }
        }
    }

    fn get_property_value(
        &mut self,
        object: &Value,
        key: &str,
        receiver: Value,
        strict: bool,
    ) -> Result<Value> {
        let promise_object = self.promise_object_view(object);
        let object = promise_object.as_ref().unwrap_or(object);
        if let Some(slots) = ecmora_value::proxy_slots(object) {
            if slots.revoked {
                bail!("không thể thực hiện [[Get]] trên Proxy đã revoke")
            }
            if self.proxy_depth >= 256 {
                bail!("Proxy trap recursion limit exceeded")
            }
            self.proxy_depth += 1;
            let result = (|| {
                if let Some(trap) = self.proxy_trap(&slots.handler, "get", strict)? {
                    return self.call_proxy_trap(
                        trap,
                        slots.handler,
                        vec![slots.target, Value::String(key.to_owned()), receiver],
                        strict,
                    );
                }
                self.get_property_value(&slots.target, key, receiver, strict)
            })();
            self.proxy_depth -= 1;
            return result;
        }

        if let Some(getter) =
            ecmora_value::get_accessor(object, key).and_then(|descriptor| descriptor.getter)
        {
            return match self.call_function_with_this(getter, receiver, Vec::new(), strict)? {
                CallOutcome::Value(value) => Ok(value),
                CallOutcome::Throw(value) => {
                    bail!("getter threw {}", ecmora_value::to_string(&value))
                }
            };
        }
        Ok(ecmora_value::get_property(object, key))
    }

    fn set_property_value(
        &mut self,
        object: &Value,
        key: String,
        value: Value,
        receiver: Value,
        strict: bool,
    ) -> Result<Value> {
        let promise_object = self.promise_object_view(object);
        let object = promise_object.as_ref().unwrap_or(object);
        if let Some(slots) = ecmora_value::proxy_slots(object) {
            if slots.revoked {
                bail!("không thể thực hiện [[Set]] trên Proxy đã revoke")
            }
            if self.proxy_depth >= 256 {
                bail!("Proxy trap recursion limit exceeded")
            }
            self.proxy_depth += 1;
            let result = (|| {
                if let Some(trap) = self.proxy_trap(&slots.handler, "set", strict)? {
                    let accepted = self.call_proxy_trap(
                        trap,
                        slots.handler,
                        vec![
                            slots.target.clone(),
                            Value::String(key.clone()),
                            value.clone(),
                            receiver,
                        ],
                        strict,
                    )?;
                    if !ecmora_value::to_boolean(&accepted) {
                        if strict {
                            bail!("Proxy set trap returned false")
                        }
                        return Ok(value);
                    }
                    if let Some(current) =
                        ecmora_value::is_non_writable_non_configurable_data_property(
                            &slots.target,
                            &key,
                        )
                    {
                        if !ecmora_value::same_value(&current, &value) {
                            bail!("Proxy set trap violated non-writable non-configurable invariant")
                        }
                    }
                    return Ok(value);
                }
                self.set_property_value(&slots.target, key, value, receiver, strict)
            })();
            self.proxy_depth -= 1;
            return result;
        }

        if let Some(setter) =
            ecmora_value::get_accessor(object, &key).and_then(|descriptor| descriptor.setter)
        {
            return match self.call_function_with_this(setter, receiver, vec![value], strict)? {
                CallOutcome::Value(value) => Ok(value),
                CallOutcome::Throw(value) => {
                    bail!("setter threw {}", ecmora_value::to_string(&value))
                }
            };
        }
        ecmora_value::set_property(object, key, value)
    }

    fn has_property_value(&mut self, object: &Value, key: &str, strict: bool) -> Result<bool> {
        let promise_object = self.promise_object_view(object);
        let object = promise_object.as_ref().unwrap_or(object);
        if let Some(slots) = ecmora_value::proxy_slots(object) {
            if slots.revoked {
                bail!("không thể thực hiện [[HasProperty]] trên Proxy đã revoke")
            }
            if self.proxy_depth >= 256 {
                bail!("Proxy trap recursion limit exceeded")
            }
            self.proxy_depth += 1;
            let result = (|| {
                if let Some(trap) = self.proxy_trap(&slots.handler, "has", strict)? {
                    let visible = ecmora_value::to_boolean(&self.call_proxy_trap(
                        trap,
                        slots.handler,
                        vec![slots.target.clone(), Value::String(key.to_owned())],
                        strict,
                    )?);
                    if !visible
                        && ecmora_value::non_configurable_own_keys(&slots.target).contains(key)
                    {
                        bail!("Proxy has trap cannot hide non-configurable property")
                    }
                    return Ok(visible);
                }
                self.has_property_value(&slots.target, key, strict)
            })();
            self.proxy_depth -= 1;
            return result;
        }
        Ok(ecmora_value::has_property(object, key))
    }

    fn delete_property_value(&mut self, object: &Value, key: &str, strict: bool) -> Result<bool> {
        let promise_object = self.promise_object_view(object);
        let object = promise_object.as_ref().unwrap_or(object);
        if let Some(slots) = ecmora_value::proxy_slots(object) {
            if slots.revoked {
                bail!("không thể thực hiện [[Delete]] trên Proxy đã revoke")
            }
            if self.proxy_depth >= 256 {
                bail!("Proxy trap recursion limit exceeded")
            }
            self.proxy_depth += 1;
            let result = (|| {
                if let Some(trap) = self.proxy_trap(&slots.handler, "deleteProperty", strict)? {
                    let deleted = ecmora_value::to_boolean(&self.call_proxy_trap(
                        trap,
                        slots.handler,
                        vec![slots.target.clone(), Value::String(key.to_owned())],
                        strict,
                    )?);
                    if deleted
                        && ecmora_value::non_configurable_own_keys(&slots.target).contains(key)
                    {
                        bail!("Proxy deleteProperty trap cannot delete non-configurable property")
                    }
                    return Ok(deleted);
                }
                self.delete_property_value(&slots.target, key, strict)
            })();
            self.proxy_depth -= 1;
            return result;
        }
        Ok(ecmora_value::delete_property(object, key))
    }

    fn own_property_keys_value(&mut self, object: &Value, strict: bool) -> Result<Vec<String>> {
        let promise_object = self.promise_object_view(object);
        let object = promise_object.as_ref().unwrap_or(object);
        if let Some(slots) = ecmora_value::proxy_slots(object) {
            if slots.revoked {
                bail!("không thể thực hiện [[OwnPropertyKeys]] trên Proxy đã revoke")
            }
            if self.proxy_depth >= 256 {
                bail!("Proxy trap recursion limit exceeded")
            }
            self.proxy_depth += 1;
            let result = (|| {
                let Some(trap) = self.proxy_trap(&slots.handler, "ownKeys", strict)? else {
                    return self.own_property_keys_value(&slots.target, strict);
                };
                let trap_result =
                    self.call_proxy_trap(trap, slots.handler, vec![slots.target.clone()], strict)?;
                let Value::Array(keys) = trap_result else {
                    bail!("Proxy ownKeys trap phải trả Array")
                };
                let entries = keys.borrow().clone();
                let mut output = Vec::with_capacity(entries.len());
                let mut unique = HashSet::new();
                for entry in entries {
                    let Some(Value::String(key)) = entry else {
                        bail!("Proxy ownKeys chỉ hỗ trợ string property keys")
                    };
                    if !unique.insert(key.clone()) {
                        bail!("Proxy ownKeys trap trả duplicate key `{key}`")
                    }
                    output.push(key);
                }
                for key in ecmora_value::non_configurable_own_keys(&slots.target) {
                    if !unique.contains(&key) {
                        bail!("Proxy ownKeys trap thiếu non-configurable key `{key}`")
                    }
                }
                if !ecmora_value::is_extensible(&slots.target) {
                    let target_keys = ecmora_value::own_property_keys_all(&slots.target)
                        .into_iter()
                        .collect::<HashSet<_>>();
                    if target_keys != unique {
                        bail!("Proxy ownKeys trap phải trả đúng key set của non-extensible target")
                    }
                }
                Ok(output)
            })();
            self.proxy_depth -= 1;
            return result;
        }
        Ok(ecmora_value::own_property_keys(object))
    }

    fn new_promise(&mut self) -> u64 {
        self.new_promise_with_constructor("Promise")
    }

    fn new_promise_with_constructor(&mut self, constructor: &str) -> u64 {
        let id = self.promises.len() as u64;
        let prototype = self.class_prototype(constructor);
        let object = ecmora_value::object_with_prototype_in_realm(prototype, self.current_realm);
        self.promises.push(PromiseObject {
            state: PromiseState::Pending,
            reactions: Vec::new(),
            handled: false,
            reported_unhandled: false,
            constructor: constructor.to_owned(),
            realm: self.current_realm,
            object,
        });
        id
    }

    fn promise_species(&self, constructor: &str) -> String {
        self.promise_subclasses
            .get(constructor)
            .and_then(|class| class.species.clone())
            .unwrap_or_else(|| constructor.to_owned())
    }

    fn is_promise_constructor(&self, name: &str) -> bool {
        name == "Promise" || self.promise_subclasses.contains_key(name)
    }

    fn promise_resolve(&mut self, value: Value) -> Result<Value> {
        self.promise_resolve_with_constructor("Promise", value)
    }

    fn promise_resolve_with_constructor(
        &mut self,
        constructor: &str,
        value: Value,
    ) -> Result<Value> {
        if let Value::Promise(id) = value {
            if self.promises[id as usize].constructor == constructor {
                return Ok(Value::Promise(id));
            }
        }
        let target = self.new_promise_capability(constructor)?;
        self.resolve_into(target, value)?;
        Ok(Value::Promise(target))
    }

    fn promise_reject_with_constructor(
        &mut self,
        constructor: &str,
        value: Value,
    ) -> Result<Value> {
        let target = self.new_promise_capability(constructor)?;
        self.settle(target, PromiseState::Rejected(value));
        Ok(Value::Promise(target))
    }

    fn settle(&mut self, id: u64, state: PromiseState) {
        let promise = &mut self.promises[id as usize];
        if !matches!(promise.state, PromiseState::Pending) {
            return;
        }
        promise.state = state.clone();
        for reaction in std::mem::take(&mut promise.reactions) {
            self.jobs.push_back(PromiseJob {
                reaction,
                settled: state.clone(),
            });
        }
    }

    fn construct_promise_with_constructor(
        &mut self,
        constructor: &str,
        arguments: Vec<Value>,
        strict: bool,
    ) -> Result<Value> {
        let promise = self.new_promise_with_constructor(constructor);
        let override_value =
            self.run_promise_constructor(constructor, promise, arguments, strict)?;
        Ok(override_value.unwrap_or(Value::Promise(promise)))
    }

    fn call_as_expression(
        &mut self,
        id: u64,
        arguments: Vec<Value>,
        strict: bool,
    ) -> Result<Value> {
        match self.call_function(id, arguments, strict)? {
            CallOutcome::Value(value) => Ok(value),
            CallOutcome::Throw(value) => bail!("uncaught {}", ecmora_value::to_string(&value)),
        }
    }

    fn call_function(
        &mut self,
        id: u64,
        arguments: Vec<Value>,
        strict: bool,
    ) -> Result<CallOutcome> {
        self.call_function_with_this(id, Value::Undefined, arguments, strict)
    }

    fn call_function_with_this(
        &mut self,
        id: u64,
        this_value: Value,
        arguments: Vec<Value>,
        strict: bool,
    ) -> Result<CallOutcome> {
        self.call_function_with_bindings(id, this_value, arguments, strict, None)
    }

    fn call_function_with_bindings(
        &mut self,
        id: u64,
        this_value: Value,
        arguments: Vec<Value>,
        strict: bool,
        extra_scope: Option<Scope>,
    ) -> Result<CallOutcome> {
        let function = self
            .functions
            .get(id as usize)
            .cloned()
            .ok_or_else(|| anyhow!("function handle không hợp lệ"))?;
        match function.kind {
            FunctionKind::Resolve(promise) => {
                let value = arguments.first().cloned().unwrap_or(Value::Undefined);
                self.resolve_into(promise, value)?;
                Ok(CallOutcome::Value(Value::Undefined))
            }
            FunctionKind::Reject(promise) => {
                self.settle(
                    promise,
                    PromiseState::Rejected(arguments.first().cloned().unwrap_or(Value::Undefined)),
                );
                Ok(CallOutcome::Value(Value::Undefined))
            }
            FunctionKind::AsyncResume { task, rejected } => {
                let value = arguments.first().cloned().unwrap_or(Value::Undefined);
                self.resume_async(task, value, rejected)?;
                Ok(CallOutcome::Value(Value::Undefined))
            }
            FunctionKind::FinallyPreserve { original, rejected } => {
                if rejected {
                    Ok(CallOutcome::Throw(original))
                } else {
                    Ok(CallOutcome::Value(original))
                }
            }
            FunctionKind::Noop => Ok(CallOutcome::Value(Value::Undefined)),
            FunctionKind::User(definition) => {
                if let Some(error) = &definition.lowering_error {
                    bail!("function reachable nhưng frontend không hạ được body: {error}")
                }
                let is_async = definition.r#async;
                let mut scopes = function.closure;
                let mut call_scope = HashMap::new();
                call_scope.insert(
                    "@this".to_owned(),
                    binding(VariableKind::Const, true, this_value),
                );
                for (index, parameter) in definition.parameters.iter().enumerate() {
                    call_scope.insert(
                        parameter.clone(),
                        binding(
                            VariableKind::Let,
                            true,
                            arguments.get(index).cloned().unwrap_or(Value::Undefined),
                        ),
                    );
                }
                if let Some(name) = &definition.name {
                    call_scope
                        .entry(name.clone())
                        .or_insert_with(|| binding(VariableKind::Const, true, Value::Function(id)));
                }
                if let Some(extra_scope) = extra_scope {
                    call_scope.extend(extra_scope);
                }
                scopes.push(call_scope);
                if definition.generator {
                    if !is_async {
                        bail!("sync generator execution chưa được bật")
                    }
                    let generator = self.create_async_generator(definition, scopes, strict)?;
                    return Ok(CallOutcome::Value(generator));
                }
                if is_async {
                    let promise = self.new_promise();
                    predeclare(&definition.body, &mut scopes, self)?;
                    self.run_async_body(definition.body, 0, scopes, strict, promise)?;
                    return Ok(CallOutcome::Value(Value::Promise(promise)));
                }
                let completion = execute_scope(&definition.body, &mut scopes, strict, self)?;
                let outcome = match completion {
                    Completion::Normal => CallOutcome::Value(Value::Undefined),
                    Completion::Return(value) => CallOutcome::Value(value),
                    Completion::Throw(value) => CallOutcome::Throw(value),
                    Completion::Break | Completion::Continue => {
                        bail!("break/continue vượt qua function boundary")
                    }
                };
                Ok(outcome)
            }
        }
    }

    fn run_async_body(
        &mut self,
        statements: Vec<Statement>,
        start: usize,
        mut scopes: Vec<Scope>,
        strict: bool,
        promise: u64,
    ) -> Result<()> {
        for index in start..statements.len() {
            if let Some((argument, action)) = direct_await(&statements[index]) {
                let awaited = evaluate_expression(&argument, &mut scopes, strict, self)?;
                let source = match awaited {
                    Value::Promise(id) => id,
                    value => {
                        let Value::Promise(id) = self.promise_resolve(value)? else {
                            unreachable!()
                        };
                        id
                    }
                };
                let task = self.async_tasks.len() as u64;
                self.async_tasks.push(Some(AsyncTask {
                    statements,
                    next_statement: index + 1,
                    scopes,
                    strict,
                    promise,
                    action,
                }));
                let fulfilled = self.register_native_function(FunctionKind::AsyncResume {
                    task,
                    rejected: false,
                });
                let rejected = self.register_native_function(FunctionKind::AsyncResume {
                    task,
                    rejected: true,
                });
                let ignored = self.new_promise();
                self.attach_reaction(
                    source,
                    PromiseReaction {
                        fulfilled: Some(fulfilled),
                        rejected: Some(rejected),
                        next: ignored,
                        finally: false,
                    },
                );
                return Ok(());
            }
            match execute_statement(&statements[index], &mut scopes, strict, self)? {
                Completion::Normal => {}
                Completion::Return(value) => {
                    self.resolve_into(promise, value)?;
                    return Ok(());
                }
                Completion::Throw(value) => {
                    self.settle(promise, PromiseState::Rejected(value));
                    return Ok(());
                }
                Completion::Break | Completion::Continue => {
                    bail!("break/continue vượt qua async function boundary")
                }
            }
        }
        self.settle(promise, PromiseState::Fulfilled(Value::Undefined));
        Ok(())
    }

    fn resume_async(&mut self, task: u64, value: Value, rejected: bool) -> Result<()> {
        let Some(task) = self
            .async_tasks
            .get_mut(task as usize)
            .and_then(Option::take)
        else {
            return Ok(());
        };
        if rejected {
            self.settle(task.promise, PromiseState::Rejected(value));
            return Ok(());
        }
        match task.action {
            AsyncResumeAction::Discard => {}
            AsyncResumeAction::Return => {
                self.resolve_into(task.promise, value)?;
                return Ok(());
            }
            AsyncResumeAction::Initialize(name) => {
                let binding = find_binding(&task.scopes, &name)
                    .ok_or_else(|| anyhow!("async binding `{name}` không tồn tại"))?;
                let mut binding = binding.borrow_mut();
                binding.initialized = true;
                binding.value = value;
            }
        }
        self.run_async_body(
            task.statements,
            task.next_statement,
            task.scopes,
            task.strict,
            task.promise,
        )
    }

    fn resolve_into(&mut self, promise: u64, value: Value) -> Result<()> {
        if !matches!(self.promises[promise as usize].state, PromiseState::Pending) {
            return Ok(());
        }

        if let Value::Promise(source) = value {
            if source == promise {
                self.settle(
                    promise,
                    PromiseState::Rejected(Value::String(
                        "Chaining cycle detected for promise".to_owned(),
                    )),
                );
            } else {
                self.attach_reaction(
                    source,
                    PromiseReaction {
                        fulfilled: None,
                        rejected: None,
                        next: promise,
                        finally: false,
                    },
                );
            }
            return Ok(());
        }

        let then = match &value {
            Value::Object(_) | Value::Array(_) => {
                match self.get_property_value(&value, "then", value.clone(), true) {
                    Ok(value) => value,
                    Err(error) => {
                        self.settle(
                            promise,
                            PromiseState::Rejected(Value::String(format!("{error:#}"))),
                        );
                        return Ok(());
                    }
                }
            }
            _ => Value::Undefined,
        };
        let Value::Function(then) = then else {
            self.settle(promise, PromiseState::Fulfilled(value));
            return Ok(());
        };

        let resolve = self.register_native_function(FunctionKind::Resolve(promise));
        let reject = self.register_native_function(FunctionKind::Reject(promise));
        match self.call_function_with_this(
            then,
            value,
            vec![Value::Function(resolve), Value::Function(reject)],
            true,
        )? {
            CallOutcome::Value(_) => {}
            CallOutcome::Throw(reason) => {
                // First-settlement-wins is enforced by settle/resolve_into.
                self.settle(promise, PromiseState::Rejected(reason));
            }
        }
        Ok(())
    }

    fn promise_then(
        &mut self,
        source: u64,
        fulfilled: Option<u64>,
        rejected: Option<u64>,
        finally: bool,
    ) -> Result<Value> {
        if source as usize >= self.promises.len() {
            bail!("promise handle không hợp lệ")
        }
        let constructor = self.promises[source as usize].constructor.clone();
        let species = self.promise_species(&constructor);
        let next = self.new_promise_capability(&species)?;
        self.attach_reaction(
            source,
            PromiseReaction {
                fulfilled,
                rejected,
                next,
                finally,
            },
        );
        Ok(Value::Promise(next))
    }

    fn attach_reaction(&mut self, source: u64, reaction: PromiseReaction) {
        // ECMAScript marks a promise handled when PerformPromiseThen attaches
        // any reaction. If the host already observed the rejection, queue the
        // matching `handle` notification.
        let late_handle = {
            let promise = &mut self.promises[source as usize];
            let event = if promise.reported_unhandled {
                match &promise.state {
                    PromiseState::Rejected(reason) => Some(PromiseRejectionEvent {
                        promise: source,
                        reason: reason.clone(),
                        operation: PromiseRejectionOperation::Handle,
                        realm: promise.realm,
                    }),
                    _ => None,
                }
            } else {
                None
            };
            if event.is_some() {
                promise.reported_unhandled = false;
            }
            promise.handled = true;
            event
        };
        if let Some(event) = late_handle {
            self.host_events.push_back(event);
        }

        let state = self.promises[source as usize].state.clone();
        if matches!(state, PromiseState::Pending) {
            self.promises[source as usize].reactions.push(reaction);
        } else {
            self.jobs.push_back(PromiseJob {
                reaction,
                settled: state,
            });
        }
    }

    fn drain_jobs(&mut self) -> Result<()> {
        while let Some(job) = self.jobs.pop_front() {
            self.run_job(job)?;
        }

        for (id, promise) in self.promises.iter_mut().enumerate() {
            if let PromiseState::Rejected(reason) = &promise.state {
                if !promise.handled && !promise.reported_unhandled {
                    promise.reported_unhandled = true;
                    self.host_events.push_back(PromiseRejectionEvent {
                        promise: id as u64,
                        reason: reason.clone(),
                        operation: PromiseRejectionOperation::Reject,
                        realm: promise.realm,
                    });
                }
            }
        }

        while let Some(event) = self.host_events.pop_front() {
            (self.host_hooks.promise_rejection_tracker)(&event)?;
        }
        Ok(())
    }

    fn run_job(&mut self, job: PromiseJob) -> Result<()> {
        let (callback, input, rejected) = match &job.settled {
            PromiseState::Fulfilled(value) => (job.reaction.fulfilled, value.clone(), false),
            PromiseState::Rejected(value) => (job.reaction.rejected, value.clone(), true),
            PromiseState::Pending => return Ok(()),
        };
        let Some(callback) = callback else {
            self.settle(
                job.reaction.next,
                if rejected {
                    PromiseState::Rejected(input)
                } else {
                    PromiseState::Fulfilled(input)
                },
            );
            return Ok(());
        };
        let arguments = if job.reaction.finally {
            Vec::new()
        } else {
            vec![input.clone()]
        };
        match self.call_function(callback, arguments, true)? {
            CallOutcome::Throw(reason) => {
                self.settle(job.reaction.next, PromiseState::Rejected(reason));
            }
            CallOutcome::Value(value) if job.reaction.finally => {
                if let Value::Promise(source) = value {
                    let preserve = self.register_native_function(FunctionKind::FinallyPreserve {
                        original: input,
                        rejected,
                    });
                    self.attach_reaction(
                        source,
                        PromiseReaction {
                            fulfilled: Some(preserve),
                            rejected: None,
                            next: job.reaction.next,
                            finally: false,
                        },
                    );
                } else {
                    self.settle(
                        job.reaction.next,
                        if rejected {
                            PromiseState::Rejected(input)
                        } else {
                            PromiseState::Fulfilled(input)
                        },
                    );
                }
            }
            CallOutcome::Value(Value::Promise(source)) => self.attach_reaction(
                source,
                PromiseReaction {
                    fulfilled: None,
                    rejected: None,
                    next: job.reaction.next,
                    finally: false,
                },
            ),
            CallOutcome::Value(value) => {
                self.settle(job.reaction.next, PromiseState::Fulfilled(value));
            }
        }
        Ok(())
    }

    fn await_value(&mut self, value: Value) -> Result<Value> {
        let promise = match value {
            Value::Promise(id) => id,
            value => {
                let Value::Promise(id) = self.promise_resolve(value)? else {
                    unreachable!()
                };
                id
            }
        };
        while matches!(self.promises[promise as usize].state, PromiseState::Pending)
            && !self.jobs.is_empty()
        {
            if let Some(job) = self.jobs.pop_front() {
                self.run_job(job)?;
            }
        }
        match self.promises[promise as usize].state.clone() {
            PromiseState::Fulfilled(value) => Ok(value),
            PromiseState::Rejected(value) => {
                bail!("await rejected: {}", ecmora_value::to_string(&value))
            }
            PromiseState::Pending => bail!("await trên Promise pending chưa có continuation job"),
        }
    }
}

fn direct_await(statement: &Statement) -> Option<(Expression, AsyncResumeAction)> {
    match &statement.kind {
        StatementKind::Expression(Expression {
            kind: ExpressionKind::Await(argument),
            ..
        }) => Some(((**argument).clone(), AsyncResumeAction::Discard)),
        StatementKind::Return(Some(Expression {
            kind: ExpressionKind::Await(argument),
            ..
        })) => Some(((**argument).clone(), AsyncResumeAction::Return)),
        StatementKind::VariableDeclaration { declarations, .. } if declarations.len() == 1 => {
            let declaration = &declarations[0];
            let ExpressionKind::Await(argument) = &declaration.init.as_ref()?.kind else {
                return None;
            };
            Some((
                (**argument).clone(),
                AsyncResumeAction::Initialize(declaration.name.clone()),
            ))
        }
        _ => None,
    }
}

pub fn execute(program: &Program) -> Result<()> {
    execute_in_realm_with_host_hooks(program, RealmId::ROOT, HostHooks::default())
}

pub fn execute_with_host_hooks(program: &Program, hooks: HostHooks) -> Result<()> {
    execute_in_realm_with_host_hooks(program, RealmId::ROOT, hooks)
}

pub fn execute_in_realm_with_host_hooks(
    program: &Program,
    realm: RealmId,
    hooks: HostHooks,
) -> Result<()> {
    let mut machine = Machine {
        current_realm: realm,
        host_hooks: hooks,
        ..Machine::default()
    };
    machine.promise_subclasses = program
        .promise_subclasses
        .iter()
        .cloned()
        .map(|class| (class.name.clone(), class))
        .collect();
    let mut scopes = vec![HashMap::new()];
    machine.predeclare_promise_subclasses(&program.promise_subclasses, &mut scopes)?;
    predeclare(&program.statements, &mut scopes, &mut machine)?;
    machine.install_promise_subclasses(&program.promise_subclasses, &mut scopes)?;
    match execute_predeclared_scope(
        &program.statements,
        &mut scopes,
        program.strict,
        &mut machine,
    )? {
        Completion::Normal => Ok::<(), anyhow::Error>(()),
        _ => bail!("break/continue không nằm trong loop hoặc switch"),
    }?;
    machine.drain_jobs()
}

fn execute_scope(
    statements: &[Statement],
    scopes: &mut Vec<Scope>,
    strict: bool,
    machine: &mut Machine,
) -> Result<Completion> {
    predeclare(statements, scopes, machine)?;
    execute_predeclared_scope(statements, scopes, strict, machine)
}

fn execute_predeclared_scope(
    statements: &[Statement],
    scopes: &mut Vec<Scope>,
    strict: bool,
    machine: &mut Machine,
) -> Result<Completion> {
    for statement in statements {
        let completion = execute_statement(statement, scopes, strict, machine)?;
        if completion != Completion::Normal {
            return Ok(completion);
        }
    }
    Ok(Completion::Normal)
}

fn predeclare(statements: &[Statement], scopes: &mut [Scope], machine: &mut Machine) -> Result<()> {
    let scope = scopes.last_mut().unwrap();
    for statement in statements {
        if let StatementKind::VariableDeclaration { kind, declarations } = &statement.kind {
            for declaration in declarations {
                if scope.contains_key(&declaration.name) {
                    bail!(
                        "identifier `{}` được khai báo trùng trong cùng lexical scope",
                        declaration.name
                    )
                }
                scope.insert(
                    declaration.name.clone(),
                    binding(*kind, false, Value::Undefined),
                );
            }
        }
        if let StatementKind::FunctionDeclaration(function) = &statement.kind {
            let name = function.name.as_ref().unwrap();
            if scope.contains_key(name) {
                bail!("identifier `{name}` được khai báo trùng trong cùng lexical scope")
            }
            scope.insert(
                name.clone(),
                binding(VariableKind::Const, false, Value::Undefined),
            );
        }
    }
    for statement in statements {
        if let StatementKind::FunctionDeclaration(function) = &statement.kind {
            let name = function.name.as_ref().unwrap();
            let id = machine.register_function(function.clone(), scopes.to_vec());
            let binding = scopes.last().unwrap().get(name).unwrap();
            let mut binding = binding.borrow_mut();
            binding.initialized = true;
            binding.value = Value::Function(id);
        }
    }
    Ok(())
}

fn execute_statement(
    statement: &Statement,
    scopes: &mut Vec<Scope>,
    strict: bool,
    machine: &mut Machine,
) -> Result<Completion> {
    match &statement.kind {
        StatementKind::Expression(expression) => {
            evaluate_expression(expression, scopes, strict, machine)?;
        }
        StatementKind::Block(statements) => {
            scopes.push(HashMap::new());
            let result = execute_scope(statements, scopes, strict, machine);
            scopes.pop();
            return result;
        }
        StatementKind::If {
            test,
            consequent,
            alternate,
        } => {
            if ecmora_value::to_boolean(&evaluate_expression(test, scopes, strict, machine)?) {
                return execute_statement(consequent, scopes, strict, machine);
            }
            if let Some(alternate) = alternate {
                return execute_statement(alternate, scopes, strict, machine);
            }
        }
        StatementKind::While { test, body } => {
            while ecmora_value::to_boolean(&evaluate_expression(test, scopes, strict, machine)?) {
                match execute_statement(body, scopes, strict, machine)? {
                    Completion::Break => break,
                    Completion::Continue | Completion::Normal => {}
                    completion => return Ok(completion),
                }
            }
        }
        StatementKind::DoWhile { body, test } => loop {
            match execute_statement(body, scopes, strict, machine)? {
                Completion::Break => break,
                Completion::Continue | Completion::Normal => {}
                completion => return Ok(completion),
            }
            if !ecmora_value::to_boolean(&evaluate_expression(test, scopes, strict, machine)?) {
                break;
            }
        },
        StatementKind::For {
            init,
            test,
            update,
            body,
        } => {
            scopes.push(HashMap::new());
            let result = (|| -> Result<Completion> {
                if let Some(init) = init {
                    match init {
                        ForInit::Expression(expression) => {
                            evaluate_expression(expression, scopes, strict, machine)?;
                        }
                        ForInit::VariableDeclaration { kind, declarations } => {
                            for declaration in declarations {
                                if scopes.last().unwrap().contains_key(&declaration.name) {
                                    bail!("identifier `{}` được khai báo trùng", declaration.name)
                                }
                                scopes.last_mut().unwrap().insert(
                                    declaration.name.clone(),
                                    binding(*kind, false, Value::Undefined),
                                );
                            }
                            for declaration in declarations {
                                let value = match &declaration.init {
                                    Some(init) => {
                                        evaluate_expression(init, scopes, strict, machine)?
                                    }
                                    None => Value::Undefined,
                                };
                                let binding = find_binding_mut(scopes, &declaration.name).unwrap();
                                let mut binding = binding.borrow_mut();
                                binding.initialized = true;
                                binding.value = value;
                            }
                        }
                    }
                }
                loop {
                    if let Some(test) = test {
                        if !ecmora_value::to_boolean(&evaluate_expression(
                            test, scopes, strict, machine,
                        )?) {
                            break;
                        }
                    }
                    match execute_statement(body, scopes, strict, machine)? {
                        Completion::Break => break,
                        Completion::Continue | Completion::Normal => {}
                        completion => return Ok(completion),
                    }
                    if let Some(update) = update {
                        evaluate_expression(update, scopes, strict, machine)?;
                    }
                }
                Ok(Completion::Normal)
            })();
            scopes.pop();
            result?;
        }
        StatementKind::ForIn {
            name,
            kind,
            right,
            body,
        } => {
            let value = evaluate_expression(right, scopes, strict, machine)?;
            let keys = machine.own_property_keys_value(&value, strict)?;
            scopes.push(HashMap::new());
            scopes
                .last_mut()
                .unwrap()
                .insert(name.clone(), binding(*kind, true, Value::Undefined));
            for key in keys {
                scopes.last().unwrap().get(name).unwrap().borrow_mut().value = Value::String(key);
                match execute_statement(body, scopes, strict, machine)? {
                    Completion::Break => break,
                    Completion::Continue | Completion::Normal => {}
                    completion => {
                        scopes.pop();
                        return Ok(completion);
                    }
                }
            }
            scopes.pop();
        }
        StatementKind::ForOf {
            name,
            kind,
            right,
            body,
        } => {
            let value = evaluate_expression(right, scopes, strict, machine)?;
            let values = match value {
                Value::String(string) => string
                    .chars()
                    .map(|character| Value::String(character.to_string()))
                    .collect::<Vec<_>>(),
                Value::Array(array) => array
                    .borrow()
                    .iter()
                    .map(|value| value.clone().unwrap_or(Value::Undefined))
                    .collect(),
                _ => bail!("for-of hiện chỉ hỗ trợ String iterable"),
            };
            scopes.push(HashMap::new());
            scopes
                .last_mut()
                .unwrap()
                .insert(name.clone(), binding(*kind, true, Value::Undefined));
            for value in values {
                scopes.last().unwrap().get(name).unwrap().borrow_mut().value = value;
                match execute_statement(body, scopes, strict, machine)? {
                    Completion::Break => break,
                    Completion::Continue | Completion::Normal => {}
                    completion => {
                        scopes.pop();
                        return Ok(completion);
                    }
                }
            }
            scopes.pop();
        }
        StatementKind::Switch {
            discriminant,
            cases,
        } => {
            let discriminant = evaluate_expression(discriminant, scopes, strict, machine)?;
            let mut default = None;
            let mut start = None;
            for (index, case) in cases.iter().enumerate() {
                match &case.test {
                    Some(test)
                        if ecmora_value::binary(
                            SemBinary::StrictEqual,
                            discriminant.clone(),
                            evaluate_expression(test, scopes, strict, machine)?,
                        )? == Value::Bool(true) =>
                    {
                        start = Some(index);
                        break;
                    }
                    None => default = Some(index),
                    _ => {}
                }
            }
            if let Some(start) = start.or(default) {
                scopes.push(HashMap::new());
                let result = (|| -> Result<Completion> {
                    let all = cases
                        .iter()
                        .flat_map(|case| case.consequent.iter())
                        .collect::<Vec<_>>();
                    for statement in &all {
                        if let StatementKind::VariableDeclaration { kind, declarations } =
                            &statement.kind
                        {
                            for declaration in declarations {
                                if scopes.last().unwrap().contains_key(&declaration.name) {
                                    bail!(
                                        "identifier `{}` được khai báo trùng trong switch",
                                        declaration.name
                                    )
                                }
                                scopes.last_mut().unwrap().insert(
                                    declaration.name.clone(),
                                    binding(*kind, false, Value::Undefined),
                                );
                            }
                        }
                    }
                    for case in &cases[start..] {
                        for statement in &case.consequent {
                            match execute_statement(statement, scopes, strict, machine)? {
                                Completion::Break => return Ok(Completion::Normal),
                                Completion::Continue => return Ok(Completion::Continue),
                                Completion::Normal => {}
                                completion => return Ok(completion),
                            }
                        }
                    }
                    Ok(Completion::Normal)
                })();
                scopes.pop();
                return result;
            }
        }
        StatementKind::Break => return Ok(Completion::Break),
        StatementKind::Continue => return Ok(Completion::Continue),
        StatementKind::FunctionDeclaration(_) => {}
        StatementKind::Return(expression) => {
            let value = match expression {
                Some(expression) => evaluate_expression(expression, scopes, strict, machine)?,
                None => Value::Undefined,
            };
            return Ok(Completion::Return(value));
        }
        StatementKind::Throw(expression) => {
            let value = evaluate_expression(expression, scopes, strict, machine)?;
            return Ok(Completion::Throw(value));
        }
        StatementKind::VariableDeclaration { kind, declarations } => {
            for declaration in declarations {
                let value = match &declaration.init {
                    Some(init) => evaluate_expression(init, scopes, strict, machine)?,
                    None => Value::Undefined,
                };
                let binding = find_binding_mut(scopes, &declaration.name)
                    .ok_or_else(|| anyhow!("binding `{}` không tồn tại", declaration.name))?;
                let mut binding = binding.borrow_mut();
                binding.kind = *kind;
                binding.initialized = true;
                binding.value = value;
            }
        }
    }
    Ok(Completion::Normal)
}

fn evaluate_expression(
    expression: &Expression,
    scopes: &mut Vec<Scope>,
    strict: bool,
    machine: &mut Machine,
) -> Result<Value> {
    match &expression.kind {
        ExpressionKind::String(value) => Ok(Value::String(value.clone())),
        ExpressionKind::Number(value) => Ok(Value::Number(*value)),
        ExpressionKind::BigInt(value) => {
            Ok(Value::BigInt(ecmora_value::parse_bigint_literal(value)?))
        }
        ExpressionKind::Bool(value) => Ok(Value::Bool(*value)),
        ExpressionKind::Null => Ok(Value::Null),
        ExpressionKind::This => {
            if let Some(flag) = find_binding(scopes, "@derived_super_called") {
                if matches!(&flag.borrow().value, Value::Bool(false)) {
                    bail!("không thể truy cập `this` trước super()")
                }
            }
            lookup(scopes, "@this")
        }
        ExpressionKind::Global(name) => match name.as_str() {
            "undefined" => Ok(Value::Undefined),
            "NaN" => Ok(Value::Number(f64::NAN)),
            "Infinity" => Ok(Value::Number(f64::INFINITY)),
            _ => lookup(scopes, name),
        },
        ExpressionKind::Member { object, property } => {
            let key = property_key(property, scopes, strict, machine)?;
            if matches!(&object.kind, ExpressionKind::Global(name) if name == "@super") {
                let base = lookup(scopes, "@super_base")?;
                let receiver = evaluate_expression(
                    &Expression {
                        kind: ExpressionKind::This,
                        span: expression.span,
                    },
                    scopes,
                    strict,
                    machine,
                )?;
                return machine.get_property_value(&base, &key, receiver, strict);
            }
            let object = evaluate_expression(object, scopes, strict, machine)?;
            machine.get_property_value(&object, &key, object.clone(), strict)
        }
        ExpressionKind::Object(properties) => {
            let object = ecmora_value::object_with_prototype_in_realm(None, machine.current_realm);
            for entry in properties {
                match entry {
                    ObjectEntry::Property(property) => {
                        let key = property_key(&property.key, scopes, strict, machine)?;
                        let value = evaluate_expression(&property.value, scopes, strict, machine)?;
                        if key == "__proto__" {
                            let prototype = match value {
                                Value::Object(prototype) => Some(prototype),
                                Value::Null => None,
                                _ => {
                                    continue;
                                }
                            };
                            ecmora_value::set_prototype(&object, prototype)?;
                            continue;
                        }
                        ecmora_value::set_property(&object, key, value)?;
                    }
                    ObjectEntry::Spread(expression) => {
                        let source = evaluate_expression(expression, scopes, strict, machine)?;
                        if matches!(source, Value::Null | Value::Undefined) {
                            continue;
                        }
                        for key in machine.own_property_keys_value(&source, strict)? {
                            let value = machine.get_property_value(
                                &source,
                                &key,
                                source.clone(),
                                strict,
                            )?;
                            ecmora_value::set_property(&object, key, value)?;
                        }
                    }
                    ObjectEntry::Accessor { key, get, set } => {
                        let getter = get
                            .as_ref()
                            .map(|expression| {
                                evaluate_expression(expression, scopes, strict, machine)
                            })
                            .transpose()?
                            .and_then(|value| match value {
                                Value::Function(id) => Some(id),
                                _ => None,
                            });
                        let setter = set
                            .as_ref()
                            .map(|expression| {
                                evaluate_expression(expression, scopes, strict, machine)
                            })
                            .transpose()?
                            .and_then(|value| match value {
                                Value::Function(id) => Some(id),
                                _ => None,
                            });
                        ecmora_value::define_accessor(&object, key.clone(), getter, setter)?;
                    }
                }
            }
            Ok(object)
        }
        ExpressionKind::Array(elements) => {
            let mut values = Vec::new();
            for element in elements {
                match element {
                    ArrayElement::Expression(expression) => values.push(Some(evaluate_expression(
                        expression, scopes, strict, machine,
                    )?)),
                    ArrayElement::Hole => values.push(None),
                    ArrayElement::Spread(expression) => {
                        match evaluate_expression(expression, scopes, strict, machine)? {
                            Value::Array(array) => values.extend(
                                array
                                    .borrow()
                                    .iter()
                                    .map(|value| Some(value.clone().unwrap_or(Value::Undefined))),
                            ),
                            Value::String(string) => values.extend(
                                string
                                    .chars()
                                    .map(|character| Some(Value::String(character.to_string()))),
                            ),
                            _ => bail!("array spread cần iterable"),
                        }
                    }
                }
            }
            Ok(ecmora_value::array_with_holes(values))
        }
        ExpressionKind::Conditional {
            test,
            consequent,
            alternate,
        } => {
            if ecmora_value::to_boolean(&evaluate_expression(test, scopes, strict, machine)?) {
                evaluate_expression(consequent, scopes, strict, machine)
            } else {
                evaluate_expression(alternate, scopes, strict, machine)
            }
        }
        ExpressionKind::Unary { operator, argument } => match operator {
            UnaryOperator::Typeof => {
                if let ExpressionKind::Global(name) = &argument.kind {
                    if find_binding(scopes, name).is_none()
                        && !matches!(name.as_str(), "undefined" | "NaN" | "Infinity")
                    {
                        return Ok(Value::String("undefined".to_owned()));
                    }
                }
                let value = evaluate_expression(argument, scopes, strict, machine)?;
                let class_constructor = ecmora_value::class_constructor_slots(&value).is_some();
                let kind = match value {
                    Value::Undefined => "undefined",
                    Value::Null => "object",
                    Value::Bool(_) => "boolean",
                    Value::Number(_) => "number",
                    Value::BigInt(_) => "bigint",
                    Value::String(_) => "string",
                    Value::Object(_) if class_constructor => "function",
                    Value::Object(_) | Value::Array(_) | Value::Promise(_) => "object",
                    Value::Function(_) => "function",
                };
                Ok(Value::String(kind.to_owned()))
            }
            UnaryOperator::Void => {
                evaluate_expression(argument, scopes, strict, machine)?;
                Ok(Value::Undefined)
            }
            UnaryOperator::Delete => match &argument.kind {
                ExpressionKind::Member { object, property } => {
                    let object = evaluate_expression(object, scopes, strict, machine)?;
                    let key = property_key(property, scopes, strict, machine)?;
                    Ok(Value::Bool(
                        machine.delete_property_value(&object, &key, strict)?,
                    ))
                }
                ExpressionKind::Global(_) => Ok(Value::Bool(false)),
                _ => {
                    evaluate_expression(argument, scopes, strict, machine)?;
                    Ok(Value::Bool(true))
                }
            },
            _ => {
                let value = evaluate_expression(argument, scopes, strict, machine)?;
                machine.unary_value(*operator, value, strict)
            }
        },
        ExpressionKind::Binary {
            left,
            operator,
            right,
        } => {
            if *operator == BinaryOperator::In {
                let key =
                    ecmora_value::to_string(&evaluate_expression(left, scopes, strict, machine)?);
                let object = evaluate_expression(right, scopes, strict, machine)?;
                return Ok(Value::Bool(
                    machine.has_property_value(&object, &key, strict)?,
                ));
            }
            if *operator == BinaryOperator::InstanceOf {
                if let ExpressionKind::Global(name) = &right.kind {
                    if find_binding(scopes, name).is_some() {
                        let constructor = lookup(scopes, name)?;
                        if let Some(class) = ecmora_value::class_constructor_slots(&constructor) {
                            let value = evaluate_expression(left, scopes, strict, machine)?;
                            return Ok(Value::Bool(match value {
                                Value::Promise(id) => {
                                    let mut current =
                                        machine.promises[id as usize].constructor.as_str();
                                    loop {
                                        if current == class.name {
                                            break true;
                                        }
                                        let Some(parent) = machine
                                            .promise_subclasses
                                            .get(current)
                                            .map(|value| value.parent.as_str())
                                        else {
                                            break false;
                                        };
                                        current = parent;
                                    }
                                }
                                _ => false,
                            }));
                        }
                    }
                    if name == "Object" && find_binding(scopes, name).is_none() {
                        return Ok(Value::Bool(matches!(
                            evaluate_expression(left, scopes, strict, machine)?,
                            Value::Object(_)
                                | Value::Array(_)
                                | Value::Function(_)
                                | Value::Promise(_)
                        )));
                    }
                    if find_binding(scopes, name).is_none() && machine.is_promise_constructor(name)
                    {
                        let value = evaluate_expression(left, scopes, strict, machine)?;
                        return Ok(Value::Bool(match value {
                            Value::Promise(id) => {
                                let mut constructor =
                                    machine.promises[id as usize].constructor.as_str();
                                loop {
                                    if constructor == name {
                                        break true;
                                    }
                                    let Some(parent) = machine
                                        .promise_subclasses
                                        .get(constructor)
                                        .map(|class| class.parent.as_str())
                                    else {
                                        break false;
                                    };
                                    constructor = parent;
                                }
                            }
                            _ => false,
                        }));
                    }
                }
            }
            let left = evaluate_expression(left, scopes, strict, machine)?;
            let right = evaluate_expression(right, scopes, strict, machine)?;
            machine.binary_value(*operator, left, right, strict)
        }
        ExpressionKind::Logical {
            left,
            operator,
            right,
        } => {
            let left = evaluate_expression(left, scopes, strict, machine)?;
            ecmora_value::logical(to_sem_logical(*operator), left, || {
                evaluate_expression(right, scopes, strict, machine)
            })
        }
        ExpressionKind::Assignment {
            target,
            operator,
            value,
        } => evaluate_assignment(target, *operator, value, scopes, strict, machine),
        ExpressionKind::Update {
            target,
            operator,
            prefix,
        } => {
            let old = read_target(target, scopes, strict, machine)?;
            let numeric = machine.to_numeric_value(old.clone(), strict)?;
            let delta = if matches!(&numeric, Value::BigInt(_)) {
                Value::BigInt(ecmora_value::parse_bigint_literal("1")?)
            } else {
                Value::Number(1.0)
            };
            let new = ecmora_value::binary(
                if *operator == UpdateOperator::Increment {
                    SemBinary::Add
                } else {
                    SemBinary::Subtract
                },
                numeric,
                delta,
            )?;
            write_target(target, new.clone(), scopes, strict, machine)?;
            Ok(if *prefix { new } else { old })
        }
        ExpressionKind::New { callee, arguments } => {
            let arguments = arguments
                .iter()
                .map(|argument| evaluate_expression(argument, scopes, strict, machine))
                .collect::<Result<Vec<_>>>()?;
            if let ExpressionKind::Global(name) = &callee.kind {
                if find_binding(scopes, name).is_none() && name == "Proxy" {
                    let [target, handler] = arguments.as_slice() else {
                        bail!("Proxy constructor cần target và handler")
                    };
                    return ecmora_value::proxy_object(
                        target.clone(),
                        handler.clone(),
                        machine.current_realm,
                    );
                }
                if find_binding(scopes, name).is_none() && machine.is_promise_constructor(name) {
                    return machine.construct_promise_with_constructor(name, arguments, strict);
                }
            }
            let constructor = evaluate_expression(callee, scopes, strict, machine)?;
            if let Some(name) = machine.class_name_from_value(&constructor) {
                return machine.construct_promise_with_constructor(&name, arguments, strict);
            }
            bail!("constructor này chưa được hỗ trợ")
        }
        ExpressionKind::Function(function) => Ok(Value::Function(
            machine.register_function(function.clone(), scopes.clone()),
        )),
        ExpressionKind::Await(argument) => {
            let value = evaluate_expression(argument, scopes, strict, machine)?;
            machine.await_value(value)
        }
        ExpressionKind::Call { callee, arguments } => {
            if matches!(&callee.kind, ExpressionKind::Global(name) if name == "@super") {
                let arguments = arguments
                    .iter()
                    .map(|argument| evaluate_expression(argument, scopes, strict, machine))
                    .collect::<Result<Vec<_>>>()?;
                let promise = match lookup(scopes, "@derived_promise_id")? {
                    Value::Number(id) => id as u64,
                    _ => bail!("derived Promise constructor thiếu promise id"),
                };
                let parent = match lookup(scopes, "@super_constructor")? {
                    Value::String(name) => name,
                    _ => bail!("derived Promise constructor thiếu super constructor"),
                };
                let flag = find_binding(scopes, "@derived_super_called")
                    .ok_or_else(|| anyhow!("super() ngoài derived constructor"))?;
                if matches!(&flag.borrow().value, Value::Bool(true)) {
                    bail!("super() chỉ được gọi một lần")
                }
                let override_value =
                    machine.run_promise_constructor(&parent, promise, arguments, strict)?;
                flag.borrow_mut().value = Value::Bool(true);
                if let Some(value) = override_value {
                    let this = find_binding(scopes, "@this")
                        .ok_or_else(|| anyhow!("derived constructor thiếu this binding"))?;
                    this.borrow_mut().value = value;
                }
                return lookup(scopes, "@this");
            }
            let callee = evaluate_runtime_expression(callee, scopes, strict, machine)?;
            let arguments = arguments
                .iter()
                .map(|a| evaluate_expression(a, scopes, strict, machine))
                .collect::<Result<Vec<_>>>()?;
            match callee {
                RuntimeValue::ConsoleLog => {
                    println!(
                        "{}",
                        arguments
                            .iter()
                            .map(ecmora_value::to_string)
                            .collect::<Vec<_>>()
                            .join(" ")
                    );
                    Ok(Value::Undefined)
                }
                RuntimeValue::NumberConstructor => {
                    if arguments.len() > 1 {
                        bail!("Number nhận tối đa một argument")
                    }
                    Ok(Value::Number(match arguments.into_iter().next() {
                        Some(value) => machine.explicit_number_value(value, strict)?,
                        None => 0.0,
                    }))
                }
                RuntimeValue::BigIntConstructor => {
                    if arguments.len() != 1 {
                        bail!("BigInt cần đúng một argument")
                    }
                    machine.bigint_value(arguments.into_iter().next().unwrap(), strict)
                }
                RuntimeValue::StringConstructor => {
                    if arguments.len() > 1 {
                        bail!("String nhận tối đa một argument")
                    }
                    Ok(Value::String(match arguments.into_iter().next() {
                        Some(value) => machine.to_string_value(value, strict)?,
                        None => String::new(),
                    }))
                }
                RuntimeValue::Function(id) => machine.call_as_expression(id, arguments, strict),
                RuntimeValue::FunctionWithThis(id, receiver) => {
                    match machine.call_function_with_this(id, receiver, arguments, strict)? {
                        CallOutcome::Value(value) => Ok(value),
                        CallOutcome::Throw(value) => {
                            bail!("uncaught {}", ecmora_value::to_string(&value))
                        }
                    }
                }
                RuntimeValue::ClassConstructor(name) => {
                    bail!("class constructor `{name}` phải được gọi bằng `new`")
                }
                RuntimeValue::AsyncGeneratorNext(id) => machine.enqueue_async_generator(
                    id,
                    ecmora_value::GeneratorCompletion::Normal(
                        arguments.first().cloned().unwrap_or(Value::Undefined),
                    ),
                ),
                RuntimeValue::AsyncGeneratorReturn(id) => machine.enqueue_async_generator(
                    id,
                    ecmora_value::GeneratorCompletion::Return(
                        arguments.first().cloned().unwrap_or(Value::Undefined),
                    ),
                ),
                RuntimeValue::AsyncGeneratorThrow(id) => machine.enqueue_async_generator(
                    id,
                    ecmora_value::GeneratorCompletion::Throw(
                        arguments.first().cloned().unwrap_or(Value::Undefined),
                    ),
                ),
                RuntimeValue::PromiseConstructor(constructor) => {
                    bail!("Promise constructor `{constructor}` phải được gọi bằng `new`")
                }
                RuntimeValue::ProxyConstructor => {
                    bail!("Proxy constructor phải được gọi bằng `new`")
                }
                RuntimeValue::ObjectCreate => {
                    let prototype = match arguments.first() {
                        Some(Value::Object(prototype)) => Some(prototype.clone()),
                        Some(Value::Null) => None,
                        _ => bail!("Object.create prototype phải là Object hoặc null"),
                    };
                    Ok(ecmora_value::object_with_prototype_in_realm(
                        prototype,
                        machine.current_realm,
                    ))
                }
                RuntimeValue::ObjectSetPrototypeOf => {
                    let target = arguments.first().cloned().unwrap_or(Value::Undefined);
                    let prototype = match arguments.get(1) {
                        Some(Value::Object(prototype)) => Some(prototype.clone()),
                        Some(Value::Null) => None,
                        _ => bail!("Object.setPrototypeOf prototype phải là Object hoặc null"),
                    };
                    let storage = machine
                        .promise_object_view(&target)
                        .unwrap_or_else(|| target.clone());
                    ecmora_value::set_prototype(&storage, prototype)?;
                    Ok(target)
                }
                RuntimeValue::ObjectGetPrototypeOf => {
                    let target = arguments.first().cloned().unwrap_or(Value::Undefined);
                    let storage = machine.promise_object_view(&target).unwrap_or(target);
                    Ok(ecmora_value::get_prototype(&storage)
                        .map(Value::Object)
                        .unwrap_or(Value::Null))
                }
                RuntimeValue::PromiseResolve(constructor) => machine
                    .promise_resolve_with_constructor(
                        &constructor,
                        arguments.first().cloned().unwrap_or(Value::Undefined),
                    ),
                RuntimeValue::PromiseReject(constructor) => machine
                    .promise_reject_with_constructor(
                        &constructor,
                        arguments.first().cloned().unwrap_or(Value::Undefined),
                    ),
                RuntimeValue::PromiseThen(id) => machine.promise_then(
                    id,
                    argument_function(&arguments, 0),
                    argument_function(&arguments, 1),
                    false,
                ),
                RuntimeValue::PromiseCatch(id) => {
                    machine.promise_then(id, None, argument_function(&arguments, 0), false)
                }
                RuntimeValue::PromiseFinally(id) => machine.promise_then(
                    id,
                    argument_function(&arguments, 0),
                    argument_function(&arguments, 0),
                    true,
                ),
                RuntimeValue::BooleanConstructor => {
                    if arguments.len() > 1 {
                        bail!("Boolean nhận tối đa một argument")
                    }
                    Ok(Value::Bool(
                        arguments
                            .first()
                            .map(ecmora_value::to_boolean)
                            .unwrap_or(false),
                    ))
                }
                _ => bail!("giá trị này không thể được gọi"),
            }
        }
    }
}

fn argument_function(arguments: &[Value], index: usize) -> Option<u64> {
    match arguments.get(index) {
        Some(Value::Function(id)) => Some(*id),
        _ => None,
    }
}

fn property_key(
    property: &MemberProperty,
    scopes: &mut Vec<Scope>,
    strict: bool,
    machine: &mut Machine,
) -> Result<String> {
    match property {
        MemberProperty::Static(key) => Ok(key.clone()),
        MemberProperty::Computed(expression) => {
            let value = evaluate_expression(expression, scopes, strict, machine)?;
            machine.to_string_value(value, strict)
        }
    }
}

fn evaluate_runtime_expression(
    expression: &Expression,
    scopes: &mut Vec<Scope>,
    strict: bool,
    machine: &mut Machine,
) -> Result<RuntimeValue> {
    if let ExpressionKind::Global(name) = &expression.kind {
        if find_binding(scopes, name).is_none() {
            return Ok(match name.as_str() {
                "console" => RuntimeValue::Console,
                "Number" => RuntimeValue::NumberConstructor,
                "BigInt" => RuntimeValue::BigIntConstructor,
                "String" => RuntimeValue::StringConstructor,
                "Boolean" => RuntimeValue::BooleanConstructor,
                "Object" => RuntimeValue::ObjectConstructor,
                "Proxy" => RuntimeValue::ProxyConstructor,
                "Promise" => RuntimeValue::PromiseConstructor("Promise".to_owned()),
                name if machine.is_promise_constructor(name) => {
                    RuntimeValue::PromiseConstructor(name.to_owned())
                }
                _ => RuntimeValue::Js,
            });
        }
    }

    if let ExpressionKind::Member { object, property } = &expression.kind {
        if let (ExpressionKind::Global(name), MemberProperty::Static(key)) =
            (&object.kind, property)
        {
            if name == "console" && key == "log" && find_binding(scopes, name).is_none() {
                return Ok(RuntimeValue::ConsoleLog);
            }
            if name == "Object" && find_binding(scopes, name).is_none() {
                return Ok(match key.as_str() {
                    "create" => RuntimeValue::ObjectCreate,
                    "setPrototypeOf" => RuntimeValue::ObjectSetPrototypeOf,
                    "getPrototypeOf" => RuntimeValue::ObjectGetPrototypeOf,
                    _ => RuntimeValue::Js,
                });
            }
            if find_binding(scopes, name).is_none() && machine.is_promise_constructor(name) {
                return Ok(match key.as_str() {
                    "resolve" => RuntimeValue::PromiseResolve(name.clone()),
                    "reject" => RuntimeValue::PromiseReject(name.clone()),
                    _ => RuntimeValue::Js,
                });
            }
        }

        if matches!(&object.kind, ExpressionKind::Global(name) if name == "@super") {
            let base = lookup(scopes, "@super_base")?;
            let receiver = evaluate_expression(
                &Expression {
                    kind: ExpressionKind::This,
                    span: expression.span,
                },
                scopes,
                strict,
                machine,
            )?;
            let key = property_key(property, scopes, strict, machine)?;
            let value = machine.get_property_value(&base, &key, receiver.clone(), strict)?;
            return Ok(match value {
                Value::Function(function) => RuntimeValue::FunctionWithThis(function, receiver),
                _ => RuntimeValue::Js,
            });
        }

        // ECMAScript evaluates the base before a computed property key.
        let receiver = evaluate_expression(object, scopes, strict, machine)?;
        let key = property_key(property, scopes, strict, machine)?;

        if let Value::Promise(id) = &receiver {
            let id = *id;
            let receiver = Value::Promise(id);
            if machine.has_property_value(&receiver, &key, strict)? {
                let value =
                    machine.get_property_value(&receiver, &key, receiver.clone(), strict)?;
                return Ok(match value {
                    Value::Function(function) => RuntimeValue::FunctionWithThis(function, receiver),
                    _ => RuntimeValue::Js,
                });
            }
            return Ok(match key.as_str() {
                "then" => RuntimeValue::PromiseThen(id),
                "catch" => RuntimeValue::PromiseCatch(id),
                "finally" => RuntimeValue::PromiseFinally(id),
                _ => RuntimeValue::Js,
            });
        }

        if let Some(slots) = ecmora_value::async_generator_slots(&receiver) {
            return Ok(match key.as_str() {
                "next" => RuntimeValue::AsyncGeneratorNext(slots.runtime_id),
                "return" => RuntimeValue::AsyncGeneratorReturn(slots.runtime_id),
                "throw" => RuntimeValue::AsyncGeneratorThrow(slots.runtime_id),
                _ => RuntimeValue::Js,
            });
        }

        if let Some(class) = ecmora_value::class_constructor_slots(&receiver) {
            if machine.has_property_value(&receiver, &key, strict)? {
                let value =
                    machine.get_property_value(&receiver, &key, receiver.clone(), strict)?;
                return Ok(match value {
                    Value::Function(function) => RuntimeValue::FunctionWithThis(function, receiver),
                    _ => RuntimeValue::Js,
                });
            }
            if machine.is_promise_subclass(&class.name) {
                match key.as_str() {
                    "resolve" => return Ok(RuntimeValue::PromiseResolve(class.name)),
                    "reject" => return Ok(RuntimeValue::PromiseReject(class.name)),
                    _ => {}
                }
            }
            return Ok(RuntimeValue::Js);
        }

        let value = machine.get_property_value(&receiver, &key, receiver.clone(), strict)?;
        return Ok(match value {
            Value::Function(function) => RuntimeValue::FunctionWithThis(function, receiver),
            _ => RuntimeValue::Js,
        });
    }

    match evaluate_expression(expression, scopes, strict, machine)? {
        Value::Function(id) => Ok(RuntimeValue::Function(id)),
        value if machine.class_name_from_value(&value).is_some() => Ok(
            RuntimeValue::ClassConstructor(machine.class_name_from_value(&value).unwrap()),
        ),
        _ => Ok(RuntimeValue::Js),
    }
}

fn evaluate_assignment(
    target: &AssignmentTarget,
    operator: AssignmentOperator,
    expression: &Expression,
    scopes: &mut Vec<Scope>,
    strict: bool,
    machine: &mut Machine,
) -> Result<Value> {
    if operator == AssignmentOperator::Assign {
        let value = evaluate_expression(expression, scopes, strict, machine)?;
        return write_target(target, value, scopes, strict, machine);
    }
    let old = read_target(target, scopes, strict, machine)?;
    let skip = match operator {
        AssignmentOperator::LogicalOr => ecmora_value::to_boolean(&old),
        AssignmentOperator::LogicalAnd => !ecmora_value::to_boolean(&old),
        AssignmentOperator::LogicalNullish => !matches!(old, Value::Null | Value::Undefined),
        _ => false,
    };
    if skip {
        return Ok(old);
    }
    let rhs = evaluate_expression(expression, scopes, strict, machine)?;
    let value = match assignment_binary(operator) {
        Some(operator) => machine.binary_value(from_sem_binary(operator), old, rhs, strict)?,
        None => rhs,
    };
    write_target(target, value, scopes, strict, machine)
}

fn read_target(
    target: &AssignmentTarget,
    scopes: &mut Vec<Scope>,
    strict: bool,
    machine: &mut Machine,
) -> Result<Value> {
    match target {
        AssignmentTarget::Identifier(name) => lookup(scopes, name),
        AssignmentTarget::Member { object, property } => {
            let key = property_key(property, scopes, strict, machine)?;
            if matches!(&object.kind, ExpressionKind::Global(name) if name == "@super") {
                let base = lookup(scopes, "@super_base")?;
                let receiver = evaluate_expression(
                    &Expression {
                        kind: ExpressionKind::This,
                        span: object.span,
                    },
                    scopes,
                    strict,
                    machine,
                )?;
                return machine.get_property_value(&base, &key, receiver, strict);
            }
            let object = evaluate_expression(object, scopes, strict, machine)?;
            machine.get_property_value(&object, &key, object.clone(), strict)
        }
    }
}

fn write_target(
    target: &AssignmentTarget,
    value: Value,
    scopes: &mut Vec<Scope>,
    strict: bool,
    machine: &mut Machine,
) -> Result<Value> {
    match target {
        AssignmentTarget::Identifier(name) => store_identifier(name, value, scopes, strict),
        AssignmentTarget::Member { object, property } => {
            let key = property_key(property, scopes, strict, machine)?;
            if matches!(&object.kind, ExpressionKind::Global(name) if name == "@super") {
                let base = lookup(scopes, "@super_base")?;
                let receiver = evaluate_expression(
                    &Expression {
                        kind: ExpressionKind::This,
                        span: object.span,
                    },
                    scopes,
                    strict,
                    machine,
                )?;
                return machine.set_property_value(&base, key, value, receiver, strict);
            }
            let object = evaluate_expression(object, scopes, strict, machine)?;
            machine.set_property_value(&object, key, value, object.clone(), strict)
        }
    }
}

fn store_identifier(
    name: &str,
    value: Value,
    scopes: &mut Vec<Scope>,
    strict: bool,
) -> Result<Value> {
    let Some(binding) = find_binding_mut(scopes, name) else {
        if strict {
            bail!("identifier `{name}` chưa được khai báo")
        }
        scopes[0].insert(
            name.to_owned(),
            binding(VariableKind::Let, true, value.clone()),
        );
        return Ok(value);
    };
    let mut binding = binding.borrow_mut();
    if !binding.initialized {
        bail!("identifier `{name}` đang ở Temporal Dead Zone")
    }
    if binding.kind == VariableKind::Const {
        bail!("không thể gán lại const `{name}`")
    }
    binding.value = value.clone();
    Ok(value)
}

fn lookup(scopes: &[Scope], name: &str) -> Result<Value> {
    for scope in scopes.iter().rev() {
        if let Some(binding) = scope.get(name) {
            let binding = binding.borrow();
            if !binding.initialized {
                bail!("identifier `{name}` đang ở Temporal Dead Zone")
            }
            return Ok(binding.value.clone());
        }
    }
    bail!("identifier `{name}` chưa được khai báo")
}
fn find_binding(scopes: &[Scope], name: &str) -> Option<BindingRef> {
    scopes
        .iter()
        .rev()
        .find_map(|scope| scope.get(name).cloned())
}
fn find_binding_mut(scopes: &mut [Scope], name: &str) -> Option<BindingRef> {
    find_binding(scopes, name)
}

fn to_sem_unary(operator: UnaryOperator) -> ecmora_value::UnaryOperator {
    match operator {
        UnaryOperator::Plus => ecmora_value::UnaryOperator::Plus,
        UnaryOperator::Minus => ecmora_value::UnaryOperator::Minus,
        UnaryOperator::Not => ecmora_value::UnaryOperator::Not,
        UnaryOperator::BitwiseNot => ecmora_value::UnaryOperator::BitwiseNot,
        UnaryOperator::Typeof | UnaryOperator::Void | UnaryOperator::Delete => unreachable!(),
    }
}
fn to_sem_binary(operator: BinaryOperator) -> SemBinary {
    match operator {
        BinaryOperator::Add => SemBinary::Add,
        BinaryOperator::Subtract => SemBinary::Subtract,
        BinaryOperator::Multiply => SemBinary::Multiply,
        BinaryOperator::Divide => SemBinary::Divide,
        BinaryOperator::Remainder => SemBinary::Remainder,
        BinaryOperator::Exponential => SemBinary::Exponential,
        BinaryOperator::Equal => SemBinary::Equal,
        BinaryOperator::NotEqual => SemBinary::NotEqual,
        BinaryOperator::StrictEqual => SemBinary::StrictEqual,
        BinaryOperator::StrictNotEqual => SemBinary::StrictNotEqual,
        BinaryOperator::LessThan => SemBinary::LessThan,
        BinaryOperator::LessEqual => SemBinary::LessEqual,
        BinaryOperator::GreaterThan => SemBinary::GreaterThan,
        BinaryOperator::GreaterEqual => SemBinary::GreaterEqual,
        BinaryOperator::ShiftLeft => SemBinary::ShiftLeft,
        BinaryOperator::ShiftRight => SemBinary::ShiftRight,
        BinaryOperator::ShiftRightZeroFill => SemBinary::ShiftRightZeroFill,
        BinaryOperator::BitwiseOr => SemBinary::BitwiseOr,
        BinaryOperator::BitwiseXor => SemBinary::BitwiseXor,
        BinaryOperator::BitwiseAnd => SemBinary::BitwiseAnd,
        BinaryOperator::In => SemBinary::In,
        BinaryOperator::InstanceOf => SemBinary::InstanceOf,
    }
}
fn from_sem_binary(operator: SemBinary) -> BinaryOperator {
    match operator {
        SemBinary::Add => BinaryOperator::Add,
        SemBinary::Subtract => BinaryOperator::Subtract,
        SemBinary::Multiply => BinaryOperator::Multiply,
        SemBinary::Divide => BinaryOperator::Divide,
        SemBinary::Remainder => BinaryOperator::Remainder,
        SemBinary::Exponential => BinaryOperator::Exponential,
        SemBinary::Equal => BinaryOperator::Equal,
        SemBinary::NotEqual => BinaryOperator::NotEqual,
        SemBinary::StrictEqual => BinaryOperator::StrictEqual,
        SemBinary::StrictNotEqual => BinaryOperator::StrictNotEqual,
        SemBinary::LessThan => BinaryOperator::LessThan,
        SemBinary::LessEqual => BinaryOperator::LessEqual,
        SemBinary::GreaterThan => BinaryOperator::GreaterThan,
        SemBinary::GreaterEqual => BinaryOperator::GreaterEqual,
        SemBinary::ShiftLeft => BinaryOperator::ShiftLeft,
        SemBinary::ShiftRight => BinaryOperator::ShiftRight,
        SemBinary::ShiftRightZeroFill => BinaryOperator::ShiftRightZeroFill,
        SemBinary::BitwiseOr => BinaryOperator::BitwiseOr,
        SemBinary::BitwiseXor => BinaryOperator::BitwiseXor,
        SemBinary::BitwiseAnd => BinaryOperator::BitwiseAnd,
        SemBinary::In => BinaryOperator::In,
        SemBinary::InstanceOf => BinaryOperator::InstanceOf,
    }
}

fn to_sem_logical(operator: LogicalOperator) -> ecmora_value::LogicalOperator {
    match operator {
        LogicalOperator::Or => ecmora_value::LogicalOperator::Or,
        LogicalOperator::And => ecmora_value::LogicalOperator::And,
        LogicalOperator::Nullish => ecmora_value::LogicalOperator::Nullish,
    }
}
fn assignment_binary(operator: AssignmentOperator) -> Option<SemBinary> {
    Some(match operator {
        AssignmentOperator::Add => SemBinary::Add,
        AssignmentOperator::Subtract => SemBinary::Subtract,
        AssignmentOperator::Multiply => SemBinary::Multiply,
        AssignmentOperator::Divide => SemBinary::Divide,
        AssignmentOperator::Remainder => SemBinary::Remainder,
        AssignmentOperator::Exponential => SemBinary::Exponential,
        AssignmentOperator::ShiftLeft => SemBinary::ShiftLeft,
        AssignmentOperator::ShiftRight => SemBinary::ShiftRight,
        AssignmentOperator::ShiftRightZeroFill => SemBinary::ShiftRightZeroFill,
        AssignmentOperator::BitwiseOr => SemBinary::BitwiseOr,
        AssignmentOperator::BitwiseXor => SemBinary::BitwiseXor,
        AssignmentOperator::BitwiseAnd => SemBinary::BitwiseAnd,
        _ => return None,
    })
}
