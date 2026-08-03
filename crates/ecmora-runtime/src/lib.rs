use anyhow::{Result, anyhow, bail};
use ecmora_hir::{
    ArrayElement, AssignmentOperator, AssignmentTarget, BinaryOperator, Expression, ExpressionKind,
    ForInit, Function as HirFunction, LogicalOperator, MemberProperty, ObjectEntry, Program,
    Statement, StatementKind, UnaryOperator, UpdateOperator, VariableKind,
};
use ecmora_value::{BinaryOperator as SemBinary, Value};
use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque},
    rc::Rc,
};

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
    StringConstructor,
    BooleanConstructor,
    ObjectConstructor,
    ObjectCreate,
    ObjectSetPrototypeOf,
    ObjectGetPrototypeOf,
    PromiseConstructor,
    PromiseResolve,
    PromiseReject,
    PromiseThen(u64),
    PromiseCatch(u64),
    PromiseFinally(u64),
    Function(u64),
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
}

#[derive(Debug, Clone)]
struct FunctionObject {
    kind: FunctionKind,
    closure: Vec<Scope>,
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

#[derive(Default)]
struct Machine {
    functions: Vec<FunctionObject>,
    promises: Vec<PromiseObject>,
    jobs: VecDeque<PromiseJob>,
    async_tasks: Vec<Option<AsyncTask>>,
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
        });
        id
    }

    fn register_native_function(&mut self, kind: FunctionKind) -> u64 {
        let id = self.functions.len() as u64;
        self.functions.push(FunctionObject {
            kind,
            closure: Vec::new(),
        });
        id
    }

    fn new_promise(&mut self) -> u64 {
        let id = self.promises.len() as u64;
        self.promises.push(PromiseObject {
            state: PromiseState::Pending,
            reactions: Vec::new(),
            handled: false,
            reported_unhandled: false,
        });
        id
    }

    fn promise_resolve(&mut self, value: Value) -> Value {
        if matches!(value, Value::Promise(_)) {
            return value;
        }
        let id = self.new_promise();
        self.settle(id, PromiseState::Fulfilled(value));
        Value::Promise(id)
    }

    fn promise_reject(&mut self, value: Value) -> Value {
        let id = self.new_promise();
        self.settle(id, PromiseState::Rejected(value));
        Value::Promise(id)
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

    fn construct_promise(&mut self, arguments: Vec<Value>, strict: bool) -> Result<Value> {
        let Some(Value::Function(executor)) = arguments.first() else {
            bail!("Promise executor phải là function")
        };
        let promise = self.new_promise();
        let resolve = self.register_native_function(FunctionKind::Resolve(promise));
        let reject = self.register_native_function(FunctionKind::Reject(promise));
        match self.call_function(
            *executor,
            vec![Value::Function(resolve), Value::Function(reject)],
            strict,
        )? {
            CallOutcome::Value(_) => {}
            CallOutcome::Throw(reason) => self.settle(promise, PromiseState::Rejected(reason)),
        }
        Ok(Value::Promise(promise))
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
        let function = self
            .functions
            .get(id as usize)
            .cloned()
            .ok_or_else(|| anyhow!("function handle không hợp lệ"))?;
        match function.kind {
            FunctionKind::Resolve(promise) => {
                let value = arguments.first().cloned().unwrap_or(Value::Undefined);
                if let Value::Promise(source) = value {
                    if source == promise {
                        self.settle(
                            promise,
                            PromiseState::Rejected(Value::String(
                                "Chaining cycle detected for promise".to_owned(),
                            )),
                        );
                    } else {
                        let relay = PromiseReaction {
                            fulfilled: None,
                            rejected: None,
                            next: promise,
                            finally: false,
                        };
                        self.attach_reaction(source, relay);
                    }
                } else {
                    self.settle(promise, PromiseState::Fulfilled(value));
                }
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
            FunctionKind::User(definition) => {
                if let Some(error) = &definition.lowering_error {
                    bail!("function reachable nhưng frontend không hạ được body: {error}")
                }
                let is_async = definition.r#async;
                let mut scopes = function.closure;
                let mut call_scope = HashMap::new();
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
                scopes.push(call_scope);
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
                        let Value::Promise(id) = self.promise_resolve(value) else {
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
                    self.resolve_into(promise, value);
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
                self.resolve_into(task.promise, value);
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

    fn resolve_into(&mut self, promise: u64, value: Value) {
        if let Value::Promise(source) = value {
            self.attach_reaction(
                source,
                PromiseReaction {
                    fulfilled: None,
                    rejected: None,
                    next: promise,
                    finally: false,
                },
            );
        } else {
            self.settle(promise, PromiseState::Fulfilled(value));
        }
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
        let next = self.new_promise();
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
        // any reaction. A missing onRejected propagates rejection to `next`,
        // whose own handled state is tracked independently.
        self.promises[source as usize].handled = true;
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
        for promise in &mut self.promises {
            if let PromiseState::Rejected(reason) = &promise.state {
                if !promise.handled && !promise.reported_unhandled {
                    promise.reported_unhandled = true;
                    bail!(
                        "unhandled promise rejection: {}",
                        ecmora_value::to_string(reason)
                    )
                }
            }
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
                let Value::Promise(id) = self.promise_resolve(value) else {
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
    let mut machine = Machine::default();
    let mut scopes = vec![HashMap::new()];
    match execute_scope(
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
            let keys = ecmora_value::own_property_keys(&value);
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
        ExpressionKind::Bool(value) => Ok(Value::Bool(*value)),
        ExpressionKind::Null => Ok(Value::Null),
        ExpressionKind::Global(name) => match name.as_str() {
            "undefined" => Ok(Value::Undefined),
            "NaN" => Ok(Value::Number(f64::NAN)),
            "Infinity" => Ok(Value::Number(f64::INFINITY)),
            _ => lookup(scopes, name),
        },
        ExpressionKind::Member { object, property } => {
            let object = evaluate_expression(object, scopes, strict, machine)?;
            let key = property_key(property, scopes, strict, machine)?;
            if let Some(getter) =
                ecmora_value::get_accessor(&object, &key).and_then(|descriptor| descriptor.getter)
            {
                return machine.call_as_expression(getter, Vec::new(), strict);
            }
            Ok(ecmora_value::get_property(&object, &key))
        }
        ExpressionKind::Object(properties) => {
            let object = ecmora_value::object();
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
                        for key in ecmora_value::own_property_keys(&source) {
                            let value = ecmora_value::get_property(&source, &key);
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
                let kind = match value {
                    Value::Undefined => "undefined",
                    Value::Null => "object",
                    Value::Bool(_) => "boolean",
                    Value::Number(_) => "number",
                    Value::String(_) => "string",
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
                    Ok(Value::Bool(ecmora_value::delete_property(&object, &key)))
                }
                ExpressionKind::Global(_) => Ok(Value::Bool(false)),
                _ => {
                    evaluate_expression(argument, scopes, strict, machine)?;
                    Ok(Value::Bool(true))
                }
            },
            _ => Ok(ecmora_value::unary(
                to_sem_unary(*operator),
                evaluate_expression(argument, scopes, strict, machine)?,
            )),
        },
        ExpressionKind::Binary {
            left,
            operator,
            right,
        } => {
            if *operator == BinaryOperator::InstanceOf {
                if let ExpressionKind::Global(name) = &right.kind {
                    if name == "Object" && find_binding(scopes, name).is_none() {
                        return Ok(Value::Bool(matches!(
                            evaluate_expression(left, scopes, strict, machine)?,
                            Value::Object(_) | Value::Array(_)
                        )));
                    }
                }
            }
            Ok(ecmora_value::binary(
                to_sem_binary(*operator),
                evaluate_expression(left, scopes, strict, machine)?,
                evaluate_expression(right, scopes, strict, machine)?,
            )?)
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
            let delta = Value::Number(1.0);
            let new = ecmora_value::binary(
                if *operator == UpdateOperator::Increment {
                    SemBinary::Add
                } else {
                    SemBinary::Subtract
                },
                Value::Number(ecmora_value::to_number(&old)),
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
            if matches!(&callee.kind, ExpressionKind::Global(name) if name == "Promise" && find_binding(scopes, name).is_none())
            {
                return machine.construct_promise(arguments, strict);
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
                    Ok(Value::Number(
                        arguments
                            .first()
                            .map(ecmora_value::to_number)
                            .unwrap_or(0.0),
                    ))
                }
                RuntimeValue::StringConstructor => {
                    if arguments.len() > 1 {
                        bail!("String nhận tối đa một argument")
                    }
                    Ok(Value::String(
                        arguments
                            .first()
                            .map(ecmora_value::to_string)
                            .unwrap_or_default(),
                    ))
                }
                RuntimeValue::Function(id) => machine.call_as_expression(id, arguments, strict),
                RuntimeValue::ObjectCreate => {
                    let prototype = match arguments.first() {
                        Some(Value::Object(prototype)) => Some(prototype.clone()),
                        Some(Value::Null) => None,
                        _ => bail!("Object.create prototype phải là Object hoặc null"),
                    };
                    Ok(ecmora_value::object_with_prototype(prototype))
                }
                RuntimeValue::ObjectSetPrototypeOf => {
                    let target = arguments.first().cloned().unwrap_or(Value::Undefined);
                    let prototype = match arguments.get(1) {
                        Some(Value::Object(prototype)) => Some(prototype.clone()),
                        Some(Value::Null) => None,
                        _ => bail!("Object.setPrototypeOf prototype phải là Object hoặc null"),
                    };
                    ecmora_value::set_prototype(&target, prototype)?;
                    Ok(target)
                }
                RuntimeValue::ObjectGetPrototypeOf => {
                    let target = arguments.first().cloned().unwrap_or(Value::Undefined);
                    Ok(ecmora_value::get_prototype(&target)
                        .map(Value::Object)
                        .unwrap_or(Value::Null))
                }
                RuntimeValue::PromiseResolve => {
                    Ok(machine
                        .promise_resolve(arguments.first().cloned().unwrap_or(Value::Undefined)))
                }
                RuntimeValue::PromiseReject => {
                    Ok(machine
                        .promise_reject(arguments.first().cloned().unwrap_or(Value::Undefined)))
                }
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
        MemberProperty::Computed(expression) => Ok(ecmora_value::to_string(&evaluate_expression(
            expression, scopes, strict, machine,
        )?)),
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
                "String" => RuntimeValue::StringConstructor,
                "Boolean" => RuntimeValue::BooleanConstructor,
                "Object" => RuntimeValue::ObjectConstructor,
                "Promise" => RuntimeValue::PromiseConstructor,
                _ => RuntimeValue::Js,
            });
        }
    }
    if let ExpressionKind::Member {
        object,
        property: MemberProperty::Static(property),
    } = &expression.kind
    {
        if let ExpressionKind::Global(name) = &object.kind {
            if name == "console" && property == "log" && find_binding(scopes, name).is_none() {
                return Ok(RuntimeValue::ConsoleLog);
            }
            if name == "Promise" && find_binding(scopes, name).is_none() {
                return Ok(match property.as_str() {
                    "resolve" => RuntimeValue::PromiseResolve,
                    "reject" => RuntimeValue::PromiseReject,
                    _ => RuntimeValue::Js,
                });
            }
            if name == "Object" && find_binding(scopes, name).is_none() {
                return Ok(match property.as_str() {
                    "create" => RuntimeValue::ObjectCreate,
                    "setPrototypeOf" => RuntimeValue::ObjectSetPrototypeOf,
                    "getPrototypeOf" => RuntimeValue::ObjectGetPrototypeOf,
                    _ => RuntimeValue::Js,
                });
            }
        }
        if let Value::Promise(id) = evaluate_expression(object, scopes, strict, machine)? {
            return Ok(match property.as_str() {
                "then" => RuntimeValue::PromiseThen(id),
                "catch" => RuntimeValue::PromiseCatch(id),
                "finally" => RuntimeValue::PromiseFinally(id),
                _ => RuntimeValue::Js,
            });
        }
    }
    match evaluate_expression(expression, scopes, strict, machine)? {
        Value::Function(id) => Ok(RuntimeValue::Function(id)),
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
        Some(operator) => ecmora_value::binary(operator, old, rhs)?,
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
            let object = evaluate_expression(object, scopes, strict, machine)?;
            let key = property_key(property, scopes, strict, machine)?;
            if let Some(getter) =
                ecmora_value::get_accessor(&object, &key).and_then(|descriptor| descriptor.getter)
            {
                return machine.call_as_expression(getter, Vec::new(), strict);
            }
            Ok(ecmora_value::get_property(&object, &key))
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
            let object = evaluate_expression(object, scopes, strict, machine)?;
            let key = property_key(property, scopes, strict, machine)?;
            if let Some(setter) =
                ecmora_value::get_accessor(&object, &key).and_then(|descriptor| descriptor.setter)
            {
                return machine.call_as_expression(setter, vec![value], strict);
            }
            ecmora_value::set_property(&object, key, value)
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
