use anyhow::{Context, Result, anyhow, bail};
use ecmora_ir::{
    BinaryNumberOperator, Builtin, CallArgument, CompareNumberOperator, DynamicBinaryOperator,
    DynamicUnaryOperator, Instruction, Program, Terminator, UnaryBoolOperator, UnaryNumberOperator,
    ValueId, ValueType,
};
use inkwell::{
    AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel,
    context::Context as LlvmContext,
    module::Module,
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine},
    values::{BasicValue, BasicValueEnum, FloatValue, IntValue, PhiValue, StructValue},
};
use std::{collections::HashMap, path::Path};

pub fn write_llvm_ir(program: &Program, output_path: &Path) -> Result<()> {
    let context = LlvmContext::create();
    let module = build_module(&context, program)?;
    module
        .print_to_file(output_path)
        .map_err(|error| anyhow!("không thể ghi LLVM IR {}: {error}", output_path.display()))?;
    Ok(())
}

pub fn write_object_file(program: &Program, output_path: &Path) -> Result<()> {
    Target::initialize_x86(&InitializationConfig::default());
    let context = LlvmContext::create();
    let module = build_module(&context, program)?;
    let triple = TargetMachine::get_default_triple();
    let target = Target::from_triple(&triple)
        .map_err(|error| anyhow!("không tìm thấy LLVM target: {error}"))?;
    let cpu_name = TargetMachine::get_host_cpu_name();
    let cpu_features = TargetMachine::get_host_cpu_features();
    let cpu_name = cpu_name
        .to_str()
        .context("LLVM host CPU name không phải UTF-8")?;
    let cpu_features = cpu_features
        .to_str()
        .context("LLVM host CPU features không phải UTF-8")?;
    let machine = target
        .create_target_machine(
            &triple,
            cpu_name,
            cpu_features,
            OptimizationLevel::Default,
            RelocMode::Default,
            CodeModel::Default,
        )
        .context("không thể tạo LLVM TargetMachine")?;
    module.set_triple(&triple);
    module.set_data_layout(&machine.get_target_data().get_data_layout());
    module
        .verify()
        .map_err(|error| anyhow!("LLVM module không hợp lệ: {error}"))?;
    machine
        .write_to_file(&module, FileType::Object, output_path)
        .map_err(|error| {
            anyhow!(
                "không thể ghi object file {}: {error}",
                output_path.display()
            )
        })?;
    Ok(())
}

fn build_module<'ctx>(context: &'ctx LlvmContext, program: &Program) -> Result<Module<'ctx>> {
    if program.functions.is_empty() {
        bail!("SSA program không có function")
    }
    let module = context.create_module("ecmora");
    let builder = context.create_builder();
    let i32_type = context.i32_type();
    let i8_type = context.i8_type();
    let i64_type = context.i64_type();
    let bool_type = context.bool_type();
    let f64_type = context.f64_type();
    let ptr_type = context.ptr_type(AddressSpace::default());
    let dynamic_type = context.struct_type(&[i8_type.into(), i64_type.into()], false);
    let pow_f64 = module.add_function(
        "llvm.pow.f64",
        f64_type.fn_type(&[f64_type.into(), f64_type.into()], false),
        None,
    );
    let printf = module.add_function("printf", i32_type.fn_type(&[ptr_type.into()], true), None);
    let strcmp = module.add_function(
        "strcmp",
        i32_type.fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let dynamic_to_bool = module.add_function(
        "ecmora_dynamic_to_bool",
        bool_type.fn_type(&[i8_type.into(), i64_type.into()], false),
        None,
    );
    let primitive_to_number = module.add_function(
        "ecmora_primitive_to_number",
        f64_type.fn_type(&[i8_type.into(), i64_type.into()], false),
        None,
    );
    let dynamic_print = module.add_function(
        "ecmora_print_dynamic",
        context
            .void_type()
            .fn_type(&[i8_type.into(), i64_type.into()], false),
        None,
    );
    let throw_uncaught = module.add_function(
        "ecmora_throw_uncaught",
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
    );
    let object_new = module.add_function("ecmora_object_new", ptr_type.fn_type(&[], false), None);
    let object_new_with_prototype = module.add_function(
        "ecmora_object_new_with_prototype",
        ptr_type.fn_type(&[ptr_type.into()], false),
        None,
    );
    let object_set_prototype = module.add_function(
        "ecmora_object_set_prototype",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let object_get_prototype = module.add_function(
        "ecmora_object_get_prototype",
        ptr_type.fn_type(&[ptr_type.into()], false),
        None,
    );
    let object_define_accessor = module.add_function(
        "ecmora_object_define_accessor",
        context.void_type().fn_type(
            &[
                ptr_type.into(),
                ptr_type.into(),
                ptr_type.into(),
                ptr_type.into(),
                bool_type.into(),
                bool_type.into(),
            ],
            false,
        ),
        None,
    );
    let object_get_number = module.add_function(
        "ecmora_object_get_number",
        f64_type.fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let object_set_number = module.add_function(
        "ecmora_object_set_number",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into(), f64_type.into()], false),
        None,
    );
    let object_get_bool = module.add_function(
        "ecmora_object_get_bool",
        bool_type.fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let object_set_bool = module.add_function(
        "ecmora_object_set_bool",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into(), bool_type.into()], false),
        None,
    );
    let object_get_string = module.add_function(
        "ecmora_object_get_string",
        ptr_type.fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let object_set_string = module.add_function(
        "ecmora_object_set_string",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let object_set_undefined = module.add_function(
        "ecmora_object_set_undefined",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let object_set_null = module.add_function(
        "ecmora_object_set_null",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let object_delete = module.add_function(
        "ecmora_object_delete",
        bool_type.fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let closure_new = module.add_function(
        "ecmora_closure_new",
        ptr_type.fn_type(&[ptr_type.into(), i32_type.into(), ptr_type.into()], false),
        None,
    );
    let closure_capture = module.add_function(
        "ecmora_closure_capture",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), i32_type.into(), ptr_type.into()], false),
        None,
    );
    let closure_call = module.add_function(
        "ecmora_closure_call",
        i8_type.fn_type(
            &[
                ptr_type.into(),
                i32_type.into(),
                ptr_type.into(),
                ptr_type.into(),
            ],
            false,
        ),
        None,
    );
    let argument_get = module.add_function(
        "ecmora_argument_get",
        context.void_type().fn_type(
            &[
                i32_type.into(),
                ptr_type.into(),
                i32_type.into(),
                ptr_type.into(),
            ],
            false,
        ),
        None,
    );
    let tail_argv_reserve = module.add_function(
        "ecmora_tail_argv_reserve",
        ptr_type.fn_type(&[i32_type.into()], false),
        None,
    );

    let closure_new_ex = module.add_function(
        "ecmora_closure_new_ex",
        ptr_type.fn_type(
            &[
                ptr_type.into(),
                i32_type.into(),
                ptr_type.into(),
                i32_type.into(),
                ptr_type.into(),
            ],
            false,
        ),
        None,
    );
    let current_this = module.add_function(
        "ecmora_current_this",
        context.void_type().fn_type(&[ptr_type.into()], false),
        None,
    );
    let arguments_object = module.add_function(
        "ecmora_arguments_object",
        ptr_type.fn_type(&[i32_type.into(), ptr_type.into()], false),
        None,
    );
    let rest_array = module.add_function(
        "ecmora_rest_array",
        ptr_type.fn_type(&[i32_type.into(), ptr_type.into(), i32_type.into()], false),
        None,
    );
    let argv_builder_init = module.add_function(
        "ecmora_argv_builder_init",
        context.void_type().fn_type(&[ptr_type.into()], false),
        None,
    );
    let argv_builder_push = module.add_function(
        "ecmora_argv_builder_push",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let argv_builder_spread = module.add_function(
        "ecmora_argv_builder_spread",
        i8_type.fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let argv_builder_len = module.add_function(
        "ecmora_argv_builder_len",
        i32_type.fn_type(&[ptr_type.into()], false),
        None,
    );
    let argv_builder_data = module.add_function(
        "ecmora_argv_builder_data",
        ptr_type.fn_type(&[ptr_type.into()], false),
        None,
    );
    let argv_builder_destroy = module.add_function(
        "ecmora_argv_builder_destroy",
        context.void_type().fn_type(&[ptr_type.into()], false),
        None,
    );
    let callable_dispatch = module.add_function(
        "ecmora_callable_dispatch",
        i8_type.fn_type(
            &[
                ptr_type.into(),
                ptr_type.into(),
                ptr_type.into(),
                bool_type.into(),
                i32_type.into(),
                ptr_type.into(),
                ptr_type.into(),
            ],
            false,
        ),
        None,
    );
    let callable_construct = module.add_function(
        "ecmora_callable_construct",
        i8_type.fn_type(
            &[
                ptr_type.into(),
                i32_type.into(),
                ptr_type.into(),
                ptr_type.into(),
            ],
            false,
        ),
        None,
    );
    let callable_bind = module.add_function(
        "ecmora_callable_bind_value",
        i8_type.fn_type(
            &[
                ptr_type.into(),
                ptr_type.into(),
                i32_type.into(),
                ptr_type.into(),
                ptr_type.into(),
            ],
            false,
        ),
        None,
    );
    let dynamic_unary = module.add_function(
        "ecmora_dynamic_unary",
        i8_type.fn_type(&[i8_type.into(), ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let dynamic_binary = module.add_function(
        "ecmora_dynamic_binary",
        i8_type.fn_type(
            &[
                i8_type.into(),
                ptr_type.into(),
                ptr_type.into(),
                ptr_type.into(),
            ],
            false,
        ),
        None,
    );
    let dynamic_get = module.add_function(
        "ecmora_dynamic_get",
        i8_type.fn_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let dynamic_set = module.add_function(
        "ecmora_dynamic_set",
        i8_type.fn_type(
            &[
                ptr_type.into(),
                ptr_type.into(),
                ptr_type.into(),
                ptr_type.into(),
            ],
            false,
        ),
        None,
    );
    let dynamic_delete = module.add_function(
        "ecmora_dynamic_delete",
        i8_type.fn_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let array_push = module.add_function(
        "ecmora_array_push",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let array_spread = module.add_function(
        "ecmora_array_spread",
        i8_type.fn_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let object_get_value = module.add_function(
        "ecmora_object_get_value",
        bool_type.fn_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let object_set_value = module.add_function(
        "ecmora_object_set_value",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let cell_new = module.add_function(
        "ecmora_cell_new",
        ptr_type.fn_type(&[ptr_type.into()], false),
        None,
    );
    let cell_get = module.add_function(
        "ecmora_cell_get",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let cell_set = module.add_function(
        "ecmora_cell_set",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let promise_resolved = module.add_function(
        "ecmora_promise_resolved",
        ptr_type.fn_type(&[ptr_type.into()], false),
        None,
    );
    let promise_rejected = module.add_function(
        "ecmora_promise_rejected",
        ptr_type.fn_type(&[ptr_type.into()], false),
        None,
    );
    let promise_pending =
        module.add_function("ecmora_promise_pending", ptr_type.fn_type(&[], false), None);
    let promise_settle = module.add_function(
        "ecmora_promise_settle",
        context
            .void_type()
            .fn_type(&[ptr_type.into(), bool_type.into(), ptr_type.into()], false),
        None,
    );
    let promise_then = module.add_function(
        "ecmora_promise_then",
        ptr_type.fn_type(&[ptr_type.into(), ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let microtask_drain = module.add_function(
        "ecmora_microtask_drain",
        context.void_type().fn_type(&[], false),
        None,
    );
    let js_function_type = i8_type.fn_type(
        &[
            ptr_type.into(),
            i32_type.into(),
            ptr_type.into(),
            ptr_type.into(),
        ],
        false,
    );
    let mut llvm_functions = HashMap::new();
    for function in &program.functions {
        let llvm_function = if function.return_type.is_none() {
            if function.name != "main" {
                bail!("chỉ process entry `main` được phép không có ECMAScript return type")
            }
            module.add_function(&function.name, i32_type.fn_type(&[], false), None)
        } else {
            module.add_function(&function.name, js_function_type, None)
        };
        if llvm_functions
            .insert(function.name.clone(), llvm_function)
            .is_some()
        {
            bail!("trùng LLVM function `{}`", function.name)
        }
    }
    let types = ecmora_ir::value_types(program)?;
    for function in &program.functions {
        let main = *llvm_functions
            .get(&function.name)
            .context("thiếu LLVM function declaration")?;
        let llvm_blocks = function
            .blocks
            .iter()
            .map(|block| context.append_basic_block(main, &block.name))
            .collect::<Vec<_>>();
        let mut values = HashMap::<ValueId, BasicValueEnum<'ctx>>::new();
        let mut phis = HashMap::<ValueId, PhiValue<'ctx>>::new();
        let mut llvm_block_exits = llvm_blocks.clone();
        // Capture this before instruction-pattern bindings such as
        // `Instruction::CallDirect { function, .. }` shadow the outer IR
        // function with a String callee name.
        let is_process_entry = function.return_type.is_none();

        for (index, block) in function.blocks.iter().enumerate() {
            builder.position_at_end(llvm_blocks[index]);
            for instruction in &block.instructions {
                if let Instruction::Phi {
                    result, value_type, ..
                } = instruction
                {
                    let phi = builder.build_phi(
                        llvm_type(
                            *value_type,
                            i8_type,
                            bool_type,
                            f64_type,
                            ptr_type,
                            dynamic_type,
                        ),
                        &format!("phi.{}", result.0),
                    )?;
                    values.insert(*result, phi.as_basic_value());
                    phis.insert(*result, phi);
                }
            }
        }

        for (index, block) in function.blocks.iter().enumerate() {
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
                match instruction {
                    Instruction::Parameter {
                        result,
                        index,
                        value_type,
                    } => {
                        let argc = main
                            .get_nth_param(1)
                            .context("JavaScript function thiếu argc")?
                            .into_int_value();
                        let argv = main
                            .get_nth_param(2)
                            .context("JavaScript function thiếu argv")?
                            .into_pointer_value();
                        let dynamic_ptr =
                            builder.build_alloca(dynamic_type, "parameter.dynamic.slot")?;
                        builder.build_call(
                            argument_get,
                            &[
                                argc.into(),
                                argv.into(),
                                i32_type.const_int(*index as u64, false).into(),
                                dynamic_ptr.into(),
                            ],
                            "parameter.get",
                        )?;
                        let dynamic = builder
                            .build_load(dynamic_type, dynamic_ptr, "parameter.dynamic")?
                            .into_struct_value();
                        values.insert(
                            *result,
                            from_dynamic(
                                &builder,
                                dynamic,
                                *value_type,
                                bool_type,
                                f64_type,
                                ptr_type,
                            )?,
                        );
                    }
                    Instruction::Capture {
                        result,
                        index,
                        value_type,
                    } => {
                        let closure = main
                            .get_nth_param(0)
                            .context("JavaScript function thiếu closure environment")?
                            .into_pointer_value();
                        let dynamic_ptr =
                            builder.build_alloca(dynamic_type, "closure.capture.value")?;
                        builder.build_call(
                            closure_capture,
                            &[
                                closure.into(),
                                i32_type.const_int(*index as u64, false).into(),
                                dynamic_ptr.into(),
                            ],
                            "closure.capture",
                        )?;
                        let dynamic = builder
                            .build_load(dynamic_type, dynamic_ptr, "closure.capture.load")?
                            .into_struct_value();
                        values.insert(
                            *result,
                            from_dynamic(
                                &builder,
                                dynamic,
                                *value_type,
                                bool_type,
                                f64_type,
                                ptr_type,
                            )?,
                        );
                    }
                    Instruction::CellNew {
                        result,
                        value,
                        value_type,
                    } => {
                        let value = values
                            .get(value)
                            .copied()
                            .context("thiếu cell initial value")?;
                        let dynamic = to_dynamic(
                            &builder,
                            value,
                            *value_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                        )?;
                        let dynamic_ptr = builder.build_alloca(dynamic_type, "cell.initial")?;
                        builder.build_store(dynamic_ptr, dynamic)?;
                        let call =
                            builder.build_call(cell_new, &[dynamic_ptr.into()], "cell.new")?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("cell_new không trả pointer")?,
                        );
                    }
                    Instruction::CellGet {
                        result,
                        cell,
                        value_type,
                    } => {
                        let cell = values
                            .get(cell)
                            .copied()
                            .context("thiếu cell SSA")?
                            .into_pointer_value();
                        let dynamic_ptr = builder.build_alloca(dynamic_type, "cell.value")?;
                        builder.build_call(
                            cell_get,
                            &[cell.into(), dynamic_ptr.into()],
                            "cell.get",
                        )?;
                        let dynamic = builder
                            .build_load(dynamic_type, dynamic_ptr, "cell.value.load")?
                            .into_struct_value();
                        values.insert(
                            *result,
                            from_dynamic(
                                &builder,
                                dynamic,
                                *value_type,
                                bool_type,
                                f64_type,
                                ptr_type,
                            )?,
                        );
                    }
                    Instruction::CellSet {
                        cell,
                        value,
                        value_type,
                    } => {
                        let cell = values
                            .get(cell)
                            .copied()
                            .context("thiếu cell SSA")?
                            .into_pointer_value();
                        let value = values.get(value).copied().context("thiếu cell set value")?;
                        let dynamic = to_dynamic(
                            &builder,
                            value,
                            *value_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                        )?;
                        let dynamic_ptr = builder.build_alloca(dynamic_type, "cell.set.value")?;
                        builder.build_store(dynamic_ptr, dynamic)?;
                        builder.build_call(
                            cell_set,
                            &[cell.into(), dynamic_ptr.into()],
                            "cell.set",
                        )?;
                    }
                    Instruction::PromiseResolved {
                        result,
                        value,
                        value_type,
                    } => {
                        let value = values.get(value).copied().context("thiếu Promise value")?;
                        let dynamic = to_dynamic(
                            &builder,
                            value,
                            *value_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                        )?;
                        let dynamic_ptr = builder.build_alloca(dynamic_type, "promise.value")?;
                        builder.build_store(dynamic_ptr, dynamic)?;
                        let call = builder.build_call(
                            promise_resolved,
                            &[dynamic_ptr.into()],
                            "promise.resolved",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("promise_resolved không trả pointer")?,
                        );
                    }
                    Instruction::PromiseRejected {
                        result,
                        reason,
                        reason_type,
                    } => {
                        let reason = values
                            .get(reason)
                            .copied()
                            .context("thiếu Promise rejection reason")?;
                        let dynamic = to_dynamic(
                            &builder,
                            reason,
                            *reason_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                        )?;
                        let dynamic_ptr = builder.build_alloca(dynamic_type, "promise.reason")?;
                        builder.build_store(dynamic_ptr, dynamic)?;
                        let call = builder.build_call(
                            promise_rejected,
                            &[dynamic_ptr.into()],
                            "promise.rejected",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("promise_rejected không trả pointer")?,
                        );
                    }
                    Instruction::PromisePending { result } => {
                        let call = builder.build_call(promise_pending, &[], "promise.pending")?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("promise_pending không trả pointer")?,
                        );
                    }
                    Instruction::PromiseSettle {
                        promise,
                        value,
                        value_type,
                        rejected,
                    } => {
                        let promise = values
                            .get(promise)
                            .copied()
                            .context("thiếu Promise capability SSA")?
                            .into_pointer_value();
                        let value = values
                            .get(value)
                            .copied()
                            .context("thiếu Promise settlement value")?;
                        let dynamic = to_dynamic(
                            &builder,
                            value,
                            *value_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                        )?;
                        let dynamic_ptr =
                            builder.build_alloca(dynamic_type, "promise.settlement")?;
                        builder.build_store(dynamic_ptr, dynamic)?;
                        builder.build_call(
                            promise_settle,
                            &[
                                promise.into(),
                                bool_type.const_int(*rejected as u64, false).into(),
                                dynamic_ptr.into(),
                            ],
                            "promise.settle",
                        )?;
                    }
                    Instruction::PromiseThen {
                        result,
                        promise,
                        on_fulfilled,
                        on_rejected,
                    } => {
                        let promise = values
                            .get(promise)
                            .copied()
                            .context("thiếu Promise SSA")?
                            .into_pointer_value();
                        let on_fulfilled = on_fulfilled
                            .map(|handler| {
                                values
                                    .get(&handler)
                                    .copied()
                                    .context("thiếu Promise fulfillment handler")
                                    .map(BasicValueEnum::into_pointer_value)
                            })
                            .transpose()?
                            .unwrap_or_else(|| ptr_type.const_null());
                        let on_rejected = on_rejected
                            .map(|handler| {
                                values
                                    .get(&handler)
                                    .copied()
                                    .context("thiếu Promise rejection handler")
                                    .map(BasicValueEnum::into_pointer_value)
                            })
                            .transpose()?
                            .unwrap_or_else(|| ptr_type.const_null());
                        let call = builder.build_call(
                            promise_then,
                            &[promise.into(), on_fulfilled.into(), on_rejected.into()],
                            "promise.then",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("promise_then không trả pointer")?,
                        );
                    }
                    Instruction::MicrotaskDrain => {
                        builder.build_call(microtask_drain, &[], "microtask.drain")?;
                    }
                    Instruction::ConstUndefined { result } | Instruction::ConstNull { result } => {
                        values.insert(*result, i8_type.const_zero().into());
                    }
                    Instruction::ConstNumber { result, value } => {
                        values.insert(*result, f64_type.const_float(*value).into());
                    }
                    Instruction::ConstBool { result, value } => {
                        values.insert(*result, bool_type.const_int(*value as u64, false).into());
                    }
                    Instruction::ConstString { result, value } => {
                        let global = builder
                            .build_global_string_ptr(value, &format!(".str.{}", result.0))?;
                        values.insert(*result, global.as_pointer_value().into());
                    }
                    Instruction::ObjectNew { result } => {
                        let call = builder.build_call(object_new, &[], "object.new")?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("object_new không trả pointer")?,
                        );
                    }
                    Instruction::ObjectNewWithPrototype { result, prototype } => {
                        let prototype_type = types.get(prototype).copied();
                        let prototype = values
                            .get(prototype)
                            .copied()
                            .context("thiếu object prototype SSA")?;
                        let prototype = if prototype_type == Some(ValueType::Null) {
                            ptr_type.const_null()
                        } else {
                            prototype.into_pointer_value()
                        };
                        let call = builder.build_call(
                            object_new_with_prototype,
                            &[prototype.into()],
                            "object.new.prototype",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("object_new_with_prototype không trả pointer")?,
                        );
                    }
                    Instruction::ObjectGet {
                        result,
                        object,
                        key,
                        value_type,
                    } => {
                        let object = values
                            .get(object)
                            .copied()
                            .context("thiếu object SSA")?
                            .into_pointer_value();
                        let key = builder
                            .build_global_string_ptr(key, &format!(".object.key.{}", result.0))?;
                        let dynamic_ptr = builder.build_alloca(dynamic_type, "object.get.value")?;
                        builder.build_store(dynamic_ptr, dynamic_type.const_zero())?;
                        builder.build_call(
                            object_get_value,
                            &[
                                object.into(),
                                key.as_pointer_value().into(),
                                dynamic_ptr.into(),
                            ],
                            "object.get.value",
                        )?;
                        let dynamic = builder
                            .build_load(dynamic_type, dynamic_ptr, "object.get.load")?
                            .into_struct_value();
                        values.insert(
                            *result,
                            from_dynamic(
                                &builder,
                                dynamic,
                                *value_type,
                                bool_type,
                                f64_type,
                                ptr_type,
                            )?,
                        );
                    }
                    Instruction::ObjectSet {
                        object,
                        key,
                        value,
                        value_type,
                    } => {
                        let object = values
                            .get(object)
                            .copied()
                            .context("thiếu object SSA")?
                            .into_pointer_value();
                        let value_ptr = box_value_pointer(
                            &builder,
                            values
                                .get(value)
                                .copied()
                                .context("thiếu property value SSA")?,
                            *value_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "object.set.value",
                        )?;
                        let key = builder.build_global_string_ptr(key, ".object.set.key")?;
                        builder.build_call(
                            object_set_value,
                            &[
                                object.into(),
                                key.as_pointer_value().into(),
                                value_ptr.into(),
                            ],
                            "object.set.value",
                        )?;
                    }
                    Instruction::ObjectDelete {
                        result,
                        object,
                        key,
                    } => {
                        let object = values
                            .get(object)
                            .copied()
                            .context("thiếu object SSA")?
                            .into_pointer_value();
                        let key = builder.build_global_string_ptr(key, ".object.delete.key")?;
                        let call = builder.build_call(
                            object_delete,
                            &[object.into(), key.as_pointer_value().into()],
                            "object.delete",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("object_delete không trả bool")?,
                        );
                    }
                    Instruction::ObjectSetPrototype { object, prototype } => {
                        let prototype_type = types.get(prototype).copied();
                        let object = values
                            .get(object)
                            .copied()
                            .context("thiếu object SSA")?
                            .into_pointer_value();
                        let prototype = values
                            .get(prototype)
                            .copied()
                            .context("thiếu prototype SSA")?;
                        let prototype = if prototype_type == Some(ValueType::Null) {
                            ptr_type.const_null()
                        } else {
                            prototype.into_pointer_value()
                        };
                        builder.build_call(
                            object_set_prototype,
                            &[object.into(), prototype.into()],
                            "object.set.prototype",
                        )?;
                    }
                    Instruction::ObjectGetPrototype { result, object } => {
                        let object = values
                            .get(object)
                            .copied()
                            .context("thiếu object SSA")?
                            .into_pointer_value();
                        let call = builder.build_call(
                            object_get_prototype,
                            &[object.into()],
                            "object.get.prototype",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("object_get_prototype không trả pointer")?,
                        );
                    }
                    Instruction::ObjectDefineAccessor {
                        object,
                        key,
                        getter,
                        setter,
                        enumerable,
                        configurable,
                    } => {
                        let object = values
                            .get(object)
                            .copied()
                            .context("thiếu object SSA")?
                            .into_pointer_value();
                        let key = builder.build_global_string_ptr(key, ".accessor.key")?;
                        let getter = getter
                            .and_then(|value| values.get(&value).copied())
                            .map(|value| value.into_pointer_value())
                            .unwrap_or_else(|| ptr_type.const_null());
                        let setter = setter
                            .and_then(|value| values.get(&value).copied())
                            .map(|value| value.into_pointer_value())
                            .unwrap_or_else(|| ptr_type.const_null());
                        builder.build_call(
                            object_define_accessor,
                            &[
                                object.into(),
                                key.as_pointer_value().into(),
                                getter.into(),
                                setter.into(),
                                bool_type.const_int(*enumerable as u64, false).into(),
                                bool_type.const_int(*configurable as u64, false).into(),
                            ],
                            "object.define.accessor",
                        )?;
                    }
                    Instruction::ToBoolean {
                        result,
                        operand,
                        operand_type,
                    } => {
                        let value = values.get(operand).copied().with_context(|| {
                            format!("SSA value %v{} chưa được codegen", operand.0)
                        })?;
                        let boolean = match operand_type {
                            ValueType::Undefined | ValueType::Null => bool_type.const_zero(),
                            ValueType::Bool => value.into_int_value(),
                            ValueType::Number => builder.build_float_compare(
                                FloatPredicate::ONE,
                                value.into_float_value(),
                                f64_type.const_zero(),
                                "to.bool",
                            )?,
                            ValueType::String
                            | ValueType::Object
                            | ValueType::Callable
                            | ValueType::Cell
                            | ValueType::Promise => {
                                builder.build_is_not_null(value.into_pointer_value(), "to.bool")?
                            }
                            ValueType::Dynamic => {
                                let dynamic = value.into_struct_value();
                                let tag = builder
                                    .build_extract_value(dynamic, 0, "dynamic.tag")?
                                    .into_int_value();
                                let payload = builder
                                    .build_extract_value(dynamic, 1, "dynamic.payload")?
                                    .into_int_value();
                                let call = builder.build_call(
                                    dynamic_to_bool,
                                    &[tag.into(), payload.into()],
                                    "dynamic.bool",
                                )?;
                                call.try_as_basic_value()
                                    .basic()
                                    .context("dynamic bool không trả bool")?
                                    .into_int_value()
                            }
                        };
                        values.insert(*result, boolean.into());
                    }
                    Instruction::ToNumber {
                        result,
                        operand,
                        operand_type,
                    } => {
                        let value = values
                            .get(operand)
                            .copied()
                            .context("thiếu ToNumber operand")?;
                        let number = match operand_type {
                            ValueType::Number => value.into_float_value(),
                            ValueType::Bool => builder.build_unsigned_int_to_float(
                                value.into_int_value(),
                                f64_type,
                                "bool.to.number",
                            )?,
                            ValueType::Null => f64_type.const_zero(),
                            ValueType::Undefined => f64_type.const_float(f64::NAN),
                            ValueType::String | ValueType::Dynamic => {
                                let dynamic = to_dynamic(
                                    &builder,
                                    value,
                                    *operand_type,
                                    i8_type,
                                    i64_type,
                                    dynamic_type,
                                )?;
                                let tag = builder
                                    .build_extract_value(dynamic, 0, "to.number.tag")?
                                    .into_int_value();
                                let payload = builder
                                    .build_extract_value(dynamic, 1, "to.number.payload")?
                                    .into_int_value();
                                let call = builder.build_call(
                                    primitive_to_number,
                                    &[tag.into(), payload.into()],
                                    "primitive.to.number",
                                )?;
                                call.try_as_basic_value()
                                    .basic()
                                    .context("primitive ToNumber không trả f64")?
                                    .into_float_value()
                            }
                            ValueType::Object
                            | ValueType::Callable
                            | ValueType::Cell
                            | ValueType::Promise => {
                                bail!("ToNumber object coercion không thuộc typed LLVM path")
                            }
                        };
                        values.insert(*result, number.into());
                    }
                    Instruction::TypeOfDynamic { result, operand } => {
                        let dynamic = values
                            .get(operand)
                            .copied()
                            .context("thiếu dynamic typeof operand")?
                            .into_struct_value();
                        let text = build_dynamic_typeof(&builder, dynamic, *result, i8_type)?;
                        values.insert(*result, text.into());
                    }
                    Instruction::UnaryNumber {
                        result,
                        operator,
                        operand,
                    } => {
                        let value = float_value(&values, *operand)?;
                        let value = match operator {
                            UnaryNumberOperator::Plus => value,
                            UnaryNumberOperator::Minus => builder.build_float_neg(value, "neg")?,
                            UnaryNumberOperator::BitwiseNot => {
                                let integer =
                                    builder.build_float_to_signed_int(value, i32_type, "to.i32")?;
                                let inverted = builder.build_not(integer, "bitwise.not")?;
                                builder.build_signed_int_to_float(
                                    inverted,
                                    f64_type,
                                    "to.number",
                                )?
                            }
                        };
                        values.insert(*result, value.into());
                    }
                    Instruction::UnaryBool {
                        result,
                        operator,
                        operand,
                    } => {
                        let value = int_value(&values, *operand)?;
                        let value = match operator {
                            UnaryBoolOperator::Not => builder.build_not(value, "not")?,
                        };
                        values.insert(*result, value.into());
                    }
                    Instruction::BinaryNumber {
                        result,
                        operator,
                        left,
                        right,
                    } => {
                        let left = float_value(&values, *left)?;
                        let right = float_value(&values, *right)?;
                        let value = match operator {
                            BinaryNumberOperator::Add => {
                                builder.build_float_add(left, right, "add")?
                            }
                            BinaryNumberOperator::Subtract => {
                                builder.build_float_sub(left, right, "sub")?
                            }
                            BinaryNumberOperator::Multiply => {
                                builder.build_float_mul(left, right, "mul")?
                            }
                            BinaryNumberOperator::Divide => {
                                builder.build_float_div(left, right, "div")?
                            }
                            BinaryNumberOperator::Remainder => {
                                builder.build_float_rem(left, right, "rem")?
                            }
                            BinaryNumberOperator::Exponential => build_ecmascript_exponentiation(
                                &builder, pow_f64, left, right, f64_type,
                            )?,
                            BinaryNumberOperator::ShiftLeft
                            | BinaryNumberOperator::ShiftRight
                            | BinaryNumberOperator::ShiftRightZeroFill
                            | BinaryNumberOperator::BitwiseOr
                            | BinaryNumberOperator::BitwiseXor
                            | BinaryNumberOperator::BitwiseAnd => {
                                let left = builder
                                    .build_float_to_signed_int(left, i32_type, "left.i32")?;
                                let right = builder.build_float_to_signed_int(
                                    right,
                                    i32_type,
                                    "right.i32",
                                )?;
                                let shift = builder.build_and(
                                    right,
                                    i32_type.const_int(31, false),
                                    "shift.mask",
                                )?;
                                let integer = match operator {
                                    BinaryNumberOperator::ShiftLeft => {
                                        builder.build_left_shift(left, shift, "shl")?
                                    }
                                    BinaryNumberOperator::ShiftRight => {
                                        builder.build_right_shift(left, shift, true, "shr")?
                                    }
                                    BinaryNumberOperator::ShiftRightZeroFill => {
                                        builder.build_right_shift(left, shift, false, "ushr")?
                                    }
                                    BinaryNumberOperator::BitwiseOr => {
                                        builder.build_or(left, right, "or")?
                                    }
                                    BinaryNumberOperator::BitwiseXor => {
                                        builder.build_xor(left, right, "xor")?
                                    }
                                    BinaryNumberOperator::BitwiseAnd => {
                                        builder.build_and(left, right, "and")?
                                    }
                                    _ => unreachable!(),
                                };
                                if *operator == BinaryNumberOperator::ShiftRightZeroFill {
                                    builder.build_unsigned_int_to_float(
                                        integer,
                                        f64_type,
                                        "to.number",
                                    )?
                                } else {
                                    builder.build_signed_int_to_float(
                                        integer,
                                        f64_type,
                                        "to.number",
                                    )?
                                }
                            }
                        };
                        values.insert(*result, value.into());
                    }
                    Instruction::CompareNumber {
                        result,
                        operator,
                        left,
                        right,
                    } => {
                        let left = float_value(&values, *left)?;
                        let right = float_value(&values, *right)?;
                        let predicate = match operator {
                            CompareNumberOperator::Equal | CompareNumberOperator::StrictEqual => {
                                FloatPredicate::OEQ
                            }
                            CompareNumberOperator::NotEqual
                            | CompareNumberOperator::StrictNotEqual => FloatPredicate::UNE,
                            CompareNumberOperator::LessThan => FloatPredicate::OLT,
                            CompareNumberOperator::LessEqual => FloatPredicate::OLE,
                            CompareNumberOperator::GreaterThan => FloatPredicate::OGT,
                            CompareNumberOperator::GreaterEqual => FloatPredicate::OGE,
                        };
                        values.insert(
                            *result,
                            builder
                                .build_float_compare(predicate, left, right, "cmp")?
                                .into(),
                        );
                    }
                    Instruction::CompareString {
                        result,
                        left,
                        right,
                    } => {
                        let left = values
                            .get(left)
                            .copied()
                            .context("thiếu string SSA")?
                            .into_pointer_value();
                        let right = values
                            .get(right)
                            .copied()
                            .context("thiếu string SSA")?
                            .into_pointer_value();
                        let call =
                            builder.build_call(strcmp, &[left.into(), right.into()], "strcmp")?;
                        let result_value = builder.build_int_compare(
                            inkwell::IntPredicate::EQ,
                            call.try_as_basic_value()
                                .basic()
                                .context("strcmp không trả int")?
                                .into_int_value(),
                            i32_type.const_zero(),
                            "string.eq",
                        )?;
                        values.insert(*result, result_value.into());
                    }
                    Instruction::CompareObject {
                        result,
                        operator,
                        left,
                        right,
                    } => {
                        let left = values
                            .get(left)
                            .copied()
                            .context("thiếu object SSA")?
                            .into_pointer_value();
                        let right = values
                            .get(right)
                            .copied()
                            .context("thiếu object SSA")?
                            .into_pointer_value();
                        let predicate = match operator {
                            CompareNumberOperator::Equal | CompareNumberOperator::StrictEqual => {
                                inkwell::IntPredicate::EQ
                            }
                            CompareNumberOperator::NotEqual
                            | CompareNumberOperator::StrictNotEqual => inkwell::IntPredicate::NE,
                            _ => bail!("object comparison operator {:?} chưa hỗ trợ", operator),
                        };
                        values.insert(
                            *result,
                            builder
                                .build_int_compare(predicate, left, right, "object.eq")?
                                .into(),
                        );
                    }
                    Instruction::Phi { .. } => {}
                    Instruction::ClosureNew {
                        result,
                        function,
                        captures,
                        capture_types,
                    } => {
                        let code = llvm_functions
                            .get(function)
                            .copied()
                            .with_context(|| format!("unknown closure function `{function}`"))?
                            .as_global_value()
                            .as_pointer_value();
                        let capture_array = build_dynamic_array(
                            &builder,
                            captures,
                            capture_types,
                            &values,
                            i8_type,
                            i32_type,
                            i64_type,
                            dynamic_type,
                        )?;
                        let call = builder.build_call(
                            closure_new,
                            &[
                                code.into(),
                                i32_type.const_int(captures.len() as u64, false).into(),
                                capture_array.into(),
                            ],
                            "closure.new",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("closure_new không trả pointer")?,
                        );
                    }
                    Instruction::CallDirect {
                        result,
                        function,
                        arguments,
                        argument_types,
                        return_type,
                    } => {
                        let target = llvm_functions
                            .get(function)
                            .copied()
                            .with_context(|| format!("unknown direct callee `{function}`"))?;
                        let argv = build_dynamic_array(
                            &builder,
                            arguments,
                            argument_types,
                            &values,
                            i8_type,
                            i32_type,
                            i64_type,
                            dynamic_type,
                        )?;
                        let dynamic_ptr =
                            builder.build_alloca(dynamic_type, "call.direct.result")?;
                        builder.build_store(dynamic_ptr, dynamic_type.const_zero())?;
                        let call = builder.build_call(
                            target,
                            &[
                                ptr_type.const_null().into(),
                                i32_type.const_int(arguments.len() as u64, false).into(),
                                argv.into(),
                                dynamic_ptr.into(),
                            ],
                            "call.direct",
                        )?;
                        let status = call
                            .try_as_basic_value()
                            .basic()
                            .context("direct call không trả completion status")?
                            .into_int_value();
                        let dynamic = builder
                            .build_load(dynamic_type, dynamic_ptr, "call.direct.load")?
                            .into_struct_value();
                        let continuation = propagate_call_completion(
                            context,
                            &builder,
                            main,
                            is_process_entry,
                            status,
                            dynamic,
                            dynamic_type,
                            i8_type,
                            throw_uncaught,
                            recursion_leave,
                            &format!("direct.{}.{}", index, result.0),
                        )?;
                        llvm_block_exits[index] = continuation;
                        values.insert(
                            *result,
                            from_dynamic(
                                &builder,
                                dynamic,
                                *return_type,
                                bool_type,
                                f64_type,
                                ptr_type,
                            )?,
                        );
                    }
                    Instruction::CallIndirect {
                        result,
                        callee,
                        arguments,
                        argument_types,
                        return_type,
                    } => {
                        let closure = values
                            .get(callee)
                            .copied()
                            .context("thiếu indirect callee")?
                            .into_pointer_value();
                        let argv = build_dynamic_array(
                            &builder,
                            arguments,
                            argument_types,
                            &values,
                            i8_type,
                            i32_type,
                            i64_type,
                            dynamic_type,
                        )?;
                        let dynamic_ptr =
                            builder.build_alloca(dynamic_type, "call.indirect.result")?;
                        builder.build_store(dynamic_ptr, dynamic_type.const_zero())?;
                        let call = builder.build_call(
                            closure_call,
                            &[
                                closure.into(),
                                i32_type.const_int(arguments.len() as u64, false).into(),
                                argv.into(),
                                dynamic_ptr.into(),
                            ],
                            "call.indirect",
                        )?;
                        let status = call
                            .try_as_basic_value()
                            .basic()
                            .context("indirect call không trả completion status")?
                            .into_int_value();
                        let dynamic = builder
                            .build_load(dynamic_type, dynamic_ptr, "call.indirect.load")?
                            .into_struct_value();
                        let continuation = propagate_call_completion(
                            context,
                            &builder,
                            main,
                            is_process_entry,
                            status,
                            dynamic,
                            dynamic_type,
                            i8_type,
                            throw_uncaught,
                            recursion_leave,
                            &format!("indirect.{}.{}", index, result.0),
                        )?;
                        llvm_block_exits[index] = continuation;
                        values.insert(
                            *result,
                            from_dynamic(
                                &builder,
                                dynamic,
                                *return_type,
                                bool_type,
                                f64_type,
                                ptr_type,
                            )?,
                        );
                    }

                    Instruction::CurrentThis { result } => {
                        let dynamic_ptr =
                            builder.build_alloca(dynamic_type, "current.this.value")?;
                        builder.build_call(current_this, &[dynamic_ptr.into()], "current.this")?;
                        let dynamic = builder
                            .build_load(dynamic_type, dynamic_ptr, "current.this.load")?
                            .into_struct_value();
                        values.insert(*result, dynamic.into());
                    }
                    Instruction::CurrentCallable { result } => {
                        let closure = main
                            .get_nth_param(0)
                            .context("JavaScript function thiếu current callable")?
                            .into_pointer_value();
                        values.insert(*result, closure.into());
                    }
                    Instruction::ArgumentsObject { result } => {
                        let argc = main
                            .get_nth_param(1)
                            .context("JavaScript function thiếu argc")?
                            .into_int_value();
                        let argv = main
                            .get_nth_param(2)
                            .context("JavaScript function thiếu argv")?
                            .into_pointer_value();
                        let call = builder.build_call(
                            arguments_object,
                            &[argc.into(), argv.into()],
                            "arguments.object",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("arguments_object không trả pointer")?,
                        );
                    }
                    Instruction::RestArray { result, start } => {
                        let argc = main
                            .get_nth_param(1)
                            .context("JavaScript function thiếu argc")?
                            .into_int_value();
                        let argv = main
                            .get_nth_param(2)
                            .context("JavaScript function thiếu argv")?
                            .into_pointer_value();
                        let call = builder.build_call(
                            rest_array,
                            &[
                                argc.into(),
                                argv.into(),
                                i32_type.const_int(*start as u64, false).into(),
                            ],
                            "rest.array",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("rest_array không trả pointer")?,
                        );
                    }
                    Instruction::ArrayPush {
                        array,
                        value,
                        value_type,
                    } => {
                        let array = values
                            .get(array)
                            .copied()
                            .context("thiếu array SSA")?
                            .into_pointer_value();
                        let value_ptr = box_value_pointer(
                            &builder,
                            values.get(value).copied().context("thiếu array value")?,
                            *value_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "array.push.value",
                        )?;
                        builder.build_call(
                            array_push,
                            &[array.into(), value_ptr.into()],
                            "array.push",
                        )?;
                    }
                    Instruction::ArraySpread {
                        array,
                        iterable,
                        iterable_type,
                    } => {
                        let array = values
                            .get(array)
                            .copied()
                            .context("thiếu array SSA")?
                            .into_pointer_value();
                        let iterable_ptr = box_value_pointer(
                            &builder,
                            values
                                .get(iterable)
                                .copied()
                                .context("thiếu array spread iterable")?,
                            *iterable_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "array.spread.iterable",
                        )?;
                        let error_ptr = builder.build_alloca(dynamic_type, "array.spread.error")?;
                        builder.build_store(error_ptr, dynamic_type.const_zero())?;
                        let call = builder.build_call(
                            array_spread,
                            &[array.into(), iterable_ptr.into(), error_ptr.into()],
                            "array.spread",
                        )?;
                        let status = call
                            .try_as_basic_value()
                            .basic()
                            .context("array_spread không trả status")?
                            .into_int_value();
                        let dynamic = builder
                            .build_load(dynamic_type, error_ptr, "array.spread.error.load")?
                            .into_struct_value();
                        let continuation = propagate_call_completion(
                            context,
                            &builder,
                            main,
                            is_process_entry,
                            status,
                            dynamic,
                            dynamic_type,
                            i8_type,
                            throw_uncaught,
                            recursion_leave,
                            &format!("array.spread.{index}"),
                        )?;
                        llvm_block_exits[index] = continuation;
                    }
                    Instruction::DynamicUnary {
                        result,
                        operator,
                        operand,
                        operand_type,
                    } => {
                        let operand_ptr = box_value_pointer(
                            &builder,
                            values
                                .get(operand)
                                .copied()
                                .context("thiếu dynamic unary operand")?,
                            *operand_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "dynamic.unary.operand",
                        )?;
                        let result_ptr =
                            builder.build_alloca(dynamic_type, "dynamic.unary.result")?;
                        builder.build_store(result_ptr, dynamic_type.const_zero())?;
                        let call = builder.build_call(
                            dynamic_unary,
                            &[
                                i8_type.const_int(*operator as u64, false).into(),
                                operand_ptr.into(),
                                result_ptr.into(),
                            ],
                            "dynamic.unary",
                        )?;
                        let status = call
                            .try_as_basic_value()
                            .basic()
                            .context("dynamic_unary không trả status")?
                            .into_int_value();
                        let dynamic = builder
                            .build_load(dynamic_type, result_ptr, "dynamic.unary.load")?
                            .into_struct_value();
                        let continuation = propagate_call_completion(
                            context,
                            &builder,
                            main,
                            is_process_entry,
                            status,
                            dynamic,
                            dynamic_type,
                            i8_type,
                            throw_uncaught,
                            recursion_leave,
                            &format!("dynamic.unary.{index}.{}", result.0),
                        )?;
                        llvm_block_exits[index] = continuation;
                        values.insert(*result, dynamic.into());
                    }
                    Instruction::DynamicBinary {
                        result,
                        operator,
                        left,
                        left_type,
                        right,
                        right_type,
                    } => {
                        let left_value = values.get(left).copied().context("thiếu dynamic left")?;
                        let right_value =
                            values.get(right).copied().context("thiếu dynamic right")?;

                        let guarded_add = *operator == DynamicBinaryOperator::Add
                            && matches!(*left_type, ValueType::Number | ValueType::Dynamic)
                            && matches!(*right_type, ValueType::Number | ValueType::Dynamic);

                        if guarded_add {
                            let suffix = format!("{index}.{}", result.0);
                            let (dynamic, continuation) = build_guarded_dynamic_add(
                                context,
                                &builder,
                                main,
                                is_process_entry,
                                left_value,
                                *left_type,
                                right_value,
                                *right_type,
                                dynamic_type,
                                i8_type,
                                i64_type,
                                f64_type,
                                dynamic_binary,
                                throw_uncaught,
                                recursion_leave,
                                &suffix,
                            )?;
                            llvm_block_exits[index] = continuation;
                            values.insert(*result, dynamic.into());
                        } else {
                            let left_ptr = box_value_pointer(
                                &builder,
                                left_value,
                                *left_type,
                                i8_type,
                                i64_type,
                                dynamic_type,
                                "dynamic.binary.left",
                            )?;
                            let right_ptr = box_value_pointer(
                                &builder,
                                right_value,
                                *right_type,
                                i8_type,
                                i64_type,
                                dynamic_type,
                                "dynamic.binary.right",
                            )?;
                            let result_ptr =
                                builder.build_alloca(dynamic_type, "dynamic.binary.result")?;
                            builder.build_store(result_ptr, dynamic_type.const_zero())?;
                            let call = builder.build_call(
                                dynamic_binary,
                                &[
                                    i8_type.const_int(*operator as u64, false).into(),
                                    left_ptr.into(),
                                    right_ptr.into(),
                                    result_ptr.into(),
                                ],
                                "dynamic.binary",
                            )?;
                            let status = call
                                .try_as_basic_value()
                                .basic()
                                .context("dynamic_binary không trả status")?
                                .into_int_value();
                            let dynamic = builder
                                .build_load(dynamic_type, result_ptr, "dynamic.binary.load")?
                                .into_struct_value();
                            let continuation = propagate_call_completion(
                                context,
                                &builder,
                                main,
                                is_process_entry,
                                status,
                                dynamic,
                                dynamic_type,
                                i8_type,
                                throw_uncaught,
                                recursion_leave,
                                &format!("dynamic.binary.{index}.{}", result.0),
                            )?;
                            llvm_block_exits[index] = continuation;
                            values.insert(*result, dynamic.into());
                        }
                    }
                    Instruction::DynamicGet {
                        result,
                        object,
                        object_type,
                        key,
                    } => {
                        let object_ptr = box_value_pointer(
                            &builder,
                            values
                                .get(object)
                                .copied()
                                .context("thiếu dynamic object")?,
                            *object_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "dynamic.get.object",
                        )?;
                        let key = builder.build_global_string_ptr(
                            key,
                            &format!(".dynamic.get.key.{}", result.0),
                        )?;
                        let result_ptr =
                            builder.build_alloca(dynamic_type, "dynamic.get.result")?;
                        builder.build_store(result_ptr, dynamic_type.const_zero())?;
                        let call = builder.build_call(
                            dynamic_get,
                            &[
                                object_ptr.into(),
                                key.as_pointer_value().into(),
                                result_ptr.into(),
                            ],
                            "dynamic.get",
                        )?;
                        let status = call
                            .try_as_basic_value()
                            .basic()
                            .context("dynamic_get không trả status")?
                            .into_int_value();
                        let dynamic = builder
                            .build_load(dynamic_type, result_ptr, "dynamic.get.load")?
                            .into_struct_value();
                        let continuation = propagate_call_completion(
                            context,
                            &builder,
                            main,
                            is_process_entry,
                            status,
                            dynamic,
                            dynamic_type,
                            i8_type,
                            throw_uncaught,
                            recursion_leave,
                            &format!("dynamic.get.{index}.{}", result.0),
                        )?;
                        llvm_block_exits[index] = continuation;
                        values.insert(*result, dynamic.into());
                    }
                    Instruction::DynamicSet {
                        object,
                        object_type,
                        key,
                        value,
                        value_type,
                    } => {
                        let object_ptr = box_value_pointer(
                            &builder,
                            values
                                .get(object)
                                .copied()
                                .context("thiếu dynamic object")?,
                            *object_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "dynamic.set.object",
                        )?;
                        let value_ptr = box_value_pointer(
                            &builder,
                            values
                                .get(value)
                                .copied()
                                .context("thiếu dynamic set value")?,
                            *value_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "dynamic.set.value",
                        )?;
                        let key = builder.build_global_string_ptr(key, ".dynamic.set.key")?;
                        let error_ptr = builder.build_alloca(dynamic_type, "dynamic.set.error")?;
                        builder.build_store(error_ptr, dynamic_type.const_zero())?;
                        let call = builder.build_call(
                            dynamic_set,
                            &[
                                object_ptr.into(),
                                key.as_pointer_value().into(),
                                value_ptr.into(),
                                error_ptr.into(),
                            ],
                            "dynamic.set",
                        )?;
                        let status = call
                            .try_as_basic_value()
                            .basic()
                            .context("dynamic_set không trả status")?
                            .into_int_value();
                        let dynamic = builder
                            .build_load(dynamic_type, error_ptr, "dynamic.set.error.load")?
                            .into_struct_value();
                        let continuation = propagate_call_completion(
                            context,
                            &builder,
                            main,
                            is_process_entry,
                            status,
                            dynamic,
                            dynamic_type,
                            i8_type,
                            throw_uncaught,
                            recursion_leave,
                            &format!("dynamic.set.{index}"),
                        )?;
                        llvm_block_exits[index] = continuation;
                    }
                    Instruction::DynamicDelete {
                        result,
                        object,
                        object_type,
                        key,
                    } => {
                        let object_ptr = box_value_pointer(
                            &builder,
                            values
                                .get(object)
                                .copied()
                                .context("thiếu dynamic object")?,
                            *object_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "dynamic.delete.object",
                        )?;
                        let key = builder.build_global_string_ptr(
                            key,
                            &format!(".dynamic.delete.key.{}", result.0),
                        )?;
                        let result_ptr =
                            builder.build_alloca(dynamic_type, "dynamic.delete.result")?;
                        builder.build_store(result_ptr, dynamic_type.const_zero())?;
                        let call = builder.build_call(
                            dynamic_delete,
                            &[
                                object_ptr.into(),
                                key.as_pointer_value().into(),
                                result_ptr.into(),
                            ],
                            "dynamic.delete",
                        )?;
                        let status = call
                            .try_as_basic_value()
                            .basic()
                            .context("dynamic_delete không trả status")?
                            .into_int_value();
                        let dynamic = builder
                            .build_load(dynamic_type, result_ptr, "dynamic.delete.load")?
                            .into_struct_value();
                        let continuation = propagate_call_completion(
                            context,
                            &builder,
                            main,
                            is_process_entry,
                            status,
                            dynamic,
                            dynamic_type,
                            i8_type,
                            throw_uncaught,
                            recursion_leave,
                            &format!("dynamic.delete.{index}.{}", result.0),
                        )?;
                        llvm_block_exits[index] = continuation;
                        values.insert(
                            *result,
                            from_dynamic(
                                &builder,
                                dynamic,
                                ValueType::Bool,
                                bool_type,
                                f64_type,
                                ptr_type,
                            )?,
                        );
                    }
                    Instruction::ClosureNewGeneric {
                        result,
                        function,
                        captures,
                        capture_types,
                        constructable,
                        strict,
                        lexical_this,
                        lexical_this_type,
                    } => {
                        let code = llvm_functions
                            .get(function)
                            .copied()
                            .with_context(|| {
                                format!("unknown generic closure function `{function}`")
                            })?
                            .as_global_value()
                            .as_pointer_value();
                        let capture_array = build_dynamic_array(
                            &builder,
                            captures,
                            capture_types,
                            &values,
                            i8_type,
                            i32_type,
                            i64_type,
                            dynamic_type,
                        )?;
                        let lexical_pointer = match (lexical_this, lexical_this_type) {
                            (Some(value), Some(value_type)) => box_value_pointer(
                                &builder,
                                values
                                    .get(value)
                                    .copied()
                                    .context("thiếu lexical this SSA")?,
                                *value_type,
                                i8_type,
                                i64_type,
                                dynamic_type,
                                "closure.lexical.this",
                            )?,
                            (None, None) => ptr_type.const_null(),
                            _ => bail!("lexical this metadata không khớp"),
                        };
                        let mut flags = 0_u64;
                        if *constructable {
                            flags |= 1;
                        }
                        if lexical_this.is_some() {
                            flags |= 2;
                        }
                        if *strict {
                            flags |= 4;
                        }
                        let call = builder.build_call(
                            closure_new_ex,
                            &[
                                code.into(),
                                i32_type.const_int(captures.len() as u64, false).into(),
                                capture_array.into(),
                                i32_type.const_int(flags, false).into(),
                                lexical_pointer.into(),
                            ],
                            "closure.new.generic",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("closure_new_ex không trả pointer")?,
                        );
                    }
                    Instruction::CallValue {
                        result,
                        callee,
                        callee_type,
                        receiver,
                        receiver_type,
                        arguments,
                    } => {
                        let callee_ptr = box_value_pointer(
                            &builder,
                            values
                                .get(callee)
                                .copied()
                                .context("thiếu generic callee")?,
                            *callee_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "call.value.callee",
                        )?;
                        let receiver_ptr = match (receiver, receiver_type) {
                            (Some(value), Some(value_type)) => box_value_pointer(
                                &builder,
                                values.get(value).copied().context("thiếu call receiver")?,
                                *value_type,
                                i8_type,
                                i64_type,
                                dynamic_type,
                                "call.value.receiver",
                            )?,
                            (None, None) => {
                                let pointer = builder
                                    .build_alloca(dynamic_type, "call.value.undefined.this")?;
                                builder.build_store(pointer, dynamic_type.const_zero())?;
                                pointer
                            }
                            _ => bail!("call receiver metadata không khớp"),
                        };
                        let new_target_ptr =
                            builder.build_alloca(dynamic_type, "call.value.new.target")?;
                        builder.build_store(new_target_ptr, dynamic_type.const_zero())?;
                        let built = build_generic_arguments(
                            &builder,
                            arguments,
                            &values,
                            i8_type,
                            i32_type,
                            i64_type,
                            ptr_type,
                            dynamic_type,
                            argv_builder_init,
                            argv_builder_push,
                            argv_builder_spread,
                            argv_builder_len,
                            argv_builder_data,
                        )?;
                        let result_ptr = builder.build_alloca(dynamic_type, "call.value.result")?;
                        builder.build_store(result_ptr, dynamic_type.const_zero())?;
                        let call = builder.build_call(
                            callable_dispatch,
                            &[
                                callee_ptr.into(),
                                receiver_ptr.into(),
                                new_target_ptr.into(),
                                bool_type.const_zero().into(),
                                built.argc.into(),
                                built.argv.into(),
                                result_ptr.into(),
                            ],
                            "call.value",
                        )?;
                        if let Some(handle) = built.builder {
                            builder.build_call(
                                argv_builder_destroy,
                                &[handle.into()],
                                "call.argv.destroy",
                            )?;
                        }
                        let status = call
                            .try_as_basic_value()
                            .basic()
                            .context("callable_dispatch không trả status")?
                            .into_int_value();
                        let dynamic = builder
                            .build_load(dynamic_type, result_ptr, "call.value.load")?
                            .into_struct_value();
                        let continuation = propagate_call_completion(
                            context,
                            &builder,
                            main,
                            is_process_entry,
                            status,
                            dynamic,
                            dynamic_type,
                            i8_type,
                            throw_uncaught,
                            recursion_leave,
                            &format!("call.value.{index}.{}", result.0),
                        )?;
                        llvm_block_exits[index] = continuation;
                        values.insert(*result, dynamic.into());
                    }
                    Instruction::ConstructValue {
                        result,
                        callee,
                        callee_type,
                        arguments,
                    } => {
                        let callee_ptr = box_value_pointer(
                            &builder,
                            values.get(callee).copied().context("thiếu constructor")?,
                            *callee_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "construct.callee",
                        )?;
                        let built = build_generic_arguments(
                            &builder,
                            arguments,
                            &values,
                            i8_type,
                            i32_type,
                            i64_type,
                            ptr_type,
                            dynamic_type,
                            argv_builder_init,
                            argv_builder_push,
                            argv_builder_spread,
                            argv_builder_len,
                            argv_builder_data,
                        )?;
                        let result_ptr = builder.build_alloca(dynamic_type, "construct.result")?;
                        builder.build_store(result_ptr, dynamic_type.const_zero())?;
                        let call = builder.build_call(
                            callable_construct,
                            &[
                                callee_ptr.into(),
                                built.argc.into(),
                                built.argv.into(),
                                result_ptr.into(),
                            ],
                            "construct.value",
                        )?;
                        if let Some(handle) = built.builder {
                            builder.build_call(
                                argv_builder_destroy,
                                &[handle.into()],
                                "construct.argv.destroy",
                            )?;
                        }
                        let status = call
                            .try_as_basic_value()
                            .basic()
                            .context("callable_construct không trả status")?
                            .into_int_value();
                        let dynamic = builder
                            .build_load(dynamic_type, result_ptr, "construct.load")?
                            .into_struct_value();
                        let continuation = propagate_call_completion(
                            context,
                            &builder,
                            main,
                            is_process_entry,
                            status,
                            dynamic,
                            dynamic_type,
                            i8_type,
                            throw_uncaught,
                            recursion_leave,
                            &format!("construct.{index}.{}", result.0),
                        )?;
                        llvm_block_exits[index] = continuation;
                        values.insert(*result, dynamic.into());
                    }
                    Instruction::BindValue {
                        result,
                        target,
                        target_type,
                        this_arg,
                        this_type,
                        arguments,
                    } => {
                        let target_ptr = box_value_pointer(
                            &builder,
                            values.get(target).copied().context("thiếu bind target")?,
                            *target_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "bind.target",
                        )?;
                        let this_ptr = box_value_pointer(
                            &builder,
                            values.get(this_arg).copied().context("thiếu bind this")?,
                            *this_type,
                            i8_type,
                            i64_type,
                            dynamic_type,
                            "bind.this",
                        )?;
                        let built = build_generic_arguments(
                            &builder,
                            arguments,
                            &values,
                            i8_type,
                            i32_type,
                            i64_type,
                            ptr_type,
                            dynamic_type,
                            argv_builder_init,
                            argv_builder_push,
                            argv_builder_spread,
                            argv_builder_len,
                            argv_builder_data,
                        )?;
                        let result_ptr = builder.build_alloca(dynamic_type, "bind.result")?;
                        builder.build_store(result_ptr, dynamic_type.const_zero())?;
                        let call = builder.build_call(
                            callable_bind,
                            &[
                                target_ptr.into(),
                                this_ptr.into(),
                                built.argc.into(),
                                built.argv.into(),
                                result_ptr.into(),
                            ],
                            "bind.value",
                        )?;
                        if let Some(handle) = built.builder {
                            builder.build_call(
                                argv_builder_destroy,
                                &[handle.into()],
                                "bind.argv.destroy",
                            )?;
                        }
                        let status = call
                            .try_as_basic_value()
                            .basic()
                            .context("callable_bind không trả status")?
                            .into_int_value();
                        let dynamic = builder
                            .build_load(dynamic_type, result_ptr, "bind.load")?
                            .into_struct_value();
                        let continuation = propagate_call_completion(
                            context,
                            &builder,
                            main,
                            is_process_entry,
                            status,
                            dynamic,
                            dynamic_type,
                            i8_type,
                            throw_uncaught,
                            recursion_leave,
                            &format!("bind.{index}.{}", result.0),
                        )?;
                        llvm_block_exits[index] = continuation;
                        values.insert(
                            *result,
                            from_dynamic(
                                &builder,
                                dynamic,
                                ValueType::Callable,
                                bool_type,
                                f64_type,
                                ptr_type,
                            )?,
                        );
                    }
                    Instruction::CallBuiltin {
                        builtin: Builtin::ConsoleLog,
                        arguments,
                        display_values,
                    } => {
                        if arguments.len() != display_values.len() {
                            bail!("console.log metadata không khớp số argument")
                        }
                        for (index, display_value) in display_values.iter().enumerate() {
                            if index > 0 {
                                let separator = builder.build_global_string_ptr(" ", ".fmt.sep")?;
                                builder.build_call(
                                    printf,
                                    &[separator.as_pointer_value().into()],
                                    "printf.sep",
                                )?;
                            }
                            if let Some(display_value) = display_value {
                                let text = builder.build_global_string_ptr(
                                    display_value,
                                    &format!(".display.{}.{index}", index),
                                )?;
                                let format =
                                    builder.build_global_string_ptr("%s", ".fmt.display")?;
                                builder.build_call(
                                    printf,
                                    &[
                                        format.as_pointer_value().into(),
                                        text.as_pointer_value().into(),
                                    ],
                                    "printf.display",
                                )?;
                            } else {
                                let argument = arguments[index];
                                let value = values
                                    .get(&argument)
                                    .copied()
                                    .context("thiếu console argument")?;
                                match types
                                    .get(&argument)
                                    .copied()
                                    .context("thiếu kiểu console argument")?
                                {
                                    ValueType::Number => {
                                        let format = builder
                                            .build_global_string_ptr("%.15g", ".fmt.number")?;
                                        builder.build_call(
                                            printf,
                                            &[
                                                format.as_pointer_value().into(),
                                                value.into_float_value().into(),
                                            ],
                                            "printf.number",
                                        )?;
                                    }
                                    ValueType::Bool => {
                                        let yes = builder
                                            .build_global_string_ptr("true", ".bool.true")?;
                                        let no = builder
                                            .build_global_string_ptr("false", ".bool.false")?;
                                        let text = builder.build_select(
                                            value.into_int_value(),
                                            yes.as_pointer_value(),
                                            no.as_pointer_value(),
                                            "bool.text",
                                        )?;
                                        let format =
                                            builder.build_global_string_ptr("%s", ".fmt.bool")?;
                                        builder.build_call(
                                            printf,
                                            &[
                                                format.as_pointer_value().into(),
                                                text.into_pointer_value().into(),
                                            ],
                                            "printf.bool",
                                        )?;
                                    }
                                    ValueType::String => {
                                        let format =
                                            builder.build_global_string_ptr("%s", ".fmt.string")?;
                                        builder.build_call(
                                            printf,
                                            &[
                                                format.as_pointer_value().into(),
                                                value.into_pointer_value().into(),
                                            ],
                                            "printf.string",
                                        )?;
                                    }
                                    ValueType::Undefined | ValueType::Null => {
                                        let text = builder.build_global_string_ptr(
                                            if types.get(&argument).copied()
                                                == Some(ValueType::Undefined)
                                            {
                                                "undefined"
                                            } else {
                                                "null"
                                            },
                                            ".fmt.nullish",
                                        )?;
                                        let format = builder
                                            .build_global_string_ptr("%s", ".fmt.nullish.spec")?;
                                        builder.build_call(
                                            printf,
                                            &[
                                                format.as_pointer_value().into(),
                                                text.as_pointer_value().into(),
                                            ],
                                            "printf.nullish",
                                        )?;
                                    }
                                    ValueType::Object
                                    | ValueType::Callable
                                    | ValueType::Cell
                                    | ValueType::Promise => {
                                        let dynamic = to_dynamic(
                                            &builder,
                                            value,
                                            types
                                                .get(&argument)
                                                .copied()
                                                .context("thiếu pointer console type")?,
                                            i8_type,
                                            i64_type,
                                            dynamic_type,
                                        )?;
                                        let tag = dynamic
                                            .get_field_at_index(0)
                                            .context("dynamic tag thiếu")?
                                            .into_int_value();
                                        let payload = dynamic
                                            .get_field_at_index(1)
                                            .context("dynamic payload thiếu")?
                                            .into_int_value();
                                        builder.build_call(
                                            dynamic_print,
                                            &[tag.into(), payload.into()],
                                            "object.print",
                                        )?;
                                    }
                                    ValueType::Dynamic => {
                                        let dynamic = value.into_struct_value();
                                        let tag = builder
                                            .build_extract_value(dynamic, 0, "dynamic.tag")?
                                            .into_int_value();
                                        let payload = builder
                                            .build_extract_value(dynamic, 1, "dynamic.payload")?
                                            .into_int_value();
                                        builder.build_call(
                                            dynamic_print,
                                            &[tag.into(), payload.into()],
                                            "dynamic.print",
                                        )?;
                                    }
                                }
                            }
                        }
                        let newline = builder.build_global_string_ptr("\n", ".fmt.nl")?;
                        builder.build_call(
                            printf,
                            &[newline.as_pointer_value().into()],
                            "printf.nl",
                        )?;
                    }
                }
            }
            match &block.terminator {
                Terminator::Jump(target) => {
                    builder.build_unconditional_branch(llvm_blocks[target.0 as usize])?;
                }
                Terminator::Branch {
                    condition,
                    then_block,
                    else_block,
                } => {
                    let condition = int_value(&values, *condition)?;
                    builder.build_conditional_branch(
                        condition,
                        llvm_blocks[then_block.0 as usize],
                        llvm_blocks[else_block.0 as usize],
                    )?;
                }
                Terminator::ReturnI32(value) => {
                    builder.build_return(Some(&i32_type.const_int(*value as u64, true)))?;
                }
                Terminator::ReturnValue { value, value_type } => {
                    builder.build_call(recursion_leave, &[], "recursion.leave")?;
                    let value = values
                        .get(value)
                        .copied()
                        .context("thiếu return SSA value")?;
                    let dynamic = to_dynamic(
                        &builder,
                        value,
                        *value_type,
                        i8_type,
                        i64_type,
                        dynamic_type,
                    )?;
                    let out = main
                        .get_nth_param(3)
                        .context("JavaScript function thiếu return out pointer")?
                        .into_pointer_value();
                    builder.build_store(out, dynamic)?;
                    builder.build_return(Some(&i8_type.const_zero()))?;
                }
                Terminator::ThrowValue { value, value_type } => {
                    let value = values
                        .get(value)
                        .copied()
                        .context("thiếu thrown SSA value")?;
                    let dynamic = to_dynamic(
                        &builder,
                        value,
                        *value_type,
                        i8_type,
                        i64_type,
                        dynamic_type,
                    )?;
                    let tag = builder
                        .build_extract_value(dynamic, 0, "throw.tag")?
                        .into_int_value();
                    let payload = builder
                        .build_extract_value(dynamic, 1, "throw.payload")?
                        .into_int_value();
                    if is_process_entry {
                        builder.build_call(
                            throw_uncaught,
                            &[tag.into(), payload.into()],
                            "throw.uncaught",
                        )?;
                        builder.build_unreachable()?;
                    } else {
                        let out = main
                            .get_nth_param(3)
                            .context("JavaScript function thiếu throw out pointer")?
                            .into_pointer_value();
                        builder.build_store(out, dynamic)?;
                        builder.build_call(recursion_leave, &[], "recursion.leave.throw")?;
                        builder.build_return(Some(&i8_type.const_int(1, false)))?;
                    }
                }
                Terminator::TailCallDirect {
                    function,
                    arguments,
                    argument_types,
                } => {
                    let target = llvm_functions
                        .get(function)
                        .copied()
                        .with_context(|| format!("unknown direct tail callee `{function}`"))?;
                    // A stack alloca cannot safely escape into a tail-called
                    // frame. Use a reusable thread-local buffer whose lifetime
                    // spans the whole tail-call chain and supports cross-arity
                    // mutual recursion without leaking one allocation per hop.
                    let tail_argc = i32_type.const_int(arguments.len() as u64, false);
                    let tail_argv_call = builder.build_call(
                        tail_argv_reserve,
                        &[tail_argc.into()],
                        "tail.argv.reserve",
                    )?;
                    let argv = tail_argv_call
                        .try_as_basic_value()
                        .basic()
                        .context("tail argv reserve không trả pointer")?
                        .into_pointer_value();
                    for (argument_index, (argument, value_type)) in
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
                                &[i32_type.const_int(argument_index as u64, false)],
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
                    let status = tail_call
                        .try_as_basic_value()
                        .basic()
                        .context("tail call không trả completion status")?;
                    builder.build_return(Some(&status))?;
                }
                Terminator::Unreachable => {
                    builder.build_unreachable()?;
                }
            }
        }
        for block in &function.blocks {
            for instruction in &block.instructions {
                let Instruction::Phi {
                    result,
                    value_type,
                    incoming,
                } = instruction
                else {
                    continue;
                };
                let phi = phis.get(result).context("thiếu LLVM phi placeholder")?;
                let mut incoming_values = Vec::with_capacity(incoming.len());
                for (block_id, value_id) in incoming {
                    let value = values
                        .get(value_id)
                        .copied()
                        .with_context(|| format!("SSA value %v{} chưa được codegen", value_id.0))?;
                    let value: BasicValueEnum<'ctx> = if *value_type == ValueType::Dynamic {
                        to_dynamic(
                            &builder,
                            value,
                            types.get(value_id).copied().context("thiếu kiểu SSA")?,
                            i8_type,
                            i64_type,
                            dynamic_type,
                        )?
                        .into()
                    } else {
                        value
                    };
                    incoming_values.push((value, llvm_block_exits[block_id.0 as usize]));
                }
                let refs = incoming_values
                    .iter()
                    .map(|(value, block)| (value as &dyn BasicValue<'ctx>, *block))
                    .collect::<Vec<_>>();
                phi.add_incoming(&refs);
            }
        }
    }
    module
        .verify()
        .map_err(|error| anyhow!("LLVM module không hợp lệ: {error}"))?;
    Ok(module)
}

struct BuiltGenericArguments<'ctx> {
    argc: IntValue<'ctx>,
    argv: inkwell::values::PointerValue<'ctx>,
    builder: Option<inkwell::values::PointerValue<'ctx>>,
}

#[allow(clippy::too_many_arguments)]
fn box_value_pointer<'ctx>(
    builder: &inkwell::builder::Builder<'ctx>,
    value: BasicValueEnum<'ctx>,
    value_type: ValueType,
    i8_type: inkwell::types::IntType<'ctx>,
    i64_type: inkwell::types::IntType<'ctx>,
    dynamic_type: inkwell::types::StructType<'ctx>,
    name: &str,
) -> Result<inkwell::values::PointerValue<'ctx>> {
    let dynamic = to_dynamic(builder, value, value_type, i8_type, i64_type, dynamic_type)?;
    let pointer = builder.build_alloca(dynamic_type, name)?;
    builder.build_store(pointer, dynamic)?;
    Ok(pointer)
}

#[allow(clippy::too_many_arguments)]
fn build_generic_arguments<'ctx>(
    builder: &inkwell::builder::Builder<'ctx>,
    arguments: &[CallArgument],
    values: &HashMap<ValueId, BasicValueEnum<'ctx>>,
    i8_type: inkwell::types::IntType<'ctx>,
    i32_type: inkwell::types::IntType<'ctx>,
    i64_type: inkwell::types::IntType<'ctx>,
    ptr_type: inkwell::types::PointerType<'ctx>,
    dynamic_type: inkwell::types::StructType<'ctx>,
    argv_builder_init: inkwell::values::FunctionValue<'ctx>,
    argv_builder_push: inkwell::values::FunctionValue<'ctx>,
    argv_builder_spread: inkwell::values::FunctionValue<'ctx>,
    argv_builder_len: inkwell::values::FunctionValue<'ctx>,
    argv_builder_data: inkwell::values::FunctionValue<'ctx>,
) -> Result<BuiltGenericArguments<'ctx>> {
    if !arguments.iter().any(|argument| argument.spread) {
        let ids = arguments
            .iter()
            .map(|argument| argument.value)
            .collect::<Vec<_>>();
        let types = arguments
            .iter()
            .map(|argument| argument.value_type)
            .collect::<Vec<_>>();
        let argv = build_dynamic_array(
            builder,
            &ids,
            &types,
            values,
            i8_type,
            i32_type,
            i64_type,
            dynamic_type,
        )?;
        return Ok(BuiltGenericArguments {
            argc: i32_type.const_int(arguments.len() as u64, false),
            argv,
            builder: None,
        });
    }

    let builder_slot = builder.build_alloca(ptr_type, "generic.argv.builder.slot")?;
    builder.build_store(builder_slot, ptr_type.const_null())?;
    builder.build_call(
        argv_builder_init,
        &[builder_slot.into()],
        "generic.argv.builder.init",
    )?;
    let handle = builder
        .build_load(ptr_type, builder_slot, "generic.argv.builder")?
        .into_pointer_value();

    for (index, argument) in arguments.iter().enumerate() {
        let value = values
            .get(&argument.value)
            .copied()
            .with_context(|| format!("thiếu generic call argument %v{}", argument.value.0))?;
        let pointer = box_value_pointer(
            builder,
            value,
            argument.value_type,
            i8_type,
            i64_type,
            dynamic_type,
            &format!("generic.argv.value.{index}"),
        )?;
        if argument.spread {
            let _ = builder.build_call(
                argv_builder_spread,
                &[handle.into(), pointer.into()],
                &format!("generic.argv.spread.{index}"),
            )?;
        } else {
            builder.build_call(
                argv_builder_push,
                &[handle.into(), pointer.into()],
                &format!("generic.argv.push.{index}"),
            )?;
        }
    }

    let argc = builder
        .build_call(argv_builder_len, &[handle.into()], "generic.argv.len")?
        .try_as_basic_value()
        .basic()
        .context("argv_builder_len không trả i32")?
        .into_int_value();
    let argv = builder
        .build_call(argv_builder_data, &[handle.into()], "generic.argv.data")?
        .try_as_basic_value()
        .basic()
        .context("argv_builder_data không trả pointer")?
        .into_pointer_value();

    Ok(BuiltGenericArguments {
        argc,
        argv,
        builder: Some(handle),
    })
}
#[allow(clippy::too_many_arguments)]
fn build_guarded_dynamic_add<'ctx>(
    context: &'ctx LlvmContext,
    builder: &inkwell::builder::Builder<'ctx>,
    function: inkwell::values::FunctionValue<'ctx>,
    function_is_entry: bool,
    left_value: BasicValueEnum<'ctx>,
    left_type: ValueType,
    right_value: BasicValueEnum<'ctx>,
    right_type: ValueType,
    dynamic_type: inkwell::types::StructType<'ctx>,
    i8_type: inkwell::types::IntType<'ctx>,
    i64_type: inkwell::types::IntType<'ctx>,
    f64_type: inkwell::types::FloatType<'ctx>,
    dynamic_binary: inkwell::values::FunctionValue<'ctx>,
    throw_uncaught: inkwell::values::FunctionValue<'ctx>,
    recursion_leave: inkwell::values::FunctionValue<'ctx>,
    suffix: &str,
) -> Result<(StructValue<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)> {
    let left_dynamic = to_dynamic(
        builder,
        left_value,
        left_type,
        i8_type,
        i64_type,
        dynamic_type,
    )?;
    let right_dynamic = to_dynamic(
        builder,
        right_value,
        right_type,
        i8_type,
        i64_type,
        dynamic_type,
    )?;

    let left_tag = builder
        .build_extract_value(left_dynamic, 0, &format!("dynamic.add.left.tag.{suffix}"))?
        .into_int_value();
    let right_tag = builder
        .build_extract_value(right_dynamic, 0, &format!("dynamic.add.right.tag.{suffix}"))?
        .into_int_value();
    let number_tag = i8_type.const_int(2, false);
    let left_is_number = builder.build_int_compare(
        IntPredicate::EQ,
        left_tag,
        number_tag,
        &format!("dynamic.add.left.is.number.{suffix}"),
    )?;
    let right_is_number = builder.build_int_compare(
        IntPredicate::EQ,
        right_tag,
        number_tag,
        &format!("dynamic.add.right.is.number.{suffix}"),
    )?;
    let both_numbers = builder.build_and(
        left_is_number,
        right_is_number,
        &format!("dynamic.add.both.number.{suffix}"),
    )?;

    let fast_block = context.append_basic_block(function, &format!("dynamic.add.fast.{suffix}"));
    let slow_block = context.append_basic_block(function, &format!("dynamic.add.slow.{suffix}"));
    let merge_block = context.append_basic_block(function, &format!("dynamic.add.merge.{suffix}"));
    builder.build_conditional_branch(both_numbers, fast_block, slow_block)?;

    builder.position_at_end(fast_block);
    let left_payload = builder
        .build_extract_value(
            left_dynamic,
            1,
            &format!("dynamic.add.left.payload.{suffix}"),
        )?
        .into_int_value();
    let right_payload = builder
        .build_extract_value(
            right_dynamic,
            1,
            &format!("dynamic.add.right.payload.{suffix}"),
        )?
        .into_int_value();
    let left_number = builder
        .build_bit_cast(
            left_payload,
            f64_type,
            &format!("dynamic.add.left.number.{suffix}"),
        )?
        .into_float_value();
    let right_number = builder
        .build_bit_cast(
            right_payload,
            f64_type,
            &format!("dynamic.add.right.number.{suffix}"),
        )?
        .into_float_value();
    let sum = builder.build_float_add(
        left_number,
        right_number,
        &format!("dynamic.add.number.{suffix}"),
    )?;
    let fast_dynamic = to_dynamic(
        builder,
        sum.into(),
        ValueType::Number,
        i8_type,
        i64_type,
        dynamic_type,
    )?;
    builder.build_unconditional_branch(merge_block)?;

    builder.position_at_end(slow_block);
    let left_ptr =
        builder.build_alloca(dynamic_type, &format!("dynamic.add.left.slot.{suffix}"))?;
    builder.build_store(left_ptr, left_dynamic)?;
    let right_ptr =
        builder.build_alloca(dynamic_type, &format!("dynamic.add.right.slot.{suffix}"))?;
    builder.build_store(right_ptr, right_dynamic)?;
    let result_ptr =
        builder.build_alloca(dynamic_type, &format!("dynamic.add.slow.result.{suffix}"))?;
    builder.build_store(result_ptr, dynamic_type.const_zero())?;

    let call = builder.build_call(
        dynamic_binary,
        &[
            i8_type
                .const_int(DynamicBinaryOperator::Add as u64, false)
                .into(),
            left_ptr.into(),
            right_ptr.into(),
            result_ptr.into(),
        ],
        &format!("dynamic.add.fallback.{suffix}"),
    )?;
    let status = call
        .try_as_basic_value()
        .basic()
        .context("dynamic add fallback không trả status")?
        .into_int_value();
    let slow_dynamic = builder
        .build_load(
            dynamic_type,
            result_ptr,
            &format!("dynamic.add.slow.load.{suffix}"),
        )?
        .into_struct_value();
    let slow_continue = propagate_call_completion(
        context,
        builder,
        function,
        function_is_entry,
        status,
        slow_dynamic,
        dynamic_type,
        i8_type,
        throw_uncaught,
        recursion_leave,
        &format!("dynamic.add.fallback.{suffix}"),
    )?;
    builder.build_unconditional_branch(merge_block)?;

    builder.position_at_end(merge_block);
    let phi = builder.build_phi(dynamic_type, &format!("dynamic.add.result.{suffix}"))?;
    let incoming_values: [(BasicValueEnum<'ctx>, inkwell::basic_block::BasicBlock<'ctx>); 2] = [
        (fast_dynamic.into(), fast_block),
        (slow_dynamic.into(), slow_continue),
    ];
    let incoming_refs = incoming_values
        .iter()
        .map(|(value, block)| (value as &dyn BasicValue<'ctx>, *block))
        .collect::<Vec<_>>();
    phi.add_incoming(&incoming_refs);

    Ok((phi.as_basic_value().into_struct_value(), merge_block))
}

fn propagate_call_completion<'ctx>(
    context: &'ctx LlvmContext,
    builder: &inkwell::builder::Builder<'ctx>,
    function: inkwell::values::FunctionValue<'ctx>,
    function_is_entry: bool,
    status: IntValue<'ctx>,
    dynamic: StructValue<'ctx>,
    dynamic_type: inkwell::types::StructType<'ctx>,
    i8_type: inkwell::types::IntType<'ctx>,
    throw_uncaught: inkwell::values::FunctionValue<'ctx>,
    recursion_leave: inkwell::values::FunctionValue<'ctx>,
    suffix: &str,
) -> Result<inkwell::basic_block::BasicBlock<'ctx>> {
    let thrown = builder.build_int_compare(
        IntPredicate::NE,
        status,
        i8_type.const_zero(),
        &format!("call.thrown.{suffix}"),
    )?;
    let throw_block = context.append_basic_block(function, &format!("call.throw.{suffix}"));
    let continue_block = context.append_basic_block(function, &format!("call.continue.{suffix}"));
    builder.build_conditional_branch(thrown, throw_block, continue_block)?;

    builder.position_at_end(throw_block);
    if function_is_entry {
        let tag = builder
            .build_extract_value(dynamic, 0, &format!("call.throw.tag.{suffix}"))?
            .into_int_value();
        let payload = builder
            .build_extract_value(dynamic, 1, &format!("call.throw.payload.{suffix}"))?
            .into_int_value();
        builder.build_call(
            throw_uncaught,
            &[tag.into(), payload.into()],
            &format!("call.throw.uncaught.{suffix}"),
        )?;
        builder.build_unreachable()?;
    } else {
        let out = function
            .get_nth_param(3)
            .context("JavaScript function thiếu completion out pointer")?
            .into_pointer_value();
        builder.build_store(out, dynamic)?;
        builder.build_call(
            recursion_leave,
            &[],
            &format!("recursion.leave.throw.{suffix}"),
        )?;
        builder.build_return(Some(&i8_type.const_int(1, false)))?;
    }

    builder.position_at_end(continue_block);
    let _ = dynamic_type;
    Ok(continue_block)
}

fn build_ecmascript_exponentiation<'ctx>(
    builder: &inkwell::builder::Builder<'ctx>,
    pow_f64: inkwell::values::FunctionValue<'ctx>,
    base: FloatValue<'ctx>,
    exponent: FloatValue<'ctx>,
    f64_type: inkwell::types::FloatType<'ctx>,
) -> Result<FloatValue<'ctx>> {
    // LLVM's pow intrinsic covers the normal IEEE-754 path and lets LLVM
    // optimize constant/integer exponents. ECMAScript differs for a few
    // ordered special cases, which are corrected with pure SSA selects:
    //
    // - x ** +/-0 is 1, including NaN ** 0.
    // - exponent NaN is NaN, including 1 ** NaN.
    // - abs(base) == 1 with an infinite exponent is NaN.
    let call = builder.build_call(pow_f64, &[base.into(), exponent.into()], "number.pow")?;
    let raw = call
        .try_as_basic_value()
        .basic()
        .context("llvm.pow.f64 không trả f64")?
        .into_float_value();

    let zero = f64_type.const_zero();
    let one = f64_type.const_float(1.0);
    let minus_one = f64_type.const_float(-1.0);
    let positive_infinity = f64_type.const_float(f64::INFINITY);
    let negative_infinity = f64_type.const_float(f64::NEG_INFINITY);
    let nan = f64_type.const_float(f64::NAN);

    let exponent_is_nan =
        builder.build_float_compare(FloatPredicate::UNO, exponent, exponent, "pow.exponent.nan")?;
    let exponent_is_zero =
        builder.build_float_compare(FloatPredicate::OEQ, exponent, zero, "pow.exponent.zero")?;

    let exponent_is_positive_infinity = builder.build_float_compare(
        FloatPredicate::OEQ,
        exponent,
        positive_infinity,
        "pow.exponent.pos_inf",
    )?;
    let exponent_is_negative_infinity = builder.build_float_compare(
        FloatPredicate::OEQ,
        exponent,
        negative_infinity,
        "pow.exponent.neg_inf",
    )?;
    let exponent_is_infinite = builder.build_or(
        exponent_is_positive_infinity,
        exponent_is_negative_infinity,
        "pow.exponent.inf",
    )?;

    let base_is_one =
        builder.build_float_compare(FloatPredicate::OEQ, base, one, "pow.base.one")?;
    let base_is_minus_one =
        builder.build_float_compare(FloatPredicate::OEQ, base, minus_one, "pow.base.minus_one")?;
    let absolute_base_is_one =
        builder.build_or(base_is_one, base_is_minus_one, "pow.base.abs_one")?;
    let infinite_unit_power = builder.build_and(
        exponent_is_infinite,
        absolute_base_is_one,
        "pow.unit_to_inf",
    )?;
    let must_be_nan = builder.build_or(exponent_is_nan, infinite_unit_power, "pow.must_nan")?;

    let corrected_nan = builder
        .build_select(must_be_nan, nan, raw, "pow.correct.nan")?
        .into_float_value();

    Ok(builder
        .build_select(exponent_is_zero, one, corrected_nan, "pow.correct.zero")?
        .into_float_value())
}

fn build_dynamic_typeof<'ctx>(
    builder: &inkwell::builder::Builder<'ctx>,
    dynamic: StructValue<'ctx>,
    result: ValueId,
    i8_type: inkwell::types::IntType<'ctx>,
) -> Result<inkwell::values::PointerValue<'ctx>> {
    let tag = builder
        .build_extract_value(dynamic, 0, "typeof.dynamic.tag")?
        .into_int_value();

    let undefined = builder
        .build_global_string_ptr("undefined", &format!(".typeof.undefined.{}", result.0))?
        .as_pointer_value();
    let object = builder
        .build_global_string_ptr("object", &format!(".typeof.object.{}", result.0))?
        .as_pointer_value();
    let number = builder
        .build_global_string_ptr("number", &format!(".typeof.number.{}", result.0))?
        .as_pointer_value();
    let boolean = builder
        .build_global_string_ptr("boolean", &format!(".typeof.boolean.{}", result.0))?
        .as_pointer_value();
    let string = builder
        .build_global_string_ptr("string", &format!(".typeof.string.{}", result.0))?
        .as_pointer_value();
    let function = builder
        .build_global_string_ptr("function", &format!(".typeof.function.{}", result.0))?
        .as_pointer_value();

    // Unknown/internal tags conservatively produce "undefined". Every
    // currently representable ECMAScript runtime tag is selected explicitly.
    let mut text = undefined;
    for (runtime_tag, candidate, suffix) in [
        (1_u64, object, "null"),
        (2_u64, number, "number"),
        (3_u64, boolean, "boolean"),
        (4_u64, string, "string"),
        (5_u64, object, "object"),
        (6_u64, function, "callable"),
        (7_u64, object, "promise"),
        (8_u64, object, "cell"),
    ] {
        let matches = builder.build_int_compare(
            IntPredicate::EQ,
            tag,
            i8_type.const_int(runtime_tag, false),
            &format!("typeof.is.{suffix}.{}", result.0),
        )?;
        text = builder
            .build_select(
                matches,
                candidate,
                text,
                &format!("typeof.select.{suffix}.{}", result.0),
            )?
            .into_pointer_value();
    }

    Ok(text)
}

fn llvm_type<'ctx>(
    value_type: ValueType,
    i8_type: inkwell::types::IntType<'ctx>,
    bool_type: inkwell::types::IntType<'ctx>,
    f64_type: inkwell::types::FloatType<'ctx>,
    ptr_type: inkwell::types::PointerType<'ctx>,
    dynamic_type: inkwell::types::StructType<'ctx>,
) -> inkwell::types::BasicTypeEnum<'ctx> {
    match value_type {
        ValueType::Undefined | ValueType::Null => i8_type.into(),
        ValueType::Number => f64_type.into(),
        ValueType::Bool => bool_type.into(),
        ValueType::String
        | ValueType::Object
        | ValueType::Callable
        | ValueType::Cell
        | ValueType::Promise => ptr_type.into(),
        ValueType::Dynamic => dynamic_type.into(),
    }
}

fn to_dynamic<'ctx>(
    builder: &inkwell::builder::Builder<'ctx>,
    value: BasicValueEnum<'ctx>,
    value_type: ValueType,
    i8_type: inkwell::types::IntType<'ctx>,
    i64_type: inkwell::types::IntType<'ctx>,
    dynamic_type: inkwell::types::StructType<'ctx>,
) -> Result<StructValue<'ctx>> {
    if value_type == ValueType::Dynamic {
        return Ok(value.into_struct_value());
    }
    let tag = i8_type.const_int(
        match value_type {
            ValueType::Undefined => 0,
            ValueType::Null => 1,
            ValueType::Number => 2,
            ValueType::Bool => 3,
            ValueType::String => 4,
            ValueType::Object => 5,
            ValueType::Callable => 6,
            ValueType::Cell => 8,
            ValueType::Promise => 7,
            ValueType::Dynamic => unreachable!(),
        },
        false,
    );
    let payload = match (value_type, value) {
        (ValueType::Undefined | ValueType::Null, _) => i64_type.const_zero(),
        (ValueType::Number, BasicValueEnum::FloatValue(value)) => builder
            .build_bit_cast(value, i64_type, "number.bits")?
            .into_int_value(),
        (ValueType::Bool, BasicValueEnum::IntValue(value)) => {
            builder.build_int_z_extend(value, i64_type, "bool.bits")?
        }
        (
            ValueType::String
            | ValueType::Object
            | ValueType::Callable
            | ValueType::Cell
            | ValueType::Promise,
            BasicValueEnum::PointerValue(value),
        ) => builder.build_ptr_to_int(value, i64_type, "string.bits")?,
        _ => bail!("không thể box giá trị runtime {:?}", value_type),
    };
    let value = dynamic_type.get_undef();
    let value = builder
        .build_insert_value(value, tag, 0, "dynamic.tag")?
        .into_struct_value();
    Ok(builder
        .build_insert_value(value, payload, 1, "dynamic.payload")?
        .into_struct_value())
}

fn from_dynamic<'ctx>(
    builder: &inkwell::builder::Builder<'ctx>,
    value: StructValue<'ctx>,
    value_type: ValueType,
    bool_type: inkwell::types::IntType<'ctx>,
    f64_type: inkwell::types::FloatType<'ctx>,
    ptr_type: inkwell::types::PointerType<'ctx>,
) -> Result<BasicValueEnum<'ctx>> {
    if value_type == ValueType::Dynamic {
        return Ok(value.into());
    }
    let payload = builder
        .build_extract_value(value, 1, "dynamic.unbox.payload")?
        .into_int_value();
    Ok(match value_type {
        ValueType::Undefined | ValueType::Null => builder
            .build_int_truncate(payload, context_i8_type(payload), "nullish.unbox")?
            .into(),
        ValueType::Number => builder
            .build_bit_cast(payload, f64_type, "number.unbox")?
            .into_float_value()
            .into(),
        ValueType::Bool => builder
            .build_int_truncate(payload, bool_type, "bool.unbox")?
            .into(),
        ValueType::String
        | ValueType::Object
        | ValueType::Callable
        | ValueType::Cell
        | ValueType::Promise => builder
            .build_int_to_ptr(payload, ptr_type, "pointer.unbox")?
            .into(),
        ValueType::Dynamic => unreachable!(),
    })
}

fn context_i8_type<'ctx>(value: IntValue<'ctx>) -> inkwell::types::IntType<'ctx> {
    value.get_type().get_context().i8_type()
}

#[allow(clippy::too_many_arguments)]
fn build_dynamic_array<'ctx>(
    builder: &inkwell::builder::Builder<'ctx>,
    arguments: &[ValueId],
    argument_types: &[ValueType],
    values: &HashMap<ValueId, BasicValueEnum<'ctx>>,
    i8_type: inkwell::types::IntType<'ctx>,
    i32_type: inkwell::types::IntType<'ctx>,
    i64_type: inkwell::types::IntType<'ctx>,
    dynamic_type: inkwell::types::StructType<'ctx>,
) -> Result<inkwell::values::PointerValue<'ctx>> {
    if arguments.len() != argument_types.len() {
        bail!("call argument metadata không khớp")
    }
    if arguments.is_empty() {
        return Ok(i8_type
            .get_context()
            .ptr_type(AddressSpace::default())
            .const_null());
    }
    let array = builder.build_array_alloca(
        dynamic_type,
        i32_type.const_int(arguments.len() as u64, false),
        "call.argv",
    )?;
    for (index, (argument, value_type)) in arguments.iter().zip(argument_types).enumerate() {
        let value = values
            .get(argument)
            .copied()
            .with_context(|| format!("thiếu call argument %v{}", argument.0))?;
        let dynamic = to_dynamic(builder, value, *value_type, i8_type, i64_type, dynamic_type)?;
        let slot = unsafe {
            builder.build_gep(
                dynamic_type,
                array,
                &[i32_type.const_int(index as u64, false)],
                "call.arg.slot",
            )?
        };
        builder.build_store(slot, dynamic)?;
    }
    Ok(array)
}

fn int_value<'ctx>(
    values: &HashMap<ValueId, BasicValueEnum<'ctx>>,
    value: ValueId,
) -> Result<IntValue<'ctx>> {
    match values.get(&value).copied() {
        Some(BasicValueEnum::IntValue(value)) => Ok(value),
        _ => bail!("SSA value %v{} không phải boolean/integer", value.0),
    }
}
fn float_value<'ctx>(
    values: &HashMap<ValueId, BasicValueEnum<'ctx>>,
    value: ValueId,
) -> Result<FloatValue<'ctx>> {
    match values.get(&value).copied() {
        Some(BasicValueEnum::FloatValue(value)) => Ok(value),
        _ => bail!("SSA value %v{} không phải Number", value.0),
    }
}
