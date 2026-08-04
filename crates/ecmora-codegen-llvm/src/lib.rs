use anyhow::{Context, Result, anyhow, bail};
use ecmora_ir::{
    BinaryNumberOperator, Builtin, CompareNumberOperator, Instruction, Program, Terminator,
    UnaryBoolOperator, UnaryNumberOperator, ValueId, ValueType,
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
        context.void_type().fn_type(
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
    let promise_pending =
        module.add_function("ecmora_promise_pending", ptr_type.fn_type(&[], false), None);
    let promise_then = module.add_function(
        "ecmora_promise_then",
        ptr_type.fn_type(&[ptr_type.into(), ptr_type.into()], false),
        None,
    );
    let microtask_drain = module.add_function(
        "ecmora_microtask_drain",
        context.void_type().fn_type(&[], false),
        None,
    );
    let js_function_type = context.void_type().fn_type(
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
                        let argv = main
                            .get_nth_param(2)
                            .context("JavaScript function thiếu argv")?
                            .into_pointer_value();
                        let slot = unsafe {
                            builder.build_gep(
                                dynamic_type,
                                argv,
                                &[i32_type.const_int(*index as u64, false)],
                                "parameter.slot",
                            )?
                        };
                        let dynamic = builder
                            .build_load(dynamic_type, slot, "parameter.dynamic")?
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
                    Instruction::PromisePending { result } => {
                        let call = builder.build_call(promise_pending, &[], "promise.pending")?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("promise_pending không trả pointer")?,
                        );
                    }
                    Instruction::PromiseThen {
                        result,
                        promise,
                        callback,
                    } => {
                        let promise = values
                            .get(promise)
                            .copied()
                            .context("thiếu Promise SSA")?
                            .into_pointer_value();
                        let callback = values
                            .get(callback)
                            .copied()
                            .context("thiếu Promise callback SSA")?
                            .into_pointer_value();
                        let call = builder.build_call(
                            promise_then,
                            &[promise.into(), callback.into()],
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
                        if matches!(value_type, ValueType::Undefined | ValueType::Null) {
                            let value = match value_type {
                                ValueType::Undefined => i8_type.const_zero(),
                                ValueType::Null => i8_type.const_int(1, false),
                                _ => unreachable!(),
                            };
                            values.insert(*result, value.into());
                            continue;
                        }
                        let function = match value_type {
                            ValueType::Number => object_get_number,
                            ValueType::Bool => object_get_bool,
                            ValueType::String | ValueType::Object => object_get_string,
                            _ => bail!("object get kiểu {:?} chưa được hỗ trợ", value_type),
                        };
                        let call = builder.build_call(
                            function,
                            &[object.into(), key.as_pointer_value().into()],
                            "object.get",
                        )?;
                        values.insert(
                            *result,
                            call.try_as_basic_value()
                                .basic()
                                .context("object_get không trả value")?,
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
                        let value = values
                            .get(value)
                            .copied()
                            .context("thiếu property value SSA")?;
                        let key = builder.build_global_string_ptr(key, ".object.set.key")?;
                        if matches!(value_type, ValueType::Undefined | ValueType::Null) {
                            let function = if *value_type == ValueType::Undefined {
                                object_set_undefined
                            } else {
                                object_set_null
                            };
                            builder.build_call(
                                function,
                                &[object.into(), key.as_pointer_value().into()],
                                "object.set.nullish",
                            )?;
                            continue;
                        }
                        let function = match value_type {
                            ValueType::Number => object_set_number,
                            ValueType::Bool => object_set_bool,
                            ValueType::String | ValueType::Object => object_set_string,
                            _ => bail!("object set kiểu {:?} chưa được hỗ trợ", value_type),
                        };
                        builder.build_call(
                            function,
                            &[object.into(), key.as_pointer_value().into(), value.into()],
                            "object.set",
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
                        builder.build_call(
                            target,
                            &[
                                ptr_type.const_null().into(),
                                i32_type.const_int(arguments.len() as u64, false).into(),
                                argv.into(),
                                dynamic_ptr.into(),
                            ],
                            "call.direct",
                        )?;
                        let dynamic = builder
                            .build_load(dynamic_type, dynamic_ptr, "call.direct.load")?
                            .into_struct_value();
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
                        builder.build_call(
                            closure_call,
                            &[
                                closure.into(),
                                i32_type.const_int(arguments.len() as u64, false).into(),
                                argv.into(),
                                dynamic_ptr.into(),
                            ],
                            "call.indirect",
                        )?;
                        let dynamic = builder
                            .build_load(dynamic_type, dynamic_ptr, "call.indirect.load")?
                            .into_struct_value();
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
                                            ValueType::Object,
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
                    builder.build_return(None)?;
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
                    // Direct LLVM lowering of an uncaught ECMAScript abrupt
                    // completion. The runtime boundary is noreturn in practice;
                    // LLVM receives an explicit unreachable terminator.
                    builder.build_call(
                        throw_uncaught,
                        &[tag.into(), payload.into()],
                        "throw.uncaught",
                    )?;
                    builder.build_unreachable()?;
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
                    incoming_values.push((value, llvm_blocks[block_id.0 as usize]));
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
        return Ok(dynamic_type.ptr_type(AddressSpace::default()).const_null());
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
