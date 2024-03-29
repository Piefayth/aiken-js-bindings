use std::error::Error;
use std::sync::Arc;
use std::{collections::HashMap};
use aiken_lang::ast::{Arg, BinOp};
use aiken_lang::tipo::Type;
use aiken_lang::{
    ast::{Definition, ModuleKind, Tracing, TypedDataType, TypedDefinition, TypedFunction, TypedValidator},
    builtins, gen_uplc::{builder::{DataTypeKey, FunctionAccessKey}, CodeGenerator}, parser::{self, error::{ErrorKind, ParseError}}, tipo::{self, error::Warning, TypeInfo}, IdGenerator,
};
use indexmap::IndexMap;
use uplc::ast::{DeBruijn, NamedDeBruijn, Program};
use uplc::machine::cost_model::ExBudget;
use uplc::ast::Type as UplcType;
use wasm_bindgen::prelude::*;
use web_sys::console;
use serde::{Serialize, Deserialize};
use miette::Diagnostic;

use crate::{stdlib};



#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(tag = "dataType", content = "value")]
enum SerializableUplcType {
    Bool,
    Integer,
    String,
    ByteString,
    Unit,
    List(Box<SerializableUplcType>),
    Pair(Box<SerializableUplcType>, Box<SerializableUplcType>),
    Data,
}

impl From<&UplcType> for SerializableUplcType {
    fn from(t: &UplcType) -> Self {
        match t {
            UplcType::Bool => SerializableUplcType::Bool,
            UplcType::Integer => SerializableUplcType::Integer,
            UplcType::String => SerializableUplcType::String,
            UplcType::ByteString => SerializableUplcType::ByteString,
            UplcType::Unit => SerializableUplcType::Unit,
            UplcType::List(sub_type) => {
                SerializableUplcType::List(Box::new(SerializableUplcType::from(sub_type.as_ref())))
            }
            UplcType::Pair(type1, type2) => {
                SerializableUplcType::Pair(
                    Box::new(SerializableUplcType::from(type1.as_ref())),
                    Box::new(SerializableUplcType::from(type2.as_ref()))
                )
            }
            UplcType::Data => SerializableUplcType::Data,
            // Handle other types recursively as needed
        }
    }
}

pub struct EvalHint {
    pub bin_op: BinOp,
    pub left: Program<NamedDeBruijn>,
    pub right: Program<NamedDeBruijn>,
}

#[derive(Clone, Serialize)]
pub struct TestResult {
    pub success: bool,
    pub spent_budget: ExBudget,
    pub logs: Vec<String>,
    pub name: String,
    pub index: usize,
}

#[derive(Clone)]
pub enum CompilerError {
    Parse(ParseError),
    Type(tipo::error::Error),
}

impl CompilerError {
    pub fn message(&self) -> String {
        match self {
            CompilerError::Parse(p) => p
                .source()
                .map_or_else(|| p.to_string(), |ps| ps.to_string()),
            CompilerError::Type(t) => t
                .source()
                .map_or_else(|| t.to_string(), |ts| ts.to_string()),
        }
    }

    pub fn line(&self) -> usize {
        match self {
            CompilerError::Parse(p) => p.span.start,
            CompilerError::Type(_) => 0 // TODO: we can get the line number for certain errors
        }
    }

    pub fn code(&self) -> Option<String> {
        match self {
            CompilerError::Parse(p) => p.code().map(|pc| pc.to_string()),
            CompilerError::Type(t) => t.code().map(|tc| tc.to_string()),
        }
    }

    pub fn help(&self) -> Option<String> {
        match self {
            CompilerError::Parse(p) => p.help().map(|ph| ph.to_string()),
            CompilerError::Type(t) => t.help().map(|th| th.to_string()),
        }
    }
}


#[derive(Serialize)]
struct CompilerWarning {
    line: usize,
    message: String,
    code: Option<String>,
    help: Option<String>,
}

impl From<Warning> for CompilerWarning {
    fn from(warning: Warning) -> Self {
        let message = warning.to_string();
        let code = warning.code().map(|c| c.to_string());
        let help = warning.help().map(|h| h.to_string());

        let line = match &warning {
            Warning::AllFieldsRecordUpdate { location }
            | Warning::ImplicitlyDiscardedResult { location }
            | Warning::NoFieldsRecordUpdate { location }
            | Warning::PubInValidatorModule { location }
            | Warning::SingleWhenClause { location, .. }
            | Warning::SingleConstructorExpect { location, .. }
            | Warning::Todo { location, .. }
            | Warning::UnexpectedTypeHole { location, .. }
            | Warning::UnusedConstructor { location, .. }
            | Warning::UnusedImportedModule { location, .. }
            | Warning::UnusedImportedValue { location, .. }
            | Warning::UnusedPrivateFunction { location, .. }
            | Warning::UnusedPrivateModuleConstant { location, .. }
            | Warning::UnusedType { location, .. }
            | Warning::UnusedVariable { location, .. }
            | Warning::ValidatorInLibraryModule { location }
            | Warning::Utf8ByteArrayIsValidHexString { location, .. } => location.start,
        };

        CompilerWarning { line, message, code, help }
    }
}

#[derive(Serialize)]
struct CompilerErrorInfo {
    code: Option<String>,
    message: String,
    help: Option<String>,
    line: usize // cursed, the value of this actually is "character_number" not "line_number" rn 
}
impl From<CompilerError> for CompilerErrorInfo {
    fn from(error: CompilerError) -> Self {
        CompilerErrorInfo {
            message: error.message(),
            help: error.help(),
            code: error.code(),
            line: error.line(),
        }
    }
}

#[derive(Serialize)]
struct ValidatorResult {
    index: usize,
    name: String,
    parameter_types: Vec<SerializableUplcType>,
    program: String,
}

#[derive(Serialize)]
#[wasm_bindgen]
struct BuildResult {
    success: bool,
    warnings: Vec<CompilerWarning>,
    errors: Vec<CompilerErrorInfo>,
    validators: Vec<ValidatorResult>,
    test_results: Vec<TestResult>,
    // Add more fields as necessary
}

#[derive(Serialize)]
#[wasm_bindgen]
struct FormatResult {
    success: bool,
    formatted_code: Option<String>,
    errors: Vec<CompilerErrorInfo>,
}

#[wasm_bindgen]
pub struct Project {
    id_gen: IdGenerator,
    module_types: HashMap<String, TypeInfo>,
    functions: IndexMap<FunctionAccessKey, TypedFunction>,
    data_types: IndexMap<DataTypeKey, TypedDataType>,
    is_stdlib_setup: bool,
}

#[wasm_bindgen]
impl Project {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Project {
        let id_gen = IdGenerator::new();
        let mut module_types = HashMap::new();
        module_types.insert("aiken".to_string(), builtins::prelude(&id_gen));
        module_types.insert("aiken/builtin".to_string(), builtins::plutus(&id_gen));

        let functions = builtins::prelude_functions(&id_gen);
        let data_types = builtins::prelude_data_types(&id_gen);

        Project {
            id_gen,
            module_types,
            functions,
            data_types,
            is_stdlib_setup: false
        }
    }

    pub fn build(&mut self, source_code: &str, should_run_tests: bool) -> Result<JsValue, JsValue> {
        self.setup_stdlib();

        let kind = ModuleKind::Validator;
        let parse_result = parser::module(source_code, kind);

        match parse_result {
            Ok((mut ast, _extra)) => {
                let name = "play".to_string();
                ast.name = name.clone();

                let mut warnings = vec![];
                let errors = vec![];
                let mut validators_results = vec![];

                match ast.infer(&self.id_gen, kind, &name, &self.module_types, Tracing::NoTraces, &mut warnings) {
                    Ok(typed_ast) => {
                        let mut module_types: IndexMap<&String, &TypeInfo> = self.module_types.iter().collect();
                        module_types.insert(&name, &typed_ast.type_info);

                        let (tests, validators, functions, data_types) = self.collect_definitions(name.clone(), typed_ast.definitions());

                        let mut generator = CodeGenerator::new(functions, data_types, module_types, false);
                        
                        let test_results = if should_run_tests {
                            run_tests(tests, &mut generator)
                        } else {
                            vec![]
                        };

                        for (index, validator) in validators.into_iter().enumerate() {
                            let name = format!(
                                "{}{}",
                                validator.fun.name,
                                validator
                                    .other_fun
                                    .clone()
                                    .map(|o| format!(".{}", o.name))
                                    .unwrap_or_else(|| "".to_string())
                            );

                            let parameter_types: Vec<SerializableUplcType> = validator.params.clone().into_iter().map(|elem| {
                                let uplc_type = elem.tipo.get_uplc_type();
                                let pretty = elem.tipo.to_pretty(4);
                                let param_variable_name = elem.get_variable_name();
                                elem.tipo.to_pretty(0);
                                //console::log_1(&format!("{}", pretty).into());
                                SerializableUplcType::from(&uplc_type)
                            }).collect();

                            let program = generator.generate(validator);

                            let program: Program<DeBruijn> = program.try_into().unwrap();

                            let program = program.to_hex().unwrap();

                            validators_results.push(ValidatorResult {
                                index,
                                name,
                                program,
                                parameter_types
                            });
                        }

                        // Convert warnings and errors to their respective structs...
                        let compiler_warnings: Vec<CompilerWarning> = warnings.into_iter().map(CompilerWarning::from).collect();
                        let build_result = BuildResult {
                            success: true,
                            warnings: compiler_warnings,
                            errors,
                            test_results,
                            validators: validators_results,
                        };

                        match serde_wasm_bindgen::to_value(&build_result) {
                            Ok(js_value) => Ok(js_value),
                            Err(e) => Err(JsValue::from_str(&e.to_string())),
                        }
                    }
                    Err(err) => {
                        let compiler_warnings: Vec<CompilerWarning> = warnings.into_iter().map(CompilerWarning::from).collect();

                        let build_result = BuildResult {
                            success: false,
                            warnings: compiler_warnings,
                            errors: vec![CompilerError::Type(err).into()],
                            validators: validators_results,
                            test_results: vec![],
                        };

                        match serde_wasm_bindgen::to_value(&build_result) {
                            Ok(js_value) => Ok(js_value),
                            Err(e) => Err(JsValue::from_str(&e.to_string())),
                        }
                    }
                }
            }
            Err(errs) => {
                let compiler_errors: Vec<CompilerErrorInfo> = errs.into_iter()
                    .map(CompilerError::Parse)
                    .map(CompilerErrorInfo::from)
                    .collect();

                let build_result = BuildResult {
                    success: false,
                    warnings: vec![],
                    errors: compiler_errors,
                    validators: vec![],
                    test_results: vec![],
                };

                match serde_wasm_bindgen::to_value(&build_result) {
                    Ok(js_value) => Ok(js_value),
                    Err(e) => Err(JsValue::from_str(&e.to_string())),
                }
            }
        }
    }

    pub fn format(&self, source_code: &str) -> Result<JsValue, JsValue> {
        let parse_result = parser::module(source_code, ModuleKind::Validator);

        match parse_result {
            Ok((ast, extra)) => {
                let mut output = String::new();

                aiken_lang::format::pretty(&mut output, ast, extra, source_code); // Assuming a function that formats the code
                
                let format_result = FormatResult {
                    success: true,
                    errors: vec![],
                    formatted_code: Some(output)
                };

                match serde_wasm_bindgen::to_value(&format_result) {
                    Ok(js_value) => Ok(js_value),
                    Err(e) => Err(JsValue::from_str(&e.to_string())),
                }
            },
            Err(errs) => {
                let format_errors: Vec<CompilerErrorInfo> = errs.into_iter()
                    .map(CompilerError::Parse)
                    .map(CompilerErrorInfo::from)
                    .collect();

                let format_result = FormatResult {
                    success: true,
                    errors: format_errors,
                    formatted_code: None
                };

                match serde_wasm_bindgen::to_value(&format_result) {
                    Ok(js_value) => Ok(js_value),
                    Err(e) => Err(JsValue::from_str(&e.to_string())),
                }
            }
        }
    }


    pub fn setup_stdlib(&mut self) {
        for (module_name, module_src) in stdlib::MODULES {
            // console::log_1(&format!("{}", module_name).into());
            let (mut ast, _extra) = parser::module(module_src, ModuleKind::Lib).unwrap();

            ast.name = module_name.to_string();

            let mut warnings = vec![];

            let typed_ast = ast
                .infer(
                    &self.id_gen,
                    ModuleKind::Lib,
                    module_name,
                    &self.module_types,
                    Tracing::NoTraces,
                    &mut warnings,
                )
                .map_err(|e| {
                    console::log_1(&format!("{}", e).into());
                })
                .unwrap();

            for def in typed_ast.definitions.into_iter() {
                match def {
                    Definition::Fn(func) => {
                        self.functions.insert(
                            FunctionAccessKey {
                                module_name: module_name.to_string(),
                                function_name: func.name.clone(),
                            },
                            func,
                        );
                    }
                    Definition::DataType(data) => {
                        self.data_types.insert(
                            DataTypeKey {
                                module_name: module_name.to_string(),
                                defined_type: data.name.clone(),
                            },
                            data,
                        );
                    }
                    Definition::TypeAlias(_)
                    | Definition::Use(_)
                    | Definition::ModuleConstant(_)
                    | Definition::Test(_)
                    | Definition::Validator(_) => (),
                }
            }

            self.module_types
                .insert(module_name.to_string(), typed_ast.type_info);
        }

        self.is_stdlib_setup = true
    }

    #[allow(clippy::type_complexity)]
    fn collect_definitions<'a>(
        &'a self,
        name: String,
        definitions: impl Iterator<Item = &'a TypedDefinition>,
    ) -> (
        Vec<&'a TypedFunction>,
        Vec<&'a TypedValidator>,
        IndexMap<FunctionAccessKey, &'a TypedFunction>,
        IndexMap<DataTypeKey, &'a TypedDataType>,
    ) {
        let mut functions = IndexMap::new();
        for (k, v) in &self.functions {
            functions.insert(k.clone(), v);
        }

        let mut data_types = IndexMap::new();
        for (k, v) in &self.data_types {
            data_types.insert(k.clone(), v);
        }

        let mut tests = vec![];
        let mut validators = vec![];

        for def in definitions {
            match def {
                Definition::Fn(func) => {
                    functions.insert(
                        FunctionAccessKey {
                            module_name: name.clone(),
                            function_name: func.name.clone(),
                        },
                        func,
                    );
                }
                Definition::DataType(dt) => {
                    data_types.insert(
                        DataTypeKey {
                            module_name: name.clone(),
                            defined_type: dt.name.clone(),
                        },
                        dt,
                    );
                }
                Definition::Test(t) => tests.push(t),
                Definition::Validator(v) => validators.push(v),
                Definition::TypeAlias(_) | Definition::ModuleConstant(_) | Definition::Use(_) => {}
            }
        }

        (tests, validators, functions, data_types)
    }
}

fn run_tests(
    tests: Vec<&TypedFunction>,
    generator: &mut CodeGenerator,
) -> Vec<TestResult> {
    tests.into_iter().enumerate().map(|(index, test)| {
        let _evaluation_hint = test.test_hint().map(|(bin_op, left_src, right_src)| {
            let left = generator
                .clone()
                .generate_test(&left_src)
                .try_into()
                .unwrap();

            let right = generator
                .clone()
                .generate_test(&right_src)
                .try_into()
                .unwrap();

            EvalHint {
                bin_op,
                left,
                right,
            }
        });

        let program = generator.generate_test(&test.body);
        let program: Program<NamedDeBruijn> = program.try_into().unwrap();
        let mut eval_result = program.eval(ExBudget::default());
        
        TestResult {
            success: !eval_result.failed(test.can_error),
            spent_budget: eval_result.cost(),
            logs: eval_result.logs(),
            name: test.name.clone(),
            index
        }
    }).collect()
}