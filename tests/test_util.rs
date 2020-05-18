#![allow(unused_macros)]

macro_rules! lowering_success {
    (program $program:tt) => {
        let program_text = stringify!($program);
        assert!(program_text.starts_with("{"));
        assert!(program_text.ends_with("}"));
        let result = chalk_integration::db::ChalkDatabase::with(
            &program_text[1..program_text.len() - 1],
            chalk_solve::SolverChoice::default(),
        )
        .checked_program();
        if let Err(ref e) = result {
            println!("lowering error: {}", e);
        }
        assert!(result.is_ok());
    };
}

macro_rules! lowering_error {
    (program $program:tt error_msg { $expected:expr }) => {
        let program_text = stringify!($program);
        assert!(program_text.starts_with("{"));
        assert!(program_text.ends_with("}"));
        let error = chalk_integration::db::ChalkDatabase::with(
            &program_text[1..program_text.len() - 1],
            chalk_solve::SolverChoice::default(),
        )
        .checked_program()
        .unwrap_err()
        .to_string();
        let expected = $expected.to_string();
        crate::test_util::assert_same(&error, &expected);
    };
}

pub fn assert_same(result: &str, expected: &str) {
    println!("expected:\n{}", expected);
    println!("actual:\n{}", result);

    let expected1: String = expected.chars().filter(|w| !w.is_whitespace()).collect();
    let result1: String = result.chars().filter(|w| !w.is_whitespace()).collect();
    assert!(!expected1.is_empty() && result1.starts_with(&expected1));
}
