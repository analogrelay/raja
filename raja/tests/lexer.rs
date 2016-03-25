// Lexer functional tests
extern crate raja;

mod lexer {
    use raja::lang;
    use std::{env,fs};
    use std::io::{Write,Read};

    macro_rules! lexer_test {
        ($name:ident) => {
            #[test]
            pub fn $name() {
                run_lexer_test(concat!(stringify!($name), ".js"), concat!(stringify!($name), ".baseline"));
            }
        }
    }

    lexer_test!(assorted_keywords);
    lexer_test!(simple_expressions);
    lexer_test!(string_literals);
    lexer_test!(numeric_literals);
    lexer_test!(comments);

    fn run_lexer_test(input_name: &'static str, baseline_name: &'static str) {
        // Locate files
        let data_dir = env::current_dir().unwrap()
            .join("tests")
            .join("lexer_testdata");
        let input_file = data_dir.join(input_name);
        let baseline_file = data_dir.join(baseline_name);

        let mut input = String::new();
        fs::File::open(&input_file)
            .expect(&format!("failed to open: {}", input_file.to_str().unwrap()))
            .read_to_string(&mut input).unwrap();

        let lex = lang::Lexer::new(input);
        let result = lex.map(|t| render(t)).collect::<Vec<_>>().join("\n");

        if generate_baseline() {
            fs::File::create(&baseline_file)
                .expect(&format!("failed to create: {}", baseline_file.to_str().unwrap()))
                .write_all(result.as_bytes()).unwrap();
        } else {
            let mut actual = String::new();
            fs::File::open(&baseline_file)
                .expect(&format!("failed to open: {}", baseline_file.to_str().unwrap()))
                .read_to_string(&mut actual).unwrap();
            assert_eq!(actual, result);
        }
    }

    fn generate_baseline() -> bool {
        match env::var("RAJA_TEST_GENERATE_BASELINES") {
            Ok(ref x) if x == "1" => true,
            _ => false
        }
    }

    fn render(t: lang::Token) -> String {
        let text : String = t.text().chars().flat_map(|c| c.escape_default()).collect();
        format!("{: >17} ({: <60}) {: <12} -> {: <12} [{}]",
            format!("{:?}", t.kind()),
            format!("{:?}", t.value()),
            format!("{}", t.start()),
            format!("{}", t.end()),
            text)
    }
}
