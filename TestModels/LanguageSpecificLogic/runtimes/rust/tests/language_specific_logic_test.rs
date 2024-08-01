use language_specific_logic::*;


mod tests_from_dafny;

// TODO manual tests

pub fn client() -> Client {
    let config = LanguageSpecificLogicConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}

#[test]
fn dafny_tests() {
    crate::tests_from_dafny::_module::_default::_Test__Main_()
}
