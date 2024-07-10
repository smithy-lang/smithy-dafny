use simple_boolean::*;


mod tests_from_dafny;

/*
    method{:test} GetBooleanTrue(){
        var client :- expect SimpleBoolean.SimpleBoolean();
        TestGetBooleanTrue(client);
    }
    method{:test} GetBooleanFalse(){
        var client :- expect SimpleBoolean.SimpleBoolean();
        TestGetBooleanFalse(client);
    }
*/

/*method TestGetBooleanTrue(client: ISimpleTypesBooleanClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetBoolean(SimpleBoolean.Types.GetBooleanInput(value:= Some(true)));
        expect ret.value.UnwrapOr(false) == true;
        print ret;
    }
} */
#[test]
fn test_get_boolean_true() {
    let result = client().get_boolean().value(true).send();
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert!(value);
}

/*method TestGetBooleanFalse(client: ISimpleTypesBooleanClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetBoolean(SimpleBoolean.Types.GetBooleanInput(value:= Some(false)));
        expect ret.value.UnwrapOr(true) == false;
        print ret;
    }
} */
#[test]
fn test_get_boolean_false() {
    let result = client().get_boolean().value(false).send();
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert!(!value);
}

pub fn client() -> Client {
    let config = SimpleBooleanConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}

#[test]
fn dafny_tests() {
    crate::tests_from_dafny::_module::_default::_Test__Main_()
}
