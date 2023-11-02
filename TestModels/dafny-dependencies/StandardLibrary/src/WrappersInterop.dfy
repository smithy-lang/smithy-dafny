include "../../libraries/src/Wrappers.dfy"

// TODO: document
module StandardLibrary.Interop {

  import opened Wrappers

  class WrappersInterop {

    static function method CreateStringSome(s: string): Option<string> {
      Some(s)
    }

    static function method CreateStringNone(): Option<string> {
      None
    }

    static function method CreateBooleanSome(b: bool): Option<bool> {
      Some(b)
    }

    static function method CreateBooleanNone(): Option<bool> {
      None
    }
  }
}