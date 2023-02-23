include "../Model/SimpleExternTypes.dfy"

module{:extern "ExternConstructor"} ExternConstructor {

    class{:extern "ExternConstructorClass"} ExternConstructorClass {

        constructor{:extern "Constructor"} ()
            // This constructor is implemented as extern and hence it might be possible
            // that the underlying runtime can actualy throw errors in constructors (say C#).
            // In these cases, dafny would halt the whole program (since constructor can't have a return type
            // and can't return the error).
    }
}