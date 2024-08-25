// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleUnionTypes.dfy"

module SimpleResource {
  import opened Types = SimpleUnionTypes
  import opened Wrappers

  /*
    It is hard to prove things about mutable state.
    Smithy-Dafny attempts to help with this
    by adding the requires, ensures, and modifies clauses.
    However making sure that this is generated correctly
    can be complicated and tests are a very good idea.

    Further it is possible to generate a Dafny specification
    that can never be used.
    So this file is to make sure that the code is generates
    and verified in both the Dafny types file,
    and in an implementation.
    As well as verify at least one implementation is callable.
  */

  class SomeResource
    extends Types.ISimpleResource
    {

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
    }

    predicate GetResourceDataEnsuresPublicly(input: GetResourceDataInput , output: Result<GetResourceDataOutput, Error>)
    {
      true
    }

    constructor() 
      ensures fresh(Modifies)
      ensures ValidState()
    {
      History := new Types.ISimpleResourceCallHistory();
      Modifies := {History};
    }

    method GetResourceData' ( input: GetResourceDataInput )
      returns (output: Result<GetResourceDataOutput, Error>)
      requires
        && ValidState()
        && (match input.requiredUnion
            case Ref(o) =>
              && o.ValidState()
              && o.Modifies !! {History}


            case _ => true)
        && ( input.optionUnion.Some?
             ==> match input.optionUnion.value
                 case Ref(o) =>
                   && o.ValidState()
                   && o.Modifies !! {History}


                 case _ => true)
      modifies Modifies - {History} ,
               (match input.requiredUnion
                case Ref(o) => o.Modifies
                case _ => {}) ,
               (if input.optionUnion.Some? then match input.optionUnion.value
                                                case Ref(o) => o.Modifies
                                                case _ => {}
                else {})
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History} ,
                (match input.requiredUnion
                 case Ref(o) => o.Modifies
                 case _ => {}) ,
                (if input.optionUnion.Some? then match input.optionUnion.value
                                                 case Ref(o) => o.Modifies
                                                 case _ => {}
                 else {})
      ensures
        && ValidState()
        && ( output.Success? ==>
               && (match output.value.requiredUnion
                   case Ref(o) =>
                     && o.ValidState()
                     && o.Modifies !! {History}
                     && fresh(o)
                     && fresh ( o.Modifies - Modifies - {History} - (match input.requiredUnion
                                                                     case Ref(o) => o.Modifies
                                                                     case _ => {}) - (if input.optionUnion.Some? then match input.optionUnion.value
                                                                                                                      case Ref(o) => o.Modifies
                                                                                                                      case _ => {}
                                                                                      else {}) )
                   case _ => true)
               && ( output.value.optionUnion.Some?
                    ==> match output.value.optionUnion.value
                        case Ref(o) =>
                          && o.ValidState()
                          && o.Modifies !! {History}
                          && fresh(o)
                          && fresh ( o.Modifies - Modifies - {History} - (match input.requiredUnion
                                                                          case Ref(o) => o.Modifies
                                                                          case _ => {}) - (if input.optionUnion.Some? then match input.optionUnion.value
                                                                                                                           case Ref(o) => o.Modifies
                                                                                                                           case _ => {}
                                                                                           else {}) )
                        case _ => true) )
      ensures GetResourceDataEnsuresPublicly(input, output)
      ensures unchanged(History)

    {

      if input.requiredUnion.Ref? {
        var tmp :- input.requiredUnion.Ref.GetResourceData(Types.GetResourceDataInput(
          requiredUnion := Types.NotRef(32)
        ));
      } else if input.optionUnion.Some? && input.optionUnion.value.Ref? {
        var tmp :- input.optionUnion.value.Ref.GetResourceData(Types.GetResourceDataInput(
          requiredUnion := Types.NotRef(32)
        ));
      } 

      var freshResource := new SomeResource();

      output := Success(Types.GetResourceDataOutput(
        requiredUnion := Types.Ref(freshResource),
        optionUnion := Some(Types.Ref(freshResource))
      ));
    }
  }

}