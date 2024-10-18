package software.amazon.polymorph.traits;

import java.util.ArrayList;
import java.util.List;
import software.amazon.polymorph.traits.MutableLocalStateTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
import software.amazon.smithy.model.selector.Selector;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.validation.AbstractValidator;
import software.amazon.smithy.model.validation.ValidationEvent;

public class MutableLocalStateTraitValidator extends AbstractValidator {

  @Override
  public List<ValidationEvent> validate(Model model) {
    List<ValidationEvent> events = new ArrayList<>();
    for (Shape shape : model.getShapesWithTrait(MutableLocalStateTrait.class)) {
      // Generate danger for any use of this trait.
      // See the danger message for details.
      events.add(
        danger(
          shape,
          """
          aws.polymorph#mutableLocalState may allow callers to introduce soundness issues.

          At this time to support dynamic mutable state smithy-dafny creates a "separated class" by using an {:axiom}.
          The idea for these seperated classes is that the resource has access to an internal modifies set.
          This is sometimes referred to as an Repr set.
          The resources internal operations are allowed to modify this InternalModifies,
          but the public operations are not.
          A Dafny `assume {:axiom}` is used to create this separation between the InternalModifies and the Modifies sets.

          Smithy-dafny operations that return these resources will always return the `trait`
          which does not have any concrete implementation of state.
          However, a clever caller could cast this trait into its concrete class.
          Such a caller now has access to observe the internal state of the resource.

          Dafny may allow such a caller to prove that this state is unchanged.
          Because the called operations do not contain these elements inside their `modifies` clause.
          But these elements would indeed be modified.
          Thus Dafny might prove false.

          ```dafny

          var Output(resource) :- expect client.GetResource();

          expect resource is ConcreteResource;
          var concreteResource := resource as ConcreteResource;

          // Get a copy of state before state changes
          var state := concreteResource.state;

          var output2 :- expect concreteResource.ChangeState();

          // State will have changed, because we called for a state change.
          // however, Dafny may be able prove that state MUST NOT have changed.
          assert state == concreteResource.state;
          expect state != concreteResource.state;
          ```

          This can be mitigated with export sets
          See TestModels/Resource/src/MutableResource.dfy for an example.
          """
        )
      );
    }

    return events;
  }
}
