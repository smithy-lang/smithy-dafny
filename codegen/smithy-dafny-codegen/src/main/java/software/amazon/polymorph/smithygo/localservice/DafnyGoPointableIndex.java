package software.amazon.polymorph.smithygo.localservice;

import software.amazon.polymorph.smithygo.utils.GoCodegenUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.RequiredTrait;

public class DafnyGoPointableIndex {

  public static boolean isNillable(final Model model, final Shape shape) {
    return (
      !shape.hasTrait(RequiredTrait.class) &&
      !GoCodegenUtils.isOperationStruct(model, shape)
    );
  }
}
