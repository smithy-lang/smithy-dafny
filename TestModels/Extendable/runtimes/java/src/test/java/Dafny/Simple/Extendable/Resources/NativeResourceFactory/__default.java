package Dafny.Simple.Extendable.Resources.NativeResourceFactory;

import simple.extendable.resources.ToDafny;

import Dafny.Simple.Extendable.Resources.Types.IExtendableResource;
import Simple.Extendable.Resources.NativeResource;

public class __default {
    public static IExtendableResource DafnyFactory() {
        return ToDafny.ExtendableResource(NativeResource.NativeFactory());
    }
}
