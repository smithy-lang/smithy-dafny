// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.extendable.resources.internaldafny.nativeresourcefactory;

import simple.extendable.resources.NativeResource;
import simple.extendable.resources.ToDafny;
import simple.extendable.resources.internaldafny.types.IExtendableResource;

public class __default {

  public static IExtendableResource DafnyFactory() {
    return ToDafny.ExtendableResource(NativeResource.NativeFactory());
  }
}
