# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import ExternDefinitions
import simple_orphaned
import simple_orphaned.smithygenerated.simple_orphaned.deserialize
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

class default__(ExternDefinitions.default__):

    @staticmethod
    def InitializeOrphanedStructure(dafny_uninitialized_structure):
        native_structure = simple_orphaned.smithygenerated.simple_orphaned.dafny_to_smithy.simple_orphaned_OrphanedStructure(dafny_uninitialized_structure)
        native_structure.string_value = "the extern MUST use Smithy-generated conversions to set this value in the native structure"
        dafny_initialized_structure = simple_orphaned.smithygenerated.simple_orphaned.smithy_to_dafny.simple_orphaned_OrphanedStructure(native_structure)
        return dafny_initialized_structure

    @staticmethod
    def CallNativeOrphanedResource(dafny_resource):
        native_resource = simple_orphaned.smithygenerated.simple_orphaned.dafny_to_smithy.simple_orphaned_OrphanedResourceReference(dafny_resource)
        native_output = native_resource.orphaned_resource_operation(
            simple_orphaned.smithygenerated.simple_orphaned.models.OrphanedResourceOperationInput(
                some_string = "the extern MUST provide this string to the native resource's operation"
            )
        )
        dafny_output = simple_orphaned.smithygenerated.simple_orphaned.smithy_to_dafny.simple_orphaned_OrphanedResourceOperationOutput(native_output)
        return Wrappers.Result_Success(dafny_output)

    @staticmethod
    def CallNativeOrphanedError(dafny_error):
        native_error = simple_orphaned.smithygenerated.simple_orphaned.deserialize._deserialize_error(dafny_error)
        native_error.message = "the extern MUST set this string using the catch-all error converter, NOT the orphaned error-specific converter"
        dafny_error_again = simple_orphaned.smithygenerated.simple_orphaned.errors._smithy_error_to_dafny_error(native_error)
        return dafny_error_again

ExternDefinitions.default__ = default__
