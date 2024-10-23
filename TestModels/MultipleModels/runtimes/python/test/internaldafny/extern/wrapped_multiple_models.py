# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from multiple_models.smithygenerated.simple_multiplemodels_dependencyproject.client import DependencyProject
from multiple_models.smithygenerated.simple_multiplemodels_dependencyproject.shim import DependencyProjectShim
from multiple_models.smithygenerated.simple_multiplemodels_dependencyproject.config import dafny_config_to_smithy_config as dependency_dafny_config_to_smithy_config
from multiple_models.smithygenerated.simple_multiplemodels_primaryproject.client import PrimaryProject
from multiple_models.smithygenerated.simple_multiplemodels_primaryproject.shim import PrimaryProjectShim
from multiple_models.smithygenerated.simple_multiplemodels_primaryproject.config import dafny_config_to_smithy_config as primary_dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleMultiplemodelsDependencyprojectService
import WrappedSimpleMultiplemodelsPrimaryprojectService

class dependency_default__(WrappedSimpleMultiplemodelsDependencyprojectService.default__):

    @staticmethod
    def WrappedDependencyProject(config):
        wrapped_config = dependency_dafny_config_to_smithy_config(config)
        impl = DependencyProject(wrapped_config)
        wrapped_client = DependencyProjectShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleMultiplemodelsDependencyprojectService.default__ = dependency_default__

class primary_default__(WrappedSimpleMultiplemodelsPrimaryprojectService.default__):

    @staticmethod
    def WrappedPrimaryProject(config):
        wrapped_config = primary_dafny_config_to_smithy_config(config)
        impl = PrimaryProject(wrapped_config)
        wrapped_client = PrimaryProjectShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleMultiplemodelsPrimaryprojectService.default__ = primary_default__