# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_multiplemodels_dependencyproject_internaldafny_wrapped
from multiple_models.smithygenerated.simple_multiplemodels_dependencyproject.client import DependencyProject
from multiple_models.smithygenerated.simple_multiplemodels_dependencyproject.shim import DependencyProjectShim
from multiple_models.smithygenerated.simple_multiplemodels_dependencyproject.config import dafny_config_to_smithy_config as dependency_dafny_config_to_smithy_config

import simple_multiplemodels_primaryproject_internaldafny_wrapped
from multiple_models.smithygenerated.simple_multiplemodels_primaryproject.client import PrimaryProject
from multiple_models.smithygenerated.simple_multiplemodels_primaryproject.shim import PrimaryProjectShim
from multiple_models.smithygenerated.simple_multiplemodels_primaryproject.config import dafny_config_to_smithy_config as primary_dafny_config_to_smithy_config

import Wrappers

class dependency_default__(simple_multiplemodels_dependencyproject_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedDependencyProject(config):
        wrapped_config = dependency_dafny_config_to_smithy_config(config)
        impl = DependencyProject(wrapped_config)
        wrapped_client = DependencyProjectShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# TODO-Python-PYTHONPATH: Remove
simple_multiplemodels_dependencyproject_internaldafny_wrapped.default__ = dependency_default__

class primary_default__(simple_multiplemodels_primaryproject_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedPrimaryProject(config):
        wrapped_config = primary_dafny_config_to_smithy_config(config)
        impl = PrimaryProject(wrapped_config)
        wrapped_client = PrimaryProjectShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# TODO-Python-PYTHONPATH: Remove
simple_multiplemodels_primaryproject_internaldafny_wrapped.default__ = primary_default__
