# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=com.amazonaws.sqs
AWS_SDK_CMD=--aws-sdk

# This project has no dependencies
# DEPENDENT-MODELS:=
# LIBRARIES :=

# There is no wrapped target for aws-sdk types
_polymorph_wrapped: ;
_polymorph_wrapped_dafny: ;
_polymorph_wrapped_net: ;
_polymorph_wrapped_java: ;

# Just defining the common target the CI uses to test these models,
# even though this use case doesn't involve "polymorph" per se
# and instead uses the Smithy Gradle plugin.
# For now this is only building with `typescript-codegen`
# as a sanity check that the model validates etc.,
# but the intent is to add `dafny-client-codegen` once we implement it.
# polymorph_dafny:
# 	./gradlew build

# verify:
# Nothing to verify yet.
# The test file is just there in TDD style
# and won't be valid until we actualy generate Dafny code.

# dafny-reportgenerator:
# Ditto
