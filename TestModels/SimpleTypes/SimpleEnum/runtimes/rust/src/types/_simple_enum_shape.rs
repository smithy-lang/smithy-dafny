// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum SimpleEnumShape {
    First,
Second,
Third,
}

impl ::std::fmt::Display for SimpleEnumShape {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match self {
            SimpleEnumShape::First => write!(f, "FIRST"),
SimpleEnumShape::Second => write!(f, "SECOND"),
SimpleEnumShape::Third => write!(f, "THIRD"),
        }
    }
}
