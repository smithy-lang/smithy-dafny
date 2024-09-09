// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum SimpleEnumV2Shape {
    First,
Second,
Third,
}

impl ::std::fmt::Display for SimpleEnumV2Shape {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match self {
            SimpleEnumV2Shape::First => write!(f, "FIRST"),
SimpleEnumV2Shape::Second => write!(f, "SECOND"),
SimpleEnumV2Shape::Third => write!(f, "THIRD"),
        }
    }
}
