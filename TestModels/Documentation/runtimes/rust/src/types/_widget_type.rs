// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(Debug, PartialEq, Copy, Clone)]
/// Types of widgets you can get.
pub enum WidgetType {
    Blue,
Large,
Squishy,
}

impl ::std::fmt::Display for WidgetType {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match self {
            WidgetType::Blue => write!(f, "BLUE"),
WidgetType::Large => write!(f, "LARGE"),
WidgetType::Squishy => write!(f, "SQUISHY"),
        }
    }
}
