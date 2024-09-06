#!/bin/bash

REQUIRED_VERSION=4.5.0

INSTALLED_VERSION=$(dafny --version 2>&1 | grep -oE '[0-9]+\.[0-9]+\.[0-9]+')

if [ "$INSTALLED_VERSION" = "" ]; then
  echo "Error: Unable to fetch dafny version"
  exit 1
fi

if [ "$(printf "$INSTALLED_VERSION\n$REQUIRED_VERSION" | sort -V | head -n1)" != "$REQUIRED_VERSION" ]; then
  echo "Error: Installed Dafny version does not meet the required $REQUIRED_VERSION version. Upgrade to $REQUIRED_VERSION or newer.";
  exit 1;
else
  echo "$INSTALLED_VERSION"
fi