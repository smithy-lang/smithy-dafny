#!/bin/bash

# Ensure all required variables are set
if [ -z "$SED_FILE_PATH" ] || [ -z "$SED_BEFORE_STRING" ] || [ -z "$SED_AFTER_STRING" ]; then
    echo "Error: SED_FILE_PATH, SED_BEFORE_STRING, and SED_AFTER_STRING must all be set and non-empty."
    exit 1
fi

# If the AFTER string is already present and the BEFORE string is not, then exit success
if grep -q "$SED_AFTER_STRING" "$SED_FILE_PATH" && ! grep -q "$SED_BEFORE_STRING" "$SED_FILE_PATH"; then
    echo "String has already been replaced in $SED_FILE_PATH"
    exit 0
fi

# If neither the AFTER nor BEFORE strings are present, then exit failure
if ! grep -q "$SED_BEFORE_STRING" "$SED_FILE_PATH"; then
    echo "Error: Could not find string to replace in $SED_FILE_PATH"
    exit 1
fi

# If both the AFTER and BEFORE strings are present, then exit failure
if grep -q "$SED_AFTER_STRING" "$SED_FILE_PATH" && grep -q "$SED_BEFORE_STRING" "$SED_FILE_PATH"; then
    echo "Error: Both BEFORE and AFTER strings are present in $SED_FILE_PATH"
    exit 1
fi

# Perform sed replacement
echo "Replacing in $SED_FILE_PATH"
sed -i "$SED_PARAMETER" "s/$SED_BEFORE_STRING/$SED_AFTER_STRING/g" "$SED_FILE_PATH"

# Verify the replacement was successful
if grep -q "$SED_BEFORE_STRING" "$SED_FILE_PATH" || ! grep -q "$SED_AFTER_STRING" "$SED_FILE_PATH"; then
    echo "Error: No replacements made in $SED_FILE_PATH"
    exit 1
else
    echo "Replacement successful in $SED_FILE_PATH"
    exit 0
fi