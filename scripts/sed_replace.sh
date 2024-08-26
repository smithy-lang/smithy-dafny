# Ensure all required variables are set
# (This SHOULD have already been checked)
if [ -z "$SED_FILE_PATH" ] || [ -z "$SED_BEFORE_STRING" ] || [ -z "$SED_AFTER_STRING" ]; then
    echo "Error: SED_FILE_PATH, SED_BEFORE_STRING, and SED_AFTER_STRING must all be set and non-empty."
    exit 1
fi

# Check if the file exists
if [ ! -f "$SED_FILE_PATH" ]; then
    echo "Error: File $SED_FILE_PATH does not exist."
    exit 1
fi

# If the AFTER string is already present and the BEFORE string is not,
# then exit success,
# because the expected result is already present.
if grep -q "$SED_AFTER_STRING" "$SED_FILE_PATH" && ! grep -q "$SED_BEFORE_STRING" "$SED_FILE_PATH"; then
    echo "String has already been replaced in $SED_FILE_PATH"
    exit 0
fi

# If neither the AFTER nor BEFORE strings are present,
# then exit failure,
# because the sed will fail as the before string is not present.
if ! grep -q "$SED_BEFORE_STRING" "$SED_FILE_PATH"; then
    echo "Error: Could not find string to replace in $SED_FILE_PATH"
    exit 1
fi

# If both the AFTER and BEFORE strings are present,
# then exit failure,
# because the sed will produce unintended results (2 after strings).
if grep -q "$SED_AFTER_STRING" "$SED_FILE_PATH" && grep -q "$SED_BEFORE_STRING" "$SED_FILE_PATH"; then
    echo "Error: Both BEFORE and AFTER strings are present in $SED_FILE_PATH"
    exit 1
fi

# Perform sed
echo "Replacing in $SED_FILE_PATH"
OS=$(uname)
echo "Using sed-like command for OS $OS"

# macOS
if [ "$OS" = "Darwin" ]; then
    echo "Replacing in $SED_FILE_PATH using macOS-formatted sed"
    sed -i "" "s/$SED_BEFORE_STRING/$SED_AFTER_STRING/g" $SED_FILE_PATH

# Windows
elif [[ "$OS" == *"NT"* ]] || [ "$OS" = "MINGW64_NT" ]; then
    echo "Replacing in $SED_FILE_PATH using PowerShell"
    powershell -Command "(Get-Content '$SED_FILE_PATH') -replace '$SED_BEFORE_STRING', '$SED_AFTER_STRING' | Set-Content '$SED_FILE_PATH'"

# Linux
else
    echo "Replacing in $SED_FILE_PATH using Linux-formatted sed"
    sed -i "s/$SED_BEFORE_STRING/$SED_AFTER_STRING/g" $SED_FILE_PATH
fi 

# Verify the replacement was successful

# If the BEFORE string is still present or the AFTER string is not present,
# then exit failure,
# because the sed did not succeed
if grep -q "$SED_BEFORE_STRING" "$SED_FILE_PATH" || ! grep -q "$SED_AFTER_STRING" "$SED_FILE_PATH"; then
    echo "Error: No replacements made in $SED_FILE_PATH"
    exit 1
else
    echo "Replacement successful in $SED_FILE_PATH"
    exit 0
fi
