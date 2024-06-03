#!/bin/bash

#TODO: Remove this file if manual change is not required

# Set the source directory
src_dir="./runtimes/go"

# Move the types directory
mv "$src_dir"/types "$src_dir"/ImplementationFromDafny-go/

# Loop through all Go files in the source directory
for go_file_path in "$src_dir"/*.go; do
    # Get the package name from the Go file
    package_name=$(grep -o '^package \([a-zA-Z0-9_]*\)' "$go_file_path" | sed 's/^package \([a-zA-Z0-9_]*\)/\1/')

    # Construct the new directory path
    if [ "$(basename $go_file_path)" == "shim.go" ]; then
        new_dir_path=$(dirname "$go_file_path")/"TestsFromDafny-go"/"$package_name"
    else
        new_dir_path=$(dirname "$go_file_path")/"ImplementationFromDafny-go"/"$package_name"
    fi

    # Create the new directory if it doesn't exist
    mkdir -p "$new_dir_path"

    # Move the Go file to the new directory
    mv "$go_file_path" "$new_dir_path"/
done