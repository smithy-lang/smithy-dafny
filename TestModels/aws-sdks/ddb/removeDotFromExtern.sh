#!/bin/bash
# TODO: remove this file if codegen is not generating extern with "." in go

removeDotFromExtern() {
  local directory="$1"
  # Recursively search for all files in the current directory and subdirectories
  for file in $(find "$directory" -type f); do
      # Check if the file contains the pattern "{:extern "XYZ" }"
      if grep -q '{:extern ".*"' "$file"; then
          # Extract the "XYZ" part from the pattern
          xyz=$(grep -o '{:extern "\([^"]*\)"' "$file" | sed 's/{:extern "\([^"]*\)"/\1/')
          # Check if the "XYZ" part contains a dot
          if [[ "$xyz" == *"."* ]]; then
              # Remove the dot from "XYZ"
              new_xyz=$(echo "$xyz" | sed 's/\.//g')
              # Update the file with the new pattern
              sed "s/{:extern \"$xyz\"/{:extern \"$new_xyz\"/g" $file > $file.tmp
              cat $file.tmp > $file
              rm $file.tmp
          fi
      fi
  done
}

removeDotFromExtern "Model"
removeDotFromExtern "src"

