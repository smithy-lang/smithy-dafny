#!/bin/bash

cd ./runtimes/go/

dafnyGeneratedDirectories=$(find . -type d -name '*-go' | sort -nr)

for directory in $dafnyGeneratedDirectories; do
  directoriesWithDot=$(find $directory -type d -name '*.*.*' | sort -nr)
  for package in $directoriesWithDot; do
    sanitizedName=$(sed -e "s,${directory}/src/,,g" -e "s,\.,,g" <<<"${package}")
    searchPattern=$(sed -e "s,${directory}/src/,,g" <<<"${package}")
#    echo $sanitizedName
#    echo $searchPattern
    grep -rl $searchPattern $dafnyGeneratedDirectories | xargs sed -i "s,$searchPattern,$sanitizedName,g"
    for file in $(find $package -type d -name "${searchPattern}*" | sort -nr); do
      mv $file $(echo $file | sed "s,$searchPattern,$sanitizedName,g");
      done
  done
done

