#!/bin/bash
# Usage: ./update.sh <Path-to-ESDK> <ESDK Branch>
# Example: ./update.sh ~/workplace/private-aws-encryption-sdk-dafny-staging v4-seperate-modules
ESDK_PATH="$1"
ESDK_BRANCH="$2"
LIB_DFY_SRC_FILES=('Wrappers.dfy')

set -e

cd "$ESDK_PATH"
if [ "$2" ]; then
  git checkout "$ESDK_BRANCH"
  git pull --recurse-submodules
fi
ESDK_COMMIT_SHA=$(git rev-parse --short HEAD)
echo -e "ESDK Commit Sha is $ESDK_COMMIT_SHA"
cd -
for DAFNY_FILE in "${LIB_DFY_SRC_FILES[@]}"; do
  cp "$ESDK_PATH/libraries/src/$DAFNY_FILE" "src/$DAFNY_FILE"
  git add "src/$DAFNY_FILE"
done
printf "Pulled Files for ESDK's libraries and staged for commit. \n"
printf "Suggest executing: \n"
COMMIT_MSG="chore(tests): Update ESDK's dafny-lang/libraries to $ESDK_COMMIT_SHA"
echo "git commit -m \"$COMMIT_MSG\""
