#!/bin/bash
# Usage: ./update.sh <Path-to-ESDK> <ESDK Branch>
# Example: ./update.sh ~/workplace/private-aws-encryption-sdk-dafny-staging v4-seperate-modules
ESDK_PATH="$1"
ESDK_BRANCH="$2"
MDL_SRC_FILES=('traits.smithy')

set -e

cd "$ESDK_PATH"
if [ "$2" ]; then
  git checkout "$ESDK_BRANCH"
  git pull
fi

ESDK_COMMIT_SHA=$(git rev-parse --short HEAD)
echo -e "ESDK Commit Sha is $ESDK_COMMIT_SHA"
cd -

for MDL_FILE in "${MDL_SRC_FILES[@]}"; do
  cp "$ESDK_PATH/model/$MDL_FILE" "."
  git add "$MDL_FILE"
done

printf "Pulled Files for ESDK's model  and staged for commit. \n"
printf "Suggest executing: \n"
COMMIT_MSG="chore(tests): Update ESDK's Model to $ESDK_COMMIT_SHA"
echo "git commit -m \"$COMMIT_MSG\""
