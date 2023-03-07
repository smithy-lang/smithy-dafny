#!/bin/bash
# Usage: ./update.sh <Path-to-ESDK> <ESDK Branch>
# Example: ./update.sh ~/workplace/private-aws-encryption-sdk-dafny-staging v4-seperate-modules
ESDK_PATH="$1"
ESDK_BRANCH="$2"
STD_DFY_SRC_FILES=('StandardLibrary.dfy' 'UInt.dfy' 'UTF8.dfy')
STD_DFY_TST_FILES=('UTF8.dfy')
STD_NET_FILES=('Extern/UTF8.cs' 'STD.csproj' 'tests/Test-STD.csproj')
STD_JAVA_FILES=('src/main/java/UTF8/__default.java' 'build.gradle.kts')

set -e

cd "$ESDK_PATH"
if [ "$2" ]; then
  git checkout "$ESDK_BRANCH"
  git pull
fi
ESDK_COMMIT_SHA=$(git rev-parse --short HEAD)
echo -e "ESDK Commit Sha is $ESDK_COMMIT_SHA"
cd -
for DAFNY_FILE in "${STD_DFY_SRC_FILES[@]}"; do
  cp "$ESDK_PATH/StandardLibrary/src/$DAFNY_FILE" "src/$DAFNY_FILE"
  git add "src/$DAFNY_FILE"
done
for DAFNY_FILE in "${STD_DFY_TST_FILES[@]}"; do
  cp "$ESDK_PATH/StandardLibrary/test/$DAFNY_FILE" "test/$DAFNY_FILE"
  git add "test/$DAFNY_FILE"
done
for CS_FILE in "${STD_NET_FILES[@]}"; do
  cp "$ESDK_PATH/StandardLibrary/runtimes/net/$CS_FILE" "runtimes/net/$CS_FILE"
  git add "runtimes/net/$CS_FILE"
done
for JAVA_FILE in "${STD_JAVA_FILES[@]}"; do
  cp "$ESDK_PATH/StandardLibrary/runtimes/java/$JAVA_FILE" "runtimes/java/$JAVA_FILE"
  git add "runtimes/java/$JAVA_FILE"
done
printf "Pulled Files for ESDK's StandardLibrary and staged for commit. \n"
printf "Suggest executing: \n"
COMMIT_MSG="chore(tests): Update ESDK STD to $ESDK_COMMIT_SHA"
echo "git commit -m \"$COMMIT_MSG\""
