// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
  First run `make setup_semantic_release` to install the required dependencies.

  Using this config semantic-release will search for the latest tag
  evaluate all commits after that tag
  generate release notes and a version bump.
  It will commit these changes, push these changes, and publish a new version tag.

  This file requires a `--branches` option to function.
  This is to facilitate point releases if needed.

  `npx semantic-release --branches main` 
*/

// This project has several runtimes
// each one has files that need to be updated.
// We model all the files and the runtimes here in this structure
const Runtimes = {
  java: {
    "AwsCryptographicMaterialProviders/runtimes/java/build.gradle.kts": {
      dependencies: [],
    },
  },
  net: {
    "AwsCryptographicMaterialProviders/runtimes/net/MPL.csproj": {
      dependencies: [
        "AWS.Cryptography.Internal.StandardLibrary",
        "AWS.Cryptography.Internal.ComAmazonawsKms",
        "AWS.Cryptography.Internal.ComAmazonawsDynamodb",
        "AWS.Cryptography.Internal.AwsCryptographyPrimitives",
      ],
    },
    "ComAmazonawsKms/runtimes/net/AWS-KMS.csproj": {
      dependencies: ["AWS.Cryptography.Internal.StandardLibrary"],
    },
    "ComAmazonawsDynamodb/runtimes/net/ComAmazonawsDynamodb.csproj": {
      dependencies: ["AWS.Cryptography.Internal.StandardLibrary"],
    },
    "AwsCryptographyPrimitives/runtimes/net/Crypto.csproj": {
      dependencies: ["AWS.Cryptography.Internal.StandardLibrary"],
    },
    "StandardLibrary/runtimes/net/STD.csproj": {
      dependencies: [],
    },
  },
};

/**
 * @type {import('semantic-release').GlobalConfig}
 */
module.exports = {
  // branches: "main",
  repositoryUrl:
    "git@github.com:aws/aws-cryptographic-material-providers-library-dafny.git",
  plugins: [
    // Check the commits since the last release
    "@semantic-release/commit-analyzer",
    // Based on the commits generate release notes
    "@semantic-release/release-notes-generator",
    // Update the change log with the generated release notes
    [
      "@semantic-release/changelog",
      {
        changelogFile: "CHANGELOG.md",
        changelogTitle: "# Changelog",
      },
    ],

    // Bump the various versions
    [
      "semantic-release-replace-plugin",
      {
        replacements: [
          // Update the version for all Gradle Java projects
          // Does not update the dependencies
          {
            files: Object.keys(Runtimes.java),
            from: 'version = ".*"',
            to: 'version = "${nextRelease.version}"',
            results: Object.keys(Runtimes.java).map(CheckResults),
            countMatches: true,
          },

          // Now update the Gradle Java  dependencies
          ...Object.entries(Runtimes.java).flatMap(([file, { dependencies }]) =>
            dependencies.map((dependency) => ({
              files: [file],
              from: `implementation("${dependency}:.*")`,
              to:
                `implementation("${dependency}:` + '${nextRelease.version}" />',
              results: [CheckResults(file)],
              countMatches: true,
            })),
          ),

          // Update the version for all DotNet projects
          // Does not update the dependencies
          {
            files: Object.keys(Runtimes.net),
            from: "<Version>.*</Version>",
            to: "<Version>${nextRelease.version}</Version>",
            results: Object.keys(Runtimes.net).map(CheckResults),
            countMatches: true,
          },

          // Now update the Dotnet project dependencies
          ...Object.entries(Runtimes.net).flatMap(([file, { dependencies }]) =>
            dependencies.map((dependency) => ({
              files: [file],
              from: `<PackageReference Include=\"${dependency}\" Version=\".*\" />`,
              to:
                `<PackageReference Include=\"${dependency}\"` +
                ' Version="${nextRelease.version}" />',
              results: [CheckResults(file)],
              countMatches: true,
            })),
          ),
        ],
      },
    ],
    // Commit and push changes the changelog and versions bumps
    [
      "@semantic-release/git",
      {
        assets: [
          "CHANGELOG.md",
          ...Object.values(Runtimes).flatMap((r) => Object.keys(r)),
        ],
        message:
          "chore(release): ${nextRelease.version} [skip ci]\n\n${nextRelease.notes}",
      },
    ],
  ],
};

function CheckResults(file) {
  return {
    file,
    hasChanged: true,
    numMatches: 1,
    numReplacements: 1,
  };
}
