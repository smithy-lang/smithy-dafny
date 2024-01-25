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
      dependencies: [],
      assemblyInfo:
        "AwsCryptographicMaterialProviders/runtimes/net/AssemblyInfo.cs",
    },
    "ComAmazonawsKms/runtimes/net/AWS-KMS.csproj": {
      dependencies: [],
      assemblyInfo: "ComAmazonawsKms/runtimes/net/AssemblyInfo.cs",
    },
    "ComAmazonawsDynamodb/runtimes/net/ComAmazonawsDynamodb.csproj": {
      dependencies: [],
      assemblyInfo: "ComAmazonawsDynamodb/runtimes/net/AssemblyInfo.cs",
    },
    "AwsCryptographyPrimitives/runtimes/net/Crypto.csproj": {
      dependencies: [],
      assemblyInfo: "AwsCryptographyPrimitives/runtimes/net/AssemblyInfo.cs",
    },
    "StandardLibrary/runtimes/net/STD.csproj": {
      dependencies: [],
      assemblyInfo: "StandardLibrary/runtimes/net/AssemblyInfo.cs",
    },
  },
};

/**
 * @type {import('semantic-release').GlobalConfig}
 */
module.exports = {
  //branches: ["main"],
  repositoryUrl:
    "git@github.com:aws/aws-cryptographic-material-providers-library.git",
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

          // Update the AssmeblyInfo.cs file of the DotNet projects
          ...Object.entries(Runtimes.net).flatMap(
            ([file, { assemblyInfo }]) => ({
              files: assemblyInfo,
              from: "assembly: AssemblyVersion(.*)",
              to: 'assembly: AssemblyVersion("${nextRelease.version}")]',
              results: [CheckResults(assemblyInfo)],
              countMatches: true,
            }),
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
          ...Object.values(Runtimes.net).flatMap((r) => r.assemblyInfo),
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
