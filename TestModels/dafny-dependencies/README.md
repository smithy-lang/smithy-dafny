# dafny-dependencies

This directory contains modules and dependencies to be used in
Dafny Source Code `*.dfy` files. These are available across projects
under TestModels directory.

# Updating

These dependencies are sourced from other repositories.
Each dependency should have an update script.

To update a dependency, execute:

```
./update.sh <Path-to-Local-Clone-Of-Repo> <Branch-In-Local-Clone>
```

The update script will copy the needed files from a local clone of the source repo.
The first arguement is the path to the local clone.
The second arguement is optional,
and is the branch name that should be used when pulling.
If the second arguement is given,
the update script will first checkout that branch,
and run `git pull`.

Example:
To update the `StandardLibrary`,
which is developed in the ESDK-Dafny repo,
in the `v4-seperate-modules` branch:

```
./update.sh /Users/tonyknap/workplace/ryan-new-world/private-aws-encryption-sdk-dafny-staging v4-seperate-modules
```

## Note on `libraries`

While `libraries` is developed in `dafny-lang/libraries`,
the ESDK-Dafny develops against a particular verision of it,
via a submodule.

As such, we pull `libraries` from the ESDK-Dafny repo.
