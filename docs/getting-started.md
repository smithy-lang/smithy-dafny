# Makefile Variables

To create a Smithy-Dafny project, you will need a Makefile with the following variables defined.
These variables apply to all languages.
Some languages have additional required variables.

- `PROJECT_SERVICES`: List of names of each local service in the project.
- `PROJECT_INDEX`: This is a space-delimited list of `Index.dfy` files for your dependencies.
- `PROJECT_DEPENDENCIES`: List of top-level directory names for dependencies for the project.
- `SERVICE_NAMESPACE_<service>`: For each service in `PROJECT_SERVICES`, this is the Smithy namespace for shapes attached to that local service.
- `SERVICE_DEPS_<service>`: For each service in `PROJECT_SERVICES`, this is the list of paths to `Model/` directories for dependencies of that service.

Examples:

- [Crypto Tools’ MPL](https://github.com/aws/aws-cryptographic-material-providers-library/blob/main/AwsCryptographicMaterialProviders/Makefile). This project sets all of these variables with multiple dependencies.
