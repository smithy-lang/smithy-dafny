TODO-Python: Add more content here

Top-level file overview:

```
├── awssdk - Generates a boto3 wrapper to call from Dafny-generated Python code
├── common - Common code across generation targets
├── localservice - Generates a Smithy client that wraps a Dafny-generated Python localService implementation
└── wrappedlocalservice - Generates a wrapper for the `localservice` code to call the Smithy client from Dafny-generated Python code
```

Each subfolder follows a similar structure:

```
├── customize - Classes referenced from a plugin's `PythonIntegration.customize` function.
│               Generates new files or adds new code to Smithy-Python generated files.
├── extensions - Classes that extend or replace Smithy-Python codegen components.
├── nameresolver - Utility classes to map Smithy model shapes to strings used in generated code.
└── shapevisitor - Classes that generate code to convert to/from Smithy client Python shapes
    │              (or AWS SDK shapes) and Dafny implementation shapes.
    └── conversionwriter - Classes that generate functions that convert to/from Smithy client Python shapes
                   (or AWS SDK shapes) and Dafny implementation shapes for StructureShapes and UnionShapes.
```
