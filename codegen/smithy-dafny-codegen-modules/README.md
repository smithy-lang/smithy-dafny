# smithy-dafny-codegen-modules

Directory containing modules that are dependencies of Smithy-Dafny codegen.

## Smithy-Python

[Smithy-Python](https://github.com/smithy-lang/smithy-python) is copied into this repository for now.

To reproduce Smithy-Python from source:

```
git clone git@github.com:smithy-lang/smithy-python.git
cd smithy-python  
git checkout 06eb6b1c361ee058ca8854c0a1ccfbeb41648a58 
rm .git  
```