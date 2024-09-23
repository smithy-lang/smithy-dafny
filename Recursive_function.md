# Recursive_function

- Divide container (structure, union, list and map) shape conversion into a function. Rest of the shape will still be inline.
- List and map can still be inline?

## To Native

function name = Shape name + "_FromDafny" (This is unique always)
Input = derivedShape (after unwrap) which will be `DafnyNameResolver.getDafnyType(shape, context.symbolProvider().toSymbol(shape))`
Output = native type of the shape `DafnyNameResolver.getDafnyType(shape, context.symbolProvider().toSymbol(shape))`

