# Concepts

## Differences between Smithy-Dafny Python projects and other languages

### Interpreted vs. Compiled

Languages like Java and .NET are compiled, but Python is interpreted. This results in some important differences in Python:

1. Python imports modules based on filepath.
   If a module is located at `my_project/internaldafny/generated/SomeModule.py`, it must be imported as `my_project.internaldafny.generated.SomeModule`. (There are some hacks to work around this, but these are hacks.)
   This contrasts with Java/.NET, which import modules based on declared namespace. (ex.) Java might have a file at `dafny-generated/SomeModule/SomeClass.java` , but that class declares `package SomeModule` . To import this class, you would write `import SomeModule.SomeClass`.
2. Python links externs to generated code at runtime.
   When a Dafny-Python module is imported, it runs initialization glue code that will 1) import all of its generated Dafny (in a topological order to avoid circular dependencies), 2) import all of its externs.
   Then, each extern class must 1) extend the generated class, 2) override the generated class with the extern class.
   This contrasts with Java/.NET, where the externs extend partial/base generated classes, and link together at compile time.

## Smithy-Python Integration

### Smithy-Python “Hard Fork”

Smithy-Dafny relies on a “hard fork” of Smithy-Python.

Alternatives rejected include:

- **Submodule; create a regular fork of Smithy-Python.**
  - `smithy-lang` can’t create its own fork of Smithy-Python because `smithy-lang/smithy-python` is the real Smithy-Python
  - It would be improper to add some prefix/suffix to make the names not collide because `smithy-lang` is a shared AWS resource, and doing this would pollute the org’s repositories
  - It would be improper to have Smithy-Dafny reference some other owner’s fork of Smithy-Python because both projects are under `smithy-lang`.
- **Submodule; create a non-main branch on Smithy-Python**. This would add churn to Smithy-Dafny’s development process. Developers would need to get a change reviewed by the Smithy-Python team before they can deploy a change through Smithy-Dafny. It would also be improper to refer to a non-main branch.

### Smithy-Dafny code integration with Smithy-Python

Smithy-Dafny generates Python code by integrating with [Smithy-Python](https://github.com/smithy-lang/smithy-python/tree/develop/codegen).
Smithy-Dafny integrates with Smithy-Python via two integration mechanisms:

1. Smithy’s [plugin Integration](https://smithy.io/2.0/guides/building-codegen/making-codegen-pluggable.html) interface. This is used by code in a protocol’s `customize/` directory. See [LocalService’s customize directory](https://github.com/smithy-lang/smithy-dafny/tree/main-1.x/codegen/smithy-dafny-codegen/src/main/java/software/amazon/polymorph/smithypython/localservice/customize) as an example.
   Codegen that uses this integration includes:
   1. Override the HTTP protocol in Smithy-Python and generate protocols for local services, wrapped local services, and Dafny AWS SDK shims
   2. Write custom content to some files from the `customize` directive
2. Extending Smithy-Python classes and overriding its methods. This is used by code in a protocol’s `extensions/` directory. See [LocalService’s extensions directory](https://github.com/smithy-lang/smithy-dafny/tree/main-1.x/codegen/smithy-dafny-codegen/src/main/java/software/amazon/polymorph/smithypython/localservice/extensions) as an example.
   Codegen that uses this integration includes:
   1. Overriding Smithy-Python’s client class generation to generate a synchronous client
   2. Overriding Smithy-Python’s shape writer to handle Smithy-Dafny-specific shapes (Positional shapes, Reference shapes, etc)

Smithy-Dafny’s Python integration uses both mechanisms, but could probably be refactored to only use one or the other. A refactor to only extend Smithy-Python’s classes would be lower-lift than only implementing the plugin interface. There isn’t a pressing need to do this refactor, other than simplification.

#### **Limitations of the Plugin Interface**

The plugin interface has some gaps that prevent Smithy-Dafny’s Python codegen from exclusively using it. This is a non-exhaustive list:

1. **Doesn’t support changing shape generation.** Smithy-Python doesn’t recognize certain shapes, like shapes with Positional and Reference traits. (We wouldn’t expect it to; these are Smithy-Dafny-specific traits.) The plugin interface doesn’t let a plugin override a codegen’s shape generation to change how shapes are generated.
2. **Doesn’t support changing symbol generation.** Smithy-Python doesn’t understand how to generate references to symbols in other namespaces (what Smithy-Dafny calls “Dependencies”). The plugin interface doesn’t let a plugin override a codegen’s symbol generation to change how shapes are referenced.
3. **Doesn’t support overriding client generation.** Smithy-Python generates an async client, while Smithy-Dafny-Python requires a synchronous client. The plugin interface doesn’t let a plugin override a codegen’s client generation.
4. **Protocols without shapes.** Smithy-Dafny generates shims for AWS SDKs and wrapped local services. These protocols don’t require shape generation. Smithy-Python always generates all shapes it visits.

The workarounds to these involve extending Smithy-Python’s classes to work around these limitations.

#### **Extending Smithy-Python’s implementation**

Where Smithy-Dafny directly extends Smithy-Python, it prefers to do so by modifying access levels in Smithy-Python (e.g., making private methods protected or public), or by refactoring to introduce a new method that can be overridden via class extension.

This appears to be discouraged by Smithy. Smithy code generators tend to declare classes as `private` and/or `final` , suggesting class extensions aren’t preferred.

#### Future Work

1. Upstreaming changes from Smithy-Dafny’s Smithy-Python fork; relying on Smithy-Python upstream
   1. This should probably wait until Smithy-Python’s interfaces are finalized. Right now, Smithy-Python notes “WARNING: All interfaces are subject to change”. It might cause unneeded churn to integrate with Smithy-Python more closely now if Smithy-Dafny needs to update again later.
1. Reworking typehints. Typing in Smithy-Dafny Python was tacked on afterward, and is very fragile and overcomplicated as a result.
   A comprehensive rewrite to override Smithy-Python's typehinting would simplify this logic and increase its robustness.
