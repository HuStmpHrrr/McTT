# Modules and Bindings: the Specification

The request this feature implements, kept verbatim.  What was built, and where it
deviates from what is written here, is in [`modules.md`](modules.md).

I am interested in supporting modules, global and local bindings. This change requires to

1. support of commands;
2. extend current terms;
3. define a theory of modules.

## Commands

To support modules and global definitions, we need to support three basic commands.

### Module declarations

At the beginning of each file, we need module declaration:

```
module X.Y.Z (x: Some) (y: Thing) where

... internal definitions

end
```

Note here modules are parameterized. We should support parameterized modules.


Module declarations can be nested.

### Global definitions

A global definition can be introduced by the `def` keyword:

```
def foo (x: Some): Thing := ...
end
```

`def` is public. We can do `private def` or `abstract def` if we want to make `foo` private or its body opaque, respectively. `private abstract def` combines both. 

### Module imports

Modules are imported by

```
import X.Y.Z
```

Then we can refer to definitions in `X.Y.Z` by `X.Y.Z.foo`.

We can do
```
import X.Y.Z as Z
```
to create an alias module `Z := X.Y.Z`.

```
import X.Y.Z use (foo; bar)
```
is the same as
```
import X.Y.Z

def foo := X.Y.Z.foo
end

def bar := X.Y.Z.bar
end
```
where `foo` and `bar`'s types are correctly filled in.

### Semantics

#### Global contexts

We need to maintain global contexts as a tree map to keep track of each dot access. For example, `X.Y.Z` is a three-level
deep entry. Each entry has two cases:

1. If `X.Y.Z` is referred to as a term, then `X.Y.Z` should be a term binding.
2. If `X.Y.Z.foo` is referred to as a term, then `X.Y.Z` is a module that contains `foo`.

The local context should also have a similar shape, which we will discuss after.

#### Import depths

Each module should maintain an import depth to break import cycle. This is defined as follows:

1. Each module begins with `0`.
2. Given the current depth `n`, for each import and its depth `m`, we update the current depth to `max(n, m + 1)`.

A module with an import depth must not have cycles. Conversely, each node in a directed import graph must have a depth.
We probably want to prove it.

#### Modifiers

Each term binding should maintain modifiers to capture `private` and `abstract`. Private symbols are not visible, i.e.
import won't expose these symbols.

## Term Judgments

Term judgments now must consider a global context, and extend a `global` case that captures global bindings. We should also module
a qualified sequence. A qualified sequence is a non-empty list. The head could be a string or a de Bruijn index. When the head is a
string, we are accessing a global module; for a de Bruijn index, we are accessing a local module. The tails are strings to look up
the module.

### Local bindings

Local bindings are introduced by let bindings:
```
let x1 (y: Some) : Thing :=  ...
    x2 ...
in
  ...
end
```
`x2` may refer to `x1`.

Local module bindings are `let module M := X.Y.Z x y z in ... end`.


### Elaboration

The name resolution rule is the following. To resolve `X.Y.Z`:

1. If `X` is a global, then the module lookup proceeds in the global context.
2. If `X` is a local, then the lookup proceeds in the local context.
3. `X.Y.Z` is attempted to be identified as a term.

We should also be concerned about modules. If `X.Y.Z` is not a term,
but a module, then we need `X.Y.Z.foo` to form a valid term.

In addition, if `X.Y.Z` is parameterized, then `(X.Y.Z x y z).foo` is a valid expression
for a term. Note that we only access this expression as a term when `X.Y.Z` is fully
applied.

## Module Theory

We need a formulation of module theory. Module is higher-order, so it does not need
to live in any universe level. The theory needs to be concerned about parameters too.
Please fan out and search the internet to find out whether there is already existing
reference of formalization.