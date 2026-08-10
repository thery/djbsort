# rocq_compile_file ignores _CoqProject -R entries outside the file's own directory (rocq_start honours them)

## Summary

In a project whose `_CoqProject` maps a *sibling* directory, `rocq_compile_file` cannot find the libraries there, while the interactive tools (`rocq_start` / `rocq_check`) resolve them fine from the same `_CoqProject`. This makes whole-file verification unusable for multi-directory projects.

## Setup

Layout:

```
code/common/       more_tuple.v  nsort.v  nbitonic.v  ...   (compiled: .vo/.vos present)
code/avx2/proof/   _CoqProject  sort_generic.v  ...
```

`code/avx2/proof/_CoqProject`:

```
-arg -w -arg -notation-overridden
-arg -w -arg -ambiguous-paths
-I .
-R . extra
-R ../../common extra
```

`sort_generic.v` starts with `Require Import more_tuple nsort nbitonic.`

## What happens

`rocq_compile_file(file=".../code/avx2/proof/sort_generic.v")`:

```
Error: Unable to locate library more_tuple (while searching for a .vos file).
```

`rocq_start(file=".../code/avx2/proof/sort_generic.v", line=130, character=0)` then
`rocq_check(body="Check bfsort.")` — works, and returns
``bfsort : bool -> forall m : nat, network (`2^ m)``, i.e. the sibling-directory
libraries resolved.

## Narrowing it down

Four variants, same file, only `_CoqProject` changed:

| `_CoqProject` mapping | shared `.vo` copied into the dir | result |
|---|---|---|
| `-R . extra` + `-R ../../common extra` | no | `Unable to locate library more_tuple` |
| `-R /abs/path/to/code/common extra` alone | no | `Unable to locate library more_tuple` |
| none (only `-I .`) | yes | `The file .../more_tuple.vo contains library extra.more_tuple and not library more_tuple` |
| `-R . extra` alone | yes | compiles |

The third row is the informative one: with no mapping at all the file in the
working directory *is* found, so the directory itself is on the load path — but
its logical name is rejected. And an absolute path in row 2 rules out any
relative-path/cwd explanation.

So `-R` entries appear to be honoured only when they point at the file's own
directory; entries pointing elsewhere seem to be dropped.

## Workaround

Copy the shared `.vo`, `.vos`, `.glob` and `.coq-native/` into the directory
being compiled and reduce the mapping to `-R . extra`. With two `-R` lines
sharing the alias `extra` this then reports `Required library more_tuple matches
several files in path`, so the second line has to go while the copies are
present.

## Why it matters

`rocq_start` cannot always substitute. In our project it fails to parse a
notation (`` `2^ ``) in one directory that `coqc` accepts, so
`rocq_compile_file` is the only way to check those files — and the only way to
write a check as a lemma proved by `vm_compute`, which is the only form of check
that fails loudly.

## Versions

mathcomp 2.x on Rocq 9.1.0; rocq-mcp as shipped in the Claude Code MCP
configuration. A minimal reproduction repository can be supplied.
