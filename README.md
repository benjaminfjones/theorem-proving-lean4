# theorem-proving-lean

Notes from [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)

## Prove, Type Check, and Build

```
$ lake build
Building TheoremProvingLean
Building TheoremProvingLean.and_commutative
Building TheoremProvingLean.implicit_args
Building TheoremProvingLean.propositions_as_types
Building TheoremProvingLean.simple_type_theory
Compiling TheoremProvingLean
Compiling TheoremProvingLean.and_commutative
Compiling TheoremProvingLean.propositions_as_types
Compiling TheoremProvingLean.implicit_args
Compiling TheoremProvingLean.simple_type_theory
Building Main
Compiling Main
Linking theorem-proving-lean
```

## Setup

### Lean toolchain

Install `elan`, the lean toolchain manager and install the lean4 nightly
toolchain:
```
$ curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
$ source $HOME/.elan/env
$ elan toolchain isntall leanprover/lean4:nightly
$ elan default leanprover/lean4:nightly
$ lean --version
Lean (version 4.0.0-nightly-2023-01-06, commit fedf235cba35, Release)
```

References:
- https://leanprover.github.io/lean4/doc/setup.html
