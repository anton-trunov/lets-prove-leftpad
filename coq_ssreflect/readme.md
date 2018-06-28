# About Coq

The [Coq](https://coq.inria.fr) system is designed to develop mathematical proofs,
and especially to write formal specifications, programs and to verify that programs
are correct with respect to their specification. It provides a specification language
named Gallina. Terms of Gallina can represent programs as well as properties of these
programs and proofs of these properties. Using the so-called Curry-Howard isomorphism,
programs, properties and proofs are formalized in the same language called Calculus of Inductive Constructions,
that is a λ-calculus with a rich type system. All logical judgments in Coq are typing judgments.
The very heart of the Coq system is the type-checking algorithm that checks the correctness of proofs,
in other words that checks that a program complies to its specification.
Coq also provides an interactive proof assistant to build proofs using specific programs called tactics.

The [Coq wiki](https://github.com/coq/coq/wiki) has a number of links, including tutorials and books on the subject.
The [Software Foundations](https://softwarefoundations.cis.upenn.edu) book is one of the gentler introductions to theorem proving with applicationsto programming languages theory.

## About SSReflect

[SSReflect](https://hal.inria.fr/inria-00258384v17) stands for *small scale reflection* proof methodology.
It is an expressive formal proof language based on Coq.
SSReflect uses Gallina and also provides addition tactics, i.e. reasoning steps,
suitable for the long mathematical proofs that SSReflect is intended to help encode.
This extension of Coq has already proved very efficient:
it was used to formally prove the [4-color theorem](https://en.wikipedia.org/wiki/Four_color_theorem)
and the [Feit-Thomspon theorem](https://en.wikipedia.org/wiki/Feit–Thompson_theorem).
The SSReflect additional tactics are few, but they can be combined with additional *tacticals*,
i.e. tactic modifiers, such that one same tactic may cope with a wide range of similar situations.
Also the tactics combine nicely with each other, so that proof scripts may be sometimes as short as the pen-and-paper proofs
that they formally encode.

# Dependencies

Our solution uses the [Mathcomp library](https://github.com/math-comp/math-comp) built upon Coq/SSReflect.
The easiest way is to do it using a source based package manager for OCaml called [OPAM](https://opam.ocaml.org).
Once you have OPAM installed and properly configured execute the following in your terminal:

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```

# About the Proof

We model strings as sequences (`seq`) of elements of some non-empty type `T`.
This condition greatly simplifies the implementation, because Coq is a total language and
we still need to return a value even if e.g. the user asks for an element of a sequence (list) `s` with an index `i`,
which is out of bounds.

Our definition of `leftpad` is a function based on Mathcomp's `ncons` (`:= iter n (cons x)`) function,
which simply prepends an element to the input list certain number of times.

```coq
Definition leftpad (c : T) (n : nat) (s : seq T) : seq T :=
  ncons (n - size s) c s.
```

TODO: mention that `replicate (n - size s) c ++ s` can be less efficient in strict languages that `ncons`.

Note that we utilize the so-called cut-off property of subtraction on natural numbers
(i.e. if `n` is smaller or equal to `size s` subtraction evaluates to `0`)
to make sure we return the original string unmodified if the input length is smaller or equal to the original string's length.

Thanks to an excellent library, the proofs are straightforward and *do not use any automation*.
