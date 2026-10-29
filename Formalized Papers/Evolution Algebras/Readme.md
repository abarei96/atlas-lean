# On Solvable Evolution Algebras and a Conjecture by García-Martínez and Pérez-Rodríguez

A Lean 4 formalization of **[On Solvable Evolution Algebras and a Conjecture by
García-Martínez and Pérez-Rodríguez](Papers/evolution_algebras.pdf)**. This paper was [announced by Meta](https://research.meta.ai/blog/solving-open-research-problems-together) on October 2nd, 2026 along with
five others.

Instead of treating Lean like an oracle to be trusted, this project intends to present a formalization in such a way that it is intuitive and accompanies natural mathematical language natively. Every definition and result in the paper is fully formalized in this repository.

[Paper (PDF)](Papers/evolution_algebras.pdf)
· [Interactive paper (HTML)](Papers/evolution_algebras_interactive.html)

Please download the HTML file and open it in your browser.



## About the paper

An **evolution algebra** over a field $K$ is a (nonassociative) $K$-algebra with a distinguished basis $B$, called a **natural basis**, such that $xy=0$ for distinct $x,y\in B$. An evolution algebra is **solvable** if its derived series terminates at zero. We disprove the conjecture proposed by García-Martínez and Pérez-Rodríguez in *A Note on Complete Evolution Algebras* (2026), which states that a complex evolution algebra is solvable if and only if it has no nonzero idempotent elements. Additionally, for finite-dimensional evolution algebras over an algebraically closed field, we introduce idempotent subspaces to properly characterize solvability as well as the existence of nonzero idempotent elements.

| Result | Lean |
|---|---|
| Disproof of G-M and P-R's conjecture | `conjecture_false` <br> [A_Example_2_1_NonSolvableIdempotentFree](Formalization/Section_2_Counterexample/A_Example_2_1_NonSolvableIdempotentFree.lean#L666) |
| Preliminary algebraic geometry result | `fixedPoint_of_idempotent` <br> [A_FixedPoint](Formalization/Appendix_FixedPoint/A_FixedPoint.lean#L52) |
| Characterization of solvable evolution algebras | `solvable_iff_no_idempotent_subspace` <br> [A_Lemma_3_1_Theorem_3_2_SolvableIff](Formalization/Section_3_SolvableAlgebras/A_Lemma_3_1_Theorem_3_2_SolvableIff.lean#L158) |
| Characterization of the existence of idempotent elements in evolution algebras | `IdempotentIff.idempotent_iff` <br> [B_Theorem_3_3_IdempotentElementsAndSubspaces](Formalization/Section_3_SolvableAlgebras/B_Theorem_3_3_IdempotentElementsAndSubspaces.lean#L146) |

## Why can we trust Lean?

### 1. If I am new to Lean and computer formalization

If you are new to Lean, we recommend starting with Christoph Spiegel’s
[Verification was never just about certification](https://christophspiegel.berlin/appendix/when-to-trust-lean)
as an approachable introduction to what “verified in Lean” does—and does
not—mean. For Lean’s own account of the successive levels of validation,
from an ordinary build to stronger rechecking, see
[Validating a Lean Proof](https://lean-lang.org/doc/reference/4.35.0/ValidatingProofs/).

Lean lets one write definitions, theorem statements, and proofs in a form
whose every deduction can be checked by its kernel. A successful check
proves the statements **as written in Lean**. It cannot decide whether
those statements faithfully capture the mathematics in the paper; judging
that translation remains a human task.

We have audited the translation, and the
[interactive paper](Papers/evolution_algebras_interactive.html)
lets readers compare the paper and Lean statements side by side.
The original standalone formalization was also checked on a clean server; together with the
human audit, this addresses the project-level concerns raised by
Spiegel. The usual residual trust in Lean’s kernel, compiler chain, and
hardware remains.

### 2. If I already have some experience with Lean

This project uses Lean `v4.35.0`. For the full check, run the comparator as instructed in
[Validating a Lean Proof](https://lean-lang.org/doc/reference/4.35.0/ValidatingProofs/#validating-comparator),
using [evolution_algebras_comparator.lean](Comparator/evolution_algebras_comparator.lean) with
[evolution_algebras_comparator.json](Comparator/evolution_algebras_comparator.json), the statements and
configuration of the comparator challenge. Lean and Mathlib
are pinned in [lean-toolchain](../../lean-toolchain) and
[lake-manifest.json](../../lake-manifest.json); to avoid version conflicts, do not run `lake update` first.

Use `Formalization/` as the solution source root and `Comparator/` as the
challenge source root.

## Authorship

The paper was written by Andres Barei with *Muse Spark* via [meta.ai](https://meta.ai), and reviewed by Nicolás Jaramillo Torres.

The formalization was produced and reviewed by Andres Barei, using *Muse Code*.
