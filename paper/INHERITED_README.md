# Holomorphic curves with few inflection points — Lean 4

This is a historical description of the initial Lean 4 formalization of
**Holomorphic curves of finite lower order with few inflection points**.
For the current verified status, see the [repository README](../README.md) and
[result registry](../PAPER_RESULTS.md).

The toolchain was pinned to `leanprover/lean4:v4.34.0-rc1`, with the corresponding
version of mathlib.

The original project could be built in PowerShell with:

```powershell
Set-Location 'E:\Lean 4\FewInflection'
lake build
```

At this checkpoint, `lake build` had completed successfully.

## Formalized content at this checkpoint

`FewInflection/Definitions.lean` and its supporting modules provided:

* Finite-dimensional entire curves, reduced representations, linear
  nondegeneracy, and polynomial representations with an entire factor.
* The Wronskian, defined using `iteratedDeriv` and a matrix determinant.
* Linear independence of the coordinate functions when the Wronskian is nonzero
  at a point, under local differentiability hypotheses.
* The paper's homogeneous-vector Cartan–Nevanlinna characteristic: the circle
  average of `log ‖f‖` minus the normalization term at the origin; also the
  Wronskian counting function, order, and lower order.
* Small ramification, slow variation, and regular variation.
* The monomial-curve Wronskian formula
  $W(1,z,\ldots,z^n)=\prod_{j=0}^n j!$.
* Linear independence and a nonzero Wronskian for monomial curves, together with
  polynomial and rational-normal representations having a differentiable
  nonvanishing factor.
* An explicit invertible diagonal matrix normalizing the Wronskian to the
  constant `1`, with proofs that the normalized curve remains linearly
  nondegenerate and has zero ramification.
* Wronskian identities under constant scalar and constant matrix gauge changes.
* Preservation of a nonzero Wronskian under an invertible constant matrix gauge.
* Identically zero ramification for monomial curves, giving their
  `SmallRamification` property directly from mathlib's `isLittleO_zero`.
* Regular variation of `rpow`, slow variation of constant functions, uniqueness
  of the regular-variation index, and eventual nonnegativity of the growth
  ratio. Under positivity and continuity hypotheses, dividing a regularly
  varying function by `r^ρ` gives a slowly varying factor and the paper's
  eventual identity `T(r)=r^ρ*ℓ(r)`.

Order and lower order take values in `EReal`, so finite lower order means that
the lower order is strictly less than `+∞`. The main target proposition also
requires the same `ρ` to equal both the order and the lower order, specifying
their common value explicitly.

The paper's convention `n ≥ 1` is included in all five target propositions.
`SlowlyVarying` requires positivity, continuity on the positive half-line, and
an ε–R condition uniform over `[1,2]`. `RegularlyVarying` uses an ε–R condition
locally uniform over compact sets of positive scale factors.

`FewInflection/Results.lean` states Lean propositions for the main theorem,
sharpness, the rational-normal conclusion for order below one, the zero-order
ramification estimate, and the radial-area corollary. It proves logical lemmas
extracting conclusions from `MainConclusion` or explicit witnesses. Using
mathlib's filter-limit operations, it also proves the radial implication:
regular variation and convergence of the area-to-characteristic ratio to `ρ`
imply convergence of the area ratio to `c^ρ`.

## Analytic proof boundary at this checkpoint

The paper's main proof requires Nevanlinna theory, Pólya peaks, potential-theory
limits, Karp–Purbhoo universal Plücker coordinates, and asymptotic integration of
linear ordinary differential equations. At this historical checkpoint, the
required versions were not available in the development or its mathlib
dependencies. The project therefore consisted of definitions, checked algebra
and calculus lemmas, and target propositions, with no added mathematical
axioms. Proving those targets still required formalizing the missing theory.

To define `logGrowthRatio` for every curve in the model, the development uses
`log (max (characteristic f r) 1)`. This explicit regularization was introduced
before the full subharmonic growth theory was formalized and adds no analytic
assumption.

The distinction between proved lemmas and target propositions could be audited
with:

```powershell
lake env lean verification/Audit.lean
```

The audit checks the foundational dependencies of the proved lemmas and the
types of the five target propositions. The project contains no user-declared
mathematical axioms or proof placeholders.

The original manuscript source is preserved in `paper/original.tex`.
