# Paper formalization instructions

The specification is `paper/submitted.tex`, the user's manuscript
“Holomorphic curves of finite lower order with few inflection points”.
Preserve this source. Historical manuscripts and inherited status documents do
not certify the submitted version.

## Zero external mathematical assumptions

- Never introduce `axiom`, `sorry`, or `admit` in project Lean source.
- Every mathematical result must be proved in this repository or in the pinned
  Lean/mathlib dependencies. A citation to a paper or book supplies no proof.
- Do not create an External/Axioms layer. Do not replace an unproved result by a
  stronger assumption, a conditional interface, or an unspecified example.
- Prefer the exact specialized result needed by the manuscript. Record any
  alternative proof in `FORMALIZATION_MAP.md`.
- Inspect source or use `#check` / `#print` before using a mathlib declaration.
  Do not guess API names.
- Give each paper lemma, proposition, and theorem a stable Lean name and include
  its LaTeX label in a comment. Use `PAPER_RESULTS.md` as the name registry.
- Split long proofs into independently compiling lemmas.

## Milestone gates

Work in the user's dependency order:

Definitions → elementary complex analysis → Wronskian/fundamental operator →
potential theory/local convergence → logarithmic derivative limit → subharmonic
compactness → polynomial/Wronskian minor estimates → local compactness → rescaled
representation → Pólya peaks/growth indices → small-order classification →
arbitrary-radius limits → finite-gradient convexity → homogeneity → regular
variation → main theorem → sharpness.

At the beginning of each milestone inspect existing support, list exact theorem
signatures, and draw its dependency DAG. Prove the lowest missing dependencies
first. Do not advance until the current milestone is complete and its checks pass.
Inherited proofs from later stages are reusable but do not certify those stages.

After each integrated change run `lake build` and `scripts/verify.ps1`. Only
successfully checked proofs belong in `ModifiedCartan/`. Keep experiments in
`work/`; failed experiments are not certificates.

The verification script scans both project libraries for forbidden placeholders
and traverses all imported project declarations, including private declarations.
For major results also run `#print axioms`. Only `Classical.choice`, `propext`, and
`Quot.sound` are allowed. No project-specific or literature-specific dependency is
acceptable. Keep the build and audit logs.

## Reporting

Update `FORMALIZATION_MAP.md`, `FORMALIZATION_STATUS.md`, and `PAPER_RESULTS.md`
honestly. A definition of a proposition is not a theorem. Declaration counts are
not a percentage of paper completion. Do not claim the main theorem or sharpness
until their exact submitted statements have kernel-checked proofs.
