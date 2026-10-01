# Historical status

This file preserves an earlier project checkpoint. The current completed status is in [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md), and the manuscript completion gate is [verification/SubmittedCompletion.lean](verification/SubmittedCompletion.lean).


M7 update: standard polytabloids now span the actual Specht module, proved by
Garnir relations and a terminating natural-number weight induction.
Checkpoint `m7-standard-spanning-*`: 4066 jobs; 2554 declarations, 2171 theorems;
192 new / 68 inherited modules; no prohibited source tokens or extra logical
dependencies. Independence and tableau dimension remain pending. M7 remains
active; the main theorem and sharpness are not certified.

M7 update: actual standard-polytabloid basis and exact Specht dimension proved.
The dimension equals the existing actual standard-skew-tableau count for empty
inner shape. The character projection and unit-vector expectation bound now
apply explicitly to the constructed Specht character. Checkpoint
`m7-standard-basis-*`: 4076 jobs, 2596 declarations including 2207 theorems;
201 new / 68 inherited modules; source scan and recursive dependency audit pass.
Branching and the KP correspondence remain open. M7 is still active.

M7 corner-tableau checkpoint: actual deletion/extension equivalence and the
corner-removal dimension recurrence are proved. Evidence:
`m7-corner-tableaux-*`; 4083 jobs; 2684 declarations, 2278 theorems; 208 new
modules. Actual restriction branching and KP correspondence remain pending.

M7 restriction-branching checkpoint: actual equivariant corner deletion,
exact filtration kernels and quotient isomorphisms, trace additivity, and
the full restriction character identity are proved. Evidence:
`m7-specht-branching-*`; 4107 jobs; 2853 declarations, 2415 theorems; 232 new
and 68 inherited modules. Source scan and complete recursive audit pass.
The full KP correspondence and subsequent M7 estimates remain pending.

M7 distinct-Specht checkpoint: finite-alphabet branching, actual KP operator
definitions, and unconditional distinctness/orthogonality of partition-indexed
Specht characters are proved. Evidence: `m7-specht-distinct-*`; 4125 jobs;
2957 declarations, 2509 theorems; 250 new / 68 inherited modules. All audits pass.
The full KP lemma and the remaining M7 estimates are still pending.

M7 Young-lattice dimension checkpoint: actual cover combinatorics, the upward
tableau-dimension recurrence, and the sum of squared actual Specht dimensions = n!
are proved. Evidence: `m7-young-dimensions-*`; 265 new / 68 inherited modules;
4140 jobs, 3136 declarations including 2655 theorems; all audits pass. The full KP
lemma and remaining M7 estimates are pending. The main theorem and sharpness
remain unproved. Declaration counts are not a completion percentage.

M7 Specht completeness checkpoint: regular and universal projector exhaustion,
classification of actual finite-dimensional irreducibles, and class-function
Fourier expansion are proved. Evidence: `m7-specht-completeness-*`; 274 new /
68 inherited modules; 4149 jobs, 3189 declarations including 2703 theorems;
all audits pass. The full KP lemma and remaining M7 estimates are pending;
the main theorem and sharpness remain unproved.

M7 alpha-induction checkpoint: one-letter induction of actual Specht characters
and the corresponding alpha identity inside every finite subset are proved.
Evidence: `m7-alpha-induction-*`; 283 new / 68 inherited modules; 4158 jobs;
3249 declarations including 2758 theorems; all audits pass. The full KP lemma,
main theorem, and sharpness remain unproved.

M7 KP translation checkpoint: actual beta operators satisfy the exact finite
translation formula with standard skew-tableau coefficients, and every center
belongs to the algebra generated at zero. Evidence: `m7-kp-translation-*`;
293 new / 68 inherited modules; 4168 jobs; 3310 declarations including 2814
theorems; all audits pass. Commutativity, Bethe identification, spectral
correspondence, remaining M7 estimates, the main theorem, and sharpness are
still unproved. M7 remains active.

M7 Gaudin checkpoint: simultaneous parameter shifts preserve the generated
algebra, and each actual beta commutes with every rational Gaudin element when
parameters are distinct. Evidence: `m7-gaudin-commutation-*`; 306 new / 68
inherited modules; 4181 jobs; 3385 declarations including 2880 theorems; all
audits pass. This is an intermediate commutation theorem. Unrestricted beta-beta
commutativity, spectral correspondence, remaining M7 estimates, the main theorem,
and sharpness remain unproved.

M7 corner-spectrum checkpoint: exact central-transposition scalars, distinct
corner contents, actual multiplicity-one embeddings, and their direct sum and
bases are proved. General cyclic-centralizer and joint-eigenbasis lemmas are
proved; actual JM/Gaudin cyclicity remains open. Evidence:
`m7-specht-corner-spectrum-*`; 328 new / 68 inherited modules; 4207 jobs;
3501 declarations including 2979 theorems; all audits pass. Full KP, remaining
M7 estimates, the main theorem, and sharpness remain unproved.

M7 actual Jucys--Murphy cyclicity checkpoint: the actual ordered elements,
restriction identities, tableau-indexed simultaneous eigenbasis with distinct
joint values, and a cyclic linear combination on each constructed Specht module
are proved. Evidence: `m7-jucys-murphy-cyclicity-*`; 336 new / 68 inherited
modules; 4215 jobs; 3561 declarations including 3020 theorems; all audits pass.
Gaudin cyclicity, unrestricted beta-beta commutativity, full spectral
correspondence, remaining M7 estimates, the main theorem, and sharpness remain
unproved. M7 remains active.

M7 unrestricted KP commutativity checkpoint: actual cyclic Gaudin degeneration,
polynomial continuation to every parameter (including collisions), faithful
Specht-family action, beta-beta commutativity, and commutativity of the generated
algebra are proved. Evidence: `m7-kp-commutativity-*`; 351 new / 68 inherited
modules; 4230 jobs; 3633 declarations including 3082 theorems; all gates pass.
Traditional Bethe identification, full spectral correspondence, remaining M7
estimates, the main theorem, and sharpness remain unproved. M7 remains active.

M7 spectral-support checkpoint: the actual alpha operators are positive in every
finite-dimensional unitary representation. Their actions, and hence beta actions,
vanish outside the Specht shape. Every actual Specht module has a nonzero KP joint
eigenspace; its eigenvalues have the exact top normalization, support, translation,
and monic Wronskian polynomial identity. Its scalar action defines a character of
the whole generated algebra. Evidence: `m7-kp-spectral-support-*`; 364 new / 68
inherited modules; 4330 jobs; 3689 declarations including 3133 theorems. The source
scan and recursive dependency audit pass with only the three permitted foundations.
Plucker decomposability, full fibre correspondence, traditional Bethe identification,
remaining M7 estimates, the main theorem, and sharpness remain unproved. M7 is active.

M7 cyclic-algebra checkpoint: the actual two-box column alpha is 1 minus the
transposition. Evaluating its beta at a prescribed root proves every Gaudin
element belongs to the generated algebra for distinct parameters. Along the
actual JM deformation, the Specht image is the full centralizer of an actual
cyclic element and has dimension equal to the standard-tableau count. For all
real parameter tuples, including collisions, the actual beta family is symmetric
and its joint eigenspaces form an internal direct sum. Evidence:
`m7-kp-cyclic-algebra-*`; 377 new / 68 inherited modules; 4351 jobs;
3735 declarations including 3175 theorems. All gates pass. Plucker relations,
full spectral correspondence, Bethe identification, remaining M7 estimates,
the main theorem, and sharpness remain unproved. M7 remains active.

M7 finite symmetric identities checkpoint: the actual scaled monomial polynomial
satisfies the signed complete-cycle power-sum identity and the one-variable
alphabet-addition identity. The Laurent realization of the adjoint Bernstein
operator satisfies the exact power-sum factor identity and its action on scaled
monomials. Its value on 1 has zero residue. Evidence:
`m7-finite-symmetric-identities-*`; 390 new / 68 inherited modules; 4364 jobs;
3808 declarations including 3228 theorems. Build, source scan, and the recursive
audit pass with only Classical.choice, propext, and Quot.sound. The general
composition residue identity, character-to-Schur bridge, KP Plucker relations,
full correspondence, remaining M7 estimates, main theorem, and sharpness remain
unproved. M7 remains active; counts do not measure manuscript completion.

M7 composition-residue checkpoint: `finiteBernstein_bounded_composition_residue`
proves the exact finite-alphabet bounded-composition identity of KP source
Lemma 2.25, with exponent |kappa|-|ell|-card A and parts indexed by Fin(ell_a)+1.
The proof constructs the formal derivative, proves Leibniz and a polynomial
change-of-variable residue identity, identifies squarefree marker coefficients
with actual injective colorings, and uses a proved finite geometric identity.
Evidence: `m7-composition-residue-*`; 417 new / 68 inherited modules; 4391 jobs;
3965 declarations including 3356 theorems. All gates pass; the recursive audit
reports only Classical.choice, propext, and Quot.sound. The character-to-Schur
bridge, actual KP Plucker relations and fibre correspondence, remaining M7
estimates, main theorem, and sharpness remain unproved. M7 remains active.

M7 factored-composition checkpoint: the Bernstein operator is extended to actual
Laurent polynomials, the literal finite composition series has zero Bernstein
residue, and every finite product of the power-sum factors is removed by a
proved ring identity. `finiteBernstein_factored_composition_residue` discharges
the symmetric-function residue required once the source's permutation expansion
is identified. Evidence: `m7-factored-composition-*`; 423 new / 68 inherited
modules; 4397 jobs; 3991 declarations including 3378 theorems. All gates pass.
The permutation expansion, character-to-Schur bridge, actual KP Plucker relations,
full correspondence, remaining M7 estimates, main theorem, and sharpness remain
unproved. M7 stays active.

M7 actual Z-factorization checkpoint: the first-return strips are constructed,
proved disjoint, and their complement is invariant. Admissible right supports
are classified exactly by nonempty strip prefixes and invariant complement
subsets. `exists_rightZFactor_iff` proves necessity and sufficiency;
`rightZFactorEquiv` constructs the actual bijection between permutations of the
strip starts and all right factors with a fixed admissible support. The actual
right permutation is conjugate, on its support, to the sum of the constructed
block inflation and the complement restriction. Its sign and fixed-coloring
cycle-power sum are computed. `rightZFactor_signed_coloring_sum` proves the
complete signed sum for one support, with the scaled monomial strip factor.
Evidence: `m7-z-factorization-*`; 457 new / 68 inherited modules; 4431 jobs;
4306 declarations including 3653 theorems. All gates pass with only
Classical.choice, propext, and Quot.sound. The remaining complement-cycle
product, support summation and identification of the actual KP coefficient are
not yet proved. The character/Schur bridge, KP Plucker relations, full fibre
correspondence, remaining M7 estimates, main theorem and sharpness remain
unproved. M7 stays active; these counts are not a completion percentage.

M7 actual right-factor residue checkpoint: the complement is decomposed into
actual permutation cycles, including singletons. Their restriction signs and
power sums are proved, and summing all invariant cycle subsets gives the literal
Laurent product. The complete actual right-factor sum is reindexed using the
proved support bijection and normalized with the exact support cardinalities.
`rightZFactorLaurentSeries_factorized` identifies it with the finite composition
series times the complement-cycle product; `rightZFactorLaurentSeries_residue`
proves its finite Bernstein residue is zero. All permutations and supports in
this statement are actual finite data, with no classification assumption.
Evidence: `m7-right-factor-residue-*`; 477 new / 68 inherited modules; 4451 jobs;
4392 declarations including 3724 theorems. The build, source scan, and recursive
dependency audit pass with only Classical.choice, propext, and Quot.sound.
The actual KP group-algebra/marker coefficient bridge, character-to-Schur bridge,
KP Plucker relations and full fibre correspondence, remaining M7 estimates,
main theorem and sharpness remain unproved. M7 remains active. Module and
declaration counts are audit coverage, not a percentage of paper completion.

M7 literal supported-quadratic residue checkpoint: the full supported
factorization data are proved equivalent to the actual right-factor data.
`supportedPowerSumQuadratic_eq_product` proves the literal product expansion in
KP equation (4.3). Squarefree marker coefficients are identified with the full
factorization Laurent series. For general coefficients, their exponents encode
the actual union and intersection of supports. Restricting to the union is an
explicit bijection preserving signs, support cardinalities and cycle power sums.
`supportedPowerSumQuadratic_residue` proves zero finite Bernstein residue for
every permutation coefficient and every marker exponent, including squared
markers. `kpBeta_column_supported` identifies the actual existing KP column
operator with its signed supported-permutation expansion.
Evidence: `m7-supported-quadratic-residue-*`; 494 new / 68 inherited modules;
4468 jobs; 4529 declarations including 3840 theorems. All gates pass, with only
Classical.choice, propext and Quot.sound. The character-to-Schur and Plucker
bridges, full KP fibre correspondence, remaining M7 estimates, main theorem and
sharpness remain unproved. M7 stays active; counts are not completion percentages.

M7 evaluated Frobenius checkpoint: the actual Laurent column series has
coefficient (-1)^k times the existing `kpBeta (columnPartition k) z 0`.
Conjugacy-invariant functions are expanded in the actual constructed Specht
characters using Schur's lemma, natural central operators, regular-representation
coefficients, and the already proved Specht completeness. The resulting finite
Frobenius character transforms are independent of alphabet labeling. The right
supported power-sum series is identified exactly with the bounded sum of the
actual `kpBeta` coefficients times these transforms, by
`evaluatedPowerSumSeries_frobenius`. General marker evaluation commutes with the
zero-residue conclusion; `supportedPowerSumProduct_evaluated_residue` proves the
literal product identity for arbitrary complex parameters, including collisions.
Evidence: `m7-evaluated-frobenius-*`; 516 new / 68 inherited modules; 4490 jobs;
4614 declarations including 3913 theorems. Build, both-library source scan and
recursive dependency audit pass with only Classical.choice, propext, Quot.sound.
The character transforms have NOT yet been identified with determinantal Schur
polynomials. That identification, the Bernstein/single-column Plucker equivalence,
actual KP Plucker relations, full fibre correspondence, remaining M7 estimates,
main theorem and sharpness remain unproved. M7 remains active. Counts measure
audit coverage and are not a completion percentage.
