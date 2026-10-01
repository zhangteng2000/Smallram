# Current formalization status

The submitted paper is fully formalized: all 35 labelled results have checked theorem declarations. The exact scalar theorem, main curve theorem, and both sharpness results are proved. Final mathematical gate: `m18-complete-scalar-theorem-a` (5332 build jobs; 9026 declarations, including 7863 theorem declarations). The submitted-result check is `verification/SubmittedCompletion.lean`. Historical checkpoint notes below describe progress at their recorded stages and are superseded by this status.

The previous project's cumulative status is preserved in
`paper/INHERITED_STATUS.md`; it is historical, not a completion certificate.
Current milestone gates and specification differences are recorded in
`FORMALIZATION_MAP.md`. The complete manuscript result inventory is in
`PAPER_RESULTS.md`.

M0 (reuse, build repair, dependency audit), M1 (exact definitions and norm bridge),
and M2 (elementary Jensen/counting identities) have passed their gates.

M3 has passed. The submitted `lem:fundamental-operator` and
`lem:canonical-gauge` are now proved in full, including global meromorphic
coefficients, branch identification, representation invariance, and dilation.
The Wronskian nontriviality criterion needed to apply them to all linearly
nondegenerate curves is also proved. M4 (potential theory and local convergence)
has passed its gate. M5 (logarithmic derivative limits) has also passed.
M6 (Wronskian lower bounds and subharmonic compactness) has passed its gate.
M7 (polynomial and Wronskian minor estimates) has passed its full gate.
M8 (local compactness) has passed its full gate: `Paper.prop_localcompact`
includes simultaneous relative compactness, holomorphic limits with a common
bound, the zero first canonical coefficient, and the full gauge comparison.
M9 has passed its full gate: `Paper.prop_representation` and `Paper.lem_replacement` are certified in full. M10 (Polya peaks and growth indices) has passed its full gate: `Paper.lem_peaks`, `Paper.lem_power_bounds`, and `Paper.prop_indices` are certified. M11 has passed its full gate: `Paper.prop_small_order`, `Paper.prop_zero_order_ramification`, and `Paper.cor_zero_ratio`, together with their exact analytic dependencies, are certified. M12 (arbitrary-radius limits and basis at a point) has passed its full gate. M13 (finite-gradient convexity) has passed its full gate: `Paper.lem_finite_gradient_convex` is certified. M14 (homogeneity) has passed its full gate: `Paper.prop_homogeneity` is certified. M15 (regular variation) has passed its full gate: `Paper.prop_regular_variation` is certified. M16 (main theorem) has passed its full gate: `Paper.thm_main` and its explicit slowly varying factor are certified. M17 (sharpness) has passed its full gate: both exact sharpness propositions are certified. The exact `lem:NH` is also certified by gate `m18-complete-nevanlinna-hiong`. The full introductory scalar `thm:A` is certified as `Paper.thm_A`, including both conclusions (a) and (b); `Paper.thm_A_deficiency_sum` proves the deficiency sum is two. All M0–M18 mathematical milestones are complete.

The checked part of M4 now includes:

- Local Lp and local measure convergence, convergence against compactly supported
  tests, and a single almost-everywhere subsequence on an open domain.
- Cauchy kernels in local Lp for 0 < p < 2 and the exact planar singular integral.
- Finite weighted sums of truncated Cauchy kernels and their uniform vanishing
  error when total coefficient masses are uniformly bounded.
- The corresponding estimate for arbitrary finite measures, including joint
  integrability, almost-everywhere slice integrability, and a uniform vanishing
  error controlled by total measure mass.
- A continuous Cauchy-kernel regularization with a quantitative error estimate,
  almost-everywhere integrability of the full transform, and local Lp membership
  for arbitrary finite measures when 1 ≤ p < 2.
- Weak convergence of finite measures implies local Lp convergence of their
  Cauchy transforms for 1 ≤ p < 2, without an atomicity assumption.
- Capped logarithmic potentials are locally L1; their lower regularization
  error is at most total mass times 2πR.
- Weak convergence with common compact support implies local L1 convergence of
  full logarithmic potentials; support of the limit is proved from Portmanteau.
- Both coordinate weak derivatives of the logarithmic kernel, at every center, are
  identified by integration against compactly supported C1 tests.
- The same weak derivative identities for logarithmic potentials, proved using
  joint integrability and Fubini for arbitrary compactly supported finite measures.
- Full logarithmic potentials in every finite positive local Lp space.
- Literal weak-gradient and local Sobolev definitions; logarithmic potentials in
  local W1p for 1 ≤ p < 2, and closure of weak gradients under local L1 limits.
- The distributional Laplacian of a logarithmic kernel is 2π times its point
  mass; that of a compactly supported finite-measure potential is 2π times the
  source measure, proved by polar integration and Fubini.
- Local integration by parts for C2 functions, zero weak Laplacian for
  harmonic functions, and convergence of Laplacian tests under local L1 limits.
- The actual finite zero-counting measure on a disk, its distributional
  Laplacian identity, and an almost-everywhere logarithmic-potential plus
  harmonic decomposition. Finiteness and finite local orders follow from
  analyticity near the closed disk and a nonzero value in its interior.
- Smooth disk cutoffs and localized normalized zero-counting measures;
  their total masses converge, and are uniformly bounded, under local L1
  convergence of normalized log moduli (for nonnegative normalizers).
- A weakly convergent subsequence of these actual measures, including the
  zero-mass case; the same subsequence gives convergence of logarithmic
  potentials and Cauchy transforms in the previously established local norms.
- The normalized log modulus equals the actual localized potential plus a
  classically harmonic remainder wherever the cutoff is one; proved directly
  by a finite weighted log-kernel correction.
- The harmonic radial weighted mean formula, a smooth nonnegative radial
  kernel of integral one, and the resulting harmonic convolution identity.
- Uniform convergence of smooth convolutions and their first two total
  derivatives under global L1 convergence, and pointwise Laplacian convergence.
- Closure of local Lp convergence under subsequences, differences (p ≥ 1),
  and almost-everywhere changes of representative.
- Local L1 limits of harmonic functions have harmonic representatives on
  smaller disks; functions and their first two total derivatives converge
  uniformly there.
- The normalized log-modulus limit is almost everywhere a compactly supported
  finite-measure logarithmic potential plus a smooth harmonic function on each
  smaller disk. The measure, cutoff, and harmonic representative are constructed.
- Classical C1 weak gradients, addition of weak gradients and Sobolev functions,
  and invariance under almost-everywhere changes of representative.
- Uniqueness of weak gradients on open sets, finite smooth decompositions of
  compact tests, and gluing of local weak gradients on countable open covers.
- Uniform harmonic convergence of every iterated total derivative on smaller
  disks, proved by induction through convolution and currying isometries.
- The limit belongs to W1p locally on the whole open connected domain for
  1 ≤ p < 2, with one weak gradient valid for all these exponents. Positivity
  on a tail and nontriviality on inner disks are derived from the original
  hypotheses, without adding assumptions to this regularity result.
- Uniform convergence implies compact Lp norm convergence; a proved
  subsequence criterion can promote a common subsequential limit to
  whole-sequence local Lp convergence.
- The weak complex gradient of the analytic log modulus is exactly h'/h,
  including across its zeros in the distributional sense, on any open
  connected domain. Compact finite covers also glue local Lp convergence.
- Logarithmic kernels and analytic log moduli in local Lp for every finite
  positive exponent; analytic logarithmic derivatives in local Lp for 0 < p < 2.

M5 is complete. `Paper.lem_logderivlimit` proves Sobolev regularity, first
derivative local Lp convergence for every 1 ≤ p < 2, and every positive-order
ordinary derivative quotient limit locally in measure, with the same weak
gradient. It uses the manuscript's holomorphic hypotheses, actual normalized
log-modulus convergence, nontrivial functions, and s → infinity. No extra
growth, regularity, convergence, or literature hypothesis is assumed.
The real L1 representative formulation is stronger: subharmonicity is not
needed as an input. The exact proof variations are in `FORMALIZATION_MAP.md`.

Verified M5 checkpoint: 3792 build jobs, empty source scan, and 1518
declarations / 1316 theorem declarations checked. The counts include inherited,
private, and generated declarations. The only logical dependencies were
`Classical.choice`, `propext`, and `Quot.sound`.

At the completed M5 checkpoint, all 68 inherited source modules and all 68 new
source modules were imported by the audited entry points. That checkpoint is retained in
`verification/logs/m5-complete-*`. The completed M4 checkpoint is retained in
`verification/logs/m4-complete-*`; the completed M3 checkpoint remains separately
available as `verification/logs/m3-complete-*`.

M6 has now proved `Paper.lem_sum` and `Paper.eq_sandwich`. The extended logarithm
retains negative infinity at zero, and the convergence hypotheses imply the
needed nontriviality on a positive tail. Finite determinant convergence and
the scaled positive-log limit are proved from M5. The subharmonic foundation
now derives finiteness almost everywhere and local integrability on connected
domains from the disk submean definition.
`Paper.lem_subharmonic_compactness_upper_bound` proves the compact-set limsup
conclusion. Subharmonic representatives are pointwise unique from AE equality.
The full subsequence dichotomy `Paper.lem_subharmonic_compactness` is proved.
Its reduction `subharmonic_collapse_or_l1_bounded_subsequence` proves that
failure of local uniform divergence to negative infinity gives a strict
subsequence with derived source finiteness and uniform L1 bounds on every
compact subset. Uniform local L1 approximation by twice-averaged truncations
on disks is now proved, as is fixed-radius compactness of the smoothed family.
Uniform approximation yields compactness of the original functions in L1
on disks. Countable product compactness selects one subsequence, and local
limits glue on the domain. The infimum of admissible disk means constructs
the upper semicontinuous subharmonic representative; Lebesgue differentiation
identifies it almost everywhere with the L1 limit. Every part is proved from
the stated submean definition and checked mathlib results.

Verified M6 checkpoint: 3843 build jobs, an empty source scan, and 1756
declarations / 1533 theorem declarations checked, including private and
generated declarations. Only `Classical.choice`, `propext`, and `Quot.sound`
occur. All 111 new modules and 68 inherited modules are included. The frozen
evidence is in `verification/logs/m6-complete-*`.

M7 has proved the polynomial-minor derivative identity and its iteration as
a finite sum over legal single-box growth paths. Partitions are actual mathlib
Young diagrams; standard skew tableaux are actual bijective fillings, with
their equivalence to row-and-column increase proved. The empty skew shape has
count one. Subpartitions of a fixed diagram form a finite type, and the
partition size and row-length identities are proved. A tableau determines
successive intermediate Young diagrams differing by one box. Conversely,
each growth path produces a standard skew tableau by insertion times.

The completed M7 foundation checkpoint covers 122 new and 68 inherited
modules: 3855 build jobs, 1972 audited declarations including 1701 theorems,
an empty source scan, and only the three permitted foundational dependencies.
Logs are frozen under `verification/logs/m7-minor-foundation-*`. This is a
partial checkpoint, not the M7 gate. The tableau/path counting equivalence,
full translation formula, Specht and spectral correspondence, universal
minor estimates, and initial-basis bounds remain pending.

The later M7 translation checkpoint supersedes the pending translation items
in the foundation checkpoint above. `Paper.lem_plucker_translation` is now
proved for the actual Schubert cell of polynomial subspaces, with exact
normalization and basis independence. Derivative-path multiplicities equal
the actual standard skew-tableau counts. Minor support, the sharp degree
upper bound, nonzero constant top coordinate, positivity of tableau counts,
and the exact Wronskian degree are all proved. The proof uses determinant
differentiation and finite Taylor expansion.

This checkpoint contains 144 new modules and 68 inherited modules: 3877 build
jobs, 2207 recursively audited declarations including 1886 theorems, an empty
source scan, and only the three permitted foundational dependencies. Frozen
logs: `verification/logs/m7-plucker-translation-*`. M7 remains active: the
character projection, Specht construction, full Karp--Purbhoo correspondence,
universal minor expansion, and initial-basis estimates remain unproved.

The universal main theorem and sharpness results remain unproved. The number of
helper theorems is not a measure of the percentage of the manuscript completed.




The later M7 character checkpoint supersedes the pending character projection
item above. `Paper.lem_character_projection` and the unit-vector factorial
coefficient bound are proved for any actual irreducible representation of the
symmetric group. The isotypic subspace is the sum of invariant isomorphic copies.
The partition-indexed Specht construction, tableau dimension and branching
formulas, full Karp--Purbhoo correspondence, universal minor expansion, and
initial-basis estimates remain open. No later milestone has been started.

Character checkpoint: 157 new and 68 inherited modules; 4031 build jobs;
2279 recursively audited declarations, including 1948 theorems. Source scan
empty; only Classical.choice, propext, and Quot.sound. Frozen evidence:
`verification/logs/m7-character-projection-*`. The universal main theorem
and sharpness are still unproved.

The later M7 Specht construction checkpoint supersedes the pending Specht
construction and irreducibility item above. Actual complex Specht modules on
the numbered symmetric groups are constructed and proved irreducible and
unitary, including the empty shape. The standard-tableau basis and dimension
formula, branching, full Karp--Purbhoo correspondence, universal minor formula,
and initial-basis estimates remain open. M7 is still active.

Specht construction checkpoint: 175 new and 68 inherited modules; 4049 build
jobs; 2414 declarations, including 2055 theorems, recursively audited. Source
scan empty; only Classical.choice, propext, and Quot.sound. Frozen evidence:
`verification/logs/m7-specht-construction-*`. The main theorem and sharpness
remain unproved.

The subsequent M7 column-spanning checkpoint identifies the standard Young
and empty-inner-shape standard skew-tableau counts and proves that actual
column-standard polytabloids span the constructed Specht module. Full standard
basis, dimension, branching, and the other open M7 results are still pending.
Evidence: `verification/logs/m7-column-spanning-*`; 180 new and 68 inherited
modules; 4054 build jobs; 2459 declarations, including 2087 theorems; empty
source scan and only the three permitted foundational dependencies.

Subsequent M7 checkpoints certify standard-polytabloid spanning, the actual
standard basis and tableau dimension, corner-tableau deletion/extension,
and now the full restriction branching character identity. The branching
proof uses actual equivariant corner-deletion maps and actual invariant
filtration quotients. It assumes neither a branching rule nor an unspecified
representation. Latest frozen checkpoint: `m7-specht-branching-*`, 232 new
and 68 inherited modules; 4107 jobs; 2853 declarations including 2415 theorems;
empty source scan and only Classical.choice, propext, and Quot.sound.
These results supersede the corresponding pending items above. The full KP
correspondence, universal minor representation, and polynomial/initial-value
estimates remain pending. M7 is active; no later milestone is certified.

The `m7-specht-distinct-*` checkpoint additionally certifies branching on any
finite alphabet, actual KP group-algebra definitions and their elementary
empty/oversized cases, and distinctness and orthogonality of the actual
partition-indexed Specht characters. The smaller-size separation premise in
the induction helpers is fully discharged by the final strong-induction
theorem. Evidence: 250 new / 68 inherited modules; 4125 jobs; 2957 declarations,
including 2509 theorems; empty source scan and only the three permitted
foundational dependencies. This does not yet certify the full KP lemma or M7.

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

M7 finite Frobenius and triangularity checkpoint: weighted Burnside is proved
for actual finite colorings, whose permutation orbits are explicitly equivalent
to multisets. This gives the finite cycle index and, using the proved Specht
Fourier kernel, `finiteFrobeniusPolynomial_cauchy`. Each monomial coefficient of
a Frobenius polynomial equals the dimension of the actual intertwining-map
space between the Specht module and the weight-coloring representation
(`finiteFrobeniusPolynomial_coeff_finrank_young`); it is a nonnegative integer.
Column-sign cancellation proves exact vanishing below the row weight, and at
the minimum weight for all other row multiplicities
(`finiteFrobeniusPolynomial_coeff_zero_of_weight_le_ne`). Symmetry and
homogeneity are proved directly. These are auxiliary results for submitted
`lem:KP-correspondence`, specifically the character/Schur identification in
KP (2.15). This constructive Burnside and representation proof is the recorded
alternative to importing the symmetric-function character formula.
Evidence: `m7-finite-frobenius-cauchy-*` at 530 new modules / 4504 jobs /
4684 declarations / 3973 theorems; `m7-frobenius-triangularity-*` at
542 new / 68 inherited modules, 4527 jobs, 4733 declarations including
4017 theorems. Both gates pass: build, both-library source scan, and recursive
dependency audit (including generated/private declarations). Only
Classical.choice, propext, and Quot.sound occur as logical dependencies.
The character transform is not yet identified with the Schur determinant.
That identification, the Bernstein/Plucker equivalence, full KP fibre
correspondence, remaining M7 estimates, main theorem, and sharpness remain
unproved. M7 remains active; counts describe audit coverage, not completion.

M7 finite alternant checkpoint: the first-pivot elimination formula and the
finite Cauchy determinant are proved directly, including the empty matrix.
The formula requires no distinctness of variables. Strict rearrangement gives
the exact staircase-weight inequality. The actual finite alternant is proved
equal to its determinant, and its ordered exponent coefficients are Kronecker
deltas. `finiteVandermondeFrobenius_coeff_zero_of_le_ne` proves the required
triangular vanishing after multiplying a Frobenius polynomial by the staircase
alternant; its diagonal coefficients are nonnegative integers. These results
are auxiliary to `lem:KP-correspondence`. The algebraic Cauchy and rearrangement
proofs are the recorded alternative path to KP's Schur-character formula.
Evidence: `m7-finite-alternant-triangularity-*`; 550 new / 68 inherited modules;
4535 jobs; 4822 declarations including 4094 theorems. The complete build,
both-library source scan, and recursive audit pass, with only Classical.choice,
propext, and Quot.sound. Formal-series coefficient extraction and the orthogonal
coefficient-matrix argument are still needed for the Schur identification.
M7 remains active. No KP fibre correspondence, main theorem, or full sharpness
statement is claimed; counts describe verification coverage, not completion.

M7 formal Cauchy kernel checkpoint: univariate series are embedded in separate
variables and their finite-product coefficients are proved exactly. The finite
Cauchy determinant is transferred to actual inverses in a domain and then to
formal power series; `finiteCauchySeriesMatrix_coeff_det` computes its
coefficients as polynomial determinants. Geometric product coefficients are
identified with finite multiset sums. A proved ring homomorphism records total
degree while retaining every polynomial monomial. This connects the formal
kernel with the existing finite Frobenius Cauchy sum, including empty alphabets.
`finiteFrobeniusPolynomial_cauchy_separated` is the exact character identity
with one alphabet in the coefficient ring. Homogeneous multiplication and
alternant-degree lemmas are also checked. These are auxiliary to submitted
`lem:KP-correspondence`. The formal coefficient proof uses no analytic
convergence assumptions and no cited symmetric-function identity.
Evidence: `m7-formal-cauchy-kernel-*`; 562 new / 68 inherited modules, 4566 jobs,
4898 declarations including 4159 theorems. Build, source scan and recursive
logical-dependency audit pass, allowing only Classical.choice, propext,
Quot.sound. The final orthogonality and Schur identification remain pending,
as do the Bernstein/Plucker equivalence, full KP fibre correspondence, remaining
M7 estimates, main theorem and sharpness. M7 stays active. Counts are not a
completion percentage.

M7 finite Frobenius--Schur checkpoint (supersedes the earlier pending status):
`finiteFrobeniusPolynomial_mul_alternant` and
`finiteFrobeniusPolynomial_schur_determinant` prove the exact finite determinantal
formula for the actual Specht character transform whenever the partition height
is at most the alphabet size. No bound by the partition's total size is imposed.
The first-column collision argument proves zero outside that height range. The
Cauchy kernel expansion gives an orthogonal coefficient matrix; weighted
triangularity and its natural-number diagonal force that matrix to be the
identity, including small and empty alphabets. This is a fully proved alternative
to importing the symmetric-function Frobenius character formula (KP (2.15)); it
is auxiliary to submitted `lem:KP-correspondence`.
Evidence: `verification/logs/m7-finite-frobenius-schur-*`; 572 new and 68 inherited
modules, 4576 build jobs, 4939 audited declarations including 4196 theorems.
The build, both-library forbidden-token scan, and recursive dependency audit
all pass. Only Classical.choice, propext, and Quot.sound occur.
The Bernstein/single-column relation, passage to all Plucker relations, actual
polynomial-space reconstruction, full KP fibre correspondence, remaining M7
estimates, main theorem, and full sharpness statement remain unproved. M7 stays
active; the counts record audit coverage, not a completion percentage.

M7 finite Bernstein checkpoint: the finite alphabet equivalence, descending
Vandermonde product, and substitution of t^{-1} for the first variable are proved.
`finiteBernstein_residue_mul_vandermonde` identifies the literal Laurent residue
with the exact first-variable coefficient of the alternating polynomial.
`finiteFrobeniusBernsteinResidue_mul_vandermonde` applies this to the actual
Frobenius polynomials using the proved Schur determinant formula. Both full KP
factors are identified, and `kpFrobeniusBernstein_residue` proves their quadratic
residue identity for all complex parameter tuples, including collisions. These
are auxiliary results for submitted `lem:KP-correspondence`. The finite
Vandermonde calculation replaces the infinite symmetric-function Bernstein
calculus of KP Lemma 2.20; no cited formula is used as an assumption.
Evidence: `verification/logs/m7-finite-bernstein-coefficients-*`; 581 new and 68
inherited modules, 4585 build jobs, 4974 declarations including 4228 theorems.
Full build, both-library source scan, and recursive dependency audit pass with
only Classical.choice, propext, and Quot.sound. Passage to the scalar joint
characters, the alternating contraction, translation to the differential
kernel, decomposability, full KP correspondence, and the remaining M7 estimates
are still pending. The main theorem and full sharpness remain unproved. M7 is
active; counts describe audit coverage, not completion.

M7 joint-contraction checkpoint: finite group coefficient relations are
transported through a proved linear extension of the actual joint algebra
character. `kpJointFrobeniusBernstein_residue` and `kpJointAlternant_contraction`
prove the scalar residue and alternating single-column contraction for every
actual nonzero joint eigenspace, allowing repeated parameters. They do not yet
assert decomposability or polynomial-space existence.
`polynomialDifferential_subspace_finrank_le` proves the required bound for a
finite-dimensional polynomial solution space of an order-n differential
operator whose leading coefficient is nonzero. The alternative proof reuses
M2's proved analytic Wronskian criterion, transfers polynomial independence to
entire functions, and applies matrix nondegeneracy over the polynomial domain.
Thus no ODE existence theorem or literature-specific assumption is introduced.
All these results are auxiliary to submitted `lem:KP-correspondence`.
Evidence: `verification/logs/m7-joint-contraction-kernel-bound-*`; 586 new and 68
inherited modules, 4590 build jobs, 4992 audited declarations including 4244
theorems. Build, both-library source scan, and recursive audit pass with only
Classical.choice, propext, and Quot.sound. Next dependencies are factorial
normalization of the alternating coefficients, all-center translation,
annihilation by the actual differential operator, and polynomial-space
reconstruction. The full KP correspondence, remaining M7 estimates, main
theorem and full sharpness remain unproved. M7 stays active; counts are not a
completion percentage.

M7 divided-power normalization checkpoint: the actual alternating polynomial is
proved nonzero and satisfies the single-column contraction. The divided-power
polynomial basis has Kronecker-delta jets at zero; its partition derivative
minors have exactly the tableau and factorial translation coefficients.
`mvDividedPowerNormalize_first_coeff` proves the factorial conversion between
raw first-variable coefficients and divided-power coefficients. These are
auxiliary to submitted `lem:KP-correspondence`; polynomial-space reconstruction
is not yet claimed.
Evidence: `verification/logs/m7-divided-power-normalization-*`; 592 new and 68
inherited modules, 4596 build jobs, 5029 audited declarations including 4276
theorems. Full build, both-library source scan, and recursive dependency audit
pass with only Classical.choice, propext, and Quot.sound. Next are translation of
the divided alternating polynomial, annihilation by the actual differential
operator, and decomposability. Full KP correspondence, the remaining M7
estimates, main theorem, and full sharpness remain unproved. M7 stays active;
counts measure audit coverage, not paper completion.

M7 divided-alternant contraction checkpoint: `finiteDividedAlternant_eq_det`
identifies the normalized alternant with the determinant of actual divided
monomials. `kpJointDividedPolynomial_first_contraction` gives the exact
factorial-weighted single-column equation for every actual nonzero joint
eigenspace. Its alternating polynomial remains nonzero after normalization.
Evidence: `verification/logs/m7-divided-alternant-contraction-*`; 594 new and 68
inherited modules, 4598 build jobs, 5039 audited declarations including 4284
theorems. Build, both-library source scan, and recursive dependency audit all
pass with only Classical.choice, propext, and Quot.sound.
Next dependency sub-DAG: ordered exponent/partition parametrization ->
coefficients of polynomial determinants -> determinant translation in the
divided-alternant basis -> translated KP contraction -> polynomial differential
kernel -> reconstruction of a polynomial space. Exact intermediate targets:
`exists_partitionAlternantExponent` for every StrictAnti exponent vector;
`polynomialAlternant_coeff` identifies each multivariate coefficient with the
determinant of univariate coefficients; translated divided alternants have
coefficient f^{nu/mu} t^{|nu|-|mu|}/(|nu|-|mu|)! in the divided-alternant basis.
Inspected pinned mathlib support: Finset.orderIsoOfFin, YoungDiagram.ofRowLens,
List.sortedGE_ofFn_iff, Fin.antitone_iff_succ_le, Matrix determinant permutation
formulas, and Polynomial.taylor. Existing repository single-variable formal
series coefficients provide independent-variable product coefficient extraction.
These targets are not assumptions and do not yet certify the translation or
reconstruction. Full KP correspondence, remaining M7 estimates, main theorem,
and full sharpness remain unproved. M7 stays active.

M7 all-center translation checkpoint: `finiteDividedAlternant_translation`
proves the literal simultaneous-variable translation formula in the divided
alternating basis. `finitePartitionDividedPolynomial_translation` identifies it
with the tableau translation of the actual KP eigenvalue polynomials.
`kpJointDividedPolynomial_translated_contraction` proves the single-column
relation at every complex center on an actual nonzero joint eigenspace, also
when parameters coincide.
The proof of KP (4.8) here uses polynomial determinant coefficients, their exact
derivative-minor values, sorting of exponent vectors into partitions, and
alternating coefficient extensionality. This is an alternative to the exterior
power calculation in the reference; no exterior-power identity is assumed.
Evidence: `verification/logs/m7-all-center-translation-*`; 601 new and 68
inherited modules, 4605 build jobs, 5093 audited declarations including 4334
theorems. Full build, both-library forbidden-token scan, and recursive dependency
audit pass, with only Classical.choice, propext, and Quot.sound.
Next are passage from translated coefficients to ordinary differential
annihilation, polynomial solution-space reconstruction and decomposability,
full KP fibre correspondence, and the remaining M7 estimates. Main theorem and
full sharpness remain unproved. M7 stays active; counts record coverage, not a
completion percentage.

M7 differential-annihilation checkpoint: `finSuccEquiv_translate_factorial_coeff`
converts the translated coefficient relation to ordinary derivatives with the
exact factorial factors. Translation is proved injective. An elementary
polynomial identity principle over the infinite scalar image then proves
`kpJointDividedPolynomial_differential_eq_zero`: the actual nonzero divided
alternating polynomial is annihilated in its first variable by the KP
polynomial differential operator. All parameter tuples, including collisions,
remain covered.
Evidence: `verification/logs/m7-differential-annihilation-*`; 603 new and 68
inherited modules, 4607 build jobs, 5107 audited declarations including 4346
theorems. Build, both-library source scan, and recursive dependency audit pass
with only Classical.choice, propext, and Quot.sound.
This completes the translation-to-annihilation step, not the polynomial-space
reconstruction. Next are the finite scalar coefficient space, its dimension
bound, alternating decomposability and recovery of the exact Plucker
coordinates. Full KP correspondence, remaining M7 estimates, main theorem and
full sharpness remain unproved. M7 stays active.

M7 scalar coefficient-space checkpoint: linear scalar contraction of polynomial
coefficients commutes with all iterated derivatives and the differential
expression. The resulting `polynomialCoefficientSpace` is a concrete submodule
of complex polynomials, proved finite-dimensional by its degree bound.
`kpJointCoefficientSpace_finrank_le` bounds its dimension by the actual
operator order; `kpJointCoefficientSpace_ne_bot` proves it nonzero. The leading
coefficient is exactly the monic product of the parameter factors, hence
nonzero even for repeated parameters.
Evidence: `verification/logs/m7-scalar-coefficient-space-*`; 606 new and 68
inherited modules, 4610 build jobs, 5132 audited declarations including 4368
theorems. Full build, both-library source scan, and recursive dependency audit
pass with only Classical.choice, propext, and Quot.sound.
Next dependency sub-DAG: pairing separate polynomial variables with univariate
linear functionals -> alternating form and its coefficient-space annihilator
condition -> descent to the finite coefficient-space dual -> dimension equality
and determinant representation -> recovery of the exact Plucker coordinates.
Relevant inspected mathlib results: Basis.ext_multilinear,
AlternatingMap.compLinearMap, AlternatingMap.map_linearDependent,
AlternatingMap.eq_smul_basis_det and LinearMap splitting over a field.
The dimension equality, determinant representation and polynomial-space
correspondence are still pending. Full KP correspondence, remaining M7
estimates, main theorem and full sharpness remain unproved. M7 stays active.

M7 coefficient-space dimension-equality checkpoint: scalar tensor pairings now
identify the divided alternating polynomial with a concrete alternating form
on the dual of the univariate polynomial module. A functional annihilating
the actual coefficient space kills that form. The form descends to the dual
of that finite-dimensional space and remains nonzero; its arity therefore
bounds the dimension below. Combined with the previously proved differential
operator bound, `kpJointCoefficientSpace_finrank_eq` proves exact dimension.
All actual parameter tuples, including collisions, remain covered.
Evidence: `verification/logs/m7-coefficient-dimension-equality-*`; 611 new and
68 inherited modules, 4616 build jobs, 5166 audited declarations including
4397 theorems. Full build, both-library source scan and recursive dependency
audit pass with only Classical.choice, propext and Quot.sound.
The algebraic proof uses inspected mathlib alternating-map and dual-space
results, with the annihilator descent proved in this repository. Next are
the determinant representation, exact derivative-minor coordinates and shape.
This is partial progress on `lem:KP-correspondence`: full fibre correspondence,
remaining M7 estimates, main theorem and full sharpness remain unproved.
M7 stays active; later milestones have not started.
M7 determinant-representation checkpoint: `alternatingDual_eq_scalar_det`
proves that the descended nonzero alternating form on an equally dimensional
space is a nonzero scalar times the evaluation determinant. Applied to the
actual coefficient space, `kpJointDividedPolynomial_decomposable` constructs
an independent tuple of polynomials with precisely the required divided
alternating polynomial. `finitePartitionDividedPolynomial_representation_minor`
recovers every fitting partition's derivative minor at every center, with the
exact factorial factors and common scalar. Both rows and columns are reversed
to match the manuscript's increasing derivative orders without a sign error.
Alternative proof for `lem:KP-correspondence`: finite scalar coefficient space,
annihilator descent and the top alternating-form determinant formula replace
the source's decomposability argument. All steps are proved here, using only
inspected mathlib linear algebra; no Plucker relations are assumed.
Evidence: `verification/logs/m7-determinant-representation-*`; 614 new and 68
inherited modules, 4619 build jobs, 5171 audited declarations including 4402
theorems. Full build, source scans and recursive dependency audit pass with
only Classical.choice, propext and Quot.sound.
Next: actual normalized coordinates, Schubert degree profile and ambient
 dimension transfer. Full KP fibre correspondence, remaining M7 estimates,
main theorem and full sharpness remain unproved. M7 stays active.
M7 exact-normalized-tuple checkpoint: `kpJointPolynomialTuple_exists` constructs
an independent tuple of parameter-cardinality dimension from every actual
nonzero joint eigenspace. Every partition minor at every center, including
nonfitting partitions, equals its actual eigenvalue polynomial up to one
nonzero scalar. The top minor is everywhere nonzero, and
`kpJointPolynomialTuple_normalized` proves the exact manuscript normalization.
This uses the full top operator and support identities; no coordinate data
or polynomial-space existence is introduced as an assumption.
Evidence: `verification/logs/m7-exact-normalized-tuple-*`; 616 new and 68 inherited
modules, 4621 build jobs, 5184 audited declarations including 4415 theorems.
Full build, both source scans and recursive audit pass with only Classical.choice,
propext and Quot.sound. M7 stays active.
Next sub-DAG: coordinate support -> vanishing of derivative determinants above
the top total order -> invertible jet normalization -> basis with the exact
Schubert degree profile -> transfer to the manuscript's specified dimension.
Inspected mathlib APIs include Matrix.det_permute, Matrix.det_updateRow_sum,
Matrix.mul_nonsing_inv, polynomial coefficient/degree bounds and finite sums.
Full KP fibre correspondence, remaining M7 estimates, main theorem and full
sharpness are still unproved.
M7 Schubert-frame reconstruction checkpoint: vanishing outside a partition
implies vanishing of every jet determinant above its total order. Inverting
the nonzero top jet matrix gives an actual polynomial change of basis. A row
replacement determinant then forces every coefficient above each prescribed
degree to vanish, while its pivot jet is one. Thus
`polynomialSchubertFrame_exists_of_minor_support` constructs the actual basis
with exactly the Schubert degree profile, preserving normalized coordinates.
This finite jet-elimination argument is an alternative proof of the shape
recovery step of `lem:KP-correspondence`; it assumes no Schubert membership.
Evidence: `verification/logs/m7-schubert-frame-reconstruction-*`; 620 new and
68 inherited modules, 4625 build jobs, 5201 audited declarations including
4431 theorems. Build, source scans and recursive audit pass with only
Classical.choice, propext and Quot.sound.
Next: package this reconstruction for actual joint eigenspaces, identify the
monic Wronskian and transfer the parameter-cardinality construction to the
paper's arbitrary allowed dimension. Full KP fibre correspondence, remaining
M7 estimates, main theorem and full sharpness remain unproved. M7 stays active.
M7 actual forward Wronski-fibre checkpoint: actual joint eigenvalues now produce
an actual Schubert space when its dimension equals the number of parameters.
`kpJointWronskiFibre_exists_card_dimension` proves both the initial normalized
coordinates and the exact monic Wronskian product. The empty normalized
coordinate has separately been identified with the normalization of the
Wronskian polynomial, using its proved top coefficient and degree formula.
Evidence: `verification/logs/m7-actual-wronski-fibre-forward-*`; 623 new and 68
inherited modules, 4628 build jobs, 5208 audited declarations including 4437
theorems. Full build, both-library source scan and recursive audit pass with
only Classical.choice, propext and Quot.sound.
The dimension restriction is explicit and does not replace the manuscript's
statement: the next obligation is algebraic dimension transfer via constants,
polynomial primitives and derivative-minor identities. The converse Wronski
fibre direction is also pending. The full `lem:KP-correspondence`, remaining
M7 estimates, main theorem and full sharpness remain unproved. M7 stays active.
M7 Schubert dimension-transfer checkpoint: an algebraically constructed
polynomial primitive has exactly the prescribed derivative. Removing a
constant first column differentiates every remaining column and preserves
all partition minors up to that constant, including nonfitting partitions.
These exact identities prove both raising and lowering of Schubert dimension.
`polynomialSchubertFrame_exists_dimension` preserves every normalized
coordinate at every center in any dimension accommodating the same shape.
No dimension equality with the parameter count is needed for the transfer.
Evidence: `verification/logs/m7-schubert-dimension-transfer-*`; 627 new and
68 inherited modules, 4632 build jobs, 5233 audited declarations including
4461 theorems. Full build, source scans and recursive dependency audit pass
with only Classical.choice, propext and Quot.sound.
Next: package the unrestricted forward KP correspondence, then prove the
converse Wronski-fibre direction and identify the Bethe algebra as required.
Full KP correspondence, remaining M7 estimates, main theorem and full sharpness
remain unproved. M7 stays active.
M7 unrestricted forward KP correspondence checkpoint:
`kpJointSchubertSpace_exists` and `kpJointWronskiFibre_exists` now prove the
forward direction for every polynomial-space dimension and ambient bound
allowed by the manuscript. The hypotheses are the actual nonzero joint
eigenspace, positive parameter count, the stated shape, and the manuscript's
ambient bound. The exact initial normalized coordinates and monic Wronskian
product are conclusions, including for repeated parameters.
Evidence: `verification/logs/m7-kp-forward-correspondence-*`; 628 new and 68
inherited modules, 4633 build jobs, 5236 audited declarations including 4464
theorems. Full build, source scans and recursive audit pass with only
Classical.choice, propext and Quot.sound. M7 remains active.
The converse is not inferred from this direction. The primary KP source,
https://arxiv.org/html/2309.04645v2, Section 4.3.1, uses generic fibre degree
and continuity to obtain that converse. Those are additional proof obligations.
New support inspection found mathlib's Grassmannian, Nullstellensatz and
Noether normalization; its Bezout file concerns principal ideals, and its
polynomial HilbertPoly file does not supply Schubert intersection degrees.
Next sub-DAG: injectivity of normalized coordinates on actual subspaces ->
precise finite Wronski-fibre count/continuation (or a proved alternative) ->
converse eigenspace construction. Required final signature: for every actual
Schubert space V with the given monic Wronskian, the joint eigenspace whose
profile is V's normalized coordinates at zero is nonzero. No such theorem
has yet been established. Bethe identification, remaining M7 estimates, main
theorem and full sharpness also remain pending.
M7 normalized-coordinate injectivity checkpoint:
`polynomialSchubertSpace_eq_of_coordinates` proves that equal normalized
coordinates at zero imply equality of the actual polynomial subspaces.
The proof recovers proportional determinant polynomials by their alternating
coefficients, and then recovers the subspaces by dual annihilators. This avoids
assuming an unformalized Plucker embedding theorem.
Evidence: `verification/logs/m7-schubert-coordinate-injectivity-*`; 630 new and
68 inherited modules, 4635 build jobs, 5243 audited declarations including
4471 theorems. Build, both source scans and recursive dependency audit pass
with only Classical.choice, propext and Quot.sound.
Next are closedness of actual joint eigenvalue profiles under parameter
limits and the separate Wronski-fibre counting/continuation obligations.
The inverse correspondence, Bethe identification, remaining M7 estimates,
main theorem and full sharpness remain unproved. M7 stays active.
M7 actual joint-profile closedness checkpoint:
`isClosed_kpJointProfiles` and `kpJointEigenspace_ne_bot_of_tendsto`
prove closedness and limit stability for the actual Specht-module KP family,
including repeated parameters. The proof normalizes eigenvectors to the
compact unit sphere and projects the closed common-eigenvector relation.
The KP action is a finite sum of continuous polynomial weights times fixed
linear operators; finite-dimensional continuity is supplied by mathlib.
Evidence: `verification/logs/m7-kp-joint-profile-closed-*`; 632 new and 68
inherited modules, 4637 build jobs, 5252 audited declarations including
4480 theorems. Build, both source scans and recursive dependency audit pass
with only Classical.choice, propext and Quot.sound.
This establishes the eigenvalue-limit part only. The inverse Wronski
correspondence, Bethe identification, remaining M7 estimates, main theorem
and full sharpness remain unproved. M7 stays active.
M7 affine Schubert chart and polynomial density checkpoint:
`polynomial_eq_zero_of_zero_on_every_fibre` proves that a polynomial
vanishing at a point in every fibre of a polynomial self-map of finite
affine space is identically zero. Surjectivity gives algebraic independence;
finite transcendence degree then supplies an algebraic relation with nonzero
constant term. This is a proved alternative tool for the converse argument,
not an assumed Wronski fibre degree.
`schubertChartSlot_card` gives exactly partitionSize free coefficients.
`schubertChartSpace_mem` constructs an actual space for every tuple, and
`polynomialSchubertSpace_exists_chart` represents every actual Schubert space
by such a tuple, using normalized pivot jets and coordinate injectivity.
Evidence: `verification/logs/m7-affine-chart-density-*`; 636 new and 68
inherited modules, 4643 build jobs, 5285 audited declarations including
4506 theorems. Build, both source scans and recursive audit pass with only
Classical.choice, propext and Quot.sound.
Next: polynomial coordinate formulas, Wronski-map surjectivity from forward
KP correspondence, and symmetric orbit equations for joint eigenspaces.
The inverse correspondence, Bethe identification, remaining M7 estimates,
main theorem and full sharpness remain unproved. M7 stays active.
M7 KP Wronski-density checkpoint:
`normalizedSchubertCoordinate_chart` and
`schubertWronskiCoefficientPolynomial_eval` identify the exact chart
coordinates and monic Wronski coefficients with multivariate polynomials.
`kpJointSchubertChart_exists` supplies an actual joint-profile chart point
over every root tuple. `polynomial_eq_zero_of_kpJointSchubertCharts` proves
that a polynomial vanishing on all such actual points is identically zero.
This uses the proved finite-transcendence-basis density lemma and complex
factorization with multiplicities; no Schubert fibre-degree theorem is assumed.
`commonEigenvector_iff_forall_det_eq_zero` characterizes joint eigenvectors
by square-composite determinants. `kpJointEigenspace_permute_ne_bot_iff`
proves root-permutation invariance. Symmetric orbit polynomial equations
are proved to recover the original polynomial certificate over a domain.
Evidence: `verification/logs/m7-kp-wronski-density-*`; 642 new and 68
inherited modules, 4651 build jobs, 5328 audited declarations including
4541 theorems. Build, both source scans and recursive audit pass with only
Classical.choice, propext and Quot.sound.
Next: descend the symmetric determinant equations using elementary symmetric
polynomials and apply them to the actual finite KP equation matrix.
The exact inverse correspondence, Bethe identification, remaining M7 estimates,
main theorem and full sharpness remain unproved. M7 stays active.
M7 exact inverse KP correspondence checkpoint:
`kpJointEigenspace_of_schubertWronskiFibre` proves that every actual Schubert
space with the prescribed monic Wronskian gives a nonzero actual KP joint
eigenspace, including repeated roots. `kpJointEigenspace_chart_of_wronskian`
proves the chart version. The intermediate symmetric-polynomial descent,
orbit equation transfer, finite joint-equation determinant criterion, and
explicit determinant polynomials are all kernel checked.
Proof divergence for LaTeX `lem:KP-correspondence`(ii): instead of a cited
Wronski fibre-degree formula, use the proved surjectivity/density theorem for
the affine Schubert chart, elementary symmetric polynomial specialization,
root-permutation invariance, and square-composite determinant equations.
This alternative now proves the exact inverse conclusion without a generic
root assumption or external mathematical assumption.
Evidence: `verification/logs/m7-kp-inverse-correspondence-*`; 648 new and 68
inherited modules, 4657 build jobs, 5360 audited declarations including
4568 theorems. Build, both source scans and recursive audit pass with only
Classical.choice, propext and Quot.sound.
Next: package the generated-algebra common-eigenspace interface and the exact
two-way correspondence, then continue the remaining M7 estimates and Bethe
algebra identification. The complete `Paper.lem_KP_correspondence`, remaining
M7 estimates, main theorem and full sharpness remain uncertified. M7 is active.
M7 common-eigenspace correspondence checkpoint:
`Paper.lem_KP_correspondence_ii` proves both directions of the exact manuscript
part (ii), with arbitrary M>=1, every allowed dimension and ambient bound,
and repeated roots. `IsCommonEigenspace` means precisely a nonzero subspace
on which every element of the generated algebra acts by a scalar; its
equivalence with containment in an actual KP joint eigenspace is proved.
Evidence: `verification/logs/m7-kp-common-eigenspace-*`; 650 new and 68
inherited modules, 4659 build jobs, 5372 audited declarations including
4579 theorems. All build/source/dependency gates pass, with only the three
approved foundational principles. This certifies part (ii), not the still
pending Bethe algebra identification in part (i). Remaining M7 estimates,
main theorem and full sharpness are not yet certified. M7 stays active.
Next dependency chain: all-center unit eigenvector + character projection
bound -> universal subset expansion -> minor estimates. In parallel within
the same milestone, finish the independent Bethe identification obligation.
M7 Schubert-space universal minor checkpoint:
`schubertUniversalMinors` proves the exact reciprocal-root subset expansion
and factorial expectation bounds for every actual Schubert space and every
basis. A single unit vector is fixed before the partition and center; repeated
roots and M=0 are included. `schubertMinor_norm_le` proves the resulting
elementary-symmetric estimate. `kpAlpha_expectation_bound` applies the proved
character projector to the supported permutation subgroup.
Evidence: `verification/logs/m7-schubert-universal-minors-*`; 656 new and 68
inherited modules, 4665 build jobs, 5392 audited declarations including
4599 theorems. Build/source/recursive audit all pass using only the approved
foundational principles.
Remaining obligation for full `Paper.lem_universal_minors`: construct a
degree-adapted basis for an arbitrary finite-dimensional polynomial space,
identify its Schubert shape and monic Wronskian, then apply the proved result.
The full paper lemma is not yet certified. M7 stays active; Bethe identification,
differential-coefficient and initial-basis estimates also remain pending.
Next exact signatures: `polynomialBasis_exists_strictMono_natDegree` produces
an actual increasing-degree basis from any finite polynomial basis;
`polynomialSpace_exists_schubertFrame` produces its actual fitting partition.
Dependency DAG: elementary invertible basis subtraction -> cancellation of
equal leading degrees -> basis minimizing total degree -> distinct degrees
-> sorted degree basis -> fitting partition -> full universal minor theorem.
The pinned mathlib transvection, polynomial degree cancellation, and finite
basis reindexing APIs have been inspected; no adapted basis is assumed.
M7 full universal derivative-minor checkpoint:
`Paper.lem_universal_minors` now proves the manuscript lemma for an arbitrary
actual polynomial space with a basis of size n+1. It constructs an actual
finite-dimensional Hermitian Specht module, its unitary symmetric-group
representation, and one unit vector giving the exact expansion and factorial
bounds for every basis, partition and off-root center. M=0 and repeated roots
are included. `Paper.eq_minor_es_bound` proves the exact resulting estimate.
`polynomialBasis_exists_strictMono_natDegree` and
`polynomialSpace_exists_schubertFrame` discharge the adapted-basis and shape
obligations. Basis independence of the monic Wronskian and equality between
partition size and number of roots are proved. The basis construction uses
minimum total degree and invertible elementary subtraction to rule out equal
degrees; this supplies the manuscript's basis choice without an extra assumption.
Evidence: `verification/logs/m7-universal-polynomial-minors-*`; 660 new and 68
inherited modules, 4690 build jobs, 5406 audited declarations including
4613 theorems. All build/source/dependency gates pass, using only the three
approved foundational principles. No external theorem is assumed.
Next: identify the fundamental coefficient with the signed single-column
minor, then prove `Paper.prop_polynomialcoeff` from the fixed universal vector.
Bethe algebra identification, initial-basis and initial-value estimates remain
pending in M7. Main theorem and full sharpness remain unproved. M7 is active.
M7 fundamental polynomial coefficients checkpoint:
`Paper.prop_polynomialcoeff` proves the exact product formula with constants
gamma(q,I) independent of the center and bounded by q!. It gives equality at
every non-root and codiscrete equality as meromorphic functions; repeated roots
and M=0 are included. `fundamentalCoefficients_eq_columnMinor` proves the Cramer
row-reordering sign (-1)^q using the actual single-column partition orders.
Evidence: `verification/logs/m7-polynomial-coefficient-expansion-*`; 663 new
and 68 inherited modules, 4693 build jobs, 5432 audited declarations including
4639 theorems. Build, both source scans and recursive dependency audit pass
with only Classical.choice, propext and Quot.sound.
Next: a replaced identity-jet row gives a fitting partition of size k-j;
combine its universal minor bound with factorial and Taylor estimates for
`Paper.prop_initial_basis` and `Paper.eq_initial_value_bound`.
Bethe algebra identification and those initial-value estimates remain pending
in M7; the main theorem and full sharpness are not certified. M7 stays active.M7 normalized initial-basis product majorant checkpoint:
`Paper.prop_initial_basis` proves equation `eq:basismajorant` for every actual
basis with the prescribed identity jets. High derivatives are identified
with a reordered derivative minor of partition size k-j; the universal
minor estimate, factorial inequality and exact finite Taylor expansion give
the product bound. The derivative orders and partition size are constructed
and proved, rather than assumed. Repeated roots and M=0 are included.
Evidence: `verification/logs/m7-initial-basis-majorant-*`; 667 new and 68
inherited modules, 4697 build jobs, 5466 audited declarations including
4672 theorems. All build/source/dependency gates pass with only the three
approved foundational principles.
Next exact signatures: `polynomialBasis_exists_identity_jets` constructs
the normalized basis from any actual basis at a nonzero Wronskian value;
`polynomialBasis_repr_eq_jet` identifies its coordinates with derivatives;
`polynomialBasis_identity_jets_unique` proves uniqueness;
`Paper.eq_initial_value_bound` proves the estimate for every member of V.
Dependency DAG: invertible jet matrix -> actual basis -> jet coordinates
-> unique normalized basis -> product bound -> exponential initial-value bound.
The pinned mathlib finite-basis construction and finite-product exponential
APIs have been inspected. Existence/uniqueness of the normalized basis and
the initial-value bound remain pending. Bethe algebra identification is also
pending in M7; the main theorem and full sharpness remain unproved. M7 is active.
M7 complete polynomial initial-value estimate checkpoint:
`polynomialBasis_existsUnique_identity_jets` constructs the unique actual
normalized basis at each off-root center. `polynomialBasis_repr_eq_jet`
identifies every coefficient with the corresponding initial derivative.
Together with `Paper.prop_initial_basis`, this certifies the existence,
uniqueness and product estimate in manuscript `prop:initial-basis`.
`Paper.eq_initial_value_bound` proves the exact exponential estimate for
every h in V, starting from an arbitrary basis. No normalized basis or
coefficient bound is assumed in its statement. M=0 and repeated roots are
included. The proof follows the manuscript, with finite Taylor sums.
Evidence: `verification/logs/m7-polynomial-initial-value-bound-*`; 670 new
and 68 inherited modules, 4700 build jobs, 5474 audited declarations including
4680 theorems. Build, both source scans and the recursive dependency audit
pass with only Classical.choice, propext and Quot.sound.
Remaining M7 obligation: identify the KP algebra with the traditional Bethe
algebra generated by the single-column operators at all centers (equivalently
by their polynomial coefficients). The exact generator definition has been
checked in Karp--Purbhoo, arXiv:2309.04645v2, Section 2.4.1; the identification
is not imported as a theorem. First formalize coefficient/value generation,
then prove the reverse inclusion. All initial-value estimates are now proved;
M7 remains active until the independent algebra identification is certified.
The submitted main theorem and full sharpness remain unproved.
M7 traditional Bethe generators and triangular ODE matrix checkpoint:
`betheAlgebra` is defined by the actual single-column generators at all
centers. `betheAlgebra_eq_adjoin_coefficients` proves equivalence with their
coefficient generators, using scalar polynomial extensionality and linear
annihilators. Its inclusion in `kpGeneratedAlgebra` and its translation
invariance are proved. This does not yet prove the reverse inclusion.
`polynomialODEJetMatrix_det` proves the exact triangular determinant for the
finite matrix prescribing initial coefficients and differential equations.
Evidence: `verification/logs/m7-bethe-generators-ode-matrix-*`; 673 new and
68 inherited modules, 4703 build jobs, 5497 audited declarations including
4700 theorems. Build, source scan and recursive audit pass with only the
approved foundational principles. The detailed reverse-inclusion dependency
DAG is in `work/M7-plan.md`; its planned adjugate argument is not yet certified.
M7 remains active. Bethe identification, the main theorem and full sharpness
are not claimed complete.


M7 polynomial-parameter and adjugate checkpoint (recovered after write access returned):
The interrupted 677-module integration has passed its full gate. Universal
parameter evaluation, the actual universal single-column Bethe algebra, and
finite polynomial ODE adjugate reconstruction and specialization are proved.
Evidence: verification/logs/m7-polynomial-parameters-adjugate-*; 677 new and
68 inherited modules, 4710 build jobs, 5528 audited declarations including
4725 theorems. Both source scans and the recursive dependency audit pass with
only Classical.choice, propext and Quot.sound. The subsequent 15-module
Bethe-identification integration is undergoing its separate gate; M7 remains
active until that gate and the exact manuscript-result review succeed.


M7 completed: full polynomial/Wronskian-minor milestone.
The exact submitted `Paper.lem_KP_correspondence` is now certified, including
the independent traditional Bethe-algebra identification, commutativity,
membership, tableau translation, and both Wronski-fibre directions for all
M>=1 and all complex parameter tuples. This closes the final M7 obligation.
The previously certified Plucker translation, character projection, universal
minor formula and bound, polynomial differential coefficients, unique normalized
basis and initial-value estimate remain covered by the same complete audit.

Final M7 evidence: `verification/logs/m7-complete-bethe-identification-*`;
692 new and 68 inherited modules; 4725 successful build jobs; 5615 declarations
including 4802 theorem declarations. Both-library source scans are empty and
the recursive dependency audit, including private/generated declarations,
permits only Classical.choice, propext and Quot.sound. Every new major theorem
has its dependency print. Source: unchanged submitted manuscript SHA256
D3F63ADE442557F0474EB117EDD0BA99405A09AB412E6D40FAE271C56F7C44CA.
The intermediate recovered 677-module gate is preserved separately as
`m7-polynomial-parameters-adjugate-*`.

M7 is complete; M8 is the next milestone. The submitted main theorem and full
sharpness are still unproved. Earlier checkpoint paragraphs below or above
describe historical states and do not override this completed M7 gate.

## M8 checkpoint: negative polynomial area

The `m8-negative-polynomial-area` gate passed: 694 modules in ModifiedCartan,
4727 build jobs, 5639 audited declarations including 4825 theorem declarations.
The recursive audit reports only `Quot.sound`, `Classical.choice`, and `propext`;
both source scans are empty. Logs are preserved in
`verification/logs/m8-negative-polynomial-area-*`.

- `NegativeLogKernel.lean` proves the integrable negative-log representative,
  the product inequality, and the exact translated kernel integral pi/2.
- `PolynomialNegativeArea.lean` proves
  `ModifiedCartan.Paper.eq_polynomial_negative_area` for every set K, the
  monic polynomial small-value area bound, and its vanishing when
  degree(P_nu)/s_nu tends to zero and s_nu tends to infinity.
- Zero values of `Real.log` are not treated as minus infinity. The finite,
  null polynomial zero set is explicitly excluded only in the AE argument
  that proves the small-value area estimate. No assumption of positive
  scales at all indices is introduced; positivity is derived on a tail.

M8 remains active. The exact `prop_localcompact`, quantitative Taylor and
Cramer approximation, separating-root count, holomorphic compactness, and
canonical gauge comparison are not yet certified by this checkpoint.

## M8 checkpoint: monic quotient comparison

The `m8-monic-quotient-comparison` gate passed: 695 ModifiedCartan modules,
4728 build jobs, 5650 audited declarations including 4836 theorem declarations.
Only the three permitted foundational principles occur; both source scans
are empty. Logs: `verification/logs/m8-monic-quotient-comparison-*`.

`MonicQuotientComparison.lean` proves the exact Cramer quotient error bound
`2 exp(-(B-1)s) + 2 exp(-(B-C-2)s)`, convergence in measure off exceptional
sets whose measures vanish, and the resulting local comparison for monic
polynomial denominators of degree o(s). The bounds are eventual, so no
positivity or approximation condition on the initial finite segment is needed.

These are proved analytic transfer lemmas for `eq:cramercomparison`. They do
not certify the manuscript's Taylor/Wronskian approximation hypotheses, which
remain to be constructed from `eq:localhyp`. M8 and `prop_localcompact` remain
in progress; no later milestone is certified.

## M8 checkpoint: actual exponential Taylor approximants

The `m8-exponential-taylor-approximation` gate passed: 697 ModifiedCartan
modules, 4730 build jobs, 5675 declarations including 4861 theorem declarations.
Only `Quot.sound`, `Classical.choice`, and `propext` occur; both source scans
are empty. Logs: `verification/logs/m8-exponential-taylor-approximation-*`.

`QuantitativeTaylor.lean` proves exact Cauchy coefficient bounds, a geometric
Taylor remainder bound, the polynomial degree bound, and simultaneous finite
jet estimates. `ExponentialTaylorApproximation.lean` proves the positive
linear cutoff exists and proves `ModifiedCartan.Paper.eq_taylorerror` from the
manuscript's local holomorphy and Euclidean norm bound. The polynomials are
literally the Taylor polynomials with ceil(L*s_nu) terms; all coordinate
indices and derivative orders through n+1 are covered on the closed disk D16.
The eventual degree bound is (L+1)*s_nu. No positive initial-scale assumption
or pre-existing approximation data is required.

M8 remains active. Wronskian/Cramer determinant approximation, root separation
and root counts, holomorphic compactness, and the gauge comparison still
remain before `prop_localcompact` can be certified.

## M8 checkpoint: determinant error bounds for the actual jets

The `m8-jet-determinant-bounds` gate passed: 698 ModifiedCartan modules,
4731 build jobs, 5687 declarations including 4873 theorem declarations.
The source scans are empty and the recursive audit has only the permitted
foundational dependencies. Logs: `verification/logs/m8-jet-determinant-bounds-*`.

`LocalJetDeterminantBounds.lean` proves the finite product telescoping bound,
the signed determinant bound and determinant difference estimate, and their
applications to the actual Wronskian and signed Cramer numerator. Replaced
rows and their negative highest derivatives are included explicitly.

The determinant difference bound uses m! * e * m * M^m for M >= 1 instead of
the slightly sharper power M^(m-1). This only changes the fixed loss in the
Taylor approximation exponent. It does not impose any extra condition on
`prop_localcompact`, whose hypotheses must still produce all the bounds.
M8 remains active and the full proposition is not yet certified.

## M8 checkpoint: constructed Wronskian and numerator approximations

The `m8-constructed-determinant-approximation` gate passed: 699 ModifiedCartan
modules, 4732 build jobs, 5695 declarations including 4881 theorem declarations.
Both source scans are empty; all dependencies are among the three allowed
foundational principles. Logs: `verification/logs/m8-constructed-determinant-approximation-*`.

`ExponentialJetApproximation.lean` now constructs polynomial approximants whose
Wronskian and every signed Cramer numerator approximate the original jets to
any prescribed exp(-B*s) accuracy on closed D16. Only the original local
holomorphy, Euclidean norm bound, and divergent scale are inputs. Their degrees
are O(s), with the constant quantified before the sequence data.

The same module proves an original-numerator growth constant C2 depending only
on n and C, before choosing any approximation precision. The factorial and
finite-product constants are absorbed on an explicitly proved eventual tail.
The complete local compactness proposition remains unproved; M8 is active.

## M8 checkpoint: nonzero approximating polynomial Wronskians

The `m8-nonzero-polynomial-wronskian` gate passed: 700 ModifiedCartan modules,
4733 build jobs, 5700 declarations including 4886 theorem declarations.
The source scans are empty and the recursive audit permits only the three
foundational principles. Logs: `verification/logs/m8-nonzero-polynomial-wronskian-*`.

`LocalPolynomialApproximation.lean` proves the manuscript-facing
`ModifiedCartan.Paper.eq_wronskiapprox`: from the original hypotheses and
monic W(g)=P on D32 it constructs polynomial p with eventually nonzero
R=W(p), degree(R)=O(s), and the prescribed exponential error for R-P and
all signed Cramer numerators on closed D12. Leading-coefficient Cauchy bounds
on the unit circle prove nonvanishing; no root-count result is assumed.

Together with the prior original-numerator bound, this certifies Step 1 of
`prop:localcompact`. M8 itself remains active; root separation, normal-family
compactness and canonical-gauge comparison are still required.

## M8 checkpoint: actual Cramer comparison from the original hypotheses

The `m8-actual-cramer-comparison` gate passed: 701 ModifiedCartan modules,
4734 build jobs, 5701 declarations including 4887 theorem declarations.
Both source scans are empty; recursive dependencies are only `Quot.sound`,
`Classical.choice`, and `propext`. Logs:
`verification/logs/m8-actual-cramer-comparison-*`.

`LocalCramerComparison.lean` proves `ModifiedCartan.Paper.eq_cramercomparison`.
The theorem constructs p from the original manuscript hypotheses; it retains
the nonzero polynomial Wronskian, linear degree bound, and exponential R-P
error, and proves local convergence in measure on D12 for the difference of
the actual fundamental coefficients. It chooses B=C2+3 from the separately
proved, precision-independent numerator bound. No approximation hypothesis
is added to the statement.

Steps 1 and 2 of `prop:localcompact` now have their assembled certificates.
M8 remains active: interior root-count control, root-sum splitting,
holomorphic subsequence compactness, and canonical-gauge comparison remain.
The full `prop_localcompact`, main theorem, and sharpness are not yet proved.

## M8 checkpoint: specialized Jensen root-count bound

The `m8-jensen-polynomial-count` gate passed: 702 ModifiedCartan modules,
4735 build jobs, 5721 declarations including 4905 theorem declarations.
Both source scans are empty, and recursive dependencies are only `Quot.sound`,
`Classical.choice`, and `propext`. Logs:
`verification/logs/m8-jensen-polynomial-count-*`.

`PolynomialApproximationCounting.lean` proves
`polynomial_approximation_divisor_count_le`: if P is monic and
|R-P| <= 1/2 on closed D12, the analytic divisor count of R on closed D8
is at most `(log 4 + (1 + log 12) * degree P) / log(10/9)`.
The estimate includes multiplicities and boundary points. Its proof derives
Cauchy coefficient bounds, constructs a maximizing center in closed D1,
controls R at that center and on its radius-ten circle, applies the existing
proved Jensen theorem, and proves monotonicity of the compact-disk count.

Proved alternative to the root-count input of Step 3: Jensen gives an
O(degree P + 1) upper bound. The manuscript's stronger Rouché equality
`eq:rouche-root-count` is not asserted. The remaining connection to root
lists and the o(s) limit is being formalized next. No root-control assumption
has been added to the paper proposition. M8 remains active; the full local
compactness proposition, main theorem, and sharpness remain unproved.

## M8 checkpoint: multiplicity-preserving root lists and sublinear count

The `m8-root-list-count` gate passed: 703 ModifiedCartan modules, 4736 build
jobs, 5735 declarations including 4919 theorem declarations. Source scans
are empty and the recursive audit permits only the three foundational
principles. Logs: `verification/logs/m8-root-list-count-*`.

`PolynomialRootCount.lean` constructs a root list indexed by the degree of
each nonzero polynomial, with the exact normalized polynomial factorization
needed by the universal-minor expansion. It proves that the analytic divisor
count equals the filtered root-list cardinality on every set; repeated roots
and boundary roots are included. Normalization invariance is proved via
meromorphic orders, with no zero-count correspondence assumed.

`polynomial_approximation_root_count_tendsto_zero` then proves the interior
count divided by s tends to zero from degree(P)/s -> 0, s -> infinity, and
an eventual uniform approximation error at most 1/2 on closed D12. This
completes the Jensen alternative for the o(s) root-count input. The exact
Rouché equality remains unclaimed. Root-sum estimates and the remaining
local compactness steps are still under development; M8 remains active.

## M8 checkpoint: inner and outer reciprocal-root sums

The `m8-root-distance-sums` gate passed: 704 ModifiedCartan modules, 4737
build jobs, 5751 declarations including 4933 theorem declarations. The
source scans are empty and the recursive audit uses only the permitted
foundational principles. Logs: `verification/logs/m8-root-distance-sums-*`.

`RootDistanceSums.lean` proves the uniform Lp bound for sums of reciprocal
root distances, for every 1 <= p < 2. For roots of norm at most eight,
D6 lies in a radius-fifteen disk about each root; the previously proved
exact planar kernel integral and Minkowski inequality give a constant
independent of the root list. Dividing by s gives Lp convergence to zero
when the list size is o(s), including p=3/2. Local convergence in measure
is also proved. Roots of norm greater than eight contribute at most half
their number at every point of D6.

These estimates are being assembled with the constructed polynomial
approximants; no root-sum hypothesis replaces part of the original
proposition. M8 remains active and the full local compactness proposition
is not yet certified.

## M8 checkpoint: root separation constructed from manuscript hypotheses

The `m8-constructed-root-separation` gate passed: 705 ModifiedCartan modules,
4738 build jobs, 5761 declarations including 4941 theorem declarations.
Both source scans are empty; recursive logical dependencies are only
`Quot.sound`, `Classical.choice`, and `propext`. Logs:
`verification/logs/m8-constructed-root-separation-*`.

`LocalRootSeparation.lean` proves `ModifiedCartan.Paper.eq_rootbounds` from
exactly the original local holomorphy, exponential Euclidean bound, monic
Wronskian, divergent scale, and degree(P)/s -> 0 hypotheses. It constructs
p and the multiplicity-preserving root lists, retains eventual nonzero R
and degree(R) <= L*s, and retains the actual Cramer-coefficient convergence
from Step 2. It proves inner-root count/s -> 0, the inner-root L^(3/2)
convergence and local convergence in measure, and the eventual uniform
outer-root bound L/2 on D6. L is quantified before sequence data.

This certifies the first three steps of `prop:localcompact`. The recorded
Jensen alternative uses the fixed radius eight and includes its boundary
roots in the inner list; the manuscript's Rouché equality remains unclaimed.
Step 4 (coefficient splitting and holomorphic compactness) and Step 5
(canonical-gauge comparison) remain to be proved. M8 is still active; the
full proposition, main theorem and sharpness are not yet certified.

## M8 checkpoint: coefficient-expansion adapter and uniform subset bounds

The `m8-subset-product-bounds` gate passed: 707 ModifiedCartan modules,
4740 build jobs, 5775 declarations including 4955 theorem declarations.
Source scans are empty and recursive dependencies are only the permitted
three foundational principles. Logs: `verification/logs/m8-subset-product-bounds-*`.

`PolynomialFamilyExpansion.lean` derives linear independence from a nonzero
polynomial Wronskian and applies the M7 universal coefficient expansion to
the original polynomial tuple via its span basis. No basis assumption is
added. `SubsetProductBounds.lean` proves bounds for full and marked subset
product sums, with constants independent of the size of the root list.

Alternative estimate for the Step 4 error: normalize nonnegative weights
by 1 + their sum, bound the generating product by exp(1), and bound its
change when marked weights are set to zero. This gives a bound proportional
to the sum of marked weights times (1 + total weight)^q, with the factor
exp(1). This coarser bound has the same required vanishing consequence once
the inner weights tend to zero in measure and the outer sum is bounded.
That analytic consequence and the actual coefficient split are still
being formalized; the manuscript's sharper `eq:F-bound` has not been
claimed verbatim. M8 remains active with Steps 1--3 certified.

## M8 checkpoint: coefficient splitting and holomorphic compactness tools

The `m8-coefficient-split-compactness-tools` gate passed: 710 ModifiedCartan
modules, 4743 build jobs, 5823 declarations including 5000 theorem declarations.
Both source scans are empty; recursive dependencies are only `Quot.sound`,
`Classical.choice`, and `propext`. Frozen logs:
`verification/logs/m8-coefficient-split-compactness-tools-*`.

`LocalCoefficientSplit.lean` proves the exact exterior/interior finite-sum
split, its almost-everywhere identification with the actual normalized
polynomial differential coefficients, holomorphy of the exterior part on
D8, its uniform bound on D6, and local convergence of the interior part to
zero in measure. The coarser generating-product estimate recorded above
supplies the same vanishing conclusion as the manuscript's `eq:F-bound`.

`HolomorphicCompactness.lean` proves a common subsequence theorem for a
finite tuple of holomorphic functions, using Cauchy derivative estimates
and Arzela--Ascoli. It yields uniform convergence on closed D5 and a
holomorphic limit on D5, retaining the uniform bound. This specialized
alternative to Montel is sufficient for the required D4 conclusion.
`MeasureLimitTransfer.lean` supplies addition, restriction, subsequences,
almost-everywhere replacement, uniform-to-measure convergence, and division
by powers of a divergent scale, without adding measurability assumptions
to the original proposition.

The assembly from the original manuscript hypotheses is in progress.
M8 remains active; the complete local compactness proposition, canonical
gauge comparison, main theorem, and sharpness are not yet certified.

## M8 checkpoint: constructed simultaneous coefficient compactness

The `m8-constructed-coefficient-compactness` gate passed: 711 ModifiedCartan
modules, 4744 build jobs, 5832 declarations including 5009 theorem declarations.
Source scans are empty; the recursive dependency audit reports only
`Quot.sound`, `Classical.choice`, and `propext`. Frozen logs:
`verification/logs/m8-constructed-coefficient-compactness-*`.

`LocalCoefficientCompactness.lean` proves `Paper.eq_splitcoeff` from the
original manuscript hypotheses and constructs all coefficient pieces. It
then proves `Paper.local_coefficient_relative_compactness`: every selected
subsequence has a further common subsequence on which all actual normalized
fundamental coefficients converge locally in measure on D4 to holomorphic
functions, with a uniform bound on D1 depending only on n+1 and C. The
constant is quantified before all sequence data and subsequence choices.
The Cramer comparison transfers limits from the polynomial approximants;
no compactness or coefficient bound is inserted as an additional hypothesis.

Steps 1--4 of `prop:localcompact` are now certified. Step 5, the canonical
gauge comparison, remains in progress. The full `prop_localcompact`, main
theorem and sharpness are not yet certified.

## M8 checkpoint: all normalized pole sums for an o(s) root list

The `m8-small-root-pole-sums` gate passed: 712 ModifiedCartan modules,
4745 build jobs, 5842 declarations including 5018 theorem declarations.
Source scans are empty and the recursive audit reports only the three
permitted foundational principles. Frozen logs:
`verification/logs/m8-small-root-pole-sums-*`.

`SmallRootPoleSums.lean` proves local convergence to zero for the sum of
all reciprocal root distances divided by s, for arbitrary moving root
lists with M/s -> 0. It then proves every normalized positive-order pole
sum tends to zero. The checked inequality sum x_i^q <= (sum x_i)^q makes
the earlier recorded first-order alternative rigorous; no root-location
hypothesis or fractional-moment assumption is added.

Steps 1--4 remain certified. Step 5 is active, and the full proposition,
main theorem and sharpness are not yet certified.

## M8 checkpoint: polynomial logarithmic jets and gaugesmall

The `m8-polynomial-gauge-smallness` gate passed: 713 ModifiedCartan modules,
4746 build jobs, 5853 declarations including 5028 theorem declarations.
Source scans are empty; recursive dependencies are only the three permitted
foundational principles. Logs: `verification/logs/m8-polynomial-gauge-smallness-*`.

`PolynomialGaugeSmallness.lean` proves the exact almost-everywhere formula
for all derivatives of the logarithmic derivative of a factored polynomial,
and constructs the root lists for each actual monic P_n. Combined with the
previous all-order pole bound, this proves `Paper.eq_gaugesmall` for the
literal ell_n = P_n'/((n+1)P_n), using only s_n -> infinity and
 degree(P_n)/s_n -> 0. It also identifies the actual canonical logarithmic
derivative on the original domain with the corresponding negative
polynomial logarithmic derivative.

Steps 1--4 and `eq:gaugesmall` are certified. The remaining Step 5 obligation
is the coefficient transformation and its vanishing normalized difference.
The full `prop_localcompact`, main theorem and sharpness remain uncertified.

## M8 checkpoint: canonical logarithmic jets and finite tuples

The `m8-canonical-jet-smallness` gate passed: 715 ModifiedCartan modules,
4748 build jobs, 5864 declarations including 5039 theorem declarations.
Source scans are empty; recursive dependencies are only the permitted
foundational principles. Logs: `verification/logs/m8-canonical-jet-smallness-*`.

`CanonicalJetSmallness.lean` identifies the actual local normalizing
factor's logarithmic jets with the M5 partition polynomial. It proves
that every positive-order normalized logarithmic jet of the canonical
factor tends to zero locally in measure on D4, from the original monic
Wronskian and degree/scale hypotheses. Branch existence and all derivative
identifications are proved, including the almost-everywhere treatment
of Wronskian zeros. `FiniteMeasureTuples.lean` proves convergence in
measure of a finite tuple from its coordinate limits by the union bound,
without additional measurability assumptions.

The coefficient transformation and final gauge comparison are being
assembled. The full local compactness proposition remains uncertified.

## M8 checkpoint: exact canonical coefficient transformation

The `m8-gauge-coefficient-algebra` gate passed: 717 ModifiedCartan modules,
4750 build jobs, 5910 declarations including 5079 theorem declarations.
Source scans are empty and recursive dependencies are only `Quot.sound`,
`Classical.choice`, and `propext`. Frozen logs:
`verification/logs/m8-gauge-coefficient-algebra-*`.

`GaugeCoefficientAlgebra.lean` proves the canonical covariant equation by
using the actual local normalizing factor, expands it by derivative order,
and uses uniqueness of the original fundamental equation to prove the
exact triangular coefficient relation. After division by the scale powers,
the transition matrix has diagonal entries one and determinant one. Its
adjugate gives the exact inverse, producing an explicit continuous finite
polynomial map of the original normalized coefficients and normalized
logarithmic jets. At the zero positive-order jet this map is the identity.
This matrix proof replaces the manuscript's informal weighted-monomial
expansion and is recorded as an alternative proof of the same transformation.
All scaling identities hold also for the project's totalized division.

`CoefficientMeasurability.lean` proves local measurability for the actual
fundamental coefficients, canonical logarithmic derivative, and all its
logarithmic jets. These are derived from analytic data and the exact Cramer
formula; no measurability assumption is added to the manuscript.

The full `prop_localcompact` assembly is undergoing experimental checking.
M8 remains active until that statement and its complete audit pass.

## M8 complete: local compactness and canonical comparison

The full `m8-complete-local-compactness` gate passed: 718 ModifiedCartan
modules, 4751 build jobs, 5914 declarations including 5083 theorem
declarations. Both project source scans are empty. Recursive dependencies
are exactly `Quot.sound`, `Classical.choice`, and `propext`. Frozen logs:
`verification/logs/m8-complete-local-compactness-*`.

`LocalCompactness.lean` proves `Paper.eq_gaugecomparison` on the full
sequence by applying the explicit continuous coefficient transformation
to every extracted coefficient-convergent subsequence. All needed
measurability and vanishing logarithmic-jet claims are proved from the
original holomorphic, monic-Wronskian, growth, and small-degree hypotheses.
The final `Paper.prop_localcompact` combines this with the common
holomorphic limits, their uniform bound, and the identically zero first
canonical coefficient. Its statement adds no stronger hypothesis.

This completes M8. M9, the rescaled representation proposition, is next.
The main theorem and sharpness are still not certified.

## M9 checkpoint: exact monic exponential factorization

Gate `m9-monic-exponential-factorization` passed: 719 ModifiedCartan modules,
4752 build jobs, 5927 declarations including 5095 theorem declarations.
Both source scans are empty; the recursive audit permits exactly
`Quot.sound`, `Classical.choice`, and `propext`. Frozen logs:
`verification/logs/m9-monic-exponential-factorization-*`.

`DivisorPolynomial.lean` constructs the actual monic polynomial from the
finite nonnegative divisor, proves its degree and root location, and
identifies its evaluation with mathlib's factorized rational function.
The extracted analytic nonzero factor gives an exact identity throughout
the open disk: equality at the zeros follows from continuity and the
proved almost-everywhere identity. A proved analytic logarithm then gives
`exists_monic_polynomial_exp_factor_on_ball`. Nontrivial entire functions
are shown to have finite local orders everywhere, including at the origin.

This is the lowest analytic ingredient of `eq:localgauge`; the complete
representation and replacement statements remain uncertified. M9 is active.

## M9 checkpoint: local gauge, center formula, and exact means

Gate `m9-local-gauge-center-and-means` passed: 721 ModifiedCartan modules,
4754 build jobs, 5950 declarations including 5117 theorem declarations.
Source scans are empty; all recursive logical dependencies are permitted.
Frozen logs: `verification/logs/m9-local-gauge-center-and-means-*`.

`OpenDiskCounting.lean` proves the exact open-disk logarithmic counting
formula, the monic divisor polynomial degree bound by the outer zero
count, and the exact value at zero of its exponential factor. Boundary
zeros contribute zero logarithmic weight; the origin correction is not
omitted. `RescaledGauge.lean` constructs `Paper.eq_localgauge` for every
positive real scale and every linearly nondegenerate curve. It proves
analyticity and reducedness of the actual rescaled representation, its
Euclidean log norm formula, the exact circular mean identity with the
explicit radius-independent constant, and the actual canonical coefficient
identification under this gauge and dilation.

`Paper.eq_meanidentity` at this gate certifies the exact identity, not yet
the asymptotic smallness of its constant. The scale counting asymptotics,
negative mean estimate, upper bound, and final compactness transfer remain.
The full representation and replacement statements are not yet certified.

## M9 checkpoint: zero counting under dilation

Gate `m9-zero-counting-dilation` passed: 722 ModifiedCartan modules,
4755 build jobs, 5959 declarations including 5126 theorem declarations.
Both source scans are empty and all recursive dependencies are the three
permitted foundational principles. Logs:
`verification/logs/m9-zero-counting-dilation-*`.

`CountingDilation.lean` proves exact transformation laws for trailing
coefficients and zero counting. For a positive dilation t, the logarithmic
count is N_F(tR) minus the origin multiplicity times log(t). A nonzero
constant factor leaves the zero count unchanged. These results give the
actual dilated Wronskian count and trailing coefficient, with no assumption
that the Wronskian is nonzero at the origin. The correction terms cancel
in the manuscript's center formula. M9 remains active; the complete
representation and replacement statements remain uncertified.

## M9 checkpoint: actual Wronskian polynomial and center identity

Gate `m9-actual-wronskian-center` passed: 723 ModifiedCartan modules,
4756 build jobs, 5966 declarations including 5132 theorem declarations.
Both source scans are empty and the recursive audit has only the permitted
foundational dependencies. Frozen logs:
`verification/logs/m9-actual-wronskian-center-*`.

`RepresentationCenter.lean` defines `rescaledWronskianPolynomial` directly
from the dilated Wronskian's divisor on D64. It proves that the polynomial
is monic and has all roots in D64. Its degree times log(2) is at most the
original Wronskian zero-counting function at 256t for t >= 1.
`Paper.eq_centeridentity` constructs an analytic H for this particular
polynomial and proves both the Wronskian identity and the manuscript's exact
center formula, including cancellation of the origin-order terms.

M9 remains active. The ensuing sequence limits are being assembled; the
negative norm estimate, norm upper bound, full representation compactness,
and replacement lemma still require proofs.

## M9 checkpoint: actual representation and center asymptotics

Gate `m9-representation-step-one` passed: 724 ModifiedCartan modules,
4757 build jobs, 5970 declarations including 5136 theorem declarations.
Both source scans are empty; the recursive audit uses only the three
permitted foundational principles. Frozen logs:
`verification/logs/m9-representation-step-one-*`.

`RepresentationAsymptotics.lean` proves `Paper.representation_step_one`
under the original scale and Wronskian-counting hypotheses. It constructs
the actual analytic gauges H and radius-independent constants c, proves
the exact mean identity, proves degree(P)/s and Re(H(0))/s tend to zero,
and proves the normalized coordinate logarithms at zero and c/s tend to
zero. The polynomial is the actual divisor polynomial from the previous
gate. No convergence assumption on H or its value was added.

M9 remains active. The norm upper bound, representation compactness, and
replacement lemma are not yet certified.

## M9 checkpoint: quotient Wronskian and negative norm bound

Gate `m9-quotient-wronskian-negative-bound` passed: 725 ModifiedCartan modules,
4758 build jobs, 5975 declarations including 5141 theorem declarations.
Both source scans are empty; the recursive audit uses only the permitted
foundational principles. Frozen logs:
`verification/logs/m9-quotient-wronskian-negative-bound-*`.

`QuotientWronskian.lean` proves scalar-gauge invariance of the normalized
Wronskian and its equality to the normalized Wronskian of the original
coordinate quotients. The exact pointwise negative Euclidean norm estimate
`rescaled_negative_norm_le_quotient_wronskian` is proved away from coordinate
and Wronskian zeros. This supports `eq:negativedeterminant` and
`eq:negativepart`; it does not yet prove their mean estimates.

Proved alternative: any fixed nonzero coordinate can be the quotient
denominator. Scalar-gauge invariance and the product bound by the Euclidean
norm remove the manuscript's partition by a maximizing coordinate.
Exceptional zeros still have to be handled for integral applications.
M9 remains active and the full proposition and replacement remain unproved.

## M9 checkpoint: Harnack and canonical kernel geometry

Gate `m9-harmonic-harnack-and-canonical-kernel` passed: 726 ModifiedCartan
modules, 4759 build jobs, 5984 declarations including 5150 theorem
declarations. Both source scans are empty; only the three permitted
foundational dependencies occur. Frozen logs:
`verification/logs/m9-harmonic-harnack-and-canonical-kernel-*`.

`HarmonicBounds.lean` proves the harmonic Harnack inequality from mathlib's
Poisson formula and the exact factor five from radius 48 to radius 32,
including the boundary of the smaller disk. It also proves the equivalent
lower bound for a harmonic function bounded above. The canonical factor
has norm at least one inside its disk away from its pole, proved from an
explicit norm-square identity. These are ingredients of the planned
alternative upper-bound proof, not a proof of the representation theorem.
M9 remains active.

## M9 checkpoint: monic unit-circle mean and analytic factor bound

Gate `m9-monic-unit-circle-mean` passed: 727 ModifiedCartan modules,
4760 build jobs, 5987 declarations including 5153 theorem declarations.
Source scans are empty and all recursive dependencies are permitted.
Frozen logs: `verification/logs/m9-monic-unit-circle-mean-*`.

`MonicCircleMean.lean` proves that a monic complex polynomial has
nonnegative mean log modulus on every unit circle, including circles
through roots. Finite root exceptions are handled by codiscrete congruence.
It then proves `analytic_exp_factor_re_le_log_bound`: if P is monic,
A is analytic near a closed unit disk, and |P exp(A)| is bounded by M on
its boundary, then Re A at the center is at most log M. No degree bound
or zero-free assumption on P is needed. This is a proved ingredient of
the alternative representation norm-bound argument; M9 remains active.

## M9 checkpoint: Poisson majorant without boundary restrictions

Gate `m9-poisson-majorant-with-boundary-zeros` passed: 728 ModifiedCartan
modules, 4761 build jobs, 5997 declarations including 5163 theorem
declarations. Both source scans are empty and the recursive dependencies
are exactly the permitted foundational principles. Frozen logs:
`verification/logs/m9-poisson-majorant-with-boundary-zeros-*`.

`PoissonMajorant.lean` proves `log_norm_le_poisson_log_majorant` for an
entire scalar function dominated in modulus by any positive continuous U.
It first uses the certified regular-boundary Poisson--Jensen formula and
nonnegative divisor terms. It then proves continuity of the Poisson mean
as the radius varies and handles arbitrary boundary zeros by removing the
finite set of zero radii in a compact disk and passing to the radius limit.
The final result has no regular-boundary or zero-free assumption. This
supplies the majorant needed for the alternative representation norm bound.
M9 remains active.

## M9 checkpoint: auxiliary Herglotz normalization and Wronskian bound

Gate `m9-herglotz-normalization-and-wronskian-bound` passed: 730
ModifiedCartan modules, 4763 build jobs, 6019 declarations including 5182
theorem declarations. Source scans are empty and the full recursive audit
contains only permitted dependencies. Frozen logs:
`verification/logs/m9-herglotz-normalization-and-wronskian-bound-*`.

`HerglotzNormalization.lean` constructs the actual analytic Herglotz
transform of the Euclidean log norm. The scalar supporting-functional
argument and the proved Poisson majorant show that its real part dominates
the log norm. Its value at zero is exactly T(256t)+log(||f(0)||), and
exp(-L)f(tz) has Euclidean norm at most one throughout D256.
`BoundedWronskian.lean` applies Cauchy's estimate to prove the explicit
dimension-only Wronskian bound on D64 and proves the exact Wronskian
transformation between L and the original paper gauge H. The auxiliary L
does not replace or change that gauge. M9 remains active; the upper-bound
assembly and the compactness transfer are still being checked.

## M9 checkpoint: exact representation norm and compactness transfer

Gate `m9-exact-representation-norm-and-compactness-transfer` passed: 732
ModifiedCartan modules, 4765 build jobs, 6026 declarations including 5189
theorem declarations. Source scans are empty and the full recursive audit
contains only the permitted dependencies. Frozen logs:
`verification/logs/m9-exact-representation-norm-and-compactness-transfer-*`.

`RepresentationBound.lean` proves the exact eventual bound in
`Paper.eq_representationbounds_norm` for the same H and monic P from Step 1.
The bound holds even on the closed disk of radius 32. It follows from an
explicit deterministic inequality, T(256t)<=Cs, Re H(0)/s->0, and s->infinity.
`CanonicalCompactness.lean` derives simultaneous compactness of actual
canonical coefficients from M8 under eventual hypotheses, with one
constant depending only on dimension and the norm-bound constant. Every
subsequence is handled by a proved deletion of its finite bad prefix.

Proved alternative to manuscript Steps 2--3 of `prop:representation`:
construct the analytic Herglotz transform L of the Euclidean log norm on
radius 256. The normalized vector exp(-L)f(tz) has norm <=1. Its Cauchy
Wronskian bound, the identity W=P exp((n+1)(H-L)), and nonnegative monic
unit-circle log means bound Re(H-L) on D48. Harnack gives factor five on
D32. The fixed constants and Re H(0) are absorbed using the certified
center limit. This proves exactly the required norm bound without needing
the manuscript's intermediate derivative-quotient mean estimate or
`eq:negativepart`; those intermediate mean assertions are not claimed as
proved by this gate. The full representation proposition is being assembled.
M9 remains active and replacement is still unproved.

## M9 checkpoint: complete rescaled representation proposition

Gate `m9-complete-representation-proposition` passed: 733 ModifiedCartan
modules, 4766 build jobs, 6027 declarations including 5190 theorem
declarations. Source scans are empty and the recursive audit reports only
Classical.choice, propext and Quot.sound. Frozen logs are
`verification/logs/m9-complete-representation-proposition-*`.

`RescaledRepresentation.lean` proves `Paper.prop_representation` with the
submitted hypotheses, the actual Step 1 gauges and divisor polynomials,
and every asserted conclusion. This includes the exact 5C+1 norm bound,
all center and degree limits, the radius-independent mean correction,
and simultaneous relative compactness for every subsequence of the actual
scaled canonical coefficients. The bound on limits is chosen before the
curve and sequences, so depends only on dimension and C. The proof uses
the Herglotz/Harnack alternative recorded at the preceding gate.

M9 remains active: `lem:replacement` is not yet proved. M10--M17 and the
main theorem and sharpness remain uncertified for the submitted paper.

## M9 checkpoint: small monic polynomial logarithms in local L1

Gate `m9-small-polynomial-log-l1` passed: 734 ModifiedCartan modules,
4767 build jobs, 6033 declarations including 5196 theorem declarations.
Both source scans are empty; the complete recursive audit contains only
the three permitted foundational dependencies. Frozen logs are
`verification/logs/m9-small-polynomial-log-l1-*`.

`SmallPolynomialLog.lean` proves `Paper.eq_small_polynomial_log`
(LaTeX `eq:small-polynomial-log`) on the whole complex plane. For monic
polynomials with roots of norm at most 64, a root-product estimate controls
the positive logarithm and the certified negative-area estimate controls
its negative part. The local integrals of the absolute logarithm divided
by s tend to zero whenever degree/s does. Polynomial zeros are included
through the already proved locally integrable representative. No extra
analytic or convergence assumption is introduced.

M9 remains active; the full replacement lemma still needs assembly and
the approximating Wronskian logarithm estimate.

## M9 checkpoint: area Jensen bound and strict separating radius

Gate `m9-area-jensen-and-strict-separating-radius` passed: 736 modules,
4769 build jobs, 6047 declarations including 5210 theorem declarations.
Source scans are empty and the full audit contains only permitted logical
dependencies. Frozen logs are
`verification/logs/m9-area-jensen-and-strict-separating-radius-*`.

`LogAreaJensen.lean` derives the disk-area integral formula from polar
integration and the proved circle Jensen inequality. For an entire h with
h(c) nonzero and log|h|<=M on the closed disk, it proves
integral_disk |log|h|| <= pi R^2 (2M-log|h(c)|), handling zeros by the
certified locally integrable logarithm. This is the analytic bound to be
applied to actual approximating Wronskians; their convergence is not yet
claimed at this gate.

`SeparatingRadius.lean` chooses eta in (8,10) in the finite gap immediately
above 8. Its strict inner/outer root sets are exactly the existing <=8 and
>8 sets, and no root lies on the separating circle. Additional prescribed
finite radii can be avoided simultaneously. This preserves the certified
M8 root-count and kernel bounds and supplies the strict radii requested
in `lem:replacement`. It is a Jensen/root-gap alternative to the original
Rouche construction; no Rouche equality is claimed. M9 remains active.

## M9 checkpoint: actual Taylor polynomials under eventual hypotheses

Gate `m9-eventual-taylor-and-preserved-jet-errors` passed. Frozen build,
placeholder scan and full declaration audit logs are retained under
`verification/logs/m9-eventual-taylor-and-preserved-jet-errors-*`.
The scans are empty and the audit permits only the three foundational
dependencies.

`EventualTaylor.lean` proves `Paper.eq_taylorerror_eventual`: one truncation
constant chosen before the sequences supplies the actual Taylor polynomial
at every index, eventual degree O(s), and the required exponential errors
for every derivative through order n+1. Analyticity and growth bounds are
needed only eventually, as supplied by the representation proposition.
`determinant_error_of_taylor_jets` proves the Wronskian and every signed
Cramer numerator error for those same jets, for every sufficiently large
prescribed A. This retains the data required by replacement instead of
choosing unrelated polynomial approximants. M9 remains active.

## M9 checkpoint: approximating Wronskian log and coefficient transfer

Gate `m9-approximating-wronskian-log-and-coefficient-transfer` passed; the
build, empty placeholder scans and complete permitted-dependency audit
are frozen as
`verification/logs/m9-approximating-wronskian-log-and-coefficient-transfer-*`.
The preceding Taylor gate contained 737 modules, 4770 build jobs, 6049
declarations and 5212 theorem declarations.

`PolynomialApproximationLog.lean` proves local L1 convergence of
log|R_n|/s_n to zero on D4 from the actual uniform approximation of the
monic P_n on D12, bounded roots of P_n, and degree(P_n)/s_n->0. A maximizing
point in D1 supplies |R_n(a_n)|>=1/2; root products give the uniform
upper bound log 2+degree(P_n) log 76. The area Jensen estimate controls
the absolute logarithm on D4 by
25 pi (3 log 2 + 2 degree(P_n) log 76). This fully proved direct integral
argument replaces the manuscript's measure-convergence/subharmonic-
compactness upgrade for this particular replacement assertion. It proves
the same local L1 limit without any extra assumption on R_n.

`EventualCoefficientComparison.lean` transfers the certified numerator
and gauge bounds across finite initial segments and proves Cramer
comparison for a specified polynomial sequence with proved determinant
errors. Final replacement will derive these estimates for the same
actual Taylor polynomials. M9 is still active until that assembly passes.

## M9 checkpoint: coordinated Taylor, root and coefficient data

Gate `m9-replacement-taylor-root-and-coefficient-data` passed. Full build,
empty scans and permitted-dependency recursive audit logs are frozen as
`verification/logs/m9-replacement-taylor-root-and-coefficient-data-*`.
The preceding logarithm/coefficient-transfer gate contained 739 modules,
4772 jobs, 6056 declarations and 5219 theorem declarations.

`ReplacementTaylorData.lean` constructs actual Taylor polynomials at the
prescribed precision A, for every A above an explicit proved threshold.
The same p_n has the coordinate and Wronskian degree bounds, exponential
jet errors, nonzero Wronskian, uniform comparison with P_n, and Cramer
coefficient convergence. No polynomial sequence is replaced during these
arguments.

`ReplacementRootData.lean` constructs the actual root lists with
multiplicity and strict separating radii in (8,10), avoiding roots of both
P_n and R_n. It proves the open-disk divisor count is o(s_n), the inner
root reciprocal sums tend to zero in L^(3/2) and locally in measure on D6,
and the outer sums divided by s_n are uniformly bounded there.

`ReplacementCoefficientData.lean` combines those specified polynomial
coefficients with the certified gauge comparison, proves the first
coefficient/s_n tends to zero, and proves the exact comparisons with
(t_n/s_n)^q Q_q(t_n z) for q=2,...,n+1. The full replacement lemma is being
assembled from these proved components; M9 is still active.

## M9 complete: representation and polynomial replacement

Gate `m9-complete-representation-and-replacement` passed. Its build,
empty source-placeholder scans and complete recursive declaration audit
are frozen in `verification/logs/m9-complete-representation-and-replacement-*`.
Both `Paper.prop_representation` and `Paper.lem_replacement` are kernel
checked; their printed dependencies contain only Classical.choice,
propext and Quot.sound. The preceding component gate contained 742 modules,
4775 build jobs, 6062 declarations and 5225 theorem declarations.

`PolynomialReplacement.lean` proves the submitted replacement lemma from
the original curve and scale hypotheses. For every sufficiently large A,
it constructs the actual Step 1 gauges, the same actual Taylor polynomials,
Wronskians, multiplicity-bearing root lists and strict separating radii.
`PolynomialReplacementData` records all proved conclusions: degree O(s),
exponential jet errors, inner zero count o(s), Wronskian log convergence in
local L1 on D4, inner L^(3/2) and measure limits and outer bounds on D6,
and first and higher canonical coefficient comparisons. It also retains
the representation center, norm and mean properties for these same gauges.
The structure is populated by a theorem, not assumed as an interface.

The three alternatives are fully proved and recorded above: Herglotz and
Harnack for the representation norm, Jensen plus a finite root gap for the
strict separating circles, and the direct area Jensen bound for the
replacement logarithm. No cited theorem is added as an assumption.

M9 is complete. M10 (Polya peaks and growth indices) is now the next active
milestone. M10--M17, the main theorem, and sharpness are not yet certified.

## M10 opened: exact joint growth indices

M9 completed with 743 modules, 4776 build jobs and an audit of 6090
declarations (5247 theorems). The M10 source/API inspection, exact initial
signatures and dependency DAG are in `work/M10-plan.md`. No matching
Drasin--Shea/Polya peak theorem was found in pinned mathlib. The next proof
block will define the literal joint-limit indices in EReal and derive
uniform ratio bounds outside their interval. Peak existence, endpoint
handling, and the index-collapse proposition remain proof obligations;
no external reference is assumed.

## M10 checkpoint: exact joint indices and one-sided powers

Gate `m10-joint-growth-indices-and-one-sided-powers` passed: 745 modules,
4778 jobs, 6098 declarations including 5252 theorem declarations. The
source scans are empty and the recursive audit contains only permitted
logical dependencies. Frozen logs:
`verification/logs/m10-joint-growth-indices-and-one-sided-powers-*`.

`StrongGrowthIndices.lean` defines the exact joint multiplier/base-radius
quotient and both EReal Drasin--Shea indices from `eq:strong-indices`.
It proves a uniform upper power bound for every exponent above the upper
index and a positive uniform lower power bound for every exponent below
the lower index. These follow directly from the actual limsup/liminf
and their order definitions, not an assumed power-bound interface.
`GrowthMultiplierBounds.lean` proves that monotonicity extends either
bound from large multipliers to every multiplier >=1, with proved new
constants. The final symmetric power lemma is being assembled. M10 is
active; peak existence and index collapse remain unproved.

## M10 checkpoint: symmetric power bound transfer

Gate `m10-symmetric-power-bound-transfer` passed. Frozen build, empty
source scans and permitted-dependency audit logs are retained as
`verification/logs/m10-symmetric-power-bound-transfer-*`.

`GrowthPowerSymmetry.lean` chooses one common constant C>=1 from the
separate lower and upper constants. Applying the multiplier estimate at
base tr with multiplier 1/t and inverting proves the exact min/max bounds
for t<1 as well. The proof uses positivity only for the divisions and
requires no continuity of T. `Paper.lem_power_bounds` is now being checked
from the joint-index definitions and these proved estimates. M10 remains
active; the full peak theorem and index collapse are still unproved.

## M10 checkpoint: complete uniform power bounds and discrete growth

Gate `m10-complete-uniform-power-bounds-and-discrete-growth` passed:
748 modules, 4781 build jobs, 6105 declarations including 5259 theorems.
Both source scans are empty; recursive dependency checking reports only
Classical.choice, propext and Quot.sound. Four logs are frozen under
`verification/logs/m10-complete-uniform-power-bounds-and-discrete-growth-*`.

`UniformPowerBounds.lean` proves the full submitted `lem:power-bounds`
as `ModifiedCartan.Paper.lem_power_bounds`, starting with the actual
joint-limit definitions and the original positivity, monotonicity and
coincident finite positive strong-index hypotheses. Positivity of the
multiplier follows from the two radius thresholds. The proof derives
all constants and covers multipliers on either side of one.
`NeighborGrowth.lean` proves the elementary neighboring-interval growth
dichotomy and its linear iteration consequences. This is a dependency
of the proposed peak proof, not yet a proof of peak existence.
M10 remains active; `lem:peaks` and `prop:indices` remain unproved.

## M10 checkpoint: converse bounds for the actual strong indices

Gate `m10-converse-strong-index-bounds` passed: 749 modules, 4782 jobs,
6107 declarations including 5261 theorems; empty source scans and only
permitted foundational dependencies. Frozen logs are retained with the
same gate prefix in `verification/logs`.

`StrongIndexPowerBounds.lean` proves that a uniform upper power estimate
with exponent p implies rho-star<=p, and a positive uniform lower estimate
implies p<=rho-substar. The proof works directly with the joint limsup and
liminf definitions in EReal and allows arbitrary real p. These converse
bounds will turn a strict slope gap into the contradiction needed for
peak existence. They do not assert that peaks have yet been constructed.

## M10 checkpoint: finite interval suprema without continuity

Gate `m10-tilted-interval-suprema` passed: 750 modules, 4783 jobs,
6112 declarations including 5265 theorems. Both scans are empty and
all recursive dependencies are permitted. Four logs are frozen with
this gate prefix in `verification/logs`.

`TiltedIntervalSup.lean` defines the supremum of u(x)-mu*x on [a,b]
for monotone u. It proves boundedness, pointwise domination, and the
endpoint upper estimate for mu>=0. If every point in the middle of
three consecutive intervals has a gain of at least d>0 within distance H,
the middle supremum plus d is no larger than the maximum of the two
neighboring suprema. No continuity or attained maximum is assumed.
The real-coordinate slope estimates and final peak theorem are pending.

## M10 checkpoint: uniform logarithmic slope bounds

Gate `m10-uniform-logarithmic-slope-bounds` passed: 752 modules,
4785 jobs, 6128 declarations including 5279 theorems. Empty scans and
recursive permitted-dependency audit are frozen with the gate prefix.

`TiltedBlockGrowth.lean` proves grid shifts, the neighboring gap on an
entire tail, and passage from increasing or decreasing discrete gaps to
uniform real-coordinate slopes mu+d/H or mu-d/H. Natural floors locate
arbitrary points; interval endpoint comparisons use only monotonicity.
`LogGrowthProfile.lean` proves that logarithmic slopes imply the
corresponding bounds on the actual joint-limit strong indices, by
exponentiating to uniform power bounds with explicit thresholds.
This completes the strict-slope contradiction ingredients of the
alternative peak construction. The full peak sequence is not yet certified.

## M10 checkpoint: approximate peaks and exact error conversion

Gate `m10-approximate-peaks-and-exact-error-conversion` passed:
754 modules, 4787 jobs, 6136 declarations including 5286 theorems.
Both scans and the recursive permitted-dependency audit passed; four
logs are frozen with this gate prefix in `verification/logs`.

`ApproximateGrowthPeaks.lean` proves an approximate logarithmic peak
beyond every prescribed threshold and on every prescribed finite window,
for every nonnegative finite mu in the closed strong-index interval.
Failure forces a strict slope gap in one direction and contradicts the
actual index bounds. This proof includes the finite endpoints.
`MultiplicativePeak.lean` exponentiates the additive error log(1+epsilon)
to precisely (1+epsilon)*t^mu and proves positivity, strict decrease,
convergence to zero and logarithmic windows for exp(-(n+1)). The exact
paper peak sequence is being assembled from these proved ingredients.

## M10 checkpoint: complete Polya peak theorem

Gate `m10-complete-polya-peaks` passed: 755 modules, 4788 build jobs,
6137 declarations including 5287 theorems. Both source scans are empty;
all recursive dependencies are Classical.choice, propext or Quot.sound.
Four frozen logs use the gate prefix in `verification/logs`.

`PolyaPeaks.lean` proves `ModifiedCartan.Paper.lem_peaks` in full for the
submitted `lem:peaks` and `eq:peak`. For a positive nondecreasing unbounded
T and every finite positive mu in the closed interval of the actual
joint-limit strong indices, it constructs positive r_n tending to infinity
and positive strictly decreasing epsilon_n tending to zero, with the
exact (1+epsilon_n)*t^mu inequality for every index and every multiplier
in [epsilon_n,epsilon_n^(-1)]. Finite positive endpoints are included.

Alternative proof, now kernel checked: in logarithmic coordinates take
suprema of log T(exp x)-mu*x on consecutive finite intervals. Missing
approximate peaks force a strict neighboring gap. A discrete dichotomy
and monotonic interpolation give a uniform slope strictly above or below
mu on a tail. Exponentiating contradicts membership in the closed strong
index interval. Select windows n+1, errors log(1+exp(-(n+1))), and centers
at least n, then exponentiate. This proves the exact cited theorem here;
no Drasin--Shea or Eremenko statement is imported as an assumption, and
no continuity of T is added. Unboundedness is retained in the paper
signature although this construction proves the asserted implication
without using it separately.

M10 remains active. The ordinary-order comparison, characteristic growth
facts and the curve-specific index-collapse proposition remain to be proved.

## M10 checkpoint: ordinary orders and affine logarithmic bounds

Gate `m10-ordinary-orders-and-affine-log-bounds` passed: 757 modules,
4790 jobs, 6148 declarations including 5295 theorems. Empty scans and
permitted-dependency audit logs are frozen with the gate prefix.

`OrdinaryGrowthOrders.lean` defines the literal logarithmic quotient,
upper order and lower order for T, and proves that at the manuscript's
characteristic these definitions are exactly the existing order and
lowerOrder. Affine upper and lower estimates on log T give the ordinary
order bounds by dividing by log r and taking limits in EReal.
`UniformPowerLogBounds.lean` derives those affine estimates from uniform
power bounds at a fixed positive base radius. Monotonicity supplies the
uniform exponent-zero lower bound, proving nonnegativity of the lower
strong index. The complete general index chain is being assembled.

## M10 checkpoint: general index chain and characteristic monotonicity

Gate `m10-general-index-chain-and-characteristic-monotonicity` passed:
759 modules, 4792 jobs, 6152 declarations including 5299 theorems.
The empty source scans and recursive permitted-dependency audit passed;
four gate-prefixed logs are frozen in `verification/logs`.

`IndexOrderBounds.lean` proves the full chain
0<=lowerStrong<=lowerOrdinary<=upperOrdinary<=upperStrong for a positive
nondecreasing T, using the literal joint and ordinary definitions.
`CharacteristicMonotone.lean` proves monotonicity of the actual Euclidean
characteristic on positive radii. The proof averages its Herglotz
majorant on an inner circle and uses the harmonic mean identity.
The strict positivity prerequisite for transcendental curves is now
being proved; the exact curve-specific comparison is not yet certified.

## M10 checkpoint: zero characteristic and strict positivity

Gate `m10-characteristic-zero-and-strict-positivity` passed: 760 modules,
4793 jobs, 6156 declarations including 5303 theorems. Both scans are
empty and the recursive audit permits all dependencies. Four logs are
frozen with this gate prefix in `verification/logs`.

`CharacteristicZero.lean` proves that zero Euclidean characteristic at
any positive radius forces all projective coordinates to be constant.
Normalize by the actual Herglotz function, apply the maximum-modulus
principle in the finite L2 product, and extend coordinate proportionality
by analytic uniqueness. Reducedness then gives an entire nowhere-zero
scalar factor times constant polynomials. Consequently transcendental
curves have strictly positive characteristic on all positive radii.
The proof derives positivity from the original curve assumptions.

## M10 checkpoint: fixed multiplier estimates along peaks

Gate `m10-fixed-multiplier-peak-bounds` passed: 761 modules, 4794 jobs,
6160 declarations including 5307 theorems. The source scans are empty;
recursive dependencies are permitted. Four logs are frozen with the
same gate prefix in `verification/logs`.

`PeakScaleBounds.lean` proves divergence of a positive-radius monotone
unbounded function, eventual inclusion of every fixed positive multiplier
in the shrinking-error peak windows, and the resulting eventual bound
T(a*r_n)<=2*a^mu*T(r_n). It also proves the manuscript's stated EReal
limsup bound for the exact ratio, with no exponent error. Curve-specific
normalization and index collapse remain pending.

## M10 checkpoint: exact characteristic index-order bounds

Gate `m10-exact-characteristic-index-order-bounds` passed: 762 modules,
4795 jobs, 6163 declarations including 5310 theorems. Empty scans and
recursive permitted dependencies are certified; four gate-prefixed logs
are frozen in `verification/logs`.

`CharacteristicIndices.lean` proves `Paper.eq_index_order_bounds` for a
nonconstant holomorphic curve, expressing nonconstancy by unequal
projective values via coordinate cross-products with the value at zero.
It also proves `Paper.eq_index_order_bounds_of_transcendental` directly
from transcendence. Both prove exactly
0<=rho-substar<=lowerOrder<=order<=rho-star for the Euclidean
characteristic and literal ordinary orders. Positivity and monotonicity
are proved dependencies, not additional paper assumptions.
M10 remains active; `prop:indices` still requires the coefficient limit
and nonvanishing arguments.

## M10 checkpoint: scalar Jensen lower bounds

Gate `m10-scalar-jensen-logarithmic-lower-bounds` passed: 764 modules,
4797 jobs, 6171 declarations including 5318 theorems. Both scans are
empty and recursive dependencies are permitted. Four logs are frozen
with this gate prefix in `verification/logs`.

`ZeroJensenLowerBound.lean` proves that a nontrivial entire scalar
function vanishing at zero has zero counting at least log r for r>=1,
and hence the corresponding lower circle-mean estimate, with its actual
trailing coefficient. `ScalarCurveBounds.lean` constructs such a scalar
linear combination from a transcendental curve and bounds its norm by a
constant times the Euclidean norm. It also proves the upper circle-mean
comparison, treating scalar zeros through codiscrete equality.
These are proved ingredients of the curve's logarithmic lower bound;
the peak normalization shortcut is being connected to them.

## M10 checkpoint: characteristic growth and peak logarithmic normalization

Gate `m10-characteristic-growth-and-peak-log-normalization` passed:
766 modules, 4799 jobs, 6176 declarations including 5323 theorems.
Empty source scans and the recursive permitted-dependency audit passed;
four gate-prefixed logs are frozen in `verification/logs`.

`CharacteristicLogLower.lean` proves T(r)>=log(r)-C for all r>=1 from
the actual scalar construction and Jensen comparison, and derives
T(r)->infinity and unboundedness for transcendental curves.
`PeakLogNormalization.lean` proves that every positive-order peak sequence
for a function with this logarithmic lower bound satisfies
log(r_n)/T(r_n)->0.

Alternative to the manuscript's cited global transcendence growth fact,
now kernel checked: for every fixed a>0, the peak bound and logarithmic
lower bound give log(r_n)<=2*a^mu*T(r_n)+C-log(a) eventually. Divide by
T(r_n), which diverges, then choose a with arbitrarily small a^mu.
This proves exactly the normalization needed at the positive peaks.
It does not assert a global rationality criterion or a global little-o
statement that has not been proved. The manuscript's remaining scale
hypotheses are being assembled, with a constant independent of R.

## M10 checkpoint: all positive-peak scale hypotheses

Gate `m10-all-positive-peak-scale-hypotheses` passed: 767 modules,
4800 jobs, 6178 declarations including 5325 theorems. Both scans are
empty and recursive dependencies are permitted. Four gate-prefixed
logs are frozen in `verification/logs`.

`CharacteristicPeaks.lean` constructs characteristic peaks together with
S_n=T(r_n)->infinity and log(r_n)/S_n->0. For every fixed R>0 it then
proves all five actual M9 scale inputs with t_n=R*r_n and s_n=R^mu*S_n:
divergence of both scales, the logarithmic normalization, the eventual
characteristic bound with constant 2*256^mu independent of R, and the
Wronskian counting ratio tending to zero. The latter is derived by
composing the original SmallRamification relation and the proved
characteristic bound. These conclusions are not assumed interfaces.
Coordinate normalization and the entire coefficient limit construction
are the next dependencies of `prop:indices`; M10 is still active.

## M10 checkpoint: finite dimensional isometry transport

Gate `m10-isometry-vector-transport` passed: 768 modules, 4801 build jobs,
6179 declarations including 5326 theorems. Both project scans are empty;
the only recursive logical dependencies are the three permitted foundational
principles. All four gate logs are frozen in `verification/logs`.

`IsometryVectorTransport.lean` proves that a nonzero vector can be sent
to any vector of the same norm by a complex-linear isometry in finite
dimension. The proof builds an isometry on its one-dimensional span and
uses the inspected mathlib extension theorem. This supplies the linear
algebra needed for the manuscript's fixed Euclidean coordinate normalization.
M10 remains active; the index classification is not yet certified.

## M10 checkpoint: exact Euclidean matrix normalization

Gate `m10-euclidean-coordinate-matrix` passed: 769 modules, 4802 build jobs,
6181 declarations including 5328 theorems. All four audit logs are frozen.
`EuclideanCoordinateNormalization.lean` constructs an invertible constant
complex matrix preserving the exact Euclidean norm, and sending any given
nonzero vector to a vector with every coordinate nonzero. It is obtained
from the proved isometry transport in the finite L2 product. No unproved
unitary-normalization assertion is used. M10 remains active.

## M10 checkpoint: coordinate normalization with all invariances

Gate `m10-curve-coordinate-invariances` passed: 770 modules, 4803 jobs,
6188 declarations including 5335 theorems. Both scans are empty and all
recursive logical dependencies are permitted. All four logs are frozen.
`exists_normalized_curve` constructs a curve with every origin coordinate
nonzero and proves equality of the exact Euclidean characteristic,
ramification function, and every canonical coefficient. Linear nondegeneracy,
transcendence, small ramification and finite lower order are equivalent
for the original and normalized curves. No extra hypothesis on the original
curve's origin coordinates is needed for the M10 index proposition.

## M10 checkpoint: compatibility under fixed dilation

Gate `m10-measure-dilation-compatibility` passed; the four frozen logs
record the successful build, empty project scans, and complete permitted
dependency audit. `LocalMeasureConvergence.dilation_compatible` proves
pointwise agreement of continuous local limits on overlapping open sets
under any fixed nonzero real dilation and exact scalar relation. Two
AE subsequences and the inspected Haar-measure dilation theorem prove
the measure step; continuity then gives pointwise equality. This is a
proved prerequisite for comparing different positive peak scales. M10
is still active.

## M10 checkpoint: uniform compactness at every peak scale

Gate `m10-peak-coefficient-compactness` passed. The four frozen logs show
successful build, empty scans and only permitted recursive dependencies.
`peak_coefficient_relative_compactness` now derives from the original
curve hypotheses a constant K independent of R>0 and analytic local
coefficient limits on D4, bounded by K on D1, after a further subsequence
of every subsequence. It uses the proved exact coordinate invariances and
actual characteristic peak scale hypotheses. The origin-coordinate
condition is discharged, not added to the original assumptions.
M10 remains active; nonvanishing and index collapse remain to be proved.

## M10 checkpoint: exact rescaling and local Cauchy quantization

Gate `m10-local-cauchy-quantization` passed; the four frozen logs certify
the full build, empty scans and permitted recursive dependencies.
`PeakRescaling.lean` proves the exact equation `eq:peak-rescaling-relation`
for every R>0 (even zero values of r or S are handled algebraically).
`AllScaleCauchyBounds.lean` proves that a nonzero analytic function on D4
whose dilations have uniformly bounded analytic models on D1 must have
integral weight. A nonzero derivative is obtained from the actual Taylor
series, Cauchy's inequality bounds it by C_m*R^(p-m) at every R>0, and an
explicit exponential choice of R forces p=m. These are proved lemmas;
existence and nonvanishing of the paper's limits are separate obligations.

Alternative proof component, now checked: the Cauchy step needs only germ
identities at zero for separate scale models. A single entire limit is not
necessary for this step of the index conclusion. The corresponding models
are being assembled from actual M9 compactness; nonvanishing is still open.
M10 and the full paper objective remain active.

## M10 checkpoint: actual local peak scale models

Gate `m10-actual-peak-scale-models` passed, with all four logs frozen.
`peak_coefficient_limit_scale_models` constructs one common subsequence
and analytic limits a_i on D4 from the original curve and actual peaks.
For every R>0 and each i, it then constructs an analytic b_R on D4,
uniformly bounded by the same K on D1, and proves the exact germ identity
at zero: a_i(R*z)=R^((n+1-i)*(mu-1))*b_R(z).

Checked divergence from the paper's Step 1 in `prop:indices`: no global
entire limit is needed for index quantization. Extract the R=1 limit;
for each fixed R separately extract a further subsequence. The proved
measure-dilation compatibility gives equality on the open overlapping
domains and hence the germ identity needed by the proved Cauchy lemma.
All these models are now derived, rather than assumed. Nonvanishing is
still a required dependency; neither `prop:indices` nor M10 is complete.

## M10 checkpoint: admissible weight and local area Jensen

Gate `m10-admissible-weight-and-local-jensen` passed. All four frozen logs
confirm the full build, empty scans and permitted logical dependencies.
`PeakScaleQuantization.lean` translates the proved integral coefficient
weight into exactly FewInflection.AdmissibleOrder n mu, including 2<=q<=n+1.
It remains a lemma for a nonzero scale model; nonvanishing of the actual
models is not assumed in a claimed final proposition.
`AnalyticLogDiskMean.lean` proves the scalar circle and disk submean
inequalities under local analyticity on a closed disk and a nonzero center.
The proof uses the inspected local Jensen formula and the already proved
polar integral identity, with a measurable extension only for that identity.
M10 remains active.

## M10 checkpoint: analytic logarithms satisfy the actual submean definition

Gate `m10-analytic-log-subharmonic-bridge` passed, and all four logs are frozen.
`AnalyticLogSubharmonic.lean` proves continuity of the normalized extended
logarithm and proves `IsSubharmonicOn` for a nontrivial analytic function on
an open connected domain with positive normalization. The proof preserves
negative infinity at zeros, uses actual AE nonvanishing and local logarithm
integrability, and derives the disk-submean condition from the newly proved
local Jensen inequality. Thus the intended M6 application now has its
subharmonic hypothesis proved rather than inferred from a textbook citation.
The compactness application and nonvanishing argument continue within M10.

## M10 checkpoint: common finite subsequence extraction

Gate `m10-finite-subsequence-extraction` passed, with all four logs frozen.
`finite_subsequence_extraction` proves by induction that finitely many
subsequence-stable properties, each extractable from every subsequence,
can hold simultaneously on a common strictly increasing subsequence.
This supplies the finite combinatorial step for the coordinate logarithm
limits. No compactness assertion is built into an unproved interface.
M10 remains active.

## M10 checkpoint: normalized log compactness and zero-gradient tests

Gate `m10-normalized-log-compactness-and-zero-tests` passed. Four frozen
logs certify the full build, empty scans and permitted dependencies.
`NormalizedLogCompactness.lean` applies M6 to the proved analytic subharmonic
logarithms, and uses the normalized origin values tending to zero to rule
out collapse. It constructs an actual local L1 limit after a strict
subsequence. `WeakGradientZeroTests.lean` proves that an AE zero complex
weak gradient can be replaced by zero, and that it annihilates compact
smooth test derivatives in every real direction. These are steps toward
the nonvanishing argument; AE constancy is not yet asserted. M10 is active.

## M10 checkpoint: simultaneous coordinate logarithm limits

Gate `m10-simultaneous-eventual-log-compactness` passed; all four logs
are frozen. `FiniteLogCompactness.lean` constructs a common strict
subsequence with local L1 limits for every coordinate of a finite family.
Its eventual version removes a finite prefix and proves positivity,
analyticity, origin nonvanishing and the exponential bounds at every
retained index. The original hypotheses require only the eventual bounds
and normalized center limits supplied by M9. This is actual compactness,
not a condition added to a final theorem. M10 remains active.

## M10 checkpoint: smoothing a zero weak gradient

Gate `m10-weak-gradient-smoothing` passed. Its four frozen logs record
the complete successful build, empty scans and permitted dependencies.
`HasWeakComplexGradient.fderiv_convolution_eq_zero` proves that smooth
convolutions have zero derivative wherever their translated test kernels
are supported in the weak-gradient domain. The proof checks the derivative
of the reflected kernel, compact support, equality with an integrable
extension, and the directional weak test identity. Local AE constancy
will follow from this lemma and shrinking bump convolution limits.
M10 remains active.

## M10 checkpoint: constant smooth convolutions on D3

Gate `m10-weak-zero-cutoff-constant-smoothing` passed: 4817 build jobs,
6233 audited declarations including 5379 theorem declarations, empty
placeholder scans, and only the three permitted logical dependencies.
`WeakZeroCutoff.lean` constructs the integrable cutoff on the closed disk
of radius 7/2 and proves that every smooth convolution with kernel support
in the disk of radius 1/4 is constant on D3. Its proof uses the checked
zero derivative theorem on a connected open disk. Shrinking these kernels
will identify the original function almost everywhere. M10 remains active.

## M10 checkpoint: zero weak gradient gives an actual constant

Gate `m10-weak-gradient-constancy-and-measure-uniqueness` passed and its
four logs are frozen. `WeakGradientConstancy.lean` proves that an AE zero
weak complex gradient on D4 makes the original function AE constant on D3.
The construction uses shrinking smooth kernels, their proved constant
convolutions, and mathlib's Lebesgue differentiation theorem. No regularity
or constancy hypothesis was added. `LocalMeasureUniqueness.lean` proves
AE uniqueness of local measure limits and transport across AE equal limits.
These certify the constancy step required in `prop:indices`; the normalized
ODE limit and the nonvanishing contradiction remain. M10 is active.

## M10 checkpoint: the normalized ODE forces zero gradients

Gate `m10-normalized-fundamental-equation-limit` passed and all four logs
are frozen. `normalized_fundamental_equation` proves the exact identity
`eq:normalized-peak-equation`, including total division at coordinate zeros.
`normalized_ode_weak_gradient_zero` applies the certified logarithmic
 derivative limit to every derivative order, proves the required local
measurability, passes finite products and sums to their measure limits,
and uses the AE nonzero Wronskian locus to identify the equation. It proves
the gradient vanishes AE when the normalized fundamental coefficients do.
The actual coefficient transfer and the nonvanishing contradiction are
still required before `prop:indices` can be certified. M10 remains active.

## M10 checkpoint: circle means, disk means and uniform log bounds

Gate `m10-disk-means-and-logarithm-uniform-bounds` passed and all four logs
are frozen. `DiskCircleUpper.lean` proves the local circle-to-disk upper
bound and convergence of disk means for a constant local L1 limit.
`NormalizedLogUpper.lean` derives an eventual exponential bound on the
closed unit disk from a nonpositive constant normalized logarithm limit,
using the previously certified M6 upper-bound theorem and the analytic
subharmonic-log bridge. The final nonvanishing contradiction is still
being assembled; these are proved dependencies, not a claim of completion.
M10 remains active.

## M10 checkpoint: actual rescaled coefficient transfer

Gate `m10-actual-rescaled-coefficient-transfer` passed; all four logs are
frozen. `RescaledZeroCoefficients.lean` transfers zero measure limits of
the original canonical peak coefficients to every normalized fundamental
coefficient of the actual rescaled representation. It uses the proved
canonical identification and eventual gauge comparison, and handles the
last coefficient by its proved vanishing identity. A second lemma proves
the AE nonzero Wronskian locus from the actual monic polynomial identity.
Both statements retain the exact eventual hypotheses supplied by M9.
M10 remains active; the nonvanishing argument is not yet certified.

## M10 checkpoint: nonpositive constants and the mean contradiction

Gate `m10-peak-constant-sign-and-mean-contradiction` passed: 4827 jobs,
6255 audited declarations including 5400 theorem declarations, empty scans,
and only the three permitted logical dependencies. All four logs are frozen.
`peak_coordinate_constant_nonpos` combines the exact peak inequality,
monotonicity, and the M9 circle mean identity on arbitrarily small disks to
prove every constant coordinate logarithm limit is nonpositive.
`representation_mean_contradicts_nonpositive_constants` uses the proved
unit-disk uniform bounds and the mean identity at radius one to derive
1<=1/2. The complete assembly from the original curve is the next gate.
M10 remains active.

## M10 checkpoint: unconditional peak nonvanishing and interval collapse

Gate `m10-peak-nonvanishing-and-interval-collapse` passed: 4829 build jobs,
6260 audited declarations including 5405 theorem declarations, empty source
scans, and only Classical.choice, propext and Quot.sound. All four logs are frozen.
`peak_coefficient_limit_nonzero` now proves the nonvanishing conclusion for
an original curve and actual positive-order peaks. Its statement imposes no
coordinate-origin normalization, nonvanishing-limit assumption, or extra
regularity hypothesis. The proof constructs and normalizes the representation,
extracts simultaneous coordinate L1 limits, proves the ODE gradients vanish
under the negated conclusion, and derives the mean contradiction.

Certified proof divergence for Step 2 of `prop:indices`: instead of forming
an L1 limit of the vector norm and the manuscript's annular identity, prove
each coordinate constant is <=0 by small-disk means, then apply the certified
M6 local uniform upper bound on the unit disk and use the exact radius-one
mean identity. The resulting contradiction is 1<=1/2.

Certified proof divergence for Step 3: `admissible_interval_eq` uses the
proved density of irrational real numbers. All admissible orders are rational,
so a nondegenerate interval of positive admissible orders is impossible.
This proves the needed interval collapse without a local-finiteness detour.
`prop:indices` is being assembled; M10 remains active until its final gate.

## M10 complete: exact Polya peaks and identification of all four indices

Final gate `m10-complete-polya-peaks-and-growth-indices` passed: 4830 build
jobs, 6262 audited declarations including 5407 theorem declarations. Both
project scans are empty, and the complete imported-declaration audit reports
only Classical.choice, propext and Quot.sound. Four immutable logs are frozen.
`ModifiedCartan.Paper.prop_indices` in `ModifiedCartan/Indices.lean` proves
`prop:indices` and `eq:indices-collapse` from the submitted assumptions:
transcendence, linear nondegeneracy, finite lower order, and small ramification.
The two joint strong indices, literal lower order, and literal order are equal
to a finite real number which is zero or an admissible order. No nonvanishing
or normalization assumption occurs in this final statement. Together with
the already certified `Paper.lem_peaks` and `Paper.lem_power_bounds`, this
completes M10. The main theorem, small-order classification, later regular
variation steps, and sharpness remain unproved. M11 is now the active milestone.

## M11 checkpoint: Tonelli and actual envelope radii

Gate `m11-tonelli-and-envelope-radii` passed: 4832 build jobs, 6265 audited
declarations including 5410 theorem declarations, empty source scans and only
the three permitted logical principles. Four logs are frozen. `Paper.lem_Tonelli`
proves the exact submitted lemma, including both measurability conclusions
and both integral identities without imposing finite integrals. It directly
uses the inspected mathlib theorems. `EnvelopeRadii.lean` constructs tail
maximizers and an actual sequence tending to infinity with the pointwise
power envelope. The complete integral envelope lemma and the remaining M11
results are still unproved. M11 is active; later stages remain uncertified.

## M11 checkpoint: integrable envelope kernel

Gate `m11-integrable-envelope-kernel` passed: 4833 build jobs, 6273 audited
declarations including 5416 theorem declarations, empty source scans and only
the three permitted logical principles. Four logs are frozen.
`EnvelopeKernel.lean` defines the literal kernel and integral constant in
`lem:envelope`. It proves nonnegativity, continuity, an integrable power tail
for every 0 <= alpha < 1, and monotonicity with respect to the exponent.
The alpha=0 endpoint is included for the exact constant and limit proof.
The full envelope lemma remains in progress. M11 remains active.
## M11 checkpoint: exact envelope integral and constant limit

Gate `m11-envelope-integral-and-constant-limit` passed: 4835 build jobs,
6288 audited declarations including 5431 theorem declarations, empty source
scans and only the three permitted logical principles. Four logs are frozen.
`EnvelopeIntegration.lean` proves the change of variables and both actual
integrability and the bound at each power-envelope radius.
`EnvelopeConstantLimit.lean` proves I_0=1 by the fundamental theorem of
calculus, I_alpha>=1, and I_alpha tends to 1 as alpha decreases to zero by
dominated convergence. These follow the submitted proof. Assembly of the
complete paper lemma is in progress. M11 remains active.
## M11 checkpoint: complete submitted envelope lemma

Gate `m11-exact-paper-envelope` passed: 4836 build jobs, 6289 audited
declarations including 5432 theorem declarations, empty source scans and
only the three permitted logical principles. Four logs are frozen.
`ModifiedCartan.Paper.lem_envelope` in `ModifiedCartan/Envelope.lean`
proves the exact submitted `lem:envelope` and `eq:envelope`: it constructs
positive radii tending to infinity with positive H values, proves actual
integrability and the inequality at every radius, and includes finiteness
of I_alpha and its limit one at zero. No extra mathematical hypothesis
is imposed. M11 remains active; the entire majorant, coordinate construction,
small-order classification and zero-order ratio remain unproved.
## M11 checkpoint: literal maximum modulus

Gate `m11-maximum-modulus` passed: 4837 build jobs, 6299 audited declarations
including 5441 theorem declarations, empty source scans and only the three
permitted logical principles. Four logs are frozen. `MaximumModulus.lean`
defines the actual supremum of |f| on a closed disk and proves attainment,
pointwise bounds, monotonicity and continuity in the nonnegative radius.
For entire functions it proves attainment on the boundary circle and exact
equality to the circle supremum, using the inspected maximum modulus theorem.
The literal scalar order and its growth consequences are in progress.
M11 remains active; no later milestone is certified by this checkpoint.
## M11 checkpoint: literal entire order and kernel primitive

Gate `m11-literal-entire-order-and-kernel-primitive` passed: 4839 build jobs,
6318 audited declarations including 5458 theorem declarations, empty source
scans and only the three permitted logical principles. Four logs are frozen.
`EntireOrder.lean` defines the exact double-positive-logarithm scalar order,
proves nonnegativity and order zero for constants, and derives the eventual
power bound, little-o estimate, and a global power bound on r>=1 from a
strict order inequality. `RootKernelPrimitive.lean` proves an explicit
primitive, its zero limit at infinity, and the integral and integrability
above the root radius. These are lower dependencies of the original M11
statements; the whole milestone remains active and incomplete.
## M11 checkpoint: root kernel and uniform Taylor bounds

Gate `m11-root-kernel-and-uniform-taylor-bounds` passed: 4841 build jobs,
6323 audited declarations including 5463 theorem declarations, empty source
scans and only the three permitted logical principles. Four logs are frozen.
`RootKernel.lean` proves the literal `eq:kernel-identity` on the entire
positive axis, including integrability. `EntireTaylorBounds.lean` proves
M(r,p_N)<=2M(2r,f) and the uniform derivative estimate
|p_N^(k)(z)|<=k!*2M(4r,f)/r^k for |z|<=r. Both constants are independent of N.
These are the first analytic steps of `lem:entire-majorant`; that complete
lemma and the remaining M11 results are still unproved. M11 is active.
## M11 checkpoint: system maximum, actual zero copies and initial jets

Gate `m11-system-maximum-zero-copies-and-initial-jets` passed: 4844 build jobs,
6353 audited declarations including 5490 theorem declarations, empty source
scans and only the three permitted logical principles. Four logs are frozen.
`SystemMaximum.lean` defines literal H_y and proves its continuity,
monotonicity, nonnegativity, little-o growth, and H_y(r)>=log r from the
normalized first derivative. `EntireZeroCopies.lean` defines the actual
analytic-multiplicity index, proves every copy is a zero and that the index
is countable, and identifies multiplicities with the global divisor.
`EntireTaylorJets.lean` proves exact preservation of the initial jets and
W_N(0)=1. M11 remains active; these do not certify the entire majorant or
small-order classification.
## M11 checkpoint: Wronskian growth and exact zero counts

Gate `m11-wronskian-growth-and-actual-zero-counts` passed: 4847 build jobs,
6373 audited declarations including 5508 theorem declarations, empty source
scans and only the three permitted logical principles. Four logs are frozen.
`TaylorWronskianGrowth.lean` constructs a common exponent and uniform
logarithmic growth bounds for every Taylor Wronskian and the actual entire
Wronskian. `EntireCountGrowth.lean` derives the actual unweighted zero-count
power bound by the inspected Jensen theorem. `ZeroCopiesCount.lean` proves
finiteness of repeated roots in each closed disk and exact equality of their
cardinality with the divisor count, including the bound for every finite
subfamily. Reciprocal-root summability and the entire majorant are in progress.
M11 remains active; later milestones remain uncertified.
## M11 checkpoint: finite reciprocal-tail integral

Gate `m11-finite-reciprocal-tail-integral` passed: 4848 build jobs,
6376 audited declarations including 5511 theorem declarations, empty source
scans and only the three permitted logical principles. Four logs are frozen.
`ReciprocalTailIntegral.lean` proves the cutoff identity integral_a^infinity
t^-2=1/a and the finite-root tail estimate C/(1-sigma)*R^(sigma-1) from a
power counting bound. Every integral used is proved integrable. Passage to
the actual repeated zero divisor and infinite sums is in progress.
M11 remains active; no later result is certified here.
## M11 checkpoint: actual reciprocal-root sums

Gate `m11-actual-reciprocal-roots` passed: 4849 build jobs, 6378 audited
project declarations including 5513 theorem declarations; both source scans
are empty and the only logical dependencies are Classical.choice, propext,
and Quot.sound. Four logs are frozen. `ReciprocalRoots.lean` proves the
summability and quantitative infinite tail bound for the actual repeated
zero divisor from its power counting bound, using finite closed-disk root
copies and the certified integral estimate. The wrapper deriving the power
counting bound from the normalized entire system is being checked. The
product-majorant assertion and the later M11 paper results remain unproved.

## M11 checkpoint: normalized Wronskian reciprocal roots

Gate `m11-normalized-wronskian-reciprocal-roots` passed: 4850 build jobs,
6381 project declarations including 5516 theorems; empty scans and only the
three permitted logical dependencies. Four logs are frozen.
`WronskianReciprocalRoots.lean` proves from exactly the normalized entire
system and component orders less than one that the actual Wronskian's
reciprocal-root sum converges. It also proves the quantitative tail bound
uniformly for every Taylor truncation retaining the initial jets. This
certifies Steps 1 and 2 of `lem:entire-majorant`; Step 3 and the full product
bound are still in progress. No later milestone is certified.

## M11 checkpoint: zero-copy counting and the convergent root product

Gate `m11-zero-copy-counting-and-root-product` passed: 4857 build jobs,
6394 project declarations including 5528 theorems; empty scans and only the
three permitted logical dependencies. Four logs are frozen.
`ZeroCopyLogCounting.lean` proves that the actual logarithmic counting
function equals the sum over analytic zero copies when the center is not a
zero. `RootMajorantProduct.lean` defines the literal product, proves its
convergence and positivity from the now-derived reciprocal-root summability,
and identifies its logarithm with the summable logarithms of its factors.
`IntegrableSum.lean` proves the required real-series integrability from
Tonelli and a finite sum of integrals of norms. The full convolution identity
is being checked; the entire component majorant remains unproved. M11 active.

## M11 checkpoint: actual root-product convolution identity

Gate `m11-root-product-convolution-identity` passed: 4858 build jobs,
6396 declarations including 5530 theorems; empty source scans and only
Classical.choice, propext, Quot.sound. Four logs are frozen.
`RootConvolution.lean` proves actual integrability of N_f(t)/(r+t)^2 and
log(rootMajorantProduct f r)=r*integral_0^infinity N_f(t)/(r+t)^2, first for
an entire function with summable reciprocal roots and then from exactly
the manuscript's normalized-system hypotheses. The proof identifies actual
analytic multiplicities, proves countability, and uses Tonelli with a finite
sum of integrals of norms. This is the equality used in `cor:convolution`;
that corollary's H_y inequality still requires the entire component majorant.
M11 remains active, and no later result is certified by this checkpoint.

## M11 checkpoint: Taylor Wronskians and Jensen limits

Gate `m11-taylor-wronskian-and-jensen-limits` passed: 4861 build jobs,
6404 declarations including 5538 theorems; empty source scans and only the
three permitted logical dependencies. Four logs are frozen.
`WronskianUniform.lean` proves local uniform convergence of the Taylor
Wronskians by finite determinant expansion and derivative convergence.
`PolynomialNormalizedMajorant.lean` constructs the actual basis from its
identity jets and supplies an actual root factorization and the polynomial
majorant. `LogCountingLimit.lean` proves bounded logarithms on compact sets
avoiding limit zeros, and convergence of actual Jensen counting functions
on those circles. The intended alternative to individual Rouche root
matching is to pass through the Jensen counting integrals; the needed
almost-everywhere and dominated-integral steps are still in progress.
The whole entire-majorant lemma is not yet certified. M11 remains active.

## M11 checkpoint: almost-everywhere counting and integrable envelopes

Gate `m11-almost-everywhere-counting-and-integrable-envelope` passed:
4864 build jobs, 6419 declarations including 5553 theorems; empty scans and
only the three permitted logical dependencies. Four logs are frozen.
`ExceptionalRadii.lean` proves countability of the actual entire zero set,
almost-everywhere zero-free circles, and almost-everywhere convergence of
Taylor-Wronskian logarithmic counts. `CountingPowerEnvelope.lean` proves
measurability, nonnegativity, the Jensen power envelope, and integrability
of max(1,t^sigma)/(r+t)^2 for 0<=sigma<1. `PolynomialRootLogCounting.lean`
identifies a finite root factorization with the analytic-divisor logarithmic
count and proves its exact kernel integral. The dominated integral passage
and the whole entire-majorant theorem are still in progress. M11 active.

## M11 checkpoint: dominated counting-integral limit

Gate `m11-dominated-counting-integral-limit` passed: 4866 build jobs,
6421 declarations including 5555 theorems; empty source scans and only the
three permitted logical dependencies. Four logs are frozen.
`WronskianCountingIntegralLimit.lean` proves convergence of the actual
Taylor-Wronskian counting integrals, deriving the integrable domination from
the component orders. `PolynomialIntegralMajorant.lean` puts the certified
normalized polynomial bound into exactly that integral form. The final
passage to entire components and the manuscript's whole product-majorant
statement are being checked. M11 remains active.

## M11 checkpoint: exact entire majorant

Gate `m11-exact-entire-majorant` passed: 4870 build jobs, 6434 audited
project declarations including 5567 theorems; empty source scans and only
Classical.choice, propext, Quot.sound. Four logs are frozen.
`Paper.lem_entire_majorant` is now certified in `EntireMajorant.lean`:
from exactly the component orders below one and identity initial jets,
it proves reciprocal summability of the actual repeated Wronskian zeros
and the exact product majorant for every component and every complex point.
The zero point is handled directly by the jets. `GenusZeroProduct.lean`
also defines the exponent-independent actual canonical product and proves
its convergence on compact sets, entire holomorphy, normalization at zero,
and norm bound. Its multiplicity/gauge properties are still in progress.

Recorded proof divergence for `lem:entire-majorant`, Step 3: the proof uses
Jensen counting integrals in place of individual Rouche root matching.
The finite polynomial root product equals the exponential of its exact
counting integral. Taylor Wronskians converge locally uniformly, their
Jensen counts converge off a countable set of radii, and the order bound
provides an integrable power envelope. Dominated convergence passes the
polynomial inequality to the entire function. The proved Tonelli identity
then identifies the limit with the literal actual-root infinite product.
This is the same conclusion under the same hypotheses; no root matching
claim or external result is assumed. M11 remains active; the coordinate
gauge, small-order classification, and zero-order ratio are not yet proved.

## M11 checkpoint: exact convolution and canonical zero set

Gate `m11-exact-convolution-and-canonical-zero-set` passed: 4872 build
jobs, 6441 audited declarations including 5573 theorems; empty source
scans and only Classical.choice, propext, Quot.sound. Four logs are frozen.
`Paper.cor_convolution` is certified in `Convolution.lean`, including
integrability of the literal Wronskian counting kernel and the full
manuscript inequality. `GenusZeroZeros.lean` proves that the fixed canonical
product has exactly the original entire function's zero set. Equality of
multiplicities and the resulting entire gauge are still in progress.
M11 remains active; the small-order classification and later milestones
are not certified.
## M11 checkpoint: canonical subproducts

Gate `m11-canonical-subproducts` passed: 4873 build jobs, 6448 audited
project declarations including 5579 theorems; empty source scans and
only the three permitted logical dependencies. Four logs are frozen.
`GenusZeroSubproduct.lean` proves convergence and entire holomorphy of
every subproduct, the exact product with the complementary subproduct,
and nonvanishing when the selected factors have no zero at the point.
These statements isolate a finite repeated-root fiber for the next
multiplicity proof. M11 remains active; the coordinate lemma is not yet
certified.
## M11 checkpoint: canonical zero multiplicities

Gate `m11-canonical-zero-multiplicities` passed: 4874 build jobs, 6462
audited declarations including 5592 theorems; empty source scans and only
the three permitted logical dependencies. Four logs are frozen.
`GenusZeroMultiplicity.lean` identifies each actual zero-copy fiber with
its finite multiplicity index, factors out the corresponding power of a
linear factor, and proves equality of analytic orders everywhere. The
remaining subproduct is entire and nonzero at the isolated root.
M11 remains active; the entire quotient and logarithmic gauge are next.
## M11 checkpoint: entire canonical logarithmic gauge

Gate `m11-entire-canonical-logarithmic-gauge` passed: 4875 build jobs,
6468 audited declarations including 5597 theorems; empty source scans and
only the three permitted logical dependencies. Four logs are frozen.
`GenusZeroGauge.lean` constructs the removable quotient by the fixed
canonical product, proves it entire and nowhere zero from equality of
orders, and obtains a single entire logarithm G with f = P exp(G).
It reuses the repository's certified analytic logarithm theorem.
No exponent-dependent product or extra gauge assumption is introduced.
The growth bounds for this gauge's coordinates and the translated
counting estimate are still required by `lem:small-order-coordinates`.
M11 remains active.
## M11 checkpoint: canonical product growth and Poisson bound

Gate `m11-canonical-product-growth-and-poisson-bound` passed: 4878 build
jobs, 6499 audited declarations including 5628 theorems; empty source scans
and only the three permitted logical dependencies. Four logs are frozen.
`CanonicalProductGrowth.lean` proves the literal head/count/tail inequality
`Paper.eq_canonical_product_growth` and the resulting power growth bound.
`CurveCoordinateCounting.lean` derives the actual coordinate logarithmic
and unweighted zero-count bounds, and reciprocal summability, from the
curve's order and nonzero central coordinate. `EntirePoissonBound.lean`
proves the exact scalar estimate log-plus M(r,h) <= 3 T(2r,h), including
zeros and constant functions. No extra growth hypotheses are added to
these curve consequences. M11 remains active; the full coordinate lemma
still needs assembly and translated counting.
## M11 checkpoint: gauged coordinate power bounds

Gate `m11-gauged-coordinate-power-bounds` passed: 4880 build jobs, 6525
audited declarations including 5653 theorems; empty source scans and only
the three permitted logical dependencies. Four logs are frozen.
`CurveOrderBasic.lean` proves nonnegativity of the literal curve order and
the scalar order consequence of a power bound. `GaugedCoordinateBounds.lean`
proves the proximity/characteristic bound for the actual coordinates
exp(-G) f_j, using equality with P(f_j/f_0) off the actual discrete zero
set, and derives maximum-modulus power bounds for every exponent above
the original order and below one. G stays fixed throughout.
M11 remains active; order-limit assembly, inverse jets and translation
estimates are not yet the full coordinate lemma.
## M11 checkpoint: fixed small-order gauge

Gate `m11-fixed-small-order-gauge` passed: 4882 build jobs, 6533 audited
project declarations including 5660 theorems; empty source scans and only
the three permitted logical dependencies. Four logs are frozen.
`SmallOrderGauge.lean` proves Step 1 of `lem:small-order-coordinates`:
from order(f)<1 and f_0(0) nonzero it constructs one entire G and proves
all exp(-G) f_j have scalar entire order at most order(f). The proof lets
an arbitrary real exponent decrease to the original extended-real order.
`ShiftedCombinations.lean` proves that translation and constant finite
linear combinations preserve a common scalar order upper bound.
M11 remains active. The full coordinate lemma still requires the actual
inverse-jet construction and both manuscript comparison inequalities.
## M11 checkpoint: inverse jets and gauge invariance

Gate `m11-inverse-jet-coordinates-and-gauge-invariance` passed: 4884 build
jobs, 6552 audited declarations including 5677 theorems; empty source scans
and only the three permitted logical dependencies. Four logs are frozen.
`ExponentialGauge.lean` constructs the reduced gauged curve and proves
exact Euclidean characteristic and ramification invariance, linear
nondegeneracy, and existence of an off-Wronskian point.
`NormalizedCoordinates.lean` uses the actual inverse derivative matrix,
proves all identity initial jets, the component order bound, reconstruction
of the original coordinates, and the exact translated Wronskian identity.
M11 remains active; the characteristic and counting comparison inequalities
are still being assembled before certifying the full coordinate lemma.
## M11 checkpoint: counting with origin multiplicities

Gate `m11-counting-with-origin-multiplicities` passed: 4885 build jobs,
6560 audited declarations including 5684 theorems; empty source scans and
only the three permitted logical dependencies. Four logs are frozen.
`WeightedZeroCounting.lean` proves the actual repeated-zero sum formula
with weight log(R) at zero and log-plus(R/|a|) elsewhere, including any
origin multiplicity. It also proves finite support at each radius and
nonnegativity for R>=1. No nonvanishing assumption at zero is added.
M11 remains active; translation and the full coordinate lemma are pending.
## M11 checkpoint: characteristic comparison and translation weights

Gate `m11-normalized-characteristic-and-translation-weights` passed:
4888 build jobs, 6581 audited declarations including 5703 theorems;
empty scans and only Classical.choice, propext, Quot.sound. Four logs
are frozen. `NormalizedCharacteristic.lean` proves the exact characteristic
comparison for the actual inverse-jet coordinates. `TranslatedZeroCopies.lean`
constructs a multiplicity-preserving bijection of the actual zero copies
and the translated counting sum, including roots moved to zero.
`TranslationWeightBound.lean` proves the global pointwise translation
error bound (|b|+1)/|a|. M11 remains active; summation of this estimate and
assembly of the full coordinate lemma are the next dependencies.
## M11 checkpoint: exact translated counting

Gate `m11-exact-translated-counting` passed: 4889 build jobs, 6584 audited
declarations including 5706 theorems, empty scans and only the three
permitted logical dependencies. Four logs are frozen.
`TranslatedCounting.lean` proves the radius-independent translated
Wronskian counting bound, with reciprocal-root summability derived from
the orders and the actual identity initial jets.
Proof divergence for `eq:translated-count`: index roots by the normalized
Wronskian W_y, whose value at zero is one. The global error (|b|+1)/|a|
is summable, including roots translated to the original origin. This
replaces the manuscript's finite-head/large-root split; the exact
hypotheses and conclusion are unchanged. Scalar gauge invariance then
identifies the original curve's count. M11 remains active.
## M11 checkpoint: complete small-order coordinates lemma

Gate `m11-exact-small-order-coordinates` passed: 4890 build jobs, 6585
audited declarations including 5707 theorems, empty scans and only the
three permitted logical dependencies. Four logs are frozen.
`ModifiedCartan.Paper.lem_small_order_coordinates` in
`ModifiedCartan/SmallOrderCoordinates.lean` proves the complete submitted
`lem:small-order-coordinates`: one fixed entire gauge, component orders
at most the curve order, existence of a regular base point, and for every
such point the actual inverse-jet system with identity initial derivatives,
order bounds, `eq:small-order-T`, and `eq:translated-count`. There is no
added hypothesis. The documented normalized-root proof replaces the
manuscript's finite-head/large-root translation split.
M11 remains active: the small-order classification and order-zero ratio
propositions are not yet certified. No main-theorem or sharpness claim.
## M11 checkpoint: divisor absorption and Cauchy polynomiality

Gate `m11-divisor-absorption-and-cauchy-polynomiality` passed: 4893 build
jobs, 6595 audited declarations including 5717 theorems; empty scans and
only the three permitted logical dependencies. Four logs are frozen.
`SystemDivisorMajorant.lean` proves the all-positive-radius divisor bound
from the actual two coordinate comparisons and small ramification, and
also handles a fixed eventual ramification ratio for the order-zero proof.
`ConvolutionAbsorption.lean` proves the kernel mass one and the exact
absorption inequality. `PolynomialSequence.lean` proves that a power bound
on maximum modulus along radii tending to infinity annihilates all higher
Taylor derivatives and yields an actual polynomial. These are proved
supporting lemmas; neither classification proposition is yet certified.
M11 remains active.
## M11 checkpoint: envelope power sequences and normal form

Gate `m11-envelope-power-sequences-and-normal-form` passed: 4897 build
jobs, 6615 audited declarations including 5737 theorems; empty scans and
only the three permitted logical dependencies. Four logs are frozen.
`SystemPowerSequence.lean` derives a common sequence with the exact power
n/(1-c I_alpha) from the proved envelope and absorption inequalities.
`NormalizedMonomials.lean` combines Cauchy vanishing and the identity jets
to obtain y_j(z)=z^j/j! whenever that exponent is below n+1.
`PolynomialNormalForm.lean` constructs the actual polynomial coordinates
when undoing translation and gauge, derives invertibility from linear
nondegeneracy, and proves rational normal form and its transfer through
constant invertible matrices. `AbsorptionConstants.lean` proves both
required coefficient/exponent choices, including the limit I_alpha to one.
M11 remains active pending assembly and audit of both paper propositions.
## M11 completed: small-order classification and the order-zero ratio

Gate `m11-complete-small-order-and-zero-ratio` passed: 4899 build jobs,
6623 audited declarations including 5745 theorems; empty scans over both
libraries and only Classical.choice, propext, Quot.sound. Four logs are
frozen. The unchanged submitted manuscript hash was rechecked.
`SmallOrderClassification.lean` proves `Paper.prop_small_order` with exactly
`SmallOrderTarget f`, including the initial coordinate change, actual gauge,
inverse jets, absorption, degree bound, and rational normal form.
`ZeroOrderRamification.lean` proves `Paper.prop_zero_order_ramification`
and `Paper.cor_zero_ratio` with exactly `ZeroRatioTarget f`, using the
extended-real limsup and deriving polynomiality from a hypothetical ratio
below one. No additional mathematical assumption is used.
Together with the already certified Tonelli, envelope, entire majorant,
convolution, and small-order coordinate lemmas, this completes M11.
The two recorded M11 proof divergences remain: Jensen-integral convergence
for the entire product majorant and normalized-root summation for translated
counting. M12 is now active. The full paper, main theorem, and sharpness
remain uncertified.
## M12 checkpoint: power normalization and scale weight

Gate `m12-power-normalization-and-scale-weight` passed: 4901 build jobs,
6639 audited declarations including 5760 theorems; empty scans over both
libraries and only the three permitted logical dependencies. Four logs
are frozen. `PowerNormalization.lean` proves log(r)/T(r) tends to zero
from the exact positive equal indices and the previously proved uniform
power bounds. Proof divergence in `sec:arbitrary-limits`: this derives
the needed limit directly from a positive power lower bound, instead of
invoking a general transcendence growth criterion. No extra assumption
is imposed. `ArbitraryScaleWeight.lean` defines the literal M_epsilon,
proves its uniform multiplier bound, and proves exact coefficient
rescaling with that normalization. M12 remains active; the complete
arbitrary-radius limits and basis-at-point lemma are not yet certified.
## M12 checkpoint: arbitrary-radius scale hypotheses

Gate `m12-arbitrary-radius-scale-hypotheses` passed: 4902 build jobs,
6640 audited declarations including 5761 theorems; empty scans and only
the three permitted logical dependencies. Four logs are frozen.
`ArbitraryScaleHypotheses.lean` proves all hypotheses of the representation
proposition for scale R*r_n and normalization M_epsilon(R)*T(r_n), for every
fixed R>0, with one constant independent of R. It proves both limits to
infinity, the logarithmic limit zero, the characteristic upper bound, and
the actual normalized Wronskian count limit zero. Only convergence of the
original radius sequence to infinity is assumed. M12 remains active;
the coefficient limits and basis-at-point result are not yet certified.
## M12 checkpoint: coefficient compactness and two-power exponents

Gate `m12-coefficient-compactness-and-two-power-exponents` passed: 4904
build jobs, 6643 audited declarations including 5764 theorems. Both source
scans are empty; only the three permitted logical principles occur.
Four logs are frozen. `ArbitraryCoefficientCompactness.lean` constructs
actual analytic coefficient limits after a further subsequence at each
fixed scale, with the common bound supplied by the proved representation
proposition. `TwoPowerExponents.lean` proves the endpoint exponent
constraints and their epsilon-to-zero consequence. These are intermediate
results; the whole-plane coefficient limit and basis-at-point lemma
remain unproved, and M12 remains active.
## M12 checkpoint: compatible scale models and Cauchy estimates

Gate `m12-compatible-scale-models-and-cauchy` passed: 4906 build jobs,
6649 declarations including 5770 theorems. Both source scans are empty;
only the permitted logical principles occur. Four logs are frozen.
`ArbitraryLimitModels.lean` obtains one actual coefficient subsequence
on the disk of radius 4 and compatible analytic germs at every positive
scale, for every admissible epsilon. `TwoPowerCauchy.lean` proves the
literal two-power derivative estimate. M12 remains active. These local
germs alone do not certify the manuscript's whole-plane limits.
## M12 checkpoint: monomial germs and measure dilation

Gate `m12-monomial-germs-and-measure-dilation` passed: 4908 build jobs,
6652 declarations including 5773 theorems; empty source scans and only
permitted logical dependencies. Four logs are frozen. `MonomialGerms.lean`
proves that any nonzero derivative has degree q*(rho-1), and reconstructs
the analytic function on the disk from that derivative support.
`MeasureDilation.lean` proves preservation of local convergence in measure
under a fixed real dilation and a complex multiplier. M12 remains active;
the whole-plane convergence has not yet been certified.
## M12 checkpoint: entire monomial extensions

Gate `m12-entire-monomial-extension` passed: 4909 build jobs, 6656
project declarations including 5776 theorems, empty source scans and
only the permitted logical principles. Four logs are frozen.
`MonomialExtension.lean` defines the exact natural-degree alternatives,
constructs the entire extension of the local germ, extends model identities
by the identity theorem, and extends the bound to the closed unit disk.
Whole-plane convergence of the original coefficient sequence still needs
its separate proof. M12 remains active.
## M12 checkpoint: global model convergence and disk bounds

Gate `m12-global-models-and-disk-bounds` passed: 4912 build jobs,
6662 declarations including 5782 theorems, empty scans and only permitted
logical principles. Four logs are frozen. `ArbitraryEntireModels.lean`
constructs compatible entire monomial extensions. `GlobalMeasureModels.lean`
proves whole-plane local measure convergence from analytic continuation
and the subsequence criterion. `TwoPowerDiskBound.lean` proves the exact
closed-disk two-power estimate. M12 remains active; the assembled paper
coefficient formulas are undergoing a separate gate.
## M12 checkpoint: complete arbitrary coefficient limits and monomial form

Gate `m12-arbitrary-coefficients-and-monomial-form` passed: 4915 build jobs,
6669 declarations including 5789 theorems. Both source scans are empty;
the recursive audit permits only Classical.choice, propext and Quot.sound.
All four logs are frozen. The following submitted formulas are now certified:

| LaTeX label | Stable Lean theorem | Exact certified scope |
| --- | --- | --- |
| `eq:arbitrary-coefficients` | `ModifiedCartan.Paper.eq_arbitrary_coefficients` | A common subsequence, entire limits of the actual scaled coefficients locally in measure on all of C, and the common closed-disk two-power bound for every admissible epsilon. |
| `eq:monomial-coefficients` | `ModifiedCartan.Paper.eq_monomial_coefficients` | Every actual entire coefficient limit is a natural-degree monomial of weight q*(rho-1), or zero if that weight is not natural. |

Proof divergence in `sec:arbitrary-limits`: first use compatible local
germs and the two-power Cauchy estimate to obtain the monomial extension.
Analytic continuation then identifies every fixed-scale subsequential
limit, and the subsequence criterion proves convergence on every compact
set of C. This replaces the manuscript's diagonal extraction over integer
scales. All hypotheses and conclusions are retained, including the same
subsequence for every epsilon and the closed-disk bound.

`SubharmonicSup.lean` also proves closure under finite maxima, and
`LogLimitRepresentatives.lean` retains actual extended subharmonic
representatives of simultaneous coordinate logarithm limits. M12 remains
active: the vector norm limit, origin estimate, good centers and complete
basis-at-point lemma are not yet certified. M13 has not started.
## M12 checkpoint: finite maxima and normalized norm comparison

Gate `m12-finite-maxima-and-norm-comparison` passed: 4919 build jobs,
6679 declarations including 5799 theorems. Both source scans are empty,
and only the permitted logical principles occur. Four logs are frozen.
Local L1 convergence is preserved under finite maxima and an AE uniformly
vanishing error. The actual coordinate maximum is subharmonic and is
nonnegative everywhere when the sum of its real representatives is
nonnegative AE. The normalized Euclidean logarithm differs from the
maximum coordinate logarithm by at most log(sqrt(n+1))/s off the coordinate
zero sets. M12 remains active; the assembled norm-limit construction,
origin estimate, good-center extraction and basis-at-point lemma remain.
## M12 checkpoint: normalized norm convergence and Wronskian sum

Gate `m12-norm-limit-and-wronskian-sum` passed: 4922 build jobs,
6684 declarations including 5804 theorems; empty source scans and only
the permitted logical dependencies. Four logs are frozen.
`NormalizedNormLimit.lean` proves the actual Euclidean logarithm converges
locally in L1 to the finite coordinate maximum. `EventualWronskianSum.lean`
proves the nonnegative sum using the actual monic Wronskian and its small
degree. `ReplacementSubsequence.lean` preserves every replacement field
under subsequences, including all repeated roots. M12 remains active;
the full arbitrary-radius data and the remaining manuscript conclusions
still require assembly and proofs.
## M12 checkpoint: common gauges, logarithm limits and radial mean

Gate `m12-common-gauges-log-limits-and-radial-mean` passed: 4924 build jobs,
6687 declarations including 5807 theorems; empty scans and only permitted
logical principles. Four logs are frozen. For the actual replacement
construction, `PolynomialReplacementData.exists_log_limits` produces
simultaneous nontrivial subharmonic component limits, local L1 convergence
of the normalized Euclidean logarithm, the nonnegative AE coordinate
sum, and a nonnegative subharmonic maximum. The same gauges are retained.
`PolynomialReplacementData.normalized_radial_mean` proves the literal
radial identity with a single error sequence independent of the radius.
M12 remains active: origin bounds, polynomial norm limits, good centers,
and the complete basis-at-point lemma are still required.
## M12 checkpoint: disk means and the subharmonic origin bound

Gate `m12-disk-means-and-subharmonic-origin` passed: 4926 build jobs,
6701 declarations including 5821 theorems; empty scans and only permitted
logical dependencies. Four logs are frozen. `DiskMeanLimits.lean` bounds
the disk average of the actual Euclidean norm limit by C*R^(rho-epsilon).
`SubharmonicOrigin.lean` proves the corresponding pointwise power bound
on the disk of radius 1/4 and the value zero at the origin.
Proof divergence in `eq:origin-bound`: monotonicity of the characteristic
bounds all inner circle means by the outer mean at fixed R. Passing that
disk-mean bound to the L1 limit avoids the manuscript's split of the radial
integral at r_epsilon/r_n. The output exponent and all hypotheses are the
same. M12 remains active; the final origin formula is being assembled.
## M12 checkpoint: origin formula and good centers

Gate `m12-origin-formula-and-good-centers` passed: 4928 build jobs,
6706 declarations including 5826 theorems; empty scans and only permitted
logical dependencies. All four logs are frozen. `Paper.eq_origin_bound`
proves U(0)=0 and the exact nonnegative power bound on D_(1/4), for every
epsilon in (0,rho), for the actual norm limit and its representative.
`PolynomialReplacementData.exists_good_centers` extracts a full-measure
subset of D_2 minus the origin, avoiding every actual polynomial Wronskian
zero, with normalized logarithms tending to zero and an explicit eventual
bound on the full reciprocal-distance sum over all repeated roots.
M12 remains active: polynomial norm convergence, final assembly and the
complete basis-at-point proof remain unproved.
## M12 checkpoint: vector integrability and exponential comparison

Gate `m12-vector-integrability-and-exponential-comparison` passed: 4931 build
jobs, 6716 declarations including 5836 theorems. Both placeholder scans are
empty; all dependencies are the permitted foundational principles. Four logs
are frozen. `VectorLogIntegrability.lean` proves compact integrability of the
actual vector logarithm from its analytic coordinates; `EuclideanTriangle.lean`
controls the vector norm error by coordinate errors. `ExponentialLogComparison.lean`
proves that exponentially close norms share a nonnegative normalized logarithm
limit, retaining positivity of the original norm and deriving positivity of the
approximating norm on a tail. M12 remains active; this is infrastructure for the
actual Taylor polynomial norm limit, not a certificate of the entire milestone.

## M12 checkpoint: polynomial log compactness and measure transfer

Gate `m12-polynomial-log-compactness-and-measure-transfer` passed: 4934 build
jobs, 6726 declarations including 5846 theorems; empty placeholder scans and
only permitted logical dependencies. Four logs are frozen. `LogMeasureTransfer`
transfers normalized logarithms in local measure under exponential norm error.
`ReplacementNormProperties` proves the exact Taylor center values, positive
original norms, exponential polynomial coordinate bounds and vector norm error.
`PolynomialNormCompactness` upgrades the polynomial vector logarithm measure
limit to local L1 convergence by simultaneous coordinate compactness and limit
uniqueness. These are consequences of the actual data; the public polynomial
norm formula and complete common-subsequence construction are still being checked.

## M12 checkpoint: polynomial norm formula and limit data

Gate `m12-polynomial-norm-formula-and-limit-data` passed: 4936 build jobs,
6806 declarations including 5886 theorems; empty scans and only permitted logical
principles. Four logs are frozen. LaTeX `eq:polynomial-norm` is proved as
`Paper.eq_polynomial_norm`, for the exact Taylor polynomials and the same gauges.
`GoodCenterData.limsup_lt_top` proves the literal finite-limsup root sum condition.
`ArbitraryRadiusLimitData` now records all common-subsequence obligations; the
record alone is not a claim that they exist. Its construction is still being checked.

Proof divergence for `eq:polynomial-norm`: an AE further-subsequence criterion
proves the measure transfer under exponential approximation. Simultaneous scalar
coordinate compactness, the norm/max comparison and uniqueness then upgrade this
to local L1. This proves the same norm limit and uses only the actual approximation,
center values and bounds, without a separate vector subharmonic compactness theorem.
M12 remains active; the basis-at-point lemma and final construction remain pending.

## M12 checkpoint: complete arbitrary-radius construction

Gate `m12-complete-arbitrary-radius-construction` passed: 4937 build jobs,
6808 declarations including 5888 theorems; empty placeholder scans and only
permitted foundational dependencies. Four logs are frozen.
`exists_arbitrary_radius_limits_normalized` constructs the entire record on one
strict subsequence. `Paper.exists_arbitrary_radius_limits` handles an arbitrary
original curve by constructing an actual fixed norm-preserving invertible matrix.
All coefficient, component, original norm and polynomial norm limits refer to
that same subsequence; the radial mean, origin estimates and full-measure good
centers are retained. The coordinate normalization is not an extra hypothesis.
This completes the objects of `sec:arbitrary-limits`. M12 is still active:
`Paper.lem_basis_at_point` and its point-value balance have not yet been proved.

## M12 checkpoint: unitary norm and positive column lengths

Gate `m12-unitary-norm-and-positive-column-lengths` passed: 4938 build jobs,
6817 declarations including 5897 theorems; empty scans and only allowed logical
principles. Four logs are frozen. `UnitaryNorm.lean` proves exact row-vector norm
invariance for unitary matrices. Applied to the actual Gram matrix, the inspected
mathlib spectral theorem constructs orthogonal columns; their positive lengths
have product equal to the absolute determinant whenever the original determinant
is nonzero. No singular-value decomposition is postulated. M12 remains active;
scaled polynomial jets, singular exponents and point balance are being proved.

## M12 checkpoint: scaled jets and singular logarithm limits

Gate `m12-scaled-jets-and-singular-log-limits` passed: 4941 build jobs,
6835 declarations including 5912 theorems; empty scans and only permitted logical
principles. Four logs are frozen. `ScaledPolynomialJets` proves exact identities
for the actual polynomial jet matrices, positive column lengths and their product,
and unchanged norms and Wronskian norms under the actual unitary changes.
`SingularExponentLimits` proves finite simultaneous exponent extraction and the
zero sum from the determinant product. `JetLengthBounds` gives Cauchy upper bounds
for complete scaled jets and bounds each derivative by its actual column length.
M12 remains active; the pointwise component compactness and balance are pending.

## M12 checkpoint: uniform unitary polynomial jet bound

Gate `m12-uniform-unitary-polynomial-jet-bound` passed: 4942 build jobs,
6839 declarations including 5916 theorems; empty scans and only permitted logical
principles. Four logs are frozen. `PointJetUpper` proves an eventual exponential
bound for each complete scaled derivative column after any actual unitary change
of the Taylor polynomials, uniformly for centers in D2. The bound is derived by
norm preservation and Cauchy estimates. M12 remains active; the singular exponent
construction and exclusion of logarithm collapse are being checked.

## M12 checkpoint: good-center singular exponents and no collapse

Gate `m12-good-center-singular-exponents-and-no-collapse` passed: 4944 build
jobs, 6843 declarations including 5920 theorems; empty scans and only permitted
logical dependencies. Four logs are frozen. For every actual good center,
`ArbitraryRadiusLimitData.exists_singular_exponents` constructs a further strict
subsequence, actual unitary matrices and positive column lengths whose normalized
logarithms converge to finite real exponents with zero sum (`eq:singular-exponents`).
`JetLogCompactness` proves that these finite jet exponents exclude local uniform
collapse of the corresponding holomorphic logarithms to negative infinity.
M12 remains active: component limits and the exact center-value balance are pending.

## M12 checkpoint: jet-anchored compactness and initial value estimate

Gate `m12-jet-anchored-component-compactness-and-initial-value` passed: 4946
build jobs, 6847 declarations including 5924 theorems; empty scans and only allowed
logical principles. Four logs are frozen. `exists_common_jet_anchored_log_limits`
constructs simultaneous nontrivial subharmonic component representatives from
actual finite singular exponents, even when component values at the center vanish.
`polynomial_matrix_initial_value_bound` proves the exact bound
`eq:point-initial-upper` for the actual polynomial matrix change and the original
Wronskian root list, constructing the polynomial space basis internally.
M12 remains active; identification of the center values and point balance remain.

## M12 checkpoint: logarithmic majorants and Cauchy value lower bound

Gate `m12-point-log-majorants-and-cauchy-value-lower-bound` passed: 4949 build
jobs, 6852 declarations including 5929 theorems; empty scans and only permitted
foundational principles. Four logs are frozen. `PolynomialLogMajorant` proves the
normalized logarithm inequality with its vanishing polynomial factor.
`PointInitialCoarse` derives this factor from the exact initial-value estimate.
`jet_exponent_le_log_limit_value` proves the reverse inequality at the center,
using Cauchy's estimate and the upper semicontinuity of the actual representative.
M12 remains active: the other inequality and complete point-balance assembly are pending.

## M12 checkpoint: point value upper bound and unitary coordinate estimates

Gate `m12-point-value-upper-and-unitary-coordinate-bounds` passed: 4951 build
jobs, 6855 declarations including 5932 theorems; empty scans and only permitted
foundational principles. Four logs are frozen. `log_limit_value_le_singular_exponent`
uses the actual polynomial initial-value majorant to identify the upper bound at
the center, extending the almost-everywhere estimate by subharmonic comparison.
`unitary_polynomial_coordinate_eventual_bound` supplies exponential bounds for the
actual unitary transforms; `ereal_coe_finset_sum` preserves the finite real sum.
M12 remains active until the complete point-balance assembly is checked.

## M12 checkpoint: center value and preservation of log balance

Gate `m12-center-value-and-unitary-log-balance` passed: 4953 build jobs,
6858 declarations including 5935 theorems; empty scans and only the permitted
logical principles. Four logs are frozen. The actual component value at each
good center equals its finite singular exponent, by the initial-value upper
bound and the Cauchy lower bound. The actual unitary polynomial changes retain
the previously fixed norm limit U and the almost-everywhere nonnegative sum.
M12 remains active until `Paper.lem_basis_at_point` is integrated and audited.

## M12 completion: arbitrary-radius limits and the exact basis-at-point lemma

Gate `m12-complete-arbitrary-limits-and-basis-at-point` passed: 4954 build
jobs, 6859 declarations including 5936 theorems; both source scans are empty,
and the recursive audit reports only Classical.choice, propext, and Quot.sound.
The four logs are frozen. `Paper.lem_basis_at_point` in `BasisAtPoint.lean`
proves the full submitted `lem:basis-at-point` and `eq:point-balance`, with
actual unitary matrices, a common further subsequence, nontrivial subharmonic
component limits, their maximum equal to the already fixed U, their sum
nonnegative almost everywhere, and their sum exactly zero at the chosen center.
Together with `Paper.exists_arbitrary_radius_limits`, the whole-plane monomial
coefficient limits, exact radial means, origin bound and actual good-center
construction, this completes M12. M13 is next; no later milestone is certified.
The manuscript SHA256 remains
D3F63ADE442557F0474EB117EDD0BA99405A09AB412E6D40FAE271C56F7C44CA.

Proof divergences for `lem:basis-at-point`: the spectral theorem is applied to
the actual Gram matrix to construct orthogonal columns, an exact specialized
singular-value decomposition. For the reverse center-value inequality the
Cauchy factor is bounded by a fixed positive K(n,r), independent of the scale;
its logarithm divided by s tends to zero. Upper semicontinuity on nested disks
then gives the same exact value using a contradiction, without a separate
supremum-limit formula. These changes add no hypotheses and preserve all
objects and conclusions of the submitted lemma.

## M13 checkpoint: weak directional derivatives and smoothing bounds

Gate `m13-weak-directional-derivatives-and-smoothing-bounds` passed: 4957 build
jobs, 6862 declarations including 5939 theorems; both scans empty, and only
Classical.choice, propext and Quot.sound in the recursive audit. Four logs are
frozen. `WeakGradientDirectional`, `WeakGradientConvolution` and
`WeakGradientSmoothBound` prove the exact test identity in every real direction,
the derivative formula for a compactly supported smoothing of the actual weak
gradient, and preservation of an almost-everywhere gradient bound by a positive
unit-mass kernel. M13 remains active. Finite-gradient convexity is not yet proved.

## M13 checkpoint: actual subharmonic Lipschitz regularity

Gate `m13-bounded-weak-gradient-and-subharmonic-lipschitz-regularity` passed:
4960 build jobs, 6867 declarations including 5944 theorems; empty scans and only
the allowed three foundational principles. Four logs are frozen.
`WeakGradientLipschitz` constructs a Lipschitz representative on smaller disks
from an actual bounded weak gradient, using smoothing, almost-everywhere
convergence and the proved mathlib Lipschitz extension. The continuous
representative is shown to agree everywhere with the original subharmonic
representative. `SubharmonicLipschitz` proves the resulting finiteness and local
Lipschitz continuity, including the finite-gradient case. M13 remains active;
nonnegative Laplacians and finite-phase convexity remain to be proved.

## M13 checkpoint: Taylor estimates, disk rotations and smooth Laplacians

Gate `m13-taylor-disk-rotation-and-smooth-laplacian` passed: 4968 build jobs,
6883 declarations including 5960 theorems; both source scans are empty and the
recursive audit reports only Classical.choice, propext and Quot.sound. Four
logs are frozen. `SecondOrderTaylor`, `QuadraticTrace`, `SecondOrderTaylorBound`
and `QuarterMeanBound` prove the integral second-order Taylor expansion, its
uniform local remainder estimate and the four-direction trace identity.
`DiskIsometry` and `QuarterDiskIntegral` prove the exact disk integral changes
under translations and rotations. `SmoothSubharmonicLaplacian` then proves
`IsSubharmonicOn.laplacian_nonneg_of_contDiff` directly from the actual disk
submean definition. M13 remains active; finite-gradient convexity is not yet
proved, and no later milestone is certified.

Proof divergence in this dependency: nonnegativity of the smooth Laplacian is
proved using Taylor error bounds in four orthogonal directions and invariance
of area integrals, rather than importing a general potential-theory theorem.
Continuity of the second derivative is used through its four real coordinate
coefficients. These are proved identities and estimates, not extra assumptions.

## M13 checkpoint: positive-kernel subharmonic smoothing

Gate `m13-positive-kernel-subharmonic-smoothing` passed: 4970 build jobs,
6893 declarations including 5970 theorems; empty source scans and only the
three permitted foundational principles in the recursive audit. Four logs are
frozen. `DiskConvolutionFubini` proves joint integrability on the compact
product and the precise exchange of a disk integral with kernel convolution.
`SubharmonicConvolution` proves that a positive compact kernel preserves the
actual disk submean definition wherever its translations stay in the original
domain. A twice continuously differentiable kernel therefore yields a smooth
function with nonnegative classical Laplacian. This proves the smoothing
property rather than assuming it. M13 remains active; the regularized-logarithm
inequality and finite-phase monotonicity are the next dependencies.

## M13 checkpoint: complex-gradient calculus and regularized logarithm

Gate `m13-classical-gradient-and-regularized-log-sign` passed: 4973 build jobs,
6900 declarations including 5977 theorems; empty scans and only the permitted
three foundational principles. Four logs are frozen. `ClassicalGradientLaplacian`
proves the derivative formula for the actual classical complex gradient and
identifies twice its antiholomorphic derivative with the real Laplacian, using
mathlib's proved symmetry of the second derivative. `RegularizedComplexLog`
proves the exact chain rule and nonpositive real antiholomorphic derivative of
log(epsilon minus gradient) on the relevant half-plane. `WeakGradientHalfPlane`
proves that positive unit-mass smoothing preserves every directional half-plane
bound of the actual weak gradient. The positive-real-part branch of the complex
logarithm is used in place of a branch on the negative half-plane; its real part
is the same log modulus, and the derivative is identical. M13 remains active;
passage to weak test inequalities and finite-phase propagation is not yet done.

## M13 checkpoint: actual gradient limits and logarithm tests

Gate `m13-smooth-gradient-limits-and-log-test-inequality` passed: 4975 build
jobs, 6907 declarations including 5984 theorems; empty scans, with only
Classical.choice, propext and Quot.sound in the recursive audit. Four logs are
frozen. `WeakGradientSmoothConvergence` proves almost-everywhere convergence of
the actual derivatives of mollifications to the original weak gradient on
smaller disks. The compact cutoff is applied only to identify the convolution
and invoke the proved Lebesgue differentiation theorem. `RegularizedLogTest`
proves local differentiability of the regularized complex logarithm and its
nonnegative-test inequality by fully justified integration by parts. M13 remains
active; passage of this inequality to the nonsmooth gradient and phase
indicator propagation remain to be proved.

## M13 checkpoint: logarithmic test inequality for the actual weak gradient

Gate `m13-weak-gradient-logarithmic-test-limit` passed: 4978 build jobs,
6914 declarations including 5991 theorems; both scans empty and only the three
permitted foundational principles. Four logs are frozen. `RegularizedLogBounds`
proves an explicit uniform bound for fixed positive regularization and the
corresponding dominated convergence theorem for logarithm test integrals.
`SubharmonicGradientSmoothing` proves that the actual mollifications
simultaneously satisfy the Laplacian sign and the half-plane and norm bounds.
`WeakGradientLogTest` combines these results to prove
`IsSubharmonicOn.weak_gradient_regularized_log_test` for the original weak
gradient. No distributional inequality is assumed. M13 remains active; the
zero-phase indicator limit and its directional propagation are next.

## M13 checkpoint: zero-phase indicator test inequality

Gate `m13-zero-phase-indicator-test-inequality` passed: 4981 build jobs,
6926 declarations including 6001 theorems; empty scans and only the three
allowed foundational principles. Four logs are frozen. `PhaseLogLimit` proves
that minus log(exp(-t) minus z) divided by t converges to the indicator of z=0,
with a uniform bound for bounded z in the closed left half-plane.
`PhaseLogDominated` passes this limit through test integrals. `ZeroPhaseTest`
then proves `IsSubharmonicOn.weak_gradient_zero_phase_test` for the original
weak gradient: its zero-phase indicator has a nonnegative distributional real
directional derivative. No phase monotonicity is assumed. M13 remains active;
arbitrary directions, cone propagation and the final convexity lemma remain.

Proof divergence: the phase-indicator limit uses exponential regularization
and a proved uniform logarithmic bound with dominated convergence. This avoids
a separate finite-valued O(1) remainder argument and works already for bounded
half-plane-valued gradients. This stronger intermediate conclusion adds no
hypotheses to the submitted finite-gradient lemma.

## M13 checkpoint: directional phases and smoothing monotonicity

Gate `m13-directional-phase-tests-and-smoothing-monotonicity` passed: 4990
build jobs, 6963 declarations including 6036 theorems; both source scans empty,
and only Classical.choice, propext and Quot.sound in the recursive audit. Four
logs are frozen. The directional complex-gradient identity derives the exact
squared-norm factor, and the corresponding regularized logarithm and test
inequalities are proved for every phase value a and direction w. Actual
mollifications preserve the shifted supporting half-plane, and dominated
convergence yields `IsSubharmonicOn.weak_gradient_phase_test` for the original
gradient. `PhaseIndicator` supplies integrable cutoffs without assuming the
gradient is measurable outside its domain. `DirectionalTestSmoothing` proves
monotonicity on line segments from the distributional test inequality.
`PhaseCutoffMonotonicity` proves one eventual smoothing bound simultaneously
for all pairs of interior points whose displacement is in the supporting cone.
M13 remains active; cone filling, essential local phases and convexity remain.

Proof divergence: arbitrary directions are handled by the explicit identity
L(w)+iL(iw)=conjugate(w)*(L(1)+iL(i)) for real-linear maps. This avoids changing
the domain by a coordinate rotation and proves the same directional inequality.

## M13 checkpoint: filling strict supporting cones

Gate `m13-strict-cone-phase-propagation` passed: 4992 build jobs,
6975 declarations including 6046 theorems; both scans empty and only the allowed
three foundational principles. Four logs are frozen. `StrictPhaseCone` proves
openness, convexity, positive scaling and the supporting half-plane inequality
for the finite set of gradient values. `PhaseConePropagation` defines essential
phases by positive measure in every neighborhood, proves almost-everywhere
convergence of actual phase cutoffs, and establishes
`IsSubharmonicOn.phase_eq_ae_on_strict_cone`: an essential phase fills its strict
supporting cone almost everywhere on a smaller disk. The proof selects a point
of the actual phase from a positive-measure neighborhood and uses the common
smoothing monotonicity. M13 remains active; local essential phase selection,
affine reconstruction and local-to-global convexity remain to be proved.

## M13 checkpoint: essential phases and weak local constancy

Gate `m13-essential-phases-and-local-constancy` passed: 4994 build jobs,
6989 declarations including 6059 theorems; both project scans empty and only
Classical.choice, propext and Quot.sound. Four audit logs are frozen.
`EssentialPhases` removes every nonessential gradient value on a common small
disk and proves that the remaining finite essential phase set is nonempty.
`WeakGradientLocalConstancy` proves that a continuous function with actual weak
gradient zero almost everywhere is locally constant, and constant on an open
preconnected domain. The proof uses the already certified Lipschitz representative
with bound zero, then continuity and mathlib's zero-derivative constancy theorem.
M13 remains active: affine reconstruction, finite affine maxima and the exact
local-to-global convexity conclusion are still required.

## M13 checkpoint: affine reconstruction on phase cones

Gate `m13-affine-reconstruction-on-phase-cones` passed: 4996 build jobs,
6996 declarations including 6066 theorems; both scans empty and only the three
allowed foundational dependencies. All four logs are frozen. `WeakGradientAffine`
proves the exact affine difference formula on any open preconnected set whose
actual weak gradient is almost everywhere constant. `PhaseConeAffine` applies it
to the strict phase cones and uses a proved radial limit and continuity to anchor
the affine value at the original center. Its final theorem derives the pointwise
affine formula from subharmonicity, the actual weak gradient and essentiality.
No extra phase-region or differentiability assumption is introduced. M13 remains
active; finite maxima and local-to-global convexity are still pending.

## M13 checkpoint: local finite affine maximum

Gate `m13-local-finite-affine-maximum` passed: 4999 build jobs, 7013
declarations including 6081 theorems; both scans empty and only the allowed
foundational dependencies. Four logs are frozen. `GenericPhaseDirections` proves
that avoiding finitely many tie hyperplanes is dense and provides a strictly
maximizing phase. `PhaseAffineMax` constructs a finite affine maximum and proves
its continuity and convexity. `LocalPhaseMaximum` extends the cone formula by
continuity to the entire small disk and proves local convexity for a continuous
representative with the actual finite weak gradient. The essential phase set
is constructed from the original gradient at each center. M13 is still active:
the original extended-real representative and local-to-global convexity must
still be connected to the exact manuscript lemma.

## M13 complete: exact finite-gradient convexity criterion

Gate `m13-complete-finite-gradient-convexity` passed: 5003 build jobs,
7019 declarations including 6087 theorems; both source scans empty and the full
recursive audit reports only Classical.choice, propext and Quot.sound. Four logs
are frozen. `ModifiedCartan.Paper.lem_finite_gradient_convex`, in
`ModifiedCartan/FiniteGradientConvexity.lean`, proves the exact registered target
for manuscript `lem:finite-gradient-convex`: the original extended-real
subharmonic representative is finite and convex on its open convex domain when
its actual weak gradient lies in a finite set almost everywhere. All intermediate
continuity and phase properties are derived, and no cited criterion is assumed.

The final proof combines bounded-gradient Lipschitz representatives, a proved
subharmonic Laplacian sign, regularized complex logarithms, dominated phase
limits, directional smoothing monotonicity, essential phase cones, affine
reconstruction, finite affine maxima and local-to-global convexity. The latter
is proved here by a one-dimensional maximum argument with a positive quadratic
perturbation, applied to every segment; it needs no differentiability assumption.
This explicit maximum argument is the final recorded proof divergence from the
paper's cited convexity criterion. M0--M13 are now certified. M14 (homogeneity)
is the next active milestone; the main theorem and sharpness remain unproved.


## M14 opened: homogeneity

M14 starts only after the complete M13 gate. `work/M14-plan.md` records the
inspected project/mathlib support, exact initial ODE/root-bound targets, exact
final homogeneity signature, and dependency DAG. The first missing dependency
is passage from actual normalized fundamental equations to the nonzero
polynomial equation for the actual weak gradient. Conformal pullback and narrow
power-sector geometry remain proof obligations; no interface assumes them.

## M14 checkpoint: polynomial gradient equation and root bounds

Gate `m14-polynomial-gradient-limit-and-root-bound` passed: 5005 build jobs,
7022 declarations including 6090 theorems; both project scans empty and only
Classical.choice, propext and Quot.sound. Four logs are frozen.
`normalized_ode_weak_gradient_polynomial` proves passage to the nonzero
polynomial equation for the actual weak gradient, using the proved logarithmic
derivative limits and convergence in measure. `norm_le_of_monic_equation`
proves the specialized root bound directly by the triangle inequality and
comparison of powers, and `monic_equation_gradient_bound_on_compact` turns
continuous coefficient bounds into an almost-everywhere gradient bound.
The elementary root estimate replaces the use of a general root-bound theorem
and proves exactly what the manuscript needs. M14 remains active: applying
these results to the constructed unitary component limits, the conformal
change of variable, and the radial equality argument are still required.

## M14 checkpoint: actual coefficients and local regularity

Gate `m14-actual-coefficients-and-local-regularity` passed: 5007 build jobs,
7028 declarations including 6095 theorems; both scans empty and only the allowed
three foundational dependencies. Four logs are frozen.
`ArbitraryPolynomialCoefficients` appends the actual zero first coefficient to
the finite coefficient family and proves convergence of the actual polynomial
coefficients from the replacement error and canonical coefficient limits.
`PolynomialGradientRegularity` proves finiteness and local Lipschitz regularity
of the original subharmonic representative from its actual polynomial weak-
gradient equation with continuous coefficients. M14 remains active; the unitary
component connection and conformal/radial homogeneity arguments are pending.

## M14 checkpoint: gradient equation for actual unitary components

Gate `m14-unitary-component-gradient-equation` passed: 5009 build jobs,
7032 declarations including 6099 theorems; both scans empty and only the three
allowed foundational principles. Four logs are frozen.
`UnitaryPolynomialCoefficients` proves constant matrix invariance for the actual
polynomial tuple, preserves its nonzero Wronskian almost everywhere, and transfers
its actual coefficient limits through any actual unitary subsequence.
`UnitaryComponentGradient` constructs the actual weak gradient from the component
logarithm limit and proves its polynomial equation. The equation is a conclusion,
not an added hypothesis. M14 remains active; component regularity, conformal
pullback and the radial homogeneity argument remain to be assembled and proved.

## M14 checkpoint: actual component regularity and pointwise balance

Gate `m14-component-regularity-and-pointwise-balance` passed: 5011 build jobs,
7037 declarations including 6104 theorems; both scans empty and only the three
allowed foundational principles. Four logs are frozen.
`UnitaryComponentRegularity` proves finiteness and local Lipschitz regularity of
each actual component and continuity of the fixed actual maximum U.
`PointwiseUnitaryBalance` transfers the gradient equation to the actual real
representative and upgrades the nonnegative sum to every point using continuity.
M14 remains active: the conformal pullback, finite-gradient application and
radial homogeneity argument are still required.

## M14 checkpoint: local L1 transport through an actual inverse

Gate `m14-local-l1-inverse-pullback` passed: 5013 build jobs,
7040 declarations including 6107 theorems; both scans empty and only the allowed
three foundational principles. Four logs are frozen.
`InversePullbackBound` proves the compact L1 norm estimate using mathlib's
proved Jacobian formula. `InversePullbackConvergence` proves local L1 transport,
including source and limit integrability; the Jacobian bound follows from
continuity on compact images. M14 remains active. The actual conformal chart,
its gradient equation, convexity and radial equality are still to be completed.

## M14 checkpoint: actual logarithm pullback and weak chain rule

Gate `m14-analytic-logarithm-pullback` passed: 5015 build jobs,
7047 declarations including 6114 theorems; both scans empty and only the allowed
three foundational principles. Four logs are frozen.
`InversePullbackAE` transfers null exceptional sets through an actual
differentiable inverse and proves continuous multiplication of local L1 limits.
`AnalyticLogPullback` proves subharmonicity of the actual continuous pullback
and identifies its actual weak gradient by the chain rule.
Proof divergence: instead of invoking a general subharmonic conformal-invariance
or Sobolev chain-rule theorem, compose the actual holomorphic logarithm sequence,
transport its proved L1 limits, identify its subharmonic representative, and use
uniqueness of the first logarithmic derivative limit. The required statement is
unchanged. M14 remains active: the explicit power chart, constant gradient
polynomial, convexity and radial equality still need to be assembled.

## M14 checkpoint: small exponent vanishing

Gate `m14-small-exponent-vanishing` passed: 5016 build jobs,
7051 declarations including 6118 theorems; both scans empty and only the allowed
three foundational principles. Four logs are frozen.
`SmallExponentNorm` proves that every coefficient vanishes when rho < 1,
then proves every actual unitary component is constant from its zero weak
gradient. Consequently the already fixed U equals U(0)=0 throughout D4.
Proof divergence: this proved case split permits a right half-disk power chart
for rho >= 1. No lower bound on rho is added to the homogeneity statement.
M14 remains active; the nontrivial power chart and convex radial argument remain.

## M14 checkpoint: convexity of the actual power-chart component limits

Gate `m14-actual-unitary-power-convexity` passed: 5020 build jobs,
7082 declarations including 6146 theorems; both scans empty and only the allowed
three foundational principles. Four logs are frozen.
`PowerChartAnalytic` and `PowerChartGeometry` construct the actual analytic
inverse pair, continuous inverse Jacobian and convex right half-disk domain,
with exact radial values and image inside D4. `PowerChartCoefficients` proves
that the weighted coefficients become constants and the resulting monic
polynomial has finitely many roots. `UnitaryPowerConvexity` applies the proved
weak chain rule, transfers the actual equation, and invokes the certified M13
criterion to prove convexity of each actual component pullback.
The coordinate is psi(w)=a*w^(1/rho), so its center is w=1; this is the paper's
power coordinate up to a constant factor. M14 remains active: radial balance,
dense-center extension and the exact homogeneity theorem are still required.

## M14 complete: exact homogeneity of the fixed norm limit

Gate `m14-complete-homogeneity` passed: 5023 build jobs,
7092 declarations including 6156 theorems. Both source scans are empty, and
recursive dependency auditing of all public and private project declarations
reports only Classical.choice, propext and Quot.sound. Four logs are frozen.
`Paper.prop_homogeneity` in `ModifiedCartan/Homogeneity.lean` proves exactly
`prop:homogeneity` / `eq:homogeneity`: U(t*z)=t^rho*U(z) for every positive t
with z and t*z in D2, for the already constructed arbitrary-radius data.
`RadialConvexBalance` proves the endpoint convexity bound and finite balance
criterion. `GoodCenterHomogeneity` proves the actual radial identities at every
good center, and `Homogeneity` extends them to all D2 by continuous AE equality
and handles t>1 by inversion. The separately proved rho<1 case has U identically
zero, so no extra order or regularity hypothesis is introduced.
Additional proof divergence: the already established continuous component
representatives, U(0)=0, their pointwise maximum and nonnegative sum give each
component's value zero at the origin directly. Thus the vertex limit follows
from proved continuity, instead of reusing the manuscript's origin growth bound.
The full paper is still incomplete. M0--M14 are certified; M15 regular variation
is now active, and the main theorem and sharpness remain uncertified.


## M15 checkpoint: actual annular ratio limits

Gate `m15-annular-ratio-limits` passed: 5026 build jobs, 7105 declarations
including 6168 theorems. Both source scans are empty and recursive auditing of
all public and private declarations reports only Classical.choice, propext and
Quot.sound. The four verification logs are frozen.
`HomogeneousRadialMeans` proves the actual homogeneous circle-mean identity and
a polar integral formula for functions continuous only near the disk.
`NormLogIntegrals` transfers the actual local L1 limit to disk integrals, and
`AnnularRatioLimit` proves convergence of the weighted characteristic ratios on
every annulus 0<a<b<2, using the actual vanishing radial-mean error.
M15 remains active: monotone pointwise limits, normalization at multiplier 1,
arbitrary original sequences, all positive multipliers and compact uniformity
are still required for the exact regular variation proposition.

## M15 checkpoint: normalized ratios and arbitrary original radii

Gate `m15-original-ratio-limits-below-two` passed: 5028 build jobs,
7110 declarations including 6173 theorems. Both source scans are empty;
recursive auditing of public and private declarations reports only the three
allowed foundational principles. Four logs are frozen.
`MonotoneWeightedIntegrals` proves the pointwise upgrade from weighted integral
limits using left and right intervals. `SubsequenceRatios` identifies the
circle-mean constant as 1 from the exact identity at multiplier 1, then proves
`characteristic_ratio_tendsto_of_lt_two` for the original curve and every
multiplier in (0,2). The proof constructs actual limit data for each sequence
and uses exact characteristic invariance under its coordinate normalization.
M15 remains active: unrestricted positive multipliers and compact uniformity
remain before the exact regular variation proposition can be certified.

## M15 complete: locally uniform regular variation

Gate `m15-complete-regular-variation` passed: 5031 build jobs,
7114 declarations including 6177 theorems. Both source scans are empty and
recursive auditing of all public and private declarations reports only
Classical.choice, propext and Quot.sound. Four logs are frozen.
`Paper.prop_regular_variation` in `ModifiedCartan/RegularVariation.lean` proves
exactly `prop:regular-variation` / `eq:ratio-limit` for the original curve:
T(c*r)/T(r) tends to c^rho locally uniformly over positive multipliers.
The hypotheses are precisely transcendence, linear nondegeneracy, small
ramification and coincidence of both strong indices at an admissible rho.
No extra continuity, convergence, or external analytic hypothesis is introduced.
`CharacteristicRatioLimit` supplies every positive multiplier;
`MonotoneCompactUniformity` supplies uniformity on every compact positive set.
Proof divergences: large multipliers are treated by the reciprocal multiplier
and inversion, instead of a product through a k-th root; compact uniformity is
proved with a finite cover of small endpoint intervals instead of a partition.
The weighted averaging argument uses strict integral inequalities on small
left and right intervals, equivalent to the manuscript's shrinking averages.
M0--M15 are certified. M16 main theorem is now active; the full paper and
sharpness remain incomplete.


## M16 complete: the exact main theorem

Gate `m16-complete-main-theorem` passed: 5032 build jobs,
7124 declarations including 6187 theorems. Both project source scans are empty,
and recursive auditing of every public and private project declaration reports
only Classical.choice, propext and Quot.sound. Four logs are frozen.
`Paper.thm_main` in `ModifiedCartan/MainTheorem.lean` proves the exact
`MainTheoremTarget` for the submitted `thm:main`, with no extra hypotheses.
`exists_common_admissible_order` excludes zero from the already proved common
indices by the actual rational normal form and transcendence.
`Paper.thm_main_explicit_factor` proves that the actual factor T(r)/r^rho is
positive, continuous on positive radii and slowly varying, and proves
T(r)=r^rho*(T(r)/r^rho) at every positive radius. This also certifies `reg`
without restricting the identity to sufficiently large radii.
The assembly follows the manuscript, using the already proved M10, M11 and M15
results and the proved elementary slow-factor lemma from the reusable library.
M0--M16 are certified. M17 sharpness is now active. The entire manuscript is
not yet complete: the sharpness results and remaining inventory entries still
require exact proofs.


## M17 checkpoint: prescribed-system Wronskian

Gate `m17-prescribed-system-wronskian` passed: 5033 build jobs,
7134 declarations including 6196 theorems. Both source scans are empty;
all public/private declarations pass the recursive dependency audit with only
the three allowed foundational principles. Four logs are frozen.
`SharpnessWronskian` proves, for the exact prescribed `IsSharpnessSystem`,
that its Wronskian derivative is zero by a repeated-row calculation, and its
initial jets give W identically 1. It constructs the actual reduced curve,
proves its linear nondegeneracy and zero ramification.
This certifies those constituent clauses of `prop:sharpness-orders`, not the
proposition: entire existence, transcendence and its exact positive asymptotic
constant are still required. The integrable-system lemma and zero-order
sharpness also remain pending. M17 stays active.

## M17 checkpoint: the actual zero-order product is entire

Gate `m17-zero-product-analytic-foundation` passed: 5034 build jobs,
7143 declarations including 6205 theorems. Both source scans are empty and the
recursive public/private audit reports only the three allowed foundational
principles. Four logs are frozen.
`ZeroSharpProduct` proves summability of the actual exponential coefficients,
multipliability at every complex point, uniform product convergence on every
compact set, local uniform convergence, and differentiability of the exact
`zeroSharpFunction`. Its value at zero is 1 and each prescribed -exp(j+1) is
proved to be a root. This is the analytic foundation of `prop:sharpness-zero`;
exact root multiplicities, growth, derivative interlacing and the final ratio
are still required. M17 remains active.

## M17 checkpoint: entire series and every derivative

Gate `m17-entire-series-differentiation` passed: 5035 build jobs,
7147 declarations including 6209 theorems. Both source scans are empty; the
recursive dependency audit passes with only the three allowed foundational
principles. Four logs are frozen.
`EntireSeries` proves that actual term bounds summable on every disk give an
entire sum and convergence of the termwise derivatives to every finite order,
using holomorphic local uniform convergence. It will be applied to explicit
solution coefficients. No solution existence or differential equation is
assumed by this helper. M17 remains active.

## M17 checkpoint: constructive solution coefficients

Gate `m17-actual-solution-coefficients` passed: 5036 build jobs,
7164 declarations including 6221 theorems. Both source scans are empty and
recursive auditing passes with only the three allowed foundational principles.
Four logs are frozen.
`SharpnessCoefficients` defines the actual positive recursive coefficients for
y^(q)=z^k*y, proves their descending-factorial recurrence, and proves a summable
majorant for every fixed disk. The construction applies to every q>=1 and
k>=0, rather than just the inherited exponential examples.
The resulting entire solutions, exact initial jets and equation are being
assembled next. M17 remains active; no sharpness proposition is yet certified.

## M17 checkpoint: prescribed entire initial-value system

Gate `m17-prescribed-entire-system` passed: 5039 build jobs,
7194 declarations including 6249 theorems. Both source scans are empty and
the recursive public/private dependency audit reports only Classical.choice,
propext and Quot.sound. Four logs are frozen.
`SharpnessBaseSolutions` proves entire sparse-series solutions of y^(q)=z^k*y,
every normalized initial jet, and the exact differential equation.
`EntirePrimitives` constructs every finite sequence of normalized entire
primitives. `SharpnessSystemExistence.sharpnessSystem_exists` assembles the
literal prescribed (n+1)-st order entire system, for every allowed n,k,q,
with no existence hypothesis. Together with `SharpnessWronskian`, this gives
actual reduced nondegenerate examples with W=1. The exact positive asymptotic
constant and transcendence remain to be proved; neither sharpness proposition
nor the integrable-system lemma is certified yet. M17 remains active.
The series-and-primitives construction expands the manuscript's invocation of
entire ODE solutions into an explicit kernel-checked existence proof; it does
not change the specified system or initial data.

## M17 checkpoint: actual integrable diagonal kernels

Gate `m17-integrable-diagonal-kernels` passed: 5040 build jobs,
7205 declarations including 6258 theorems. Both source scans are empty and
the recursive dependency audit reports only the three allowed foundational
principles. Four logs are frozen.
`DichotomyKernels` defines both signed, truncated exponential kernels appearing
in `lem:integrable-system`, proves their norm is at most one, proves measurable
and integrable products with every L1 input, and proves that both integral
branches tend to zero. Subtraction of inputs commutes with the operator.
The forward-branch split-tail proof is replaced by direct dominated convergence
on the fixed half-line; the result and hypotheses are unchanged. Derivatives,
contraction, fundamental-system independence and extension are still required.
M17 remains active.

## M17 checkpoint: differentiated integral equations

Gate `m17-diagonal-integral-differentiation` passed: 5041 build jobs,
7216 declarations including 6268 theorems. Both source scans are empty and
the recursive audit reports only the allowed foundational principles.
Four logs are frozen. `DichotomyPrimitive` identifies both kernel integrals
with explicit normalized primitives and proves u'=a*u+f on the closed
half-line, including the one-sided derivative at its initial endpoint.
Continuity on that half-line is a theorem consequence. The bounded continuous
operator and its contraction are being assembled; M17 remains active.

## M17 checkpoint: actual contraction solutions

Gate `m17-actual-contraction-solutions` passed: 5043 build jobs,
7234 declarations including 6284 theorems. Both source scans are empty;
the recursive audit reports only the allowed foundational principles.
Four logs are frozen. `DichotomyOperator` constructs the actual bounded
continuous vector integral operator and proves its Lipschitz constant is at most
the integral of the perturbation's operator norm. `DichotomyFixedPoint` applies
Banach's theorem when that tail norm is less than one, then derives the ODE and
zero normalization limit for the constructed solution. This is a proved lower
level lemma; the manuscript's L1 assumption must still supply its tail, and the
full fundamental system must be extended to the original starting time.
M17 remains active.

## M17 checkpoint: actual tail fundamental systems

Gate `m17-tail-fundamental-systems` passed: 5045 build jobs,
7240 declarations including 6290 theorems. Both scans are empty and the
recursive audit reports only the three allowed foundational principles.
Four logs are frozen. `DiagonalTail` obtains a sufficiently small tail from
actual integrability, constructs all exponential solutions and proves their
exact vector normalization limits. `DiagonalTailIndependent` proves the
normalized determinant tends to one and constructs a common tail on which the
solutions form a fundamental system at every time. The proof even allows
coincident real parts. The final manuscript lemma still requires conversion
from its Euclidean matrix formulation and extension to its original t0; those
are not assumed. M17 remains active.

## M17 checkpoint: actual linear ODE existence

Gate `m17-actual-linear-ode-existence` passed: 5047 build jobs,
7267 declarations including 6311 theorems. Both scans are empty and recursive
auditing reports only the allowed foundational principles. Four logs are frozen.
`LinearPicardTerms` constructs actual successive integrals, proves the factorial
bound in both time directions and proves summability. `LinearPicardSolution`
proves that the actual sum solves the continuous bounded linear system, with
any prescribed initial time and value. This supplies the existence ingredient
for extension over a compact interval after clipping the coefficient.
The final manuscript lemma's Euclidean formulation, extension, and preservation
of independence remain to be assembled. M17 remains active.

## M17 checkpoint: compact extension ingredients and original continuity domain

Gate `m17-compact-ode-and-halfline-continuity` passed: 5053 build jobs,
7272 declarations including 6316 theorems. Both scans are empty and the recursive
audit reports only allowed foundational principles. Four logs are frozen.
`LinearODECompact` constructs actual solutions for a continuous coefficient on
any compact interval, using a proved clipping and bound, and specializes both
endpoint uniqueness theorems. `DiagonalHalfLine` removes the intermediate global
continuity hypothesis from the tail construction: continuity and integrability
only on the original half-line suffice. Euclidean conjugacy, actual extension
and preservation of independence are being assembled. M17 remains active.

## M17 checkpoint: complete integrable-system lemma

Gate `m17-complete-integrable-system-lemma` passed: 5057 build jobs,
7276 declarations including 6320 theorems. Both source scans are empty and
recursive public/private auditing reports only Classical.choice, propext and
Quot.sound. Four logs are frozen. `Paper.lem_integrable_system` now proves the
exact submitted lemma: continuous integrable Euclidean matrix perturbation,
actual solutions on [t0,infinity), independence at every such time, and the
specified exponential normalization limits. It assumes no solution existence,
ODE extension, asymptotic theorem, or literature result.
Proof detail: direct dominated convergence replaces the manuscript's forward
split-tail estimate; constructive successive-integral series and overlap
uniqueness expand its ODE extension sentence. The internal L1 contraction also
works for coincident real parts, but the public statement retains the paper's
hypotheses. This certifies this lemma, not either sharpness proposition.
M17 remains active: the sharpness equations' exact growth constant, their
ray transformations and circle domination, and the zero-order example's exact
growth/interlacing/ratio are still required.

## M17 checkpoint: uniform disk derivative bounds

Gate `m17-uniform-disk-derivative-bounds` passed: 5059 build jobs,
7312 declarations including 6353 theorems. Both source scans are empty and
recursive auditing reports only Classical.choice, propext and Quot.sound.
All four logs are frozen. `ScaledJets` computes the actual derivative along
each radial segment. `SharpnessDerivativeBounds` uses the exact differential
equation and the prescribed initial jets in the proved Gronwall inequality.
For every R>=1, |z|<=R and 0<=i,j<=n it proves
|f_j^(i)(z)| <= R^(i*k/q) exp(R^(1+k/q)). No growth assumption is introduced.
M17 remains active: the determinant lower bound and ray growth calculation,
the circular constant, and the zero-order example remain to be completed.

## M17 checkpoint: sharpness circle domination

Gate `m17-sharpness-circle-domination` passed: 5061 build jobs,
7319 declarations including 6360 theorems. Both scans are empty; all recursively
audited dependencies are the three allowed foundational principles. Four logs
are frozen. `IsSharpnessSystem.abs_log_vector_norm_le` proves the manuscript's
`eq:sharpness-domination`, uniformly on whole disks for every R>=1, using the
actual prescribed solutions, their proved derivative bounds, and W=1.
Alternative proof: `DeterminantRowBounds` uses the Leibniz determinant expansion
instead of Hadamard's inequality. This introduces only a fixed factorial
constant, which is absorbed into the required constant C. The statement and
its hypotheses are unchanged. M17 remains active; the ray asymptotic and exact
circular constant, and the zero-order example, are still pending.

## M17 checkpoint: integrable first-order gauge

Gate `m17-integrable-first-order-gauge` passed: 5064 build jobs,
7350 declarations including 6386 theorems. Both scans are empty and the recursive
audit reports only allowed foundational principles. Four logs are frozen.
`FirstOrderElimination` proves the actual entrywise commutator cancellation.
`FirstOrderError` constructs M(t)=I+C/t, proves its inverse tends to I and exists
on a tail, and proves continuity, the t^(-2) norm bound and integrability of
E(t)=t^(-2)M(t)^(-1)((B-bI)C+C). `FirstOrderGaugeSolutions` proves by actual
differentiation that Z=M(t)t^b X solves Z'=(L+B/t)Z when X solves the proved
integrable-error equation. M17 remains active; the transformed fundamental
system and its application to the prescribed sharpness equation are next.

## M17 checkpoint: diagonal first-order asymptotics

Gate `m17-diagonal-first-order-asymptotics` passed: 5066 build jobs,
7356 declarations including 6392 theorems. Both scans are empty and the
recursive audit reports only the three allowed logical principles. Four logs
are frozen. `FirstOrderGaugeAsymptotics` proves the actual power-gauge
normalization limit and preservation of independence. `FirstOrderDiagonalTail`
assembles a genuine fundamental system for Z'=(diag(lam)+B/t)Z when B has the
common real diagonal b, with t^(-b) exp(-lam_j*t) Z_j -> e_j.
This uses the fully proved integrable perturbation theorem and the actual
near-identity error. Alternative proof detail: distinct complex eigenvalues
suffice; the stronger internally proved integrable-system result permits equal
real parts. Thus spectral real-part coincidences need not be excluded at this
stage. M17 remains active; applying this to the concrete companion equation,
scalar primitives and the exact circular integral is still required.

## M17 checkpoint: explicit Fourier companion

Gate `m17-explicit-fourier-companion` passed: 5068 build jobs,
7395 declarations including 6426 theorems. Both scans are empty and recursive
public/private auditing reports only allowed foundational principles. Four logs
are frozen. `SharpnessFourier` constructs the actual qth roots of unity, proves
their injectivity, and proves both inverse identities for the literal Fourier
matrices using finite geometric sums. `SharpnessCompanion` proves their exact
diagonalization of the cyclic companion and proves that conjugating the degree
diagonal produces the common diagonal entry (q-1)/2. These are the exact matrix
facts required by sharpness Step 2. M17 remains active; the actual scalar ray
transformation and its growth consequences are next.

## M17 checkpoint: actual scaled ray equation

Gate `m17-actual-scaled-ray-equation` passed: 5072 build jobs,
7448 declarations including 6472 theorems. Both scans are empty; the recursive
audit permits only Classical.choice, propext and Quot.sound. Four logs are frozen.
`RayPowerClock` proves the exact inverse clock, derivatives and limits.
`RayScaledDerivatives` differentiates the literal normalized derivatives of an
entire scalar solution. `RayScaleAlgebra` proves the power balance and the top
row closure from the actual equation y^(q)=z^k*y. `RayCompanionSystem` assembles
the exact matrix equation with cyclic leading part and the degree diagonal
correction -beta/(rho*t). No transformed-system hypothesis is assumed.
M17 remains active: Fourier conjugation and the concrete ray fundamental system,
scalar growth and circle integration, and the zero-order example are pending.

## M17 checkpoint: concrete ray fundamental system

Gate `m17-concrete-ray-fundamental-system` passed: 5076 build jobs,
7476 declarations including 6495 theorems. Both project scans are empty; the
recursive audit reports only Classical.choice, propext and Quot.sound. Four
logs are frozen. `RayFourierSystem` proves the literal conjugation of the actual
scaled scalar equation. `RayPhases` supplies the exact exponential phases,
including all power-balance identities. `FirstOrderPiTail` converts the proved
integrable-error construction to actual finite coordinate vectors.
`RayCompanionAsymptotics.rayCompanion_tail_fundamental_system_exists` constructs
an actual linearly independent family on a real half-line, solving the cyclic
companion equation and tending, after its exact power/exponential normalization,
to the explicit root vector. The first normalized coordinate tends to 1.
No asymptotic basis is assumed. This remains a dependency of
`prop:sharpness-orders`; the proposition itself and `prop:sharpness-zero` remain
unproved. M17 is active. Next: constant-coefficient comparison by initial-value
uniqueness, scalar log growth, primitive asymptotics and the circle integral.

## M17 checkpoint: ray comparison and logarithmic growth

Gate `m17-ray-comparison-log-growth` passed: 5080 build jobs,
7507 declarations including 6525 theorems, empty scans in both libraries,
and only the three permitted foundational principles in the recursive audit.
Four logs are frozen. `LinearODESpan` proves constant-coefficient spanning by
initial-value uniqueness. `RayMatrixContinuity` supplies the literal continuous
matrix-to-operator bridge. `RaySolutionExpansion` proves that every actual
entire scalar solution has a constant-coefficient expansion in the constructed
ray fundamental family. `PowerExpLog` proves that a nonzero normalized limit
`t^(-b)*exp(-lam*t)*f(t)` implies `log(norm(f(t)))/t -> Re(lam)`.
These prove dependencies, not the remaining sharpness propositions. M17 remains
active: positive-rate primitives, exact ray/circle limits and the zero-order
example are still required.

## M17 checkpoint: positive-rate ray primitives

Gate `m17-positive-rate-ray-primitives` passed: 5084 build jobs,
7541 declarations including 6556 theorems, empty scans in both libraries, and
only permitted foundational principles. Four logs are frozen.
`WeightedPrimitive` proves negligible primitive errors from a scalar derivative
fence. `PowerExpProfile` proves the exact derivatives, norms and growth of the
actual power/exponential profiles. `PowerExpPrimitive` proves the primitive
ratio limit c/lam whenever Re(lam)>0. `RayPrimitives` applies this to the actual
ray clock and proves repeated entire primitives retain a nonzero normalized
leading coefficient, with the exact shifted power b + m*(1-rho)/rho.
Proof divergence in sharpness Step 2: the manuscript's integration-by-parts
and absolute-error estimate is expanded using a derivative fence for the
primitive error. It proves the same exact asymptotic, including the coefficient,
and needs no additional hypothesis. M17 remains active; sharpness propositions
are not yet proved. Next: realize modes inside the prescribed solution space,
prove the upper rate and vector ray limit, and integrate the exact indicator.

## M17 checkpoint: realized modes and upper rates

Gate `m17-realized-modes-and-upper-rates` passed: 5089 build jobs,
7581 declarations including 6594 theorems. Both scans are empty; the recursive
public/private audit reports only permitted foundational principles. Four logs
are frozen. `SharpnessCombinations` constructs arbitrary jets by the actual
inverse Wronskian matrix. `RayModeRealization` proves that each actual companion
mode is the scaled derivative jet of a constant combination of the prescribed
entire solutions; a positive mode therefore supplies a nonzero scalar primitive
asymptotic in that very solution space. `ExponentialUpperRate` and
`RayUpperPrimitives` prove that finite sums, constant multiplication, real powers
and repeated primitives retain the required upper exponential rate.
`ScalarRayGrowthUpper` applies these to every coordinate of the prescribed
system. There is no assumed change-of-basis or growth premise in these
applications. M17 remains active: combine the upper/lower vector limits, prove
the root indicator geometry and circle integral, and finish the zero-order
example. The two sharpness propositions remain unproved.

## M17 checkpoint: exact vector ray limit

Gate `m17-exact-vector-ray-limit` passed: 5091 build jobs, 7593 declarations
including 6606 theorems. Both library scans are empty and the recursive audit
reports only the three permitted foundational principles. Four logs are frozen.
`VectorRayGrowth` proves the vector logarithmic limit from coordinate upper
rates and an actual controlled scalar lower mode. `SharpnessRayLimit` supplies
that mode from the prescribed solution system and proves the limit in both ray
time and the original radius. For every ray with a positive maximal spectral
real part H, the actual Euclidean coordinate log norm divided by r^rho tends
to H/rho. All initial-value, primitive and norm comparison steps are proved.
This is the analytic content of `eq:sharpness-ray-limit`; the geometry establishing
the condition almost everywhere and the exact circle average are still pending.
M17 remains active, and neither sharpness proposition is claimed complete.

## M17 checkpoint: exact sharpness characteristic asymptotic

Gate `m17-exact-sharpness-characteristic-limit` passed: 5096 build jobs,
7645 declarations including 6657 theorems. Both scans are empty and the recursive
audit permits only the three foundational principles. Four logs are frozen.
`SharpnessRootIndicator` proves positivity almost everywhere from the zero root
sum and a countable cosine-zero set. `RootIndicatorSectors` proves period 2*pi/q
and the cosine formula on the centered sector. `RootIndicatorIntegral` proves
the exact period integral and q+k-period rescaling. `SharpnessRayAE` discharges
all spectral premises. `SharpnessCharacteristicLimit` proves the exact positive
limit q*sin(pi/q)/(pi*rho) by dominated convergence of the actual coordinates.
Divergence: use a countable exceptional set on the whole real angle line; equal
real parts do not need exclusion in the proved asymptotic system. The angular
integral uses [0,2*pi], as in mathlib, with the same exact manuscript constant.
Transcendence must still be attached to certify `prop:sharpness-orders`.
M17 remains active; the zero-order example is pending.

## M17 checkpoint: complete positive-order sharpness

Gate `m17-complete-sharpness-orders` passed: 5099 build jobs,
7654 declarations including 6666 theorems. Both project scans are empty;
the recursive audit reports only Classical.choice, propext, and Quot.sound.
All four logs are frozen. `PolynomialCurveGrowth` and
`RationalCharacteristicGrowth` prove logarithmic characteristic growth for an
actual polynomial representation, so the exact positive power limit forces
transcendence. `SharpnessOrders` proves the exact submitted
`Paper.prop_sharpness_orders`, together with
`Paper.prop_sharpness_orders_realized`, which constructs the prescribed system
for every permitted n, k, q. The exact characteristic constant, reducedness,
linear nondegeneracy, Wronskian one, and transcendence are all proved.
M17 remains active: `prop:sharpness-zero` is pending. The introductory scalar
`thm:A` also remains in the outstanding manuscript inventory.


## M17 checkpoint: zero-product growth and actual Rolle roots

Gate `m17-zero-product-growth-and-rolle` passed: 5105 build jobs,
7683 declarations including 6694 theorems. Both source scans are empty and the
recursive audit has only the three permitted foundational dependencies.
Four certificate logs are frozen. `EntireDerivativeNontrivial` proves that
an entire function with a vanishing iterated derivative is a genuine polynomial.
`ZeroSharpRealRoots` proves nonpolynomiality of the actual infinite product,
nontriviality of every derivative, and reality on the real axis.
`ZeroSharpRolle` constructs a strictly decreasing actual root sequence for every
D_m g, with roots between -exp(j+m+1) and -exp(j+1).
`FiniteRootCountingLower` embeds selected distinct roots into the actual
analytic-multiplicity fibers and proves a quantitative counting lower bound.
`ZeroSharpCountingLower` obtains N(D_m g,0,r) >= log(r)^2/2-(m+1)*log(r)-1.
`ZeroSharpMajorant` proves the uniform disk estimate
|g(z)| <= exp(log(r)^2/2+A*log(r)+B), with actual fixed nonnegative A,B.
Its exact exponential-grid recurrence replaces the manuscript's two tail
geometric estimates with the same required growth accuracy.

Proof divergence for `prop:sharpness-zero`: use Rolle directly on the actual
entire derivatives and their ordered zeros, followed by Cauchy/Jensen upper
bounds. No finite-product Hurwitz step or classification of all derivative
zeros is needed for the exact proposition. M17 remains active; the full
zero-order sharpness conclusion is not yet certified.

## M17 complete: exact zero-order sharpness

Gate `m17-complete-sharpness-zero` passed: 5110 build jobs,
7718 declarations including 6728 theorems. Both source scans are empty;
all public/private declarations depend only on Classical.choice, propext,
and Quot.sound. All four certificate logs are frozen.
`ZeroSharpWronskian` constructs the exact reduced curve, proves its literal
factorial-times-D_n g Wronskian and linear nondegeneracy, and identifies its
ramification with the derivative zero count. `QuadraticLogDerivative` proves
Cauchy and Jensen upper bounds with the same leading quadratic coefficient.
`ZeroSharpCurveBounds` bounds the actual Euclidean characteristic on both sides.
`QuadraticLogLimits` proves the limiting quotients, order zero, and transcendence
criterion. `SharpnessZero` proves the exact `Paper.prop_sharpness_zero` target:
the prescribed product converges, the exact curve is transcendental and linearly
nondegenerate of order zero, and its ramification/characteristic ratio tends to 1.
Both the characteristic and every derivative zero count divided by log(r)^2
tend to 1/2. M17 is complete, with `prop:sharpness-orders` also certified.

The manuscript still has two explicit quoted results awaiting certification:
`Paper.lem_NH` and `Paper.thm_A`. They are not assumed by the certified proofs.
The full-paper goal remains active until this remaining coverage is proved.


## M18 checkpoint: local characteristic and fractional circle kernels

Gate `m18-circle-kernels-and-local-characteristic` passed: 5115 build jobs,
7753 declarations including 6759 theorems. Both source scans are empty;
the recursive dependency audit reports only Classical.choice, propext, and
Quot.sound. All four logs are frozen.
`SineHalfPower` proves integrability of |sin(theta)|^(-1/2) on every finite
interval from Jordan's inequality and reflection. `CircleSingularHalfPower`
proves a uniform K*r^(-1/2) bound for the actual circle average of
|z-a|^(-1/2), including singularities on the circle.
`DiskCharacteristic` defines counting from the actual closed-disk divisor,
proves local Jensen and nonnegativity at a regular nonzero center, and proves
agreement with global counting/characteristic for globally meromorphic functions.
`DiskBoundaryMean` bounds the absolute boundary logarithmic mean by twice the
local characteristic plus log^+(1/|h(0)|). `CircleMomentProximity` proves the
fractional-moment logarithmic averaging bound by an elementary logarithm tangent.

These are dependencies of `Paper.lem_NH`; they do not yet prove that result.
The local disk definition avoids an unjustified global meromorphicity premise:
mathlib's global divisor otherwise defaults to zero for a merely local function.
The log tangent with an additive constant replaces probability-space Jensen;
this proves the exact inequality needed by the manuscript's estimate.
M18 remains active. The exact `lem:NH` and scalar `thm:A` remain outstanding.

## M18 checkpoint: finite circle sums and local analytic dependencies

Gate `m18-local-divisor-and-poisson-dependencies` passed: 5120 build jobs,
7776 declarations including 6782 theorems. Both source scans are empty;
the recursive audit has only the three permitted foundational dependencies.
All four logs are frozen. `CircleSingularSums` proves integrable fractional
moments and proximity bounds for arbitrary finite weighted pole sums, with
all coefficient mass inside a single logarithm. `DiskDivisorMass` controls
actual local absolute divisor mass by the outer local characteristic and the
negative central logarithm. `DiskRegularRadius` constructs a regular boundary
radius in every permitted interval, including discrete modifications of the
original meromorphic function. `LocalReducedPair` constructs analytic local
numerators and entire polynomial-factor denominators without common zeros.
`LocalPoissonMajorant` proves local scalar Poisson majorization, removing
boundary zero radii by a limit from within the original disk.

All local results retain only the original local analytic/meromorphic premises.
The next dependency is the local characteristic comparison in the radius,
followed by all differentiated Poisson--Jensen estimates and the exact NH bound.
`Paper.lem_NH` and `Paper.thm_A` remain unproved; M18 and the full-paper goal
remain active. The preceding alternative proofs are recorded as dependencies,
not as substitutes for either missing manuscript statement.

## M18 checkpoint: exact local characteristic monotonicity

Gate `m18-local-characteristic-monotonicity` passed: 5122 build jobs,
7785 declarations including 6791 theorems. Both project scans are empty;
all recursive dependencies are the permitted foundational principles.
All four logs are frozen. `LocalPairMean` proves exact radial monotonicity
of the circle mean of log(max(|p|,|q|)) for an actual local analytic pair
without common zeros. `LocalPairCharacteristic` identifies that mean minus
log|q(0)| with the actual disk characteristic, using the actual pole divisor
and local Jensen, and proves `diskCharacteristic_mono` for every permitted
pair of positive radii. No global extension or regular-boundary condition
is added to the original meromorphic hypotheses.

The NH proof will use the proved first Poisson--Jensen formula, exact singular
kernel derivatives, and Cauchy estimates for the remaining analytic term.
This avoids unnecessary repeated differentiation under a boundary integral;
the resulting exact radius estimate is still to be assembled and certified.
`Paper.lem_NH` and `Paper.thm_A` remain outstanding. M18 stays active.

## M18 checkpoint: all derivative orders of the local decomposition

Gate `m18-all-derivative-decomposition` passed: 5126 build jobs,
7813 declarations including 6817 theorems. Both source scans are empty;
the recursive audit has only Classical.choice, propext, and Quot.sound.
All four logs are frozen. `LocalKernelBounds` proves arbitrary-radius
reflected and boundary kernel bounds and the needed local Cauchy estimate.
`LocalPoissonRemainder` constructs the actual analytic remainder, bounds
all of its iterated derivatives, and proves the actual singular-plus-remainder
logarithmic derivative identity. `MeromorphicDerivativeDecomposition` proves
codiscrete congruence for all derivative orders and the exact higher pole terms.
`LocalProximityArithmetic` proves finite-sum and finite-product proximity
inequalities under meromorphicity only on the averaging circle.

Proof divergence for `lem:NH`: apply Cauchy to the analytic reflected/boundary
remainder and differentiate the finite singular part exactly. This avoids a
higher boundary-integral differentiation theorem while preserving the full
local estimate. The NH constants and exact radius logarithms still need to be
assembled. `Paper.lem_NH` and `Paper.thm_A` remain outstanding; M18 is active.

## M18 checkpoint: complete Nevanlinna--Hiong estimate

Gate `m18-complete-nevanlinna-hiong` passed: 5134 build jobs,
7847 declarations including 6849 theorems. Both project source scans are empty;
the recursive audit reports only Classical.choice, propext, and Quot.sound.
All four logs are frozen. `Paper.lem_NH` in `NevanlinnaHiong.lean` proves the
exact submitted local estimate, including arbitrary allowed positive radii,
the infinite outer radius, all derivative orders, and all six logarithmic terms.
The local disk characteristic agrees with the standard characteristic whenever
the function is globally meromorphic. No global extension, regular boundary,
or auxiliary control hypothesis is added to the final theorem.

The proof constructs regular interior radii and the actual finite divisor,
uses the half-power circle kernel for the differentiated singular part, and
Cauchy estimates for all derivatives of the analytic Poisson--Jensen remainder.
The proved ordered-partition identity then controls h^(k)/h. An explicitly
constructed control sum is eliminated by the finite-sum logarithm inequality.
This is a fully proved alternative to the cited literature theorem; the
fractional-moment logarithm tangent and Cauchy remainder steps are the recorded
proof divergences. Every intermediate scalar control premise is discharged.

Only the introductory scalar `Paper.thm_A` remains uncertified in the result
inventory. M18 and the full-paper goal remain active. The next dependencies
are exact scalar meromorphic definitions, representation/counting bridges,
and deficiency-sector quantization; no cited scalar theorem is assumed.


## M18 checkpoint: general entire product with prescribed divisor

Gate `m18-general-entire-divisor-product` passed: 5139 build jobs,
7901 declarations including 6895 theorems. Both project scans are empty,
and the recursive audit contains only the three permitted foundational
principles. All four logs are frozen.

`CorrectedLinearFactor` proves uniform polynomial approximation on a smaller
disk from the already proved Taylor remainder estimate, and constructs the
exponential correction of a linear factor. `DivisorCopies` proves countability
and compact finiteness of the actual divisor copies. `CorrectedDivisorFactor`
proves the exact simple zero and the prescribed geometric error bound.
`DivisorEntireProduct` proves local uniform convergence and entire analyticity
of the full product and every subproduct. `DivisorEntireMultiplicity` isolates
each finite fiber and proves the exact multiplicity at every point, including
zero. `exists_entire_with_nonnegative_divisor` has no growth hypothesis.

This construction supplies the missing general Weierstrass-product dependency
of scalar `thm:A`. Polynomial logarithm corrections at geometrically decreasing
errors replace an explicit variable-genus formula. It is a proved alternative,
not an assumed source result. Only `Paper.thm_A` remains uncertified in the
manuscript result inventory; M18 and the full-paper goal remain active.

## M18 checkpoint: exact global scalar lift and counting bridges

Gate `m18-scalar-lift-and-counting-bridges` passed: 5144 build jobs,
7933 declarations including 6919 theorems. Both source scans are empty;
all recursive dependencies are the allowed foundational principles.
All four logs are frozen.

`GlobalMeromorphicPair` constructs the reduced entire numerator and denominator
for every globally meromorphic function, including the zero germ as (0,1).
It proves the actual positive/negative divisor identities. `ScalarDefinitions`
records the exact scalar rationality, critical count, classical characteristic,
lower limiting deficiency, and ScalarTheoremATarget. The target is a proposition
definition only. `ScalarCurveLift` constructs the transcendental linearly
nondegenerate n=1 lift from scalar transcendence, without assuming a lift.
`ScalarRamificationBridge` proves the exact critical-divisor and integrated-count
equalities with the Wronskian, including ramified poles. `ScalarCharacteristicBridge`
proves the exact scalar maximum-norm mean formula with the actual denominator
trailing coefficient, and a uniformly bounded difference from the Euclidean
curve characteristic. Poles at the origin are permitted throughout.

The proved lift, divisor cancellation, and Jensen/norm comparison are explicit
representation bridges used in the alternative reduction of A(a) to the already
certified n=1 main theorem. They do not assert the scalar growth or deficiency
conclusions. Only Paper.thm_A remains uncertified; M18 remains active.

## M18 checkpoint: exact scalar Theorem A(a)

Gate `m18-scalar-theorem-a-growth` passed: 5146 build jobs,
7942 declarations including 6928 theorems. Both project scans are empty,
and all recursively audited dependencies are Classical.choice, propext,
and Quot.sound. All four logs are frozen.

`BoundedGrowthTransfer` proves asymptotic equivalence from a bounded difference
and equality of the literal extended-real lower/upper growth orders; infinite
orders are retained rather than truncated. `ScalarTheoremGrowth` proves
`Paper.thm_A_growth`, the complete submitted conclusion (a), with the original
scalar hypotheses: actual meromorphicity, transcendence, finite lower order,
and N1=o(T). It constructs the reduced lift, transfers both hypotheses through
the proved bridges, and applies the certified n=1 main theorem. The common
order is m/2 for an integer m >= 2, and T is asymptotic to r^rho times a positive
continuous slowly varying function. No lift or sector premise is added.

This is the recorded alternative proof of A(a). It does not prove the remaining
conclusion A(b): integer deficiency multiplicities and their exact complete sum.
Paper.thm_A and the full-paper goal remain active until that conclusion is proved.

## M18 checkpoint: literal scalar deficiency foundations

Gate `m18-scalar-deficiency-foundations` passed: 5148 build jobs,
7957 declarations including 6943 theorems. Both project source scans are empty;
the full recursive audit reports only Classical.choice, propext, and Quot.sound.
All four verification logs are frozen.

`ScalarValueCharacteristic` proves divergence of the actual scalar characteristic
for every transcendental meromorphic function, with no order or ramification
premise, and exact finite-value inversion/translation identities. The verified
mathlib first main theorem gives a uniform bounded difference for every target
value and convergence of every value-characteristic ratio to one.
`ScalarDeficiencyBasics` proves that the literal EReal lower limiting deficiency
lies in [0,1], that counting upper limits lie in [0,1], and the exact formula
`scalarDeficiency_eq_one_sub_limsup_counting`. Actual real proximity/counting
limits identify the deficiency; conversion to a real preserves its value only
after its finiteness has been proved. Codiscrete representative changes preserve
the deficiency. No default infinite sum or infinite-value conversion is used.

These are exact first-main-theorem consequences needed by A(b). The integer
weights and complete sum are still outstanding. The full Paper.thm_A and M18
remain active; the independently certified Paper.thm_A_growth remains A(a).


## M18 checkpoint: exact scalar local two-phase limits

Gate `m18-scalar-two-phase-local-limits` passed: 5152 build jobs,
7969 declarations including 6955 theorems. Both source scans are empty;
all recursive logical dependencies are the three allowed foundational principles.
All four verification logs are frozen.

`LocalAffineMaximum` retains the exact local affine-maximum identity from the
proved essential-phase propagation and Lipschitz-representative construction.
`TwoPhaseLocalForm` proves that two opposite gradient values give exactly a
linear real part, its negative, or its absolute value, with the actual central
value. `UnitaryPowerGradient` proves the actual power-chart subharmonicity,
weak chain rule, and constant gradient polynomial. `ScalarPowerGradient`
specializes this to the actual n=1 quadratic, constructs both opposite roots,
and proves the three local formulas for the actual component logarithmic limits.
No quadratic equation or affine form is introduced as a premise of the scalar
paper theorem.

This is an explicit local alternative to the source paper's potential-theoretic
classification, using the already certified finite-gradient argument. Global
sector continuation, identification of actual asymptotic values, and the
integer deficiency sum remain to be proved. The complete Paper.thm_A remains
undeclared and M18 remains active.

## M18 checkpoint: actual homogeneous scalar norm profile

Gate `m18-scalar-homogeneous-norm-profile` passed: 5157 build jobs,
7989 declarations including 6973 theorems. Both source scans are empty, and
every recursive dependency is Classical.choice, propext, or Quot.sound.
All four logs are frozen.

`TwoPhaseForms` proves preservation of the explicit local forms under a root
sign change and a maximum of two continuous functions. `TwoPhaseHomogeneous`
proves that actual radial homogeneity eliminates every affine intercept.
`ScalarNormTwoPhase` constructs an actual basis and applies one common root
to both coordinates, yielding local two-phase formulas for their actual maximum.
`ScalarNormLocalAbsolute` combines these formulas with the already proved
homogeneity and nonnegativity to prove the exact local absolute-real-part
formula for U, with the actual canonical quadratic coefficient retained.
`ScalarNormSquare` gives the branch-independent pointwise square formula and
proves the scalar coefficient is a nonzero monomial. Its nonvanishing is forced
by the previously certified unit-circle average one, not assumed.

This is the explicit local-to-coefficient alternative needed for A(b). The
pending global power-profile and angular normalization are separate steps;
actual sector values and the full integer deficiency sum are still outstanding.
M18 and the full Paper.thm_A remain active.

## M18 checkpoint: normalized scalar polar profile

Gate `m18-scalar-normalized-polar-profile` passed: 5161 build jobs,
8003 declarations including 6987 theorems. Both source scans are empty;
the full recursive audit reports only Classical.choice, propext, and Quot.sound.
All four verification logs are frozen.

`ScalarNormPowerProfile` proves the actual global disk profile
U(z).toReal = |Re(kappa*z^rho)| with kappa nonzero, including the origin
and the principal-power branch cut. `ScalarCosineIntegral` proves the exact
integral 4 over a full circle for every positive half-integer frequency and
any phase, using the already certified q=2 root-indicator integral.
`ScalarPowerPolar` identifies the polar expression by equality of squares.
`ScalarNormNormalizedProfile.scalar_norm_polar_profile` constructs a phase
phi and proves U(R*exp(i*theta)).toReal = (pi/2)*R^rho*|cos(rho*theta+phi)|
for every 0<R<2 and every theta. The amplitude is deduced from the actual
unit-circle average one. No angular-profile or sector-value premise is added.

This continues the documented alternative local classification proof. Actual
asymptotic values, their sector multiplicities, and the complete deficiency
sum remain outstanding. The full Paper.thm_A remains undeclared; M18 and
the full-paper goal remain active.

## M18 checkpoint: spherical path control through poles

Gate `m18-scalar-spherical-path-control` passed: 5165 build jobs,
8038 declarations including 7018 theorems. Both project scans are empty;
all recursive logical dependencies are Classical.choice, propext, and Quot.sound.
All four logs are frozen.

`ScalarSphereProjection` constructs explicit reduced-pair projective coordinates
in Complex x Complex and proves common-scalar invariance. Its real path derivative
is expressed exactly using W=q*p'-p*q'; the derivative norm is at most
|W|/(|q|^2+|p|^2). The verified mean-value theorem then proves the endpoint path
bound without excluding poles of either scalar chart. `ScalarSphericalSpeed`
identifies the denominator with the squared Euclidean norm, proves the exact
Wronskian formula for arbitrary pairs, proves gauge cancellation and the absolute
dilation factor, and applies the path estimate to actual holomorphic curves.

This explicit coordinate proof replaces a dependence on an undeveloped abstract
spherical metric API. It proves a tool for the actual asymptotic-value argument,
not the existence of those values. The remaining good-path construction,
sector continuation, and deficiency sum are still active work in M18.

## M18 checkpoint: compact target and actual exponential speed decay

Gate `m18-scalar-compact-target-and-speed-decay` passed: 5167 build jobs,
8067 declarations including 7045 theorems. Both project scans are empty;
the recursive dependency audit reports only the three permitted foundations.
All four logs are frozen.

`ScalarSphereValues` proves that the explicit target map on WithTop Complex is
injective and its range is a concrete closed bounded sphere in Complex x Complex.
Every sequence of target values therefore has a convergent subsequence in these
coordinates; infinity is included. Reduced-pair coordinates are identified with
the actual finite quotient when its denominator is nonzero.
`ScalarSphericalDecay` proves uniform exponential bounds for monic polynomials
from bounded roots and small normalized degree. It applies this to the actual
Wronskian, then proves the physical curve speed bound using the original small
ramification and equal positive growth indices. The norm lower bound required
along a path is explicit and remains to be constructed on suitable paths.

This supplies compactness and the precise analytic estimate needed for actual
asymptotic values. It does not yet identify those values or prove A(b). Work
continues with good paths and the exact deficiency sum; M18 remains active.

## M18 checkpoint: proved polynomial good-line construction

Gate `m18-polynomial-good-lines` passed: 5173 build jobs,
8086 declarations including 7062 theorems. Both source scans are empty;
all recursive dependencies are Classical.choice, propext, and Quot.sound.
All four verification logs are frozen.

`GoodLineIntegral` proves the interval supremum bound by the function integral
and an integrable derivative majorant. `GoodLineSelection` proves the exact
Fubini first-moment selection while preserving any almost-everywhere side
condition, and proves that almost every horizontal line avoids every zero
of an entire sequence of nonzero polynomials. `LogNormPathDerivative` derives
actual real path derivatives by local complex logarithms, eliminating their
branch. `LogNormLineEstimate` converts those formulas into a uniform log-error
bound. `PolynomialGoodLine.polynomial_exists_good_horizontal_line` constructs
an actual zero-free line and bounds its entire log-modulus error by the two
planar error integrals.

This proves the initial alternative to the source's exceptional-disk construction.
The connection to actual local convergence, good paths within sectors, fixed
asymptotic values, and the complete deficiency sum still remain; M18 is active.

## M18 checkpoint: actual local log limits yield good lines

Gate `m18-local-log-limits-to-good-lines` passed: 5175 build jobs,
8096 declarations including 7071 theorems. Both project scans are empty;
all recursively audited dependencies are the three allowed foundations.
All four verification logs are frozen.

`ComplexRectangleIntegral` proves exact measure and integral transfer between
the compact complex rectangle and product coordinates. Local L1 convergence
therefore gives both integrability and vanishing planar error integrals.
`PolynomialGoodLineLimit` derives the polynomial logarithmic derivative limit
from the already proved first log-derivative theorem, then proves that every
positive error tolerance eventually admits a zero-free horizontal line with
uniform error below that tolerance. The gradient convergence needed by the
selection is proved, not included as an extra hypothesis.

The smooth local limit and its weak gradient are explicit in this intermediate
analytic lemma. Their construction for positive scalar sectors, the transfer
to the physical curve, and the eventual fixed-value/deficiency argument remain
active work. The full scalar Paper.thm_A is still undeclared.

## M18 checkpoint: polynomial lower bounds control the physical speed

Gate `m18-polynomial-gauge-lower-and-speed` passed: 5176 build jobs,
8100 declarations including 7075 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs
are frozen under this gate name.

`PolynomialGaugeLower` proves the uniform norm error is eventually at most
one and proves that any actual unitary polynomial component with log-modulus
at least delta*T forces actual gauge log-norm at least (delta/2)*T.
Combining the proved gauge transfer with the original curve hypotheses gives
physical rescaled spherical speed at most exp(-(delta/2)*T) at those same
points. This connects the constructed polynomial paths to the physical curve;
no uniform lower bound for the curve is silently inferred from L1 convergence.

The remaining work is positive-region smoothness and path geometry, continuation
to fixed asymptotic values, and the exact scalar deficiency quantization and sum.
The full `Paper.thm_A` remains undeclared and M18 remains active.

## M18 checkpoint: smooth positive norm limits and vertical good lines

Gate `m18-positive-norm-smoothness-and-vertical-lines` passed: 5178 build jobs,
8115 declarations including 7090 theorems. Both source scans are empty and
all recursive dependencies are the three permitted foundations. Four logs
are frozen.

`ScalarNormSmooth` proves the square-root formula including the origin,
then infinite real smoothness wherever the actual norm limit is positive.
It constructs the actual classical weak gradient on every open subset of
this region and proves the horizontal path derivative formula.
`PolynomialVerticalLine` proves vertical zero-free line selection, the exact
vertical logarithmic derivative estimate, and uniform errors tending to zero
on constructed vertical lines from actual local L1 convergence. Product-measure
swapping is proved explicitly; multiplication by I preserves the error norm.
The vertical derivative of a differentiable real function is also identified
with its classical complex gradient.

These results supply the smoothness and both line directions needed for the
path argument. Actual dominant components, connected paths, fixed asymptotic
values, and the scalar deficiency sum remain active work in M18.

## M18 checkpoint: constructed actual dominant component

Gate `m18-actual-dominant-component` passed: 5179 build jobs,
8117 declarations including 7092 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarDominantComponent` proves that positive balanced two-component maxima
are strictly attained, then applies the actual paper basis-at-point theorem.
It constructs a further subsequence, actual unitary matrices, a component and
a positive ball on which the selected polynomial normalized log converges in
local L1 to the already fixed norm limit. Every selected polynomial is proved
nonzero from the actual extended-log source finiteness. All positivity and
neighborhood equality are conclusions, not extra curve assumptions.

This supplies the actual input for the good-path construction near positive
good centers. The fixed asymptotic values and exact deficiency sum are pending;
M18 and the full-paper goal remain active.

## M18 checkpoint: actual good crosses and physical path diameters

Gate `m18-actual-good-crosses-and-path-diameters` passed: 5181 build jobs,
8132 declarations including 7106 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarSphericalLine` extends the actual curve path estimate to any two points
of an interval and proves the scaled horizontal and vertical diameter bounds.
`ScalarGoodCross` combines actual component convergence, derived smooth weak
gradients, both good-line constructions, and physical speed transfer. Its
existence theorem starts from the original curve hypotheses and a positive
good center and constructs the subsequence, positive neighborhood, and
intersecting lines. On each line the physical rescaled spherical speed is at
most exp(-(delta/2)*T), with the norm lower bound supplied by the actual limit
on the compact rectangle. No path or derivative convergence is assumed.

Continuation across positive sectors, fixed asymptotic values, and the exact
scalar deficiency quantization and sum remain active work. M18 is not complete.

## M18 checkpoint: convex contact and global power-chart norm profile

Gate `m18-convex-contact-and-global-chart-profile` passed: 5185 build jobs,
8151 declarations including 7123 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.
The newly used mathlib convex-extrema module was compiled from the pinned source.

`ConvexAffineContact` proves the required interior contact comparison by a
reflection argument followed by mathlib's proved local-minimum theorem.
`ScalarPowerChartProfile` proves the exact derivative-times-coordinate identity,
transforms the actual weighted coefficient, and extends the norm profile to
all chart points mapping into the radius-two disk. `ScalarPowerDomain` defines
and proves openness, convexity, inclusion, and center membership for the actual
positive chart region. These ingredients support extending the selected
component beyond its initial neighborhood, without importing an unproved
maximum principle or assuming sector dominance.

The actual extension, connected paths and fixed-value deficiency argument remain
active; the full scalar theorem A(b) is not yet certified.

## M18 checkpoint: actual component on a connected positive chart

Gate `m18-actual-positive-sector-component` passed: 5187 build jobs,
8165 declarations including 7136 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarPositiveChart` proves the power chart has nonzero derivative, applies the
proved analytic open-mapping theorem, and establishes openness, connectedness,
radius-two inclusion and center membership for the actual positive chart image.
`ScalarSectorComponent` constructs a positive central quadratic root and proves
the norm is its positive affine phase in that chart. The component chosen from
the actual balanced basis has proved convexity in the power chart; the proved
contact comparison extends its equality with the norm limit over the entire
positive chart image. Its actual nonzero unitary polynomial sequence therefore
converges locally in L1 to that same norm limit there.

This replaces the earlier small-neighborhood restriction by a connected chart
region, with no sector dominance assumption. It remains to connect physical
paths across chart regions and scales and prove the fixed asymptotic values
and exact scalar deficiencies. M18 remains active.

## M18 checkpoint: constructed nonempty chart and physical small crosses

Gate `m18-constructed-positive-chart-paths` passed: 5190 build jobs,
8175 declarations including 7145 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarPositiveCenters` proves the good centers meet every nonempty open subset
of the disk and constructs a positive good center from the actual normalized
polar profile. `ScalarCrossDiameter` proves the full physical spherical diameter
bound for any pair of points on a selected cross, including different segments.
`ScalarChartPaths.scalar_exists_positive_chart_with_small_crosses` starts from
the original scalar curve hypotheses, constructs a positive chart, actual
subsequence and component, and then constructs exponentially small physical
crosses in every compact rectangle inside the chart. The positive log-norm
lower bound is obtained from compactness and is not an extra hypothesis.

This completes the local chart path input. The outstanding work is geometric
continuation across charts and scales, fixed target values, and the exact scalar
proximity limits and deficiency sum. M18 remains active.

## M18 checkpoint: quantitative target gluing and finite rectangle connectivity

Gate `m18-target-gluing-and-rectangle-connectivity` passed: 5193 build jobs,
8189 declarations including 7157 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarValueGluing` proves that halving bounds for consecutive target projection
steps give an actual limit target, including infinity, with distance at most twice
the current error. It specializes this to exponential weights with an explicit
scale increment bound. These are generic gluing lemmas; actual target-step
bounds across scales remain to be constructed. `ScalarScaleSeparation` derives
the required characteristic increment and halving of exponential weights at
doubled radii from the original curve hypotheses and the proved regular variation.
`RectangleConnectivity` constructs interior rectangle neighborhoods and proves
that any two points of an open connected domain are connected by a finite
inductive chain of rectangle links.

The geometric connection between selected paths, its extension across scales,
and the final scalar proximity/deficiency statements remain active. No fixed
asymptotic values or full theorem A(b) are claimed by this checkpoint.

## M18 checkpoint: overlapping rectangles and physical three-segment bridges

Gate `m18-overlapping-rectangle-bridges` passed: 5195 build jobs,
8228 declarations including 7175 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`RectangleBridge` proves that the common horizontal strip and combined vertical
interval of two overlapping rectangles lie in their union. Actual horizontal
speed estimates on both rectangles and a vertical estimate on this bridge give
an explicit spherical distance bound along three physical line segments.
`ComplexRect` packages nondegenerate rectangles, overlap and bridge geometry,
and proves finite connectivity by overlapping rectangles inside an open
connected domain. No assumption that independently chosen crosses intersect
is used. Fixed asymptotic values and scalar deficiency quantization remain open.


## M18 checkpoint: actual adjacent physical anchors

Gate `m18-adjacent-physical-anchors` passed: 5197 build jobs,
8235 declarations including 7181 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarRectangleCrosses` packages the exponential speed estimates as the
literal property `HasSmallRectangleCrosses` and constructs this property on
a nonempty open connected positive chart from the original curve hypotheses.
`ScalarAdjacentAnchors` proves that selected horizontal anchors on any two
overlapping contained rectangles have spherical distance tending to zero.
The proof selects an actual vertical bridge and estimates all three segments.
Common subsequence targets, full asymptotic values and exact deficiencies
remain separate outstanding conclusions.


## M18 checkpoint: simultaneous horizontal selections

Gate `m18-simultaneous-horizontal-selections` passed: 5198 build jobs,
8259 declarations including 7190 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarHorizontalSelection` chooses globally indexed good horizontal lines
for every contained rectangle from the proved cross property. It proves that
the selected physical anchors of any two rectangles in an open connected
domain have distance tending to zero, by induction over a finite rectangle
chain. The selections add no analytical hypothesis: their existence is proved.
Fixed asymptotic values and the deficiency assertions remain outstanding.


## M18 checkpoint: common chart target and exponential finite chains

Gate `m18-common-chart-target-and-exponential-chains` passed: 5201 build jobs,
8271 declarations including 7201 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarChartTarget` proves one subsequence and one actual sphere target work
for every selected rectangle anchor in an open connected domain; each selected
horizontal line converges uniformly to that target. `ScalarActualChartTarget`
constructs this data on an actual positive chart from the original curve
hypotheses and an actual positive good center.
`ScalarAnchorExponential` retains a positive exponential rate for differences
between any two selected anchors at the same scale, using minimum rates and
finite path lengths. This same-scale bound is not asserted to be a rate of
approach to a fixed target across scales.

The outstanding scalar A(b) work still includes fixed asymptotic values across
scales, exact proximity limits, integer sector counts and their total sum.


## M18 checkpoint: overlap uniqueness and geometric chart centers

Gate `m18-overlap-uniqueness-and-geometric-centers` passed: 5203 build jobs,
8273 declarations including 7203 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarTargetOverlap` proves equality of targets on overlapping open domains
when they use the same physical sequence, even with independently chosen lines.
`ScalarChartDominance` removes the good-center requirement on the geometric
power-chart center. It constructs a good center inside the positive chart,
selects a component attaining the norm there, and uses proved convex affine
contact to identify that component on the entire chart. Its actual nonzero
polynomials converge locally in L1 to the actual norm limit.

This permits geometrically chosen sector centers. Across-scale fixed targets,
exact proximity limits and the full scalar theorem remain outstanding.


## M18 checkpoint: actual full positive peak chart

Gate `m18-full-positive-peak-chart` passed: 5205 build jobs,
8281 declarations including 7211 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarPeakChart` proves the actual unit-circle norm upper bound pi/2,
constructs a unit peak center, and proves its actual quadratic root is the
positive real number pi/2. The proof tests the phase in the normalized conjugate
direction and uses the exact polar norm profile. A positive real root makes the
positive power domain equal to the entire inner right-half power domain.
`ScalarGeometricTarget` constructs actual selected-line targets for arbitrary
geometric positive-root charts and, in particular, this full peak chart.
The targets remain common subsequence targets on selected lines; across-scale
asymptotic values and the exact deficiency statement remain outstanding.


## M18 checkpoint: finite explicit peak directions

Gate `m18-finite-peak-directions` passed: 5206 build jobs,
8302 declarations including 7230 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarPeakDirections` defines the explicit circle rotations and proves their
unit norm, natural power identity, and injectivity on Fin m. The actual
monomial quadratic is invariant under those rotations. Consequently there are
m distinct unit peak centers, with m >= 2 and rho=m/2, each carrying the actual
positive real root pi/2. This checkpoint counts centers; sector coverage and
deficiencies are not conclusions of the center count.


## M18 checkpoint: exact finite positive-sector partition

Gate `m18-exact-finite-positive-sector-partition` passed: 5209 build jobs,
8341 declarations including 7267 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarSectorRoots` proves the explicit rotations exhaust all roots of unity
using the inspected and proved mathlib primitive-root theorem, and rewrites the
actual scalar quadratic as one monomial. `ScalarSectorGeometry` proves distinct
peak centers give disjoint full positive charts: their two preimages have the
same square and positive real parts. `ScalarSectorCover` constructs a chart
preimage for every actual positive norm point from its positive quadratic root.
The positive part of the radius-two disk is therefore exactly partitioned into
m nonempty open connected charts, with m >= 2 and rho=m/2.

This is an exact geometric statement about the constructed rescaling limit.
It does not yet identify fixed asymptotic values or prove scalar deficiencies.


## M18 checkpoint: complete actual limit-data reindexing

Gate `m18-complete-actual-data-reindexing` passed: 5210 build jobs,
8361 declarations including 7285 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ArbitraryRadiusReindex` reindexes every field of the actual arbitrary-radius
data, including polynomial replacement, dependent root multiplicities,
coordinate and norm limits, coefficients, radial means and good centers.
The actual norm and coefficient limit functions are retained unchanged.
This supplies the missing actual-data input for successive finite extraction;
it adds no assumed convergence or auxiliary mathematical principle.


## M18 checkpoint: simultaneous finite-sector targets

Gate `m18-simultaneous-finite-sector-targets` passed: 5212 build jobs,
8364 declarations including 7288 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarFiniteTargets` proves that a finite family of actual cross domains has
one common subsequence, preserving all cross estimates and supplying one
target per domain with anchor and uniform selected-horizontal-line convergence.
`ScalarFinitePeakTargets` constructs the simultaneous crosses and targets for
every finite family of actual unit peak centers. Successive extractions use
the complete actual-data reindexing, so the norm and coefficient limits remain
unchanged. Targets of different sectors are allowed to coincide.

These are simultaneous subsequence targets. Their independence across scales,
the exact proximity limits and the deficiency formula remain outstanding.


## M18 checkpoint: constructed finite sector subsequence data

Gate `m18-constructed-sector-subsequence-data` passed: 5213 build jobs,
8400 declarations including 7307 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarSectorData` packages the actual finite positive-region partition,
unit peak center, quadratic roots, common subsequence, cross estimates, target
family and anchor limits. Its existence theorem constructs every field from
the original curve hypotheses and actual arbitrary-radius data. Uniform limits
on the selected horizontal lines follow from the proved anchor and diameter
bounds. The data type is accompanied by this construction, and is not used as
an unproved replacement for any paper conclusion.

Across-scale target independence and the exact scalar deficiencies remain open.


## M18 checkpoint: integer sector-target multiplicities

Gate `m18-integer-sector-target-multiplicities` passed: 5214 build jobs,
8413 declarations including 7319 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarSectorMultiplicity` defines the multiplicity of each actual subsequence
target as the number of sectors mapping to it, including the target at infinity.
Finite fiber counting proves finite support and an exact HasSum equal to m=2 rho.
The construction allows different sectors to have the same target.

This counts the constructed subsequence targets. Identifying these counts with
rho times the scalar deficiencies still requires the across-scale analytic proof.

## M18 checkpoint: gauge-independent spherical potential limit

Gate `m18-gauge-independent-spherical-potential-limit` passed: 5217 build jobs,
8433 declarations including 7337 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarSpherePotential` defines the concrete physical potential
2 log EuclideanNorm(F) - log |W(F)|, proves exact gauge cancellation and the
physical dilation identity, and proves compact integrability at every real
scale. `LocalLpEventualEquality` transfers limits without ignoring membership
of the exceptional initial terms. `ScalarSpherePotentialLimit` proves local
L1 convergence of the actual normalized physical potential to twice the actual
norm limit, using the proved small polynomial-log estimate and log(r)/T(r) -> 0.

This is the spherical version of the derivative-potential step in the scalar
source proof, needed for comparing phases at nearby radii. Variable dilation,
across-scale target independence and the exact deficiencies remain to prove.

## M18 checkpoint: variable dilation and scalar normalization

Gate `m18-variable-dilation-and-scalar-normalization` passed: 5219 build jobs,
8443 declarations including 7347 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`VariableDilation` proves that pushforward of area under dilation c>=1 is
bounded by area on a containing image set. It transfers vanishing local errors
through c_n in [1,2]; compact uniform continuity then gives the exact local
measure limit for c_n -> c. `VariableScaling` derives variable-multiplier ratios
from the existing compact-uniform regular-variation theorem, proves physical
potential measurability, and transfers convergence under convergent scalar
multipliers. No pointwise convergence of the original potentials is assumed.

These are the analytic change-of-scale tools. The scalar deficiency assertion
has not yet been obtained from them.

## M18 checkpoint: exact comparable-radius limit compatibility

Gate `m18-exact-comparable-radius-limit-compatibility` passed: 5221 build jobs,
8458 declarations including 7362 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarComparableLimits` combines the actual physical dilation identity,
variable dilation, proved regular variation and homogeneity. Normalized physical
potentials at c_n r_n have the same local measure limit as at r_n when
c_n -> c in [1,2]. Any actual limit data subsequently constructed at those
radii has exactly the same norm limit on disk 2. `ScalarComparableBounded`
removes the convergence condition on c_n by compactness and subsequence
extraction. Only the bound c_n in [1,2] remains.

This proves compatibility of the actual angular shapes. Fixed asymptotic target
values and their exact proximity ratios still require the across-scale paths.

## M18 checkpoint: original-curve potential slow change

Gate `m18-original-curve-potential-slow-change` passed: 5223 build jobs,
8463 declarations including 7367 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarSphereIsometry` proves that an actual Euclidean matrix isometry has
determinant norm one, using the proved singular-value product formula. Thus
both the raw and normalized physical spherical potentials are exactly invariant
under the constructed coordinate normalization, including critical points.
`ScalarPotentialSlowChange` proves, for the original curve and every r_n tending
to infinity and c_n in [1,2], local convergence in measure to zero of the
difference of its normalized potentials at c_n r_n and r_n.

This is the actual slow-change assertion for the physical potential. It is
proved by arbitrary-radius construction and subsequence extraction; no angular
phase map or fixed asymptotic target is assumed. Deficiency identification
remains outstanding.

## M18 checkpoint: compact continuous angular profile family

Gate `m18-compact-continuous-angular-profile-family` passed: 5227 build jobs,
8481 declarations including 7384 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarQuadraticProfile` expresses every actual scalar potential limit as
sqrt(2 (|C z^m| + Re(C z^m))), with m=2 rho and |C|=(pi/2)^2.
The formula is jointly continuous without argument branches, including zero
rays and the origin. `ScalarProfileUniqueness` proves coefficient uniqueness
from pointwise or AE agreement on the unit disk. `ScalarProfileContinuity`
proves uniform convergence on compacts for convergent coefficients and the
converse implication from local measure convergence on the coefficient circle.
`ScalarProfileCompactness` constructs an actual local L1 profile subsequence
for every original radius sequence, retaining the original physical potential.

This replaces cosine phase representatives with an equivalent uniquely
determined complex coefficient. The remaining global coefficient choice and
path gluing must still be constructed before proving the scalar deficiencies.

## M18 checkpoint: constructed slow phase and coherent peak centers

Gate `m18-constructed-slow-phase-and-coherent-peak-centers` passed: 5232 build jobs,
8549 declarations including 7442 theorems. Both source scans are empty;
all recursive dependencies are the three permitted foundations. Four logs frozen.

`ScalarPhaseChoice` constructs an actual minimizer of the physical L1 profile
error at every radius, proving compactness, continuity and existence.
`ScalarPhaseApproximation` proves its minimum error tends to zero and the
chosen profile approximates the actual physical potential locally in L1.
`ScalarPhaseSlowChange` proves that the actual chosen coefficient changes by
a quantity tending to zero between arbitrary comparable radii. It also
identifies its subsequential limit with the coefficient of actual limit data.
`ScalarRootCorrection` transports m-th roots by a principal correction near one.
`ScalarPeakTracking` recursively constructs actual coherently numbered unit
peak centers at dyadic radii, proves the exact peak equation, and proves
successive centers differ by a quantity tending to zero.

The phase and peak-center choices are now constructed and proved, not assumed.
The remaining cross-scale spherical paths and exact proximity asymptotics are
still required for scalar deficiencies and the full thm:A.

## M18 checkpoint: uniform phase change and actual peak identification

Gate `m18-uniform-phase-change-and-actual-peak-identification` passed: 5234 build
jobs, 8553 declarations including 7446 theorems. Both source scans are empty;
recursive logical dependencies are exactly the three permitted foundations.
All four verification logs are frozen.

`ScalarPhaseUniformity.scalarPhaseCoefficient_slow_change_uniform` strengthens
the constructed phase estimate to all comparable multipliers c in [1,2]
uniformly at sufficiently large physical radii. `ScalarPhasePeakLimits`
identifies the quadratic polynomial of actual limit data from its continuous
profile and proves that every limit of constructed phase peaks is an actual
unit peak satisfying the exact quadratic-root equation.

These are proved consequences of actual curve hypotheses, not extra phase or
root assumptions in the scalar theorem. Cross-scale path gluing and exact
proximity asymptotics remain necessary for scalar A(b); full thm:A is not yet
declared.

## M18 checkpoint: original-curve crosses from constructed phase peaks

Gate `m18-original-curve-crosses-from-constructed-phase-peaks` passed: 5236 build
jobs, 8559 declarations including 7452 theorems. Both source scans are empty;
recursive logical dependencies are the three permitted foundations. Four logs
are frozen.

`ScalarPhaseIsometry` proves exact invariance of physical spherical speed,
profile error, and the chosen minimizing phase under the actual Euclidean
normalization. It transfers rectangle crosses back to the original curve.
`scalar_phase_peaks_subsequence_crosses` starts with actual convergent phase
peaks of the original curve and constructs one physical subsequence supplying
all full-sector cross estimates. No coordinate nonvanishing assumption is
added to the original curve.

Scalar A(b) still requires across-scale fixed targets and exact proximity
asymptotics; current sector targets remain subsequential.

## M18 checkpoint: uniform moving peak crosses and endpoint bridges

Gate `m18-uniform-moving-peak-crosses-and-endpoint-bridges` passed: 5241 build
jobs, 8585 declarations including 7476 theorems. Both source scans are empty;
recursive dependencies are exactly the three permitted foundations. All four
verification logs are frozen. One initial build attempt had a transient read
failure for an existing mathlib private object; the repeated full build and
recursive audit both passed.

`ScalarPeakDisks` proves rotation of full sectors and constructs one positive
disk width at both unit peaks and their half-radius points, uniformly over
all unit directions. `ScalarMovingCrosses` transfers fixed wide/narrow cross
estimates to moving squares with convergent centers. `PositiveRateCompactness`
proves the diagonal compactness principle that constructs an eventual positive
rate from positive rates on every subsequence refinement.
`ScalarUniformPeakCrosses` applies it to actual phase peaks of the original
curve: the widths and eventual exponential rates are now proved, not assumed.
`ScalarMovingAnchors` constructs exponential endpoint bridges between moving
squares and smaller fixed squares inside the same positive sector.

This replaces quantitative exceptional-disk detours by actual selected
horizontal/vertical paths. Across-scale step gluing and proximity asymptotics
remain outstanding; the full scalar thm:A is not yet declared.

## M18 checkpoint: constructed fixed dyadic targets for all sectors

Gate `m18-constructed-fixed-dyadic-targets-for-all-sectors` passed: 5248 build
jobs, 8635 declarations including 7508 theorems. Both source scans are empty;
recursive dependencies are exactly the three permitted foundations. All four
logs are frozen.

`ScalarExponentialBounds` absorbs constants, concatenates paths, and promotes
subsequence bounds to a full-sequence positive rate. `ScalarMovingLines`
constructs actual horizontal choices and proves their exact change of
coordinates at double physical radius. `ScalarMovingConnections` joins two
moving anchors through a finite chain inside one positive sector.
`scalar_dyadic_peak_anchor_steps` constructs the across-scale connection using
the old half-radius center and the new unit center; its exponential step bound
is a proved consequence of the original curve and actual coherent phase.
`ScalarEventualGluing` handles finite initial segments in quantitative summation.

`scalar_exists_dyadic_peak_target` constructs every field of
`ScalarDyadicPeakTargetData`: actual line bounds, a fixed sphere target, full
dyadic-sequence convergence, and an exponential error. Applying this to the
coherently numbered m peaks constructs all fixed dyadic targets in
`scalar_exists_all_dyadic_sector_targets`. Their integer multiplicities have
HasSum 2 rho, proved in `scalar_dyadic_target_multiplicities_hasSum`.

This is full dyadic-sequence target convergence, strengthening the earlier
subsequence-only targets. Extension to arbitrary radii and exact proximity
asymptotics, and hence equality with deficiencies, are still required for
scalar A(b). Full Paper.thm_A remains undeclared.

## M18 checkpoint: sharp physical cross rates and radial corridors

Gate `m18-sharp-physical-cross-rates-and-radial-corridors` passed: 5251 build
jobs, 8655 declarations including 7528 theorems. Both source scans are empty;
recursive dependencies are exactly the three permitted foundations. Four logs
are frozen.

`ScalarSharpSpeed` improves the actual Taylor replacement lower bound to any
strict positive exponential margin and transfers it to the physical spherical
speed. `scalar_component_good_cross_sharp` constructs actual horizontal and
vertical line estimates at every positive rate k strictly below 2u whenever
the actual norm limit is at least u on the rectangle. The exact coefficient
2 is retained for the later proximity calculation.
`scalarFullSector_uniform_radial_disks` constructs a uniform neighborhood of
any compact positive radial interval below radius two, in every unit direction.

These sharpen the already constructed fixed dyadic targets. Their connection
to arbitrary radii and exact scalar deficiencies is still outstanding; the
multiplicity count is not yet a deficiency identification.

## M18 checkpoint: target uniqueness and variable-width connections

Gate `m18-fixed-target-uniqueness-and-variable-width-connections` passed:
5256 build jobs, 8664 declarations including 7536 theorems. Both source scans
are empty; recursive dependencies are exactly the three permitted foundations.
All four logs are frozen.

`ScalarDyadicLineTargets` proves exponential convergence uniformly on the
entire selected physical horizontal segment. `scalar_dyadic_peak_target_unique`
proves the fixed target for a numbered actual peak is independent of the width
and line selections. `ScalarDyadicTargetRefinement` constructs the target data
at any proved admissible width, including a width valid over the entire radial
corridor [1/2,1]. `ScalarVariableAnchors` and `ScalarVariableConnections`
extend the endpoint bridges and finite path connections to centers and widths
that both vary and converge.

This justifies later geometric refinements without resetting the target.
Arbitrary-radius target identification and exact proximity/deficiency formulas
are still unproved; full Paper.thm_A remains undeclared.

## M18 checkpoint: dyadic decomposition and comparable-scale transfers

Gate `m18-exact-dyadic-decomposition-and-comparable-scale-transfers` passed:
5261 build jobs, 8707 declarations including 7576 theorems. Both source scans
are empty; recursive dependencies are exactly the three permitted foundations.
All four verification logs are frozen.

`ScalarComparablePeaks` constructs actual peaks at every comparable radius,
proves their exact root equations and unit norms, and proves their displacement
from the starting peak tends to zero. `ScalarScaledLines` retains the exact
physical segment and anchor coordinates under positive radius changes.
`ScalarScaledHorizontalBounds` transfers the exponential line bounds through
varying ratios in [1,2] and a proved comparison of normalization scales.
`ScalarDyadicDecomposition` constructs the actual index n and multiplier c with
r=c*2^n, c in [1,2] for r>=1, and proves n->infinity as r->infinity.
`CharacteristicComparableBounds` derives one characteristic comparison constant
uniformly over c in [1,2] from regular variation, and converts positive
exponential error rates from T(2^n) to T(r).

The remaining connection of arbitrary-radius anchors to the fixed targets is
specified in work/M18-plan.md. Exact proximity and deficiency identification
remain unproved; full Paper.thm_A remains undeclared.

## M18 checkpoint: comparable-radius anchors share the fixed target

Gate `m18-comparable-radius-anchors-share-the-fixed-target` passed:
5265 build jobs, 8712 declarations including 7581 theorems. Both source scans
are empty. The recursive audit reports only Classical.choice, propext and
Quot.sound. All four logs are frozen under the gate name.

`scalar_comparable_peaks_have_horizontal_lines` constructs actual good lines
at radii c_nu*2^(n_nu), with c_nu in [1,2], from the transported phase peaks.
`scalar_horizontal_line_at_dyadic_ceiling` retains their exact physical points
at the common larger scale 2*2^(n_nu). The actual original-curve cross bounds,
variable-width connections, and radial corridor disks prove
`scalar_comparable_anchor_target_subsequence`. Compactness of the multipliers
and unit peak directions, followed by the positive-rate diagonal lemma, proves
`scalar_comparable_anchor_fixed_target` for the whole sequence, on the actual
scale T(c_nu*2^(n_nu)). No convergence of the original phase or multipliers is
assumed. These are auxiliary results for LaTeX thm:A (b).

This implements the alternative spherical-path proof recorded above. The next
wrappers instantiate all new line choices and the exact dyadic decomposition of
an arbitrary escaping radius sequence. Exact proximity and deficiency formulas
are still unproved, and full Paper.thm_A remains undeclared.

## M18 checkpoint: constructed fixed targets at arbitrary radii

Gate `m18-constructed-fixed-targets-at-arbitrary-radii` passed: 5268 build
jobs, 8725 declarations including 7592 theorems. The scans are empty and the
recursive dependencies are exactly the three permitted foundations. All four
logs are frozen.

`scalar_comparable_peaks_have_fixed_target` constructs both the horizontal
line choices and exponential convergence to the already fixed dyadic target.
`scalarRadiusPeakCenter` extends the coherent numbering using the exact dyadic
index and multiplier; its unit norm and exact phase equation are proved.
`scalar_arbitrary_radii_have_fixed_target` now applies to every escaping real
radius sequence, with error exp(-eta*T(r_nu)) at the actual physical anchors.
Its proof clips only a finite initial segment below radius one and then uses
eventual equality; it adds no hypothesis to the original curve assumptions.
`scalarRadiusSectorCenter_eq` proves that all m numbered peaks use one common
rotation at every radius. `scalar_exists_all_radial_sector_targets` constructs
all refined target data simultaneously.

These results finish the arbitrary-radius fixed-target connection used in the
alternative proof of LaTeX thm:A (b). The exact proximity asymptotics and the
identification of target multiplicities with deficiencies remain to be proved.
Full Paper.thm_A remains undeclared.

Next dependency: specified-rate rectangle crosses -> finite connections that
preserve that rate -> connected strict level regions of the actual norm limit
-> sharp approach to the fixed target -> exact proximity and deficiency formula.
The first three steps are being proved from existing sharp physical speed
bounds and actual component limits, without supplying a new analytic premise.

## M18 checkpoint: sharp level crosses and rate-preserving paths

Gate `m18-sharp-level-crosses-and-rate-preserving-paths` passed: 5273 build
jobs, 8747 declarations including 7611 theorems. Source scans are empty;
recursive dependencies are only the three permitted foundations. All four
logs are frozen.

`HasRectangleCrossesAtRate` records the actual specified speed bound.
Its horizontal selections have exactly that rate. The adjacent-rectangle
bridge and `ScalarHorizontalSelection.anchors_close_at_rate` preserve the
rate through any finite path; only the multiplicative length changes.
`scalarLevelChart` is the power-chart image of a convex strict half-plane
cut. Its openness, preconnectedness, inclusion in the positive chart, and
strict lower bound for the actual norm limit are proved.
`scalar_component_crosses_at_rate` derives a positive compact margin from
kappa<2U and constructs actual crosses with rate kappa.
`scalar_exists_sharp_level_crosses` uses one actual component subsequence for
all positive rates and their level regions. Finally,
`scalar_phase_peak_subsequence_sharp_crosses` transfers these exact estimates
to the original curve using the proved phase-peak identification and exact
Euclidean-isometry invariance. No extra component or speed premise is added
to this final construction theorem.

This continues the alternative spherical-path proof of LaTeX thm:A (b).
Moving endpoints must next be connected while retaining the specified rate.
Exact proximity and deficiency identification remain outstanding;
full Paper.thm_A remains undeclared.

## M18 checkpoint: moving paths retain sharp rates and large-scale domination

Gate `m18-moving-paths-retain-sharp-rates-and-large-scale-domination` passed:
5276 build jobs, 8762 declarations including 7626 theorems. Both source scans
are empty and the recursive audit uses only the three permitted foundations.
All four logs are frozen.

`HasRectangleCrossesAtRate.variable_box_anchors` constructs a fixed vertical
bridge for a moving center and converging positive width with the same rate.
`two_variable_box_anchors` connects both endpoints through a finite path and
preserves that rate exactly. `constant_mul_exp_neg_le_eventually` absorbs a
constant with any chosen strictly smaller rate, rather than a fixed loss.
`complex_fixed_shift_sub_tendsto_zero` proves that every fixed dyadic index
shift preserves the limiting coherent peak direction.
`characteristic_large_dyadic_multiple_eventually` chooses a fixed large dyadic
multiplier whose characteristic dominates any prescribed rate at all smaller
comparable radii. The choice follows from proved regular variation.

These are auxiliary steps for LaTeX thm:A (b). The next geometric lemmas give
a positive uniform level margin for the existing target disks and the exact
homogeneous transformation of level regions. They will allow connection to
farther dyadic target anchors, whose target errors and speeds can be made
arbitrarily small on the original radius scale. Exact proximity and deficiency
identification remain unproved; full Paper.thm_A remains undeclared.

## M18 checkpoint: exact level dilations and arbitrarily accurate far targets

Gate `m18-exact-level-dilations-and-arbitrarily-accurate-far-targets` passed:
5279 build jobs, 8780 declarations including 7644 theorems. Source scans are
empty, only the three permitted foundations occur in the recursive audit,
and all four logs are frozen.

`scalarPositiveChart_compact_level_margin` constructs a positive level margin
for any compact subset by a directed open cover. Rotation gives
`scalar_peak_disks_have_uniform_level_margin`, valid for the existing fixed
width and every unit peak direction. `powerChart_positive_dilation` and
`scalarLevelChart_dilation_mem` prove the exact positive-radius transformation
of points and levels, with homogeneous factor t^rho and no coefficient loss.
`ScalarDyadicPeakTargetData.far_target_and_line_bounds` constructs one fixed
positive dyadic shift K such that both the actual reference line speed and its
error from the already fixed target have any prescribed exponential accuracy
on T(c*2^n), uniformly for c in [1,2]. The target and selected physical line
are the existing q data at index n+K.

This completes these geometric and scale dependencies for the alternative
proof of LaTeX thm:A (b). A rate-preserving propagation lemma is being checked
next. The conversion to exact proximity and deficiencies is still outstanding;
full Paper.thm_A remains undeclared.

## M18 checkpoint: constructed sharp propagation to local moving lines

Gate `m18-constructed-sharp-propagation-to-local-moving-lines` passed:
5280 build jobs, 8782 declarations including 7646 theorems. The scans are
empty and the recursive audit reports only the three permitted foundations.
All four logs are frozen.

`HasRectangleCrossesAtRate.moving_box` constructs actual crosses in moving
squares with the specified rate unchanged. The theorem
`moving_box_to_fixed_target` constructs a positive width and actual horizontal
line near any converging center in the connected level domain. It connects
the new line to an actual moving reference segment already approaching a
fixed target. The whole new physical horizontal segment has the same specified
exponential rate. The only changed quantity is the proved finite multiplier.
Every new line and finite path is selected inside the proof.

This is the rate-preserving propagation step of the alternative proof of
LaTeX thm:A (b). Work now includes the exact algebraic conversion from the
compact sphere embedding to the target linear form, including infinity.
Exact proximity and deficiency identification remain outstanding;
full Paper.thm_A remains undeclared.

## M18 checkpoint: exact target linear and logarithmic bounds

Gate `m18-exact-target-linear-and-logarithmic-bounds` passed: 5281 build
jobs, 8799 audited declarations including 7661 theorem declarations. Both
source scans are empty; recursive dependencies are only Classical.choice,
propext, and Quot.sound. All four verification logs are frozen.

`scalarTargetLinearForm_le_sphere_distance` proves linear control of the
actual target form by the compact sphere distance and the reduced pair norm,
including the target at infinity. The proof reconstructs the form using the
entries of the rank-one projection; no square-root loss occurs.
`scalarRescaled_target_exp_bound` retains the exact exponent M - kappa.
`scalarRescaled_target_log_bound_eventually` absorbs the fixed factor with
any positive epsilon, uniformly on actual sets of points and at zeros of the
form, using the extended logarithm. These are auxiliary results for LaTeX
thm:A (b), in the recorded alternative proof via physical spherical paths.

Next signatures: `exists_dyadic_sharp_rate` chooses K with a small positive
rate and an exact rescaling identity; `characteristic_fixed_to_variable_ratio_tendsto`
proves T(L*r_n)/T(c_n*r_n) -> (L/c_0)^rho; `characteristic_sharp_rate_transfer`
converts a strict limiting rate inequality into an eventual inequality.
Dependency DAG: positive real powers + proved regular variation -> exact
radius ratio -> sharp rate transfer -> far-anchor propagation -> target log
identification -> exact proximity -> deficiency quantization and sum.
Exact proximity/deficiencies remain unproved; full `Paper.thm_A` is undeclared.

## M18 checkpoint: exact radius rate transfer and prescribed widths

Gate `m18-exact-radius-rate-transfer-and-prescribed-widths` passed: 5283
build jobs, 8803 declarations including 7665 theorem declarations. Source
scans are empty, only the three permitted foundations occur, and all four
logs are frozen.

`exists_dyadic_sharp_rate` constructs a distant dyadic scale and a positive
rate below any specified margin, with its exact homogeneous rescaling identity.
`characteristic_fixed_to_variable_ratio_tendsto` proves the exact ratio for a
fixed dilation and a varying comparable multiplier. `characteristic_sharp_rate_transfer`
converts any strict limiting inequality into an eventual inequality for actual
characteristics. `moving_box_to_fixed_target_of_width` constructs the propagated
line for any specified width whose closed disk fits inside the level region.

These are auxiliary results for LaTeX thm:A (b). The next combination uses
coherent far dyadic peaks, the fixed target, exact level dilations, sharp
crosses, and the verified rate transfer to construct actual local segments
with every rate below 2U. Their widths may be arbitrarily small. The target
log identification and exact proximity/deficiency formulas are still pending;
full `Paper.thm_A` remains undeclared.

## M18 checkpoint: constructed local target lines at every sharp rate

Gate `m18-constructed-local-target-lines-at-every-sharp-rate` passed: 5285
build jobs, 8806 declarations including 7668 theorem declarations. Empty
source scans and the recursive three-foundation audit passed; four logs are frozen.

`ScalarDyadicPeakTargetData.good_at_rate` and `close_at_rate` independently
check the rate weakening for the already constructed dyadic data.
`scalar_sharp_local_target_lines` now combines those estimates with exact
level dilations and proved regular variation. Given a point in a strict
level above kappa/2, it constructs a fixed distant dyadic shift and a common
subsequence. At every sufficiently small positive width it constructs an
actual horizontal line approaching the same fixed target at rate kappa on
the original characteristic scale. Kappa can be any positive rate strictly
below the doubled profile value. All lines and subsequences are derived.

This is an auxiliary step in the alternative proof of LaTeX thm:A (b).
The coordinate conversion back to the comparable radius is next, followed
by fixed-target logarithmic compactness and identification. Exact proximity
and deficiencies remain unproved; full `Paper.thm_A` remains undeclared.

## M18 checkpoint: sharp target lines in original radius coordinates

Gate `m18-sharp-target-lines-in-original-radius-coordinates` passed: 5287
build jobs, 8815 declarations including 7677 theorem declarations. Both
source scans are empty; only the three permitted foundations occur. Four
verification logs are frozen.

`scalar_horizontal_target_rescale` proves the exact coordinate change for
an arbitrary function on the physical plane, uniformly in c in [1,2].
`scalar_sharp_target_lines_at_comparable_radii` places the previously
constructed sharp segments at the original radii c_n*2^(n_n). For every
sufficiently small epsilon, their horizontal half-width is epsilon and their
height lies within 2*epsilon of the prescribed point. They retain the fixed
target and every rate kappa strictly below the doubled local norm profile.

Next signatures: `scalar_wronskian_le_jet_product` bounds the actual scalar
Wronskian by the two first-jet lengths; `scalar_jet_exp_lower` derives a
lower bound for either column; `scalar_unitary_jet_exp_lower` applies this
to every actual unitary polynomial basis at a good center. DAG: actual
Wronskian lower bound + uniform jet upper bound -> column jet lower bounds
-> non-collapse and fixed-target log compactness -> sharp local identification
-> proximity integral -> deficiency formula. These remain auxiliary results
for LaTeX thm:A (b); full `Paper.thm_A` is not yet declared.

## M18 checkpoint: prescribed unitary log compactness with actual jet bounds

Gate `m18-prescribed-unitary-log-compactness-with-actual-jet-bounds` passed:
5290 build jobs, 8824 declarations including 7686 theorem declarations.
The source scans are empty; recursive dependencies are exactly the three
permitted foundations. All four logs are frozen.

`scalar_wronskian_le_jet_product` and `scalar_jet_exp_lower` derive lower
bounds for both scalar jet columns from the actual determinant and column
upper bounds. `scalar_unitary_jet_exp_lower` proves these for every prescribed
sequence of unitary matrices at an actual good center.
`not_log_collapse_of_jet_exp_lower` and `exists_common_jet_lower_log_limits`
use these bounds to construct nontrivial component limits without assuming
finite jet exponents. `scalar_exists_prescribed_unitary_log_limits` constructs
the limits for any prescribed basis and proves both lie between -U and U.

These support the alternative proof of LaTeX thm:A (b). Next are the explicit
unitary target matrix and a construction with freely prescribed Taylor-error
accuracy. The latter is needed when a component exponent is negative: the
existing data only assert A > 0, so a proof cannot silently assume A exceeds U.
The existing replacement construction permits an arbitrary larger A; a new
existence theorem will record that choice. Then polynomial vertical good lines
can intersect the constructed sharp horizontal target lines to identify limits.
Exact proximity/deficiencies remain outstanding; full `Paper.thm_A` is undeclared.

## M18 checkpoint: target unitary polynomial caps and crossing identification

Gate `m18-target-unitary-polynomial-caps-and-crossing-identification` passed:
5294 build jobs, 8843 declarations including 7702 theorem declarations.
Source scans are empty, all recursive dependencies are the three permitted
foundations, and four logs are frozen.

`scalarTargetUnitary` is an explicit actual unitary matrix for every target,
including infinity. Its first coordinate is exactly the normalized target
linear form; its perturbation bound is proved. `scalarTargetPolynomial_exp_bound`
and `PolynomialReplacementData.scalar_target_log_cap` transfer the sharp
physical sphere estimate to the actual target Taylor polynomial. The required
accuracy inequality is explicit. Both arbitrary-radius construction theorems
with suffix `with_accuracy` construct data meeting any prescribed lower bound
on A from the original curve hypotheses and existing replacement theorem.

`LocalLpConvergence.polynomial_limit_le_of_horizontal_caps` proves a smooth
local logarithmic limit is bounded above by caps on arbitrarily small actual
horizontal segments, even if the subsequence and heights depend on the width.
Its proof intersects each segment with a constructed zero-free vertical good
line and uses the proved logarithmic derivative convergence. This is a general
crossing lemma, not yet the identification of the fixed target's limit.

Next signatures are `actual_norm_eventually_upper_bound` and
`actual_norm_near_point`, deriving uniform bounds from the actual continuous
norm limit while accounting for finite-prefix gauge analyticity. These feed
the sharp polynomial caps; subsequent work identifies -U on matching sectors
and +U for other targets, then proves proximity and deficiency formulas.
All items remain auxiliary to LaTeX thm:A (b); full `Paper.thm_A` is undeclared.

## M18 checkpoint: actual local norm upper bounds

Gate `m18-actual-local-norm-upper-bounds` passed: 5295 build jobs, 8849
declarations including 7708 theorem declarations. Empty source scans,
recursive three-foundation audit, and all four frozen logs are recorded.

`subharmonic_eventually_upper_bound_eventual` removes a finite prefix before
applying the checked compactness upper estimate. `actual_norm_eventually_upper_bound`
then proves the uniform sharp exponential bound for the actual gauged vector
from an upper bound on its continuous norm limit. The proof handles every
original coordinate and absorbs the finite-dimensional norm constant with
an arbitrarily small exponent margin. `actual_norm_near_point` constructs
a positive closed disk around any point with bound U(z) + epsilon.

Next, `scalar_target_horizontal_caps` combines this disk bound with the
constructed target segments and Taylor accuracy. The theorem
`scalar_target_component_le_norm_sub_rate_of_smooth` will use the crossing
lemma to bound the actual fixed-target logarithmic limit by U(z) - kappa
at a smooth point. Coherent-peak compatibility and density of smooth points
will then identify -U throughout matching sectors. Proximity integrals and
exact deficiencies remain pending; full `Paper.thm_A` is still undeclared.

## M18 checkpoint: constructed sharp target bound at smooth points

Gate `m18-actual-target-component-sharp-bound-at-smooth-points` passed:
5297 build jobs, 8852 declarations including 7711 theorem declarations.
Both source scans are empty; the recursive audit uses only the three permitted
foundations. All four gate logs have been frozen.

`PolynomialReplacementData.scalar_target_horizontal_caps` converts the actual
sphere estimates on horizontal segments to sharp polynomial bounds, using the
proved local norm estimate and the explicit Taylor accuracy condition.
`scalar_target_component_le_norm_sub_rate_of_smooth` constructs these segments
from coherent dyadic peaks and proves u(z) <= U(z) - kappa for every admissible
sharp rate at a smooth point of the actual fixed-target logarithmic limit.
These are auxiliary results for LaTeX `thm:A` (b).

Next exact signatures: `scalar_comparable_peak_limit` identifies the limiting
coherent peak with the actual quadratic root; `scalarLevelChart_mem_of_lt`
recovers level membership from U(z); `scalar_target_component_le_neg_norm_of_smooth`
lets kappa approach 2 U(z). Dependency DAG: comparable phase transport ->
actual root -> actual level profile -> sharp smooth bound -> negative limit
at smooth points -> continuity extension -> actual proximity -> deficiencies.
The smoothness restriction will be removed using the proved local two-phase
structure; it is not an extra hypothesis in the final scalar theorem.
Full `Paper.thm_A` and its deficiency conclusion remain undeclared.

## M18 checkpoint: negative target limit at smooth points

Gate `m18-negative-target-limit-at-smooth-points` passed: 5299 build jobs,
8855 declarations including 7714 theorem declarations. Both source scans are
empty and the recursive audit permits only the three foundations; four logs
are frozen.

`ArbitraryRadiusLimitData.scalar_comparable_peak_limit` proves that the limiting
coherent dyadic peak is a unit root of the actual quadratic at comparable
radii. `scalarLevelChart_mem_of_lt` converts the actual norm level into chart
membership. `scalar_target_component_le_neg_norm_of_smooth` now proves
u(z) <= -U(z) on matching positive sectors at smooth points, when the constructed
Taylor accuracy covers U(z). It selects rates strictly below 2 U(z) and uses
the already constructed actual horizontal lines. Auxiliary to LaTeX `thm:A` (b).

Next, smooth patches will be constructed in every open set from the proved
local two-phase alternatives, transported by the analytic power-chart inverse,
and used with continuity to remove smoothness from the target limit theorem.
Actual proximity integrals, deficiency quantization, and the full `Paper.thm_A`
remain pending.

## M18 checkpoint: matching-sector negative bound without smoothness

Gate `m18-negative-target-upper-bound-throughout-matching-sector` passed:
5301 build jobs, 8863 declarations including 7722 theorem declarations. Empty
source scans and the recursive three-foundation audit passed; four logs frozen.

`TwoPhaseSmoothPatches` proves that every nonempty open part of a locally
two-phase limit contains a smooth ball. The absolute-value case is handled
by an explicit displacement off its crease. The analytic inverse power chart
transports these patches to the physical plane. Continuity extends inequalities
from their centers to the entire open region.

`scalar_positive_sector_norm_lt` proves the explicit universal threshold
U(z) < (pi/2) * 2^rho on any unit-centered matching positive sector.
`scalar_target_component_le_neg_norm_on_positive_chart` now proves u(z) <= -U(z)
everywhere in that sector for the actual fixed-target logarithmic component.
The accuracy threshold is supplied by the previously proved arbitrary-accuracy
construction. Smoothness is no longer an assumption. This continuity argument
is a recorded specialized alternative in the proof of LaTeX `thm:A` (b).

Next signatures: constructed `ScalarTargetLogLimitData`, the matching-sector
identity u = -U, and a norm comparison for two distinct target linear forms.
DAG: constructed target limits + negative upper bound + proved lower bound ->
matching identity; independent forms + common limits -> other-target +U ->
actual proximity integrals -> exact deficiencies. `Paper.thm_A` remains pending.

## M18 checkpoint: constructed target limits and matching-sector identity

Gate `m18-constructed-target-limits-and-matching-sector-identity` passed:
5304 build jobs, 8900 declarations including 7743 theorem declarations.
The source scans are empty, the recursive audit uses only three foundations,
and all four logs are frozen.

`ArbitraryRadiusLimitData.exists_scalar_target_log_limit` constructs actual
`ScalarTargetLogLimitData` for every prescribed target after a subsequence.
The data includes proved subharmonicity, convergence, and bounds -U <= u <= U;
its real convergence, regularity, nonzero polynomials, and subsequence stability
are proved. `ScalarTargetLogLimitData.eq_neg_norm_on_positive_chart` combines
these constructed lower bounds with the sharp upper estimate to prove u = -U
throughout the matching sector. This is an exact auxiliary identity for
LaTeX `thm:A` (b), not yet the deficiency formula.

`scalarTargetLinearForm_common_zero` proves distinct target forms independent,
including infinity. `scalar_distinct_target_norm_bound` obtains a finite
comparison constant using the inspected finite-dimensional linear-map theorem.
Next: `norm_eq_max` passes this comparison to the actual logarithmic limits,
and `eq_norm_of_other_neg` will identify +U for distinct targets. The remaining
DAG is both sector identities -> actual proximity convergence -> quantization
and sum -> full `Paper.thm_A`; the last theorem remains undeclared.

## M18 checkpoint: other-target positive-sector identity

Gate `m18-other-target-positive-sector-identity` passed: 5306 build jobs,
8905 declarations including 7748 theorem declarations. Empty source scans,
recursive three-foundation audit, and all four frozen logs are recorded.

`ScalarTargetLogLimitData.norm_eq_max` proves U = max(u_alpha,u_beta) for any
two distinct target limits from the same actual data. It passes the proved
finite norm comparison to common almost-everywhere subsequences, then uses
continuity. `eq_norm_of_other_neg` and `eq_norm_on_other_positive_chart` prove
u_beta = +U throughout a sector assigned to a different target. The auxiliary
matching-target limit is constructed on a further subsequence while retaining
the original prescribed limit. Both sector signs are now proved.

Next signatures: `normalized_log_close_of_margin` for negative finite limits
above the approximation error exponent, `localMeasure_log_transfer_of_margin`,
and an analytic logarithmic compactness upgrade from measure convergence to
local L1. These bridge actual Taylor polynomials to the original components;
then sector integrals must still be identified with actual scalar proximity
and deficiencies. Full `Paper.thm_A` remains undeclared.

## M18 checkpoint: negative log margin and analytic measure upgrade

Gate `m18-negative-log-margin-and-analytic-measure-upgrade` passed:
5308 build jobs, 8909 declarations including 7752 theorem declarations.
All four logs are frozen; source scans are empty and the recursive dependency
audit permits only the three foundational principles.

`normalized_log_close_of_margin` proves both eventual positivity and preservation
of a finite logarithmic limit u whenever -A < u, including negative u.
`localMeasure_log_transfer_of_margin` handles local measure convergence and
null zero sets. `normalized_log_not_collapse_of_localMeasure` excludes collapse
for actual nontrivial analytic logarithms. `normalized_log_localL1_of_localMeasure`
then upgrades finite local measure convergence to local L1 by the already
proved subharmonic compactness theorem and uniqueness.

Next, `exists_analytic_log_limit_of_exponential_approximation` constructs a
nonzero anchor and removes the finite prefix, and `ScalarActualTargetBasics`
connects the actual target forms to their Taylor polynomials. These are needed
before any proximity integral or deficiency can be certified. The scalar
endpoint `Paper.thm_A` remains pending.

## M18 checkpoint: actual target logarithmic limits

Gate `m18-actual-target-logarithmic-limits` passed: 5311 build jobs,
8921 declarations including 7763 theorem declarations. All four logs are
frozen; both library source scans are empty and the recursive dependency audit
uses only Classical.choice, propext, and Quot.sound.

`exists_analytic_log_limit_of_exponential_approximation` constructs nontriviality
of the approximating analytic functions from a finite logarithmic limit and
removes a finite prefix. `scalarActualTarget` is the actual gauged holomorphic
target component. Its analyticity, norm bound, and exponential approximation
are proved. `ArbitraryRadiusLimitData.scalar_norm_lt_explicit_bound` gives the
strict error margin throughout the radius-two disk. Consequently
`ScalarTargetLogLimitData.exists_actual_target_log_limit` constructs a strict
subsequence on which these actual components have the prescribed local L1
logarithmic limit, including negative limits on matching sectors. No additional
nontriviality or smoothness hypothesis is imposed on the final scalar theorem.

Next exact auxiliary statements: continuity and monotonicity of analytic-log
circle means; convergence of these circle means from local L1 convergence;
the bounded comparison between target circle means and actual scalar
proximity; and the sector-integral formula. The dependency DAG is actual
component L1 limits -> circle-mean limits -> proximity ratios -> deficiencies
and multiplicity sum -> full `Paper.thm_A`. The last theorem is still pending.
This is a specialized compactness/integral proof within LaTeX `thm:A` (b).

## M18 checkpoint: analytic logarithmic circle means

Gate `m18-analytic-logarithmic-circle-means` passed: 5312 build jobs,
8926 declarations including 7768 theorem declarations. The four logs are
frozen, scans pass, and the full dependency audit uses only three foundations.

`circleAverage_log_norm_sub_eq_log_max` identifies the logarithmic kernel's
circle mean, including a circle through its zero. The inspected mathlib
factorization theorem yields `analytic_log_circleAverage_finite_formula` with
nonnegative weights. `analytic_log_circleAverage_continuous_monotone` proves
continuity and monotonicity on positive radii for each nontrivial analytic
function on a disk. No exclusion of zero-containing circles is assumed.

Next signatures: `integral_ball_log_norm_eq_radial_mean`,
`analytic_log_circleAverage_weighted_integrable`, and the normalized analytic
circle-mean convergence theorem for local L1 limits with continuous limit.
DAG: finite formula -> weighted integrability; local logarithm integrability ->
polar identity; these + local L1 + monotonicity -> circle-mean limits -> scalar
proximity/deficiency identities. These are auxiliary to LaTeX `thm:A` (b);
`Paper.thm_A` is still pending.

## M18 checkpoint: analytic logarithmic circle limits

Gate `m18-analytic-logarithmic-circle-limits` passed: 5314 build jobs,
8937 declarations including 7779 theorem declarations. Four frozen logs,
empty source scans, and the three-foundation recursive audit certify the gate.

`integral_ball_log_norm_eq_radial_mean` proves polar integration for analytic
logarithms without global measurability assumptions. The finite zero formula
proves weighted integrability at radius zero. The main auxiliary result
`normalized_analytic_log_circleAverage_tendsto` now proves: for nontrivial
analytic f_n on a disk and positive s_n, local L1 convergence of log|f_n|/s_n
to a continuous u implies convergence of the circle means at every interior
positive radius. The proof uses annular integrals and the already verified
monotone weighted-integral convergence lemma, so exceptional zero radii need
not be removed. This is a specialized alternative proof within `thm:A` (b).

Next: apply this result to the constructed actual target limits; identify the
fixed-target function and its exact exponential-gauge circle-mean correction;
then compare the resulting projective proximity with scalar proximity.
DAG: actual target L1 -> actual circle limits -> gauge cancellation -> scalar
proximity limits -> sector multiplicities and deficiencies -> `Paper.thm_A`.
The last theorem is not yet declared.

## M18 checkpoint: actual projective proximity limits

Gate `m18-actual-projective-proximity-limits` passed: 5317 build jobs,
8949 declarations including 7789 theorem declarations. All four logs are
frozen; both source scans and the full recursive three-foundation audit pass.

`ScalarTargetLogLimitData.exists_actual_target_circle_limit` applies the proved
analytic circle convergence theorem to the original target components.
`scalarTargetFunction` is entire and nontrivial by linear nondegeneracy.
`scalarActualTarget_circleAverage_log` identifies the exact harmonic center
correction, including targets with a zero at the origin. The same correction
cancels against the curve norm in `scalarProjectiveProximity_eq_gauged_means`.
`exists_projective_proximity_ratio_limit` constructs a strict subsequence on
which the actual projective proximity divided by the characteristic tends to
one minus the prescribed target-limit circle mean. No proximity convergence
is postulated as an assumption.

Next exact signatures: the actual numerator/target pair norm comparison,
`scalar_proximity_eq_pair_log_means`, a uniform bounded difference between
classical and projective proximity, and the resulting scalar ratio limit.
DAG: actual projective ratio -> bounded comparison -> actual scalar proximity
ratio; sector signs + exact sector integrals -> multiplicity value; all-radius
subsequence argument -> deficiency quantization and full `Paper.thm_A`.
The scalar deficiency conclusion of LaTeX `thm:A` (b) remains pending.

## M18 checkpoint: classical scalar proximity limits

Gate `m18-classical-scalar-proximity-limits` passed: 5321 build jobs,
8975 declarations including 7812 theorem declarations. Four frozen logs,
empty source scans, and the full three-foundation recursive audit are recorded.

The actual numerator/target pair has a proved explicit norm comparison.
`scalar_proximity_eq_pair_log_means` identifies classical proximity, including
infinity, by the actual pair and target means. The normalization constant is
computed exactly. `scalar_proximity_abs_sub_projective_le` proves a uniform
bounded difference for every nonzero radius. `scalar_proximity_ratio_tendsto_of_lift`
transfers the constructed projective limits to the original scalar function
and its own characteristic. In particular,
`ScalarTargetLogLimitData.exists_scalar_proximity_ratio_limit` constructs a
strict subsequence with limit 1 minus the actual target-limit unit-circle mean.
This closes the scalar/proximity bridge without invoking an external theorem.

Next exact signatures: `unit_arc_mem_scalarPositiveChart` and
`ArbitraryRadiusLimitData.scalar_norm_unit_arc`; the circle-integral partition
into m equal arcs; and `circleAverage_of_sector_cosine_profiles`. On the open
arc with |rho*theta| < pi/2, the actual norm must equal (pi/2)*cos(rho*theta),
and the target signs already proved determine its contribution. The DAG is
power-chart arc identity -> exact arc profiles -> finite circular integral ->
sector multiplicity value -> all-radius uniqueness -> full `Paper.thm_A`.
The final deficiency quantization remains pending, as does the change-of-basis
target correspondence for the arbitrary-radius normalization.

## M18 checkpoint: exact sector mean multiplicities

Gate `m18-exact-sector-mean-multiplicities` passed: 5325 build jobs,
9008 declarations including 7845 theorem declarations. All four logs are
frozen; both project source scans are empty and the recursive dependency
audit reports only Classical.choice, propext, and Quot.sound.

`powerChart_unit_arc` and `ArbitraryRadiusLimitData.scalar_norm_unit_arc`
identify the actual open unit-circle arc profile. The circle mean is split
into m adjacent explicit intervals, and `circleAverage_of_sector_cosine_profiles`
computes their integrals without imposing endpoint assumptions.
`ScalarTargetLogLimitData.circle_mean_defect_eq_dyadic_multiplicity` proves
that the actual target-limit defect equals its fixed coherent dyadic target
multiplicity divided by rho. The roots and both signs are discharged by the
previously constructed dyadic target theorems. This specialized integration
proof is an alternative organization of the manuscript's scalar argument.

Next signatures: `scalar_projective_proximity_ratio_dyadic` for the normalized
curve, a proved bijective target change under the normalization matrix, and
the all-radius classical scalar deficiency theorem. DAG: exact circle defect
-> all-radius subsequence uniqueness -> target change of basis -> scalar
proximity ratios -> exact deficiency quantization -> `Paper.thm_A`.
The final scalar conclusion (b) remains pending; `Paper.thm_A` is undeclared.

## M18 checkpoint: all-radius normalized projective proximity

Gate `m18-all-radius-normalized-proximity` passed: 5326 build jobs,
9010 declarations including 7847 theorem declarations. Four frozen logs,
empty project scans, and the three-foundation recursive audit are recorded.
`scalar_projective_proximity_ratio_dyadic` proves the all-radius limit for
curves whose two coordinates are nonzero at the origin. The proof constructs
dyadic decompositions, extracts the multiplier and peak phase in compact sets,
constructs arbitrary-radius data at the required accuracy, and applies the
proved target circle-defect identity. The subsequence criterion removes all
radius and phase choices. The normalization hypothesis is still an internal
step and is not being added to the manuscript theorem.

Next DAG: classify nonzero two-dimensional linear forms -> bijective target
change under an invertible normalization matrix -> exact constant difference
of projective proximities -> original curve all-radius limit -> scalar lift
transfer -> deficiency quantization and `Paper.thm_A`.

## M18 checkpoint: target bijection under normalization

Gate `m18-target-matrix-bijection` passed: 5329 build jobs, 9019 declarations
including 7856 theorem declarations. Both source scans and the recursive
three-foundation audit pass; the four logs are frozen.
`exists_scalar_target_coordinate_form` classifies nonzero two-dimensional
complex linear functionals by the exact normalized target forms, including
infinity. `exists_scalar_target_equiv_matrix` constructs a bijection of all
targets under every invertible homogeneous coordinate change.
`scalarProjectiveProximity_matrixGauge` proves the exact logarithmic constant
correction for an isometric change; zeros of the target function are handled
by codiscrete circle congruence. The correction vanishes on the characteristic
scale. Thus the normalization at the origin can now be removed internally.

Next: transfer the fixed finite sector multiplicities through this bijection,
construct all-radius limits for the original scalar lift, identify the literal
EReal deficiencies, and assemble the exact `ScalarTheoremATarget` as
`Paper.thm_A`. No extra normalization hypothesis will enter the final statement.

## M18 complete: exact scalar theorem A

Gate `m18-complete-scalar-theorem-a` passed: 5332 build jobs,
9026 declarations including 7863 theorem declarations. The four logs are
frozen. Both project source scans are empty, and all transitive dependencies
are Classical.choice, propext, and Quot.sound.

`scalar_exists_projective_proximity_multiplicities` constructs integer target
counts for the original curve without an origin-normalization assumption.
`scalarDeficiency_quantization_of_lift` transfers all-radius projective limits
to the actual scalar characteristic and identifies the literal EReal deficiency.
`ModifiedCartan.Paper.thm_A` proves the entire exact `ScalarTheoremATarget`;
`Paper.thm_A_deficiency_sum` proves HasSum of the real values of all deficiencies
is two. No stronger hypothesis or conditional literature interface is used.

This completes the last outstanding mathematical result in the registered
submitted-manuscript inventory. The separate final submission gate is now
checking all 35 labelled declarations and exact principal target applications.
The specialized scalar proof uses coherent dyadic sectors, logarithmic circle
means, and a proved target bijection under normalization; these are recorded
above as a fully proved alternative organization of the cited scalar argument.

## Final submitted-paper completion gate

`submitted-paper-complete` passed. `scripts/verify.ps1` now reproducibly checks:

- `lake build`: 5332 jobs completed successfully.
- Both project libraries and root imports: no forbidden theorem placeholders.
- Recursive dependencies of all 9026 declarations, including 7863 theorem
  declarations and private declarations: only Classical.choice, propext,
  and Quot.sound.
- The unchanged SHA256 of `paper/submitted.tex`.
- Exact agreement of the 35 submitted LaTeX result labels with the completion
  registry, and theorem declarations for all 35.
- Exact principal target applications for scalar theorem A, the curve main
  theorem, small order, zero ratio, entire sharpness-system existence, and
  both sharpness propositions; `#print axioms` for all 35 labelled results.

The five logs are frozen as `verification/logs/submitted-paper-complete-*.log`.
The separate `verification/SubmittedCompletion.lean` is the completion entry
for this manuscript. The old `verification/Completion.lean` is preserved as
historical material for the previous manuscript and is not the current gate.
The pinned mathlib checkout is clean at
`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

All M0–M18 milestones and the submitted manuscript result inventory are complete.
The declaration counts describe audited coverage, not a percentage estimate.
