# Formalization status

Project root: `E:\Lean 4\FewInflection`  
Toolchain: Lean `v4.34.0-rc1`, mathlib at the pinned lake revision.

The five target propositions were frozen in
`verification/TargetSnapshot.lean` before further work on the result file.
The snapshot copies the exact proposition bodies currently named
`MainTheoremStatement`, `SharpnessStatement`, `SmallOrderStatement`,
`ZeroOrderStatement`, and `RadialAreaStatement`.

Current state:

- The definitions, Wronskian identities, monomial examples, constant and
  matrix gauge lemmas, regular-variation lemmas, and the radial quotient lemma
  compile with ordinary Lean proofs.
- `Curve.constGauge` is a reduced nonzero scalar gauge, and
  `Curve.characteristic_constGauge` proves its exact characteristic
  invariance using continuity and circle-average additivity.
- `Curve.characteristic_continuous` proves continuity of the current
  circle-average characteristic from the reducedness and holomorphicity
  hypotheses.
- `scalar_circleAverage_log_norm_sub_nonneg` is a genuine Jensen-formula
  consequence for an entire scalar coordinate, including the nonnegative
  divisor sum.
- `scalar_circleAverage_log_norm_sub_nonneg_at` transports that estimate to
  every centre by an explicit translation.
- `logCounting_zero_eq_circleAverage_sub_const_of_entire` identifies the
  zero-counting function with the Jensen increment for an entire function
  nonzero at the centre, proving that the pole term vanishes from the divisor.
- `ramification_eq_circleAverage_sub_const_of_wronskian_nezero_at_zero`
  specializes that identity to the Wronskian, with the genuine differentiability
  and nonzero-at-centre hypotheses exposed rather than hidden.
- `differentiable_wronskian` proves from the curve's entire holomorphic
  coordinates that the finite determinant of iterated derivatives is entire;
  the resulting Wronskian Jensen identity is available without an extra
  differentiability parameter.
- `wronskian_zero_or_nonzero_codiscrete` applies the analytic identity theorem:
  the Wronskian is either identically zero or its nonzero locus is codiscrete.
- Consequently, `ramification_nonneg_of_wronskian_nezero_at_zero` is proved
  from Jensen rather than assumed.
- `exists_coord_norm_eq_vector_norm` identifies a coordinate attaining the
  finite-product norm at every centre (with the zero-centre specialization
  retained), and `characteristic_nonneg_of_reduced_curve_at` proves the
  nonnegative vector characteristic increment from translated scalar Jensen.
  The proof handles the coordinate's isolated circle zeros by a codiscrete
  modification before applying circle-average monotonicity.
- `lowerOrder_le_order`, `order_nonneg`, and
  `characteristic_nonneg_eventually` record the basic filter-theoretic growth
  consequences without conflating liminf with limsup.
- `ramification_nonneg_eventually` and `ramification_monotoneOn` expose the
  corresponding zero-counting facts directly from Mathlib's
  `ValueDistribution.logCounting` API.
- `fundamental_coefficients_exists_unique` proves the pointwise fundamental
  differential relation at every nonzero Wronskian point by matrix
  invertibility, including uniqueness of all coefficients.
- `fundamentalCoefficients` is a choice from that proved unique local
  solution (zero on the Wronskian-zero locus), and
  `fundamentalCoefficients_spec`/`fundamentalCoefficients_unique` expose its
  exact equation without treating the coefficient construction as an axiom.
- `vecMul_solution_cramer` and `fundamentalCoefficients_cramer` rewrite the
  same local coefficient vector by Mathlib's Cramer's rule, so its numerator
  and Wronskian denominator are explicit finite determinants.
- `fundamentalCoefficients_eq_quotient` identifies each chosen coefficient
  with its Cramer quotient.  `analyticAt_fundamentalNumerator`,
  `analyticAt_fundamentalCoefficients`, and
  `meromorphic_fundamentalCoefficients` prove the corresponding local analytic
  and global meromorphic facts from the entire coordinate functions; no
  coefficient regularity is assumed.
- `deriv_det_updateRow` differentiates a finite determinant by its rows, and
  `deriv_wronskian_update_last` proves the Wronskian derivative identity by
  cancelling the repeated lower rows.  Consequently
  `fundamental_last_coefficient_mul_wronskian` rigorously establishes the
  paper's coefficient-of-the-top-derivative relation at every nonzero
  Wronskian point.
- `fundamentalCoefficients_const_mul` proves invariance of the pointwise
  fundamental coefficient vector under a nonzero constant scalar gauge by
  uniqueness, using Mathlib's field version of the iterated-derivative rule.
- `fundamental_last_coefficient_eq_neg_deriv_div` rewrites the top coefficient
  itself as the logarithmic derivative `-W'/W` on the nonzero Wronskian locus,
  matching the paper's item (iii).
- `RationalNormalForm.hasPolynomialRepresentation` turns the matrix normal
  form into the literal polynomial representation used by `Curve`, while
  `RationalNormalForm.linearlyNonDegenerate` proves independence by cancelling
  the nowhere-zero factor and using matrix injectivity.  Its
  `not_transcendental` corollary is available for the rational alternative.
- `monomial_vector_norm_on_sphere`, `monomial_vector_norm_zero`, and
  `characteristic_monomialCurve_atTop` give the exact characteristic formula
  for the explicit polynomial model on all radii `r ≥ 1`.
- `monomialCurve_order_zero` proves, from the resulting logarithmic growth
  ratio and `tendsto_order`, that both the order and lower order of this model
  are exactly zero.
- As a model-specific certificate, `smallOrderStatement_monomialCurve`
  supplies the frozen small-order conclusion for the explicit polynomial
  curve; the universal small-order theorem remains open.
- `regularlyVarying_log` establishes the compact-multiplier regular variation
  estimate for `log r` at index zero, including the uniform compact-set bound
  on `|log c|`.
- `characteristic_monomialCurve_regularlyVarying` transfers that estimate to
  the explicit degree-`n` monomial characteristic for every `n > 0`, using
  the exact circle formula and a compact positive lower bound on multipliers.
- `slowlyVarying_monomial_log` and `monomial_characteristic_factor` provide a
  positive continuous slowly varying factor and the eventual factorization of
  the monomial characteristic at index zero.
- `radial_area_statement_of_mainConclusion` and
  `verification/Completion.lean:completion_radial_area_statement` genuinely
  prove the frozen radial-area target once a `MainConclusion` and the
  area/characteristic limit are supplied.
- `Nevanlinna.lean` now proves the first global quotient estimate from the
  paper: the pointwise positive-log bound, the pole-counting bound for a
  coordinate quotient, and the finite-radius inequality
  `quotient_characteristic_le_curve`.  The proof uses Mathlib's meromorphic
  divisors, circle integrability, Jensen identity, and codiscrete invariance
  of circle averages; no quotient estimate is postulated.
- `LogDerivativeFacts.lean` proves meromorphicity of the Wronskian logarithmic
  derivative, its exact order `-1` at every genuine Wronskian zero, and the
  codiscrete equality between the top fundamental coefficient and the negative
  logarithmic derivative.
- `GrowthBasics.lean` now isolates the filter-theoretic implication that a
  normalized logarithmic-ratio limit fixes both order and lower order, and
  gives finite lower order for a finite real limit.
- `Gauge.lean` now also defines an invertible constant matrix gauge on curves,
  proves reducedness from Mathlib's `vecMul` injectivity criterion, identifies
  the transformed vector, proves preservation of linear nondegeneracy, and
  proves the determinant transformation law for the Wronskian.
- `MatrixGaugeBounds.lean` proves an explicit positive finite operator bound for
  the sup norm of `vecMul v A`.  This is the norm-equivalence estimate needed
  to compare characteristics under a general constant matrix gauge.
- `MatrixGaugeBounds.lean` now also proves the inverse-matrix estimate,
  pointwise logarithmic norm bounds, and two-sided finite-radius characteristic
  comparison (including an explicit absolute-difference bound).
- `GaugeFundamental.lean` proves that the pointwise fundamental differential
  coefficients are unchanged by an invertible constant matrix gauge.
- `ScalarGauge.lean` proves the Jensen equality for a nowhere-zero entire
  scalar factor and the eventual characteristic invariance under that scalar
  gauge.
- `ScalarGauge.lean` now also proves the exact equivalence of polynomial
  representability (and hence transcendence) before and after a nowhere-zero
  entire scalar gauge, by explicitly dividing or multiplying the factor.
- `GaugeTranscendental.lean` proves the corresponding equivalence for an
  invertible constant matrix gauge, including the explicit polynomial
  transformation by `A` and recovery through the nonsingular inverse.
- `ScalarGauge.lean` also proves preservation of linear nondegeneracy under a
  nowhere-zero scalar gauge by pointwise cancellation of the common factor.
- `RationalGauge.lean` identifies every rational-normal-form curve's
  characteristic, eventually, with the characteristic of the corresponding
  scalar gauge of a constant matrix gauge of the monomial curve.  It also
  proves the matrix-gauged monomial logarithmic growth ratio tends to zero,
  and hence proves `RationalNormalForm.order_eq_zero` and the conditional
  theorem `smallOrderStatement_of_rationalNormalForm`.
- The other four frozen targets do not yet have complete proofs from Mathlib.

New work in this invocation:

- `Growth/Scaling.lean` proves that a positive constant change of the radial
  variable preserves the compact-uniform `RegularlyVarying` definition and
  the project `SlowlyVarying` definition.  It also proves the corresponding
  characteristic statement for positive real dilations of a curve.
- `Nevanlinna/CountingBounds.lean` proves the first fixed-radius
  logarithmic-derivative counting step for an arbitrary nonnegative locally
  finite divisor: the unweighted divisor mass in a smaller disk times
  `log (R/r)` is bounded by the outer logarithmic counting function, with the
  centre coefficient handled explicitly.  The quotient form is included.
- `FewInflection.lean` and `verification/Audit.lean` import and audit these
  new results; all their printed dependencies remain only
  `propext`, `Classical.choice`, and `Quot.sound`.

The current earliest missing theorem in the paper's main chain remains the
fixed-radius proximity estimate for logarithmic derivatives (after the
counting step), followed by the normalized derivative limits and the
subharmonic compactness/rescaling argument.  Sharpness still needs the actual
transcendental ODE realization; the universal small-order and zero-order
ramification arguments are also open.

Latest checks for this invocation: `lake build` completed 3545 jobs;
`lake env lean verification/Audit.lean`,
`lake env lean verification/Completion.lean`, and
`lake env lean verification/TargetSnapshot.lean` all succeeded.  The four
non-radial frozen target certificates remain absent, so no completion marker
has been written.

Remaining proof frontier:

- The main target needs the paper's Nevanlinna, subharmonic compactness,
  rescaling, and growth-index arguments.
- Sharpness needs a genuine transcendental ODE realization with the stated
  two-sided characteristic bounds.
- The small-order and zero-order targets need the polynomial reduction and
  ramification lower-bound arguments.
- The radial-area target still needs the analytic theorem producing its
  `MainConclusion` and area asymptotic hypotheses.

Verification files:

- `verification/TargetSnapshot.lean` freezes and checks target identity.
- `verification/Completion.lean` is the completion gate and currently contains
  only compile-time checks; target certificates will be added there only after
  they are genuinely proved.
- `verification/Audit.lean` checks the axioms of the proved helper theorems.

Latest check: full `lake build`, `lake env lean verification/TargetSnapshot.lean`,
`lake env lean verification/Completion.lean`, and
`lake env lean verification/Audit.lean` all pass after the matrix-gauge,
fundamental-coefficient, scalar-gauge, and rational-normal-form additions.
The audit reports only `propext`, `Classical.choice`, and `Quot.sound` for
these proofs.  A source scan found no `sorry`, `admit`, custom axiom
declaration, or opaque escape.
The next earliest missing theorem remains the global rescaling/growth-index
compactness argument (including the fixed-radius logarithmic derivative bound);
the four non-radial frozen target certificates are still open.
- `ScalarWronskian.lean` now proves the full Leibniz lower-triangular matrix factorization for a scalar gauge and derives the Wronskian multiplication formula `W(g f)=g^(n+1)W(f)` from Mathlib determinant identities. The curve-level scalar-gauge Wronskian theorem is available for later canonical-gauge work.
- `CanonicalGauge.lean` proves the top fundamental-operator coefficient transformation under a nowhere-vanishing differentiable scalar gauge, using the Wronskian multiplication theorem, Mathlib derivative rules, and the existing Cramer/logarithmic-derivative identity.
- `Dilation.lean` defines the holomorphic precomposition dilation and proves the exact iterated-derivative and Wronskian scaling law using Mathlib's chain-rule lemma and diagonal determinant/product identities.
- `FundamentalDilation.lean` proves the exact scaling law for all fundamental differential coefficients under precomposition by `z ↦ t z`, by transporting the defining linear system through the iterated-derivative chain rule and uniqueness.
- `Dilation.lean` now also proves that nonzero precomposition preserves
  linear nondegeneracy, using surjectivity of multiplication by the scale.
- The same module proves preservation of `Curve.Transcendental` under a
  nonzero dilation by explicitly composing each polynomial representation with
  the inverse scale.
- `Dilation.lean` also proves the exact positive-real scaling identity for the
  projective characteristic, by reducing both circle averages to the unit
  circle and matching the rescaled arguments.
- `AnalyticLogBranch.lean` upgrades Mathlib's continuous logarithm lift on a
  simply connected open set to a local analytic logarithm, using the local
  slit-plane identity for `Complex.log`.
- `CanonicalLocalGauge.lean` constructs an analytic inverse-root gauge on a
  zero-free simply connected domain, proves the Wronskian becomes one, and
  proves the top fundamental coefficient is zero on that domain.  This is a
  genuine local version of the paper's canonical-gauge lemma.
- The same module proves the global zero-free specialization and proves that
  any two analytic inverse-root gauges on a simply connected domain differ by
  a constant `m`th root of unity, by differentiating the quotient and using
  connectedness.

Latest check after these additions: `lake build`,
`lake env lean verification/Audit.lean`,
`lake env lean verification/Completion.lean`, and
`lake env lean verification/TargetSnapshot.lean` all pass.  The new audit
entries depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The five frozen targets remain unchanged; only the radial-area target has an
actual completion theorem so far.
The follow-up inverse-root branch-independence proof and the source scan also
pass; no forbidden proof escape was found in project sources.
The latest full build and all three verification entry points pass after the
dilation/transcendence and scalar-gauge-transcendence additions; the audit
still reports only the three accepted foundational axioms for every added
theorem.
- `ScalarGauge.lean` now also proves the exact equivalence of linear
  nondegeneracy before and after multiplication by a nowhere-zero entire
  scalar, by cancelling the common value pointwise in the finite family.

Latest verification after this addition: `lake build` completed all 3539 jobs;
`verification/Audit.lean`, `verification/Completion.lean`, and
`verification/TargetSnapshot.lean` all compile successfully.  The audit for
the new theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
The repository source scan reports no `sorry`, `admit`, custom `axiom`,
`opaque`, or `native_decide`, and temporary scratch files were removed.  The
four non-radial frozen target proofs remain open; no completion marker is
written.
- `Dilation.lean` now contains the composition law for dilations and the
  reverse implications for transcendence and linear nondegeneracy, obtained by
  applying the proved forward lemmas to the inverse scale.
- `GaugeTranscendental.lean` now proves the two-way linear-nondegeneracy
  equivalence for every invertible constant matrix gauge.
- `ScalarGaugeRamification.lean` proves, from the divisor multiplication
  theorem and the zero-free factor's zero divisor, that scalar and matrix
  gauges preserve Wronskian ramification.  It also transfers the
  `SmallRamification` property through a scalar gauge using Mathlib's
  `isLittleO_congr`.

The newest full check passes: `lake build` completed 3540 jobs, and
`verification/Audit.lean`, `verification/Completion.lean`, and
`verification/TargetSnapshot.lean` compile.  The audit entries for all new
results contain only `propext`, `Classical.choice`, and `Quot.sound`.
The source scan still finds no forbidden proof escapes, and no temporary
scratch files remain.  The four non-radial frozen target certificates are
still absent; the radial-area certificate remains the only completed frozen
target.
- Added `Growth/PowerBounds.lean`: positive two-sided bounds
  `c r^ρ ≤ T(r) ≤ C r^ρ` with `c,C,ρ>0` now give a genuine squeeze proof of
  `logGrowthRatio T → ρ` in `EReal`, hence exact order and lower order.  The
  proof explicitly handles the `max` cutoffs and positivity before all real
  logarithms.
- Added `Growth/SharpnessBounds.lean`: every `RealizationWitness` with its
  stated two-sided growth clause consequently has order and lower order equal
  to its witness order parameter.

Latest check: `lake build` completed 3542 jobs; Audit, Completion, and
TargetSnapshot all passed.  The audit reports only `propext`,
`Classical.choice`, and `Quot.sound` for the new power-bound results; source
scan reports no forbidden tokens and no scratch files remain.  The four
non-radial frozen target theorems are still not proved.

Update (2026-09-27, affine rescaling and operator transport):
- Added `FewInflection/AffineDilation.lean` to formalize the paper's local change of variables `z ↦ a + t z`: the curve remains holomorphic and reduced, iterated derivatives and the Wronskian scale by the exact determinant factor, nonzero affine scales preserve linear nondegeneracy and transcendence in both directions, and successive affine changes compose with the expected parameters.
- The same module proves the exact characteristic identity on translated/rescaled circles, `characteristic (f.affineDilate a (t : ℂ)) r = circleAverage (log ‖f.vector ·‖) a (t*r) - log ‖f.vector a‖` (with the stated positive-scale hypothesis).
- Added `FewInflection/FundamentalAffineDilation.lean`: all fundamental differential-operator coefficients transform with the exact factor `t^(n+1-i)` under affine precomposition, including the nonzero-scale specialization.
- Root imports and `verification/Audit.lean` now include these results. Direct module checks pass; the full build/audit/completion/snapshot checks are being rerun after this batch.
- The earliest missing analytic result is still the paper's fixed-radius logarithmic-derivative/proximity estimate. The four non-radial frozen target certificates remain open; no completion marker is written.

Verification after the affine/operator batch: `lake build` completed 3547 jobs; `verification/Audit.lean`, `verification/Completion.lean`, and `verification/TargetSnapshot.lean` all compile. The audit reports only `propext`, `Classical.choice`, and `Quot.sound` for the new affine and fundamental-coefficient theorems. The forbidden-token source scan is empty. Four frozen target proofs remain open.

Verification after Wronskian-limit and analytic-count additions: `lake build` completed 3552 jobs; `verification/Audit.lean`, `verification/Completion.lean`, and `verification/TargetSnapshot.lean` all pass. The audit entries for local-uniform Wronskian convergence and the analytic Jensen count use only `propext`, `Classical.choice`, and `Quot.sound`; the forbidden-token scan remains empty. The four non-radial frozen targets are still not certified.

Verification after the jet/Cramer/log-derivative batch: `lake build` completed 3554 jobs; `verification/Audit.lean`, `verification/Completion.lean`, and `verification/TargetSnapshot.lean` pass. The new proofs use only `propext`, `Classical.choice`, and `Quot.sound`; no forbidden proof-escape token is present. The earliest missing theorem remains the full fixed-radius logarithmic-derivative proximity estimate and its potential-theoretic limit machinery; the four non-radial frozen target certificates remain open.

Update (2026-09-27, fixed-radius kernel and characteristic bookkeeping):
- Added `FewInflection/Nevanlinna/PoissonKernelBounds.lean`.  The file proves, from norm inequalities and Mathlib's iterated reciprocal derivative formula, the lower bound for `|R exp(iθ)-z|`, the `6 m!` Poisson-kernel derivative bound for `2<R<3` and `|z|=1`, the exact higher derivative formula, its boundary integral estimate, and the reflected-kernel/power/sum bounds on the unit disk.
- Added `FewInflection/Nevanlinna/CountingCharacteristic.lean`.  It proves the First-Main-Theorem bookkeeping used in Step 1: at an analytic nonzero center, the inverse characteristic is the original characteristic minus `log ‖h 0‖`, and the sum of zero/pole logarithmic counts is bounded by twice the characteristic plus `|log ‖h 0‖|`.
- Root imports and `verification/Audit.lean` include all new theorems.  `lake build` completed 3556 jobs; focused module, Audit, Completion, and TargetSnapshot checks pass.  The audit entries for this batch use only `propext`, `Classical.choice`, and `Quot.sound`; the forbidden-token scan is empty.
- The earliest missing analytic dependency remains the full Poisson--Jensen representation/proximity estimate (including its singular-kernel fractional integral and differential-polynomial recursion), followed by the subharmonic/Riesz-measure compactness chain.  The four non-radial frozen targets remain uncertified; no completion marker is written.

Update (2026-09-27, Poisson--Jensen derivative kernels and boundary means):
- Extended `PoissonKernelBounds.lean` with the exact iterated derivative of the singular kernel `(z-a)⁻¹`, the exact iterated derivative of the reflected kernel `conj(a)/(R²-conj(a)z)`, and the factorial bound for that reflected derivative on `|z|≤1`, together with the finite reflected multiplicity sum bound.
- Added `BoundaryMean.lean`: pointwise `|log x| = log⁺ x + log⁺(x⁻¹)` and its circle-average version for meromorphic functions, proved using Mathlib circle integrability and the two proximity functions.
- Added the combined `log(4/3)` divisor-count estimate to `CountingBounds.lean`.  Root exports and Audit include these results.  The prior 3557-job build passed before the latest derivative addition; the derivative module itself passes directly.  A fresh full build and audit are the next check.
- The earliest missing dependency remains the full finite Poisson--Jensen representation with its singular-kernel fractional-integral estimate, then subharmonic/Riesz compactness.  Four frozen target certificates remain open; `FORMALIZATION_COMPLETE` is not present.

Verification after the reflected-kernel/boundary-mean batch: `lake build` completed 3557 jobs; `verification/Audit.lean`, `verification/Completion.lean`, and `verification/TargetSnapshot.lean` all pass. Audit axioms for the new results remain only `propext`, `Classical.choice`, and `Quot.sound`, and the forbidden-token scan is empty. Temporary scratch files were removed. The four non-radial frozen target proofs remain open.

Update (2026-09-27, finite meromorphic sums and Poisson--Jensen):
- Added `Nevanlinna/FiniteSingularSums.lean`.  Translated reciprocal kernels
  and reflected kernels are proved meromorphic pointwise, and Mathlib's finite
  `proximity_sum_top_le` / `characteristic_sum_top_le` are specialized to the
  two finite singular sums occurring in the logarithmic-derivative proof.
- Added `Nevanlinna/PoissonJensen.lean`.  Using Mathlib's extended canonical
  decomposition, harmonic Poisson formula, and meromorphic divisors, it proves
  a genuine scalar Poisson--Jensen identity on a disk whose boundary is free of
  zeros and poles.  The formula explicitly retains the finite divisor sum and
  canonical-factor term; no Jensen or representation axiom is introduced.
- Root exports and `verification/Audit.lean` include these theorems.  The two
  focused files compile directly; a fresh full build and audit are pending.
- The earliest missing dependency is now the differentiated Poisson--Jensen
  representation and its uniform fractional-integral estimate (then the
  differential-polynomial recursion and the subharmonic/Riesz compactness
  chain).  Four non-radial frozen targets remain uncertified; the completion
  marker is absent.

Verification after the finite-sum/Poisson--Jensen batch: `lake build` completed
3561 jobs; `verification/Audit.lean`, `verification/Completion.lean`, and
`verification/TargetSnapshot.lean` all pass.  Audit entries for the new
meromorphic sums and the Poisson--Jensen identity use only `propext`,
`Classical.choice`, and `Quot.sound`; the forbidden-token scan is empty.  The
radial-area target is still the only frozen target with a certificate.

Update (2026-09-27, differentiated harmonic term):
- Added `Nevanlinna/PoissonDerivative.lean`.  It transports Mathlib's
  differentiation-under-the-circle-integral theorem to the complex-valued
  boundary function `log ‖f‖`, proving the exact first derivative of the
  Herglotz transform for every meromorphic `f` and every interior point.
  Circle integrability is obtained from the meromorphic log-norm theorem and
  the real-to-complex continuous linear map, with no hidden a.e. convention.
- Root exports and Audit include this result; the focused module passes.  A
  fresh full build is still pending after this small addition.

Verification after differentiated harmonic term: `lake build` completed 3562
jobs; `verification/Audit.lean`, `verification/Completion.lean`, and
`verification/TargetSnapshot.lean` all pass.  The audit reports only
`propext`, `Classical.choice`, and `Quot.sound`; the forbidden-token scan is
empty.  The radial-area target is still the only frozen target with a genuine
certificate.  The next missing analytic step is differentiation of the full
canonical-factor Poisson--Jensen decomposition, followed by the uniform
logarithmic-derivative estimate and compactness/growth-index arguments.

Update (2026-09-27, differentiated canonical decomposition):
- Added `Nevanlinna/PoissonLogDerivative.lean`.  Mathlib's meromorphic
  logarithmic-derivative API now differentiates the canonical decomposition on
  the interior ball: the logarithmic derivative of the finite canonical-factor
  product is the divisor-weighted `finsum`, and the zero-free normal-form factor
  contributes its logarithmic derivative.  The proof establishes finite orders
  and meromorphicity directly from the canonical decomposition and the
  canonical-factor order theorem.
- Root exports and Audit include the theorem.  The four non-radial frozen
  targets remain open; a fresh full build and verification run follows.

Update (2026-09-28, user-supplied paper revision):
- Preserved the previous manuscript as `paper/original_v1.tex` and installed
  the new attachment as `paper/original.tex`.  The Lean target declarations and
  `verification/TargetSnapshot.lean` were not changed.
- Marked corrections to the new manuscript in red through the local
  `\revision{...}` macro: the omitted `n\geq1` scope, the Drasin/Hiong textual
  typos, the unmatched parenthesis, the duplicated `for`, the duplicated
  corollary sentence, the repeated `\rho_*(T)` term, and the sharpness
  derivative equation `w^{(n+1)}=z^k w^{(n+1-q)}`.  The revision also fixes the
  spelling errors `siilar` and `elininated`.
- The revised source compiles with TeX Live `pdflatex` in three passes to
  `paper/original.pdf` (53 pages); the final log has no LaTeX errors, undefined
  references, or duplicate labels.  The built-in Codex LaTeX compiler was also
  invoked, but its host reported `Unable to find standard directories for
  platform`; the source and the successful `pdflatex` result are retained.
- Direct Lean checks using the fixed Lean 4.34.0-rc1 executable and the
  repository's package paths pass for `verification/Audit.lean`,
  `verification/Completion.lean`, and `verification/TargetSnapshot.lean`.
  Audit axioms remain only `propext`, `Classical.choice`, and `Quot.sound`.
  The ordinary `lake` package check is still sensitive to the shared junction
  under `.lake/packages`; `lake build` had already completed 3564 jobs before
  the manuscript-only changes.
- The revised paper removes its former sharpness/radial-area section, while
  the frozen Lean targets intentionally retain both statements.  This is a
  manuscript/target-scope discrepancy, not a reason to weaken the targets.
  The four non-radial frozen target proofs remain open.  The earliest missing
  mathematical dependency is still a genuine fixed-radius logarithmic-
  derivative/proximity estimate (Nevanlinna--Hiong), followed by the
  subharmonic/Riesz compactness and growth-index arguments.
- A second pass found fifteen pasted-text line-break corruptions of the
  `W_{\fv}` macro in the indices and zero-order sections.  They were repaired
  as red `W_{\revision{\fv}}` corrections; the manuscript was recompiled and
  still has no LaTeX errors or unresolved references.

Update (2026-09-28, explicit order-one realization):
- Added `FewInflection/ExplicitExamples.lean`.  It constructs the entire curve
  `(1, exp z)`, proves directly from polynomial degree and the derivative of
  `exp` that it is transcendental and linearly nondegenerate, computes its
  Wronskian, and applies the scalar gauge `exp (-z/2)` to obtain Wronskian one.
- The module proves the exact logarithmic norm formula
  `log ‖(1, exp z)‖ = max 0 (Re z)`, two-sided characteristic bounds
  `r/4 ≤ T(r) ≤ r` for positive radii, and packages these into a genuine
  `RealizationWitness 1 1`.  It then derives order and lower order one and
  zero small ramification for the normalized curve.  These are concrete
  instances of the paper's sharpness mechanism, not assumptions added to a
  frozen target.
- `lake build` completed successfully (3568 jobs).  `verification/Audit.lean`,
  `verification/Completion.lean`, and `verification/TargetSnapshot.lean` all
  pass; the new audit entries use only `propext`, `Classical.choice`, and
  `Quot.sound`.  The forbidden-token scan remains empty.
- The radial-area target is still the only frozen target with a complete
  certificate.  The earliest missing general dependency is the fixed-radius
  logarithmic-derivative estimate and the subsequent compactness/growth-index
  chain; the new explicit order-one witness does not weaken or alter any
  frozen proposition.  `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, explicit main-conclusion instance):
- Strengthened `FewInflection/ExplicitExamples.lean` with the exact homogeneity
  of the exponential characteristic on nonnegative radii, its positivity,
  and a direct locally-uniform `RegularlyVarying` proof.  The scalar-gauged
  curve is shown to have the same characteristic on every nonnegative radius;
  a positive constant slowly varying factor is constructed explicitly.
- The normalized exponential curve now has a genuine `MainConclusion` and a
  theorem proving `MainTheoremStatement` for that concrete curve.  The
  completion gate checks the corresponding frozen-main-target instance in
  `verification/Completion.lean`; its audit uses only the ordinary foundation
  axioms.
- After regenerating caches, `lake build` completed 3568 jobs and Audit,
  Completion, and TargetSnapshot all pass.  The four universal non-radial
  frozen targets are still not proved; this concrete instance does not replace
  them.  The earliest missing universal step remains the fixed-radius
  logarithmic-derivative estimate followed by the subharmonic compactness and
  growth-index argument.  `FORMALIZATION_COMPLETE` remains absent.

Verification after the explicit sharpness-instance addition: `lake build`
completed successfully (3568 jobs), and `verification/Audit.lean`,
`verification/Completion.lean`, and `verification/TargetSnapshot.lean` all
exit successfully.  The audit of every new theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`; the forbidden-token scan has
no matches.  The revised TeX log remains free of errors and unresolved
references.  The universal sharpness, small-order, zero-order, and main
theorem certificates are still open, so the completion marker is deliberately
not present.

Update (2026-09-28, regular-variation transfer layer):
- Added `FewInflection/Growth/Transfer.lean`.  It proves from the definition
  that compact-uniform regular variation is preserved by eventual equality;
  the proof extracts a positive minimum of each nonempty compact multiplier
  set and controls both `r` and `c*r` on one threshold.  It also proves the
  direct positive-homogeneity criterion for regular variation.
- Added the corresponding scalar-gauge consequences: regular variation is
  equivalent before and after a nowhere-zero entire scalar gauge, and a
  `MainConclusion` certificate can be transported through that gauge.  The
  certificate transport preserves the order fields, admissible index,
  regular variation, and the slowly varying factor using the actual eventual
  characteristic equality.
- Refactored the explicit exponential example to use these general transfer
  and homogeneity lemmas, and to obtain its slowly varying factor from the
  general positive-continuous regular-variation factor theorem.
- `lake build` completed successfully (3569 jobs).  `verification/Audit.lean`,
  `verification/Completion.lean`, and `verification/TargetSnapshot.lean`
  pass; the new audit entries have only `propext`, `Classical.choice`, and
  `Quot.sound`; the forbidden-token scan is clean.
- The earliest missing universal mathematical step remains the fixed-radius
  logarithmic-derivative/proximity estimate.  The universal main, sharpness,
  small-order, and zero-order target proofs remain open.  The only complete
  frozen target is still the radial-area statement (plus the separately
  audited concrete order-one main instance).  `FORMALIZATION_COMPLETE`
  remains absent.

Update (2026-09-28, finite reflected-sum derivative bound):
- Extended `FewInflection/Nevanlinna/PoissonKernelBounds.lean` with
  `norm_iteratedDeriv_reflected_sum_le`.  For a finite family of poles outside
  the radius-two region, every iterated derivative of the reflected kernel sum
  is bounded by the factorial times the total absolute integer multiplicity.
  The proof uses the already established denominator nonvanishing, exact
  derivative formula, single-kernel bound, and `norm_sum_le_of_le`.
- Added the theorem to `verification/Audit.lean`; it uses only
  `propext`, `Classical.choice`, and `Quot.sound`.  `lake build` remains
  successful (3569 jobs), and the prior Audit/Completion/TargetSnapshot checks
  remain valid with a clean forbidden-token scan.
- This completes another finite-sum component of the fixed-radius argument,
  but does not yet prove the full Nevanlinna--Hiong estimate: the harmonic
  remainder, exceptional-radius control, and subsequent compactness/growth
  steps are still missing.  The four universal non-radial frozen targets stay
  open; no completion marker is present.

Update (2026-09-28, higher-dimensional order-one realization):
- Added `FewInflection/ExplicitHigherDim.lean`.  The factorial-normalized
  family
  `if j = lastIndex n then exp else (factorial j)⁻¹ z^j` has Wronskian
  exactly `exp z`; the proof is an upper-triangular determinant calculation
  with all finite derivative jets explicit.  For `1 ≤ n`, the constant
  coordinate and exponential coordinate give direct proofs of linear
  nondegeneracy and transcendence.
- The logarithmic norm is bounded below by `max 0 (Re z)` and, on a circle of
  radius `r ≥ 0`, above by `r` using the proved inequality
  `r^j/j! ≤ exp r`.  This yields genuine two-sided characteristic bounds
  `r/4 ≤ T(r) ≤ r`.  The scalar gauge `exp(-z/(n+1))` is then shown to have
  Wronskian one, and its characteristic is eventually equal to the original
  one.  These fields form `exponentialMonomialRealization n` and a verified
  sharpness instance at every dimension `n ≥ 1` and admissible order `ρ=1`.
- Added the higher-dimensional instance to `verification/Completion.lean` as
  a separately named concrete theorem, and audited all new declarations.  A
  full `lake build` succeeds (3570 jobs); Audit, Completion, and
  TargetSnapshot succeed; all audited declarations use only
  `propext`, `Classical.choice`, and `Quot.sound`; the forbidden-token scan is
  clean.
- This is a substantial sharpness subcase, not the universal sharpness
  statement for every admissible `ρ=1+k/q`.  The main theorem, universal
  sharpness, small-order classification, and zero-order ramification target
  remain open, so `FORMALIZATION_COMPLETE` is still absent.

Update (2026-09-28, Vandermonde exponential family):
- Added `FewInflection/ExplicitExponentialFamily.lean`.  The family
  `exp(j z)` for `j = 0, ..., n` has Wronskian equal to the Vandermonde
  determinant times `exp((∑ j)z)`.  The determinant calculation is proved
  using Mathlib's `det_vandermonde`, the exact iterated derivative formula for
  `exp`, and a diagonal factorization of the Wronskian matrix.
- The module proves linear nondegeneracy and transcendence, the exact vector
  norm `exp(max 0 (n Re z))`, and exact radial homogeneity of its
  characteristic.  A complex polynomial-root argument supplies a constant
  scalar gauge whose `(n+1)`st power cancels the Vandermonde factor; the
  normalized family therefore has Wronskian one.  Its characteristic is
  regularly varying of order one and yields a genuine higher-dimensional
  order-one `RealizationWitness` for every `n ≥ 1`.
- Added the instance to `verification/Completion.lean` and audited the new
  declarations in `verification/Audit.lean`.  `lake build` succeeds with
  3571 jobs; Audit, Completion, and TargetSnapshot all pass, and the
  forbidden-token scan is clean.  The only diagnostics are existing linter
  suggestions.
- This is a concrete order-one realization, not the universal sharpness
  theorem for every admissible order.  The universal main, sharpness,
  small-order, and zero-order targets remain open; `FORMALIZATION_COMPLETE`
  is still absent.

Update (2026-09-28, high-dimensional concrete MainConclusion):
- Extended the Vandermonde family with a fully constructed
  `MainConclusion` and `MainTheoremStatement` instance.  The slowly varying
  factor is obtained from the proved positive homogeneous base characteristic
  and the general regular-variation factor theorem; the normalized scalar
  gauge is transferred by its actual eventual characteristic equality.
- `verification/Completion.lean` now checks both the corresponding concrete
  main instance (including the complex root chosen for the normalization) and
  the sharpness instance.  No frozen target was changed or weakened.
- The new module, `lake build`, Audit, Completion, TargetSnapshot, and the
  forbidden-token scan all pass.  The four universal non-radial frozen
  statements still require the paper's missing Nevanlinna--Hiong,
  compactness, growth-index, and polynomial-classification arguments;
  `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, separated singular-kernel derivative bound):
- Added `norm_iteratedDeriv_singular_sum_le` to
  `FewInflection/Nevanlinna/PoissonKernelBounds.lean`.  For a finite pole
  set whose distance from the evaluation point is at least `δ > 0`, every
  iterated derivative of the ordinary reciprocal-kernel sum is bounded by
  `m! · δ⁻¹^(m+1)` times the sum of coefficient norms.  The proof uses the
  exact finite-sum derivative identity, the norm of a complex power, and the
  order-reversing inverse inequality; no analytic estimate is assumed.
- Added the theorem to `verification/Audit.lean`; the audited dependency is
  only `propext`, `Classical.choice`, and `Quot.sound`.  The generic
  `RealizationWitness.mainConclusion` constructor is audited as well.
- `lake build` succeeds (3571 jobs), and `verification/Audit.lean`,
  `verification/Completion.lean`, and `verification/TargetSnapshot.lean`
  all succeed.  The forbidden-token scan remains empty.
- This supplies another finite-kernel component of the fixed-radius
  logarithmic-derivative argument.  The harmonic-remainder estimate,
  subharmonic compactness, universal Plücker-coordinate theorem, growth-index
  collapse, and the four universal non-radial frozen target proofs remain
  open; `FORMALIZATION_COMPLETE` is absent.

Update (2026-09-28, derivative-minor change-of-basis layer):
- Added `FewInflection/DerivativeMinors.lean`.  It defines arbitrary finite
  derivative minors and proves their exact scalar-gauge and constant-matrix
  change-of-basis formulas, including preservation of nonvanishing when the
  matrix determinant is a unit.  The Wronskian is proved as the special order
  list `i ↦ i`.
- Exported the module from `FewInflection.lean` and audited all four new
  declarations.  `lake build` succeeds (3572 jobs); Audit, Completion, and
  TargetSnapshot succeed, and the forbidden-token scan remains empty.
- These are proved algebraic prerequisites for the paper's derivative-minor
  and Plücker-coordinate section.  The universal Karp--Purbhoo identity is
  still not asserted; the four universal non-radial targets remain open and
  `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, canonical-factor kernel expansion):
- Added `FewInflection/Nevanlinna/CanonicalKernels.lean`.  It proves the
  explicit logarithmic derivative of Mathlib's canonical factor, including
  all nonvanishing conditions, and rewrites the canonical decomposition's
  finite `logDeriv` sum on the codiscrete complement of its divisor support
  as the ordinary pole kernel plus the reflected kernel, followed by the
  zero-free remainder.
- Exported and audited these three declarations.  `lake build` succeeds
  (3573 jobs); Audit, Completion, and TargetSnapshot succeed, with only
  `propext`, `Classical.choice`, and `Quot.sound` in the new theorem
  dependencies.  The forbidden-token scan remains empty.
- The full Nevanlinna--Hiong proximity estimate and its compactness/growth
  consequences are still missing; all four universal non-radial frozen
  targets remain uncertified and `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, polynomial jet and Taylor layer):
- Added `FewInflection/PolynomialJets.lean`.  It proves from
  `Polynomial.hasDerivAt` and the finite polynomial Taylor theorem that
  analytic iterated derivatives of a polynomial are evaluations of formal
  iterated derivatives, that Taylor coefficients are exactly the derivatives
  divided by factorials, and that every polynomial of degree at most `d` has
  an exact finite jet reconstruction at an arbitrary center.
- The same file proves a norm majorant on a disk for that finite jet sum and
  rewrites every derivative minor of a polynomial basis as a determinant of
  evaluations of formal derivative polynomials.  These are actual estimates
  and identities, not assumptions about polynomial solution spaces.
- Exported the module from `FewInflection.lean` and added all declarations to
  `verification/Audit.lean`.  `lake build` succeeds with 3574 jobs;
  `verification/Audit.lean`, `verification/Completion.lean`, and
  `verification/TargetSnapshot.lean` all succeed, and the forbidden-token
  scan remains clean.
- The first missing result in the paper's universal chain is still the
  Karp--Purbhoo universal Plücker-coordinate identity (followed by the
  Nevanlinna--Hiong compactness and growth-index arguments).  The four
  universal non-radial frozen targets remain uncertified and
  `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, combined canonical-kernel derivative bound):
- Extended `FewInflection/Nevanlinna/CanonicalKernels.lean` with
  `norm_iteratedDeriv_canonical_kernel_sum_le`.  This combines the ordinary
  pole derivative estimate and the reflected-kernel estimate into one bound
  for a finite canonical-factor kernel sum, with all separation and
  denominator nonvanishing hypotheses proved explicitly.
- The proof establishes the needed `ContDiffAt` facts for each finite sum,
  applies Mathlib's iterated-derivative addition rule, and then combines the
  two norm estimates.  It does not assume a proximity theorem or hide a
  singularity argument in a definition.
- Added the declaration to `verification/Audit.lean`.  The full build now
  succeeds with 3574 jobs; Audit, Completion, and TargetSnapshot succeed, and
  the forbidden-token scan is still clean.  The four universal non-radial
  targets remain open because the global proximity-to-compactness passage,
  universal Plücker theorem, and subsequent growth arguments are not yet
  formalized; `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, recursive differential-polynomial layer):
- Extended `FewInflection/LogDerivativeRecursion.lean` with the concrete
  recursive operator `normalizedDifferentialPolynomial`.  Its first two
  nontrivial cases are proved explicitly (`L` and `L' + L^2`), and the
  general identity
  `h^(k)/h = normalizedDifferentialPolynomial (logDeriv h) k` is derived by
  induction from the previously proved quotient recursion for every
  zero-free differentiable `h`.
- Added the declarations to `verification/Audit.lean`.  The module and all
  verification files continue to compile with only the ordinary Mathlib
  foundational axioms in the audit.  This formalizes the paper's
  differential-polynomial expansion step without asserting the expansion as
  an assumption.
- The universal Plücker-coordinate theorem, the global subharmonic and
  growth-index arguments, and the four universal non-radial target proofs
  are still missing; `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, convergence-in-measure utilities):
- Added `FewInflection/MeasureConvergence.lean`.  It proves that a uniform
  norm majorant tending to zero implies convergence in measure, with the
  measure and filter left explicit, and exposes Mathlib's strict-monotone
  subsequence extraction from convergence in measure to almost-everywhere
  convergence.
- Exported and audited both declarations.  The new module compiles and uses
  only the standard Mathlib foundations.  This preserves the paper's
  distinction between convergence in measure and a.e. convergence instead of
  silently identifying them.
- Added the translated version with a general limit function `g`: a uniform
  bound on `‖fᵢ-g‖` tending to zero yields convergence in measure to `g`.
  This will be the form used for local normalized logarithms.
- The first genuinely global missing statements are unchanged: the
  Karp--Purbhoo universal identity, subharmonic compactness, and the growth
  index and classification arguments.  The four universal non-radial frozen
  targets remain open and `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, initial-value basis):
- Added `FewInflection/InitialBasis.lean`.  At a point where the Wronskian is
  nonzero, the inverse of the finite jet matrix is used to construct an
  explicit linear-combination basis whose derivatives of orders `0, ..., n`
  are the Kronecker delta.  The determinant identity with the Wronskian and
  the derivative calculation are proved from Mathlib's matrix inverse and
  iterated-derivative addition rules.
- Exported and audited the construction.  It is an algebraic/local analytic
  prerequisite for the paper's initial-value estimate; it does not assert the
  missing universal Pluecker-coordinate bound for higher derivatives.
- Also proved the exact reconstruction identity for every finite linear
  combination of the original functions in terms of this initial-value basis.
  This is the finite-dimensional coefficient step used before applying a
  Taylor majorant.
- The same construction now has a curve-level wrapper: the holomorphicity
  field of `Curve` supplies all finite `ContDiffAt` hypotheses automatically.
- Added `FewInflection/PolynomialGauge.lean`, proving the polynomial-level
  constant matrix gauge formula
  `Wronskian(A·p) = Wronskian(p) · C(det A)` by iterating the polynomial
  derivative and applying `Matrix.det_mul`.  This is the algebraic polynomial
  counterpart of the pointwise derivative-minor gauge identity.
- Extended `PolynomialJets.lean` with a finite polynomial-combination norm
  majorant obtained by summing the individual Taylor jet bounds.  The degree
  bound is explicit for every coordinate and the disk-radius positivity is
  used in the power estimate.
- Added its evaluated form after polynomial matrix gauge, so the determinant
  factor is visible at every complex point as well as in the polynomial ring.
- Added the explicit polynomial initial-value basis obtained from the inverse
  formal jet matrix.  Its evaluation agrees with the analytic `initialBasis`,
  and, at a nonzero polynomial Wronskian, its first jet is proved to be the
  Kronecker delta.  This links the polynomial-space and local analytic layers.
- Proved its explicit degree majorant by the polynomial finite-sum degree API;
  the bound is the sum of the original coordinate degrees and requires no
  genericity assumption on the coefficients.
- Using the determinant-of-inverse identity, proved that the polynomial
  initial-value basis has Wronskian equal to `1` at the chosen center.  This
  is the exact normalization needed before local polynomial estimates.
- Added `FewInflection/EntireTaylor.lean`, using Mathlib's proved entire
  Taylor-series summation theorem.  Finite Taylor partial sums are represented
  by genuine polynomials, converge pointwise to each entire coordinate, and
  evaluate to the nonzero center value at the center whenever that value is
  nonzero.
- Extended that module with the formal-power-series partial-sum identity and
  proved locally uniform convergence on the whole plane, plus uniform
  convergence on every prescribed closed disk.  The latter uses the strict
  smaller-ball estimate from Mathlib's `HasFPowerSeriesOnBall` API and keeps
  the radius inequality explicit.
- Added `FewInflection/TaylorLimits.lean`: the existing locally-uniform
  derivative-convergence theorem now yields convergence of every fixed jet of
  these Taylor polynomials, and determinant continuity yields convergence of
  their Wronskians at every point.  The holomorphicity hypotheses are supplied
  by the polynomial evaluation API.
- Added `FewInflection/DerivativeMinorLimits.lean`, generalizing the same
  finite determinant-continuity argument from Wronskians to every fixed list
  of derivative orders.  This preserves the paper's distinction between a
  finite derivative minor and the special Wronskian case.
- The four universal non-radial frozen targets remain open, and
  `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, local derivative and remainder control):
- Proved that locally uniform convergence of holomorphic functions on an open set gives locally uniform convergence of every fixed iterated derivative, with the differentiability-on-domain hypothesis explicit.
- Applied this to Taylor polynomials on a ball and audited the resulting derivative convergence.
- Added uniform convergence on every strict closed subdisk and a geometric remainder estimate from Mathlib's power-series-on-a-ball theorem. These are quantitative local estimates; they do not assert the missing global compactness or growth-index results.
- Audited the new local Taylor and remainder declarations. The four universal non-radial frozen targets remain open, and `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, Taylor derivative minors):
- Generalized the Taylor-limit chain from consecutive Wronskian jets to arbitrary fixed derivative-order minors. The global entire and local ball versions are proved by finite determinant continuity and the previously established derivative convergence.
- Added both declarations to the audit. This is a reusable algebraic limit lemma for later gauge and Pluecker-coordinate arguments; it does not assert the missing universal Pluecker theorem.

Update (2026-09-28, basis-independent derivative-minor ratios):
- Added and proved the exact quotient invariance of an arbitrary derivative minor divided by the Wronskian under an invertible constant matrix basis change.
- Added the corresponding theorem for any second function family presented by that matrix change, with all derivative regularity and nonvanishing conditions explicit.
- These are the elementary basis-independence identities used before the universal Pluecker estimate; the external representation-theoretic estimate itself remains unasserted.

Update (2026-09-28, elementary symmetric estimate):
- Added a concrete `elementarySymmetric` finite-sum definition and proved its zero-cardinality and beyond-cardinality identities.
- Proved the norm estimate for a finite reciprocal-root expansion whose coefficients are bounded by `s!`; this is exactly the elementary analytic implication of the coefficient bound in the paper's universal-minor formula.
- The coefficient expansion itself is still intentionally absent until its Karp--Purbhoo representation-theoretic source is formalized; no external theorem is treated as a Lean axiom.

Update (2026-09-28, polynomial/Vieta bridge):
- Generalized `elementarySymmetric` to any commutative semiring and proved the exact Vieta coefficient identity for a finite product of linear factors. This connects the finite symmetric sums used in the reciprocal-root estimate to actual polynomial coefficients.
- The identity is proved from Mathlib's `Finset.prod_X_add_C_coeff`; no root-factorization or representation-theoretic statement is assumed.

Update (2026-09-28, translated-root Taylor identities):
- Added the exact translated-root identity `(p.taylor a).roots = p.roots.map (· - a)` from Mathlib's polynomial composition root theorem.
- Added the Vieta formula for every Taylor coefficient and its iterated-derivative form, with the polynomial splitting and degree hypotheses explicit.
- This supplies the polynomial root/coefficient bridge needed before reciprocal-root minor estimates, while leaving the universal Pluecker-coordinate expansion itself open.

Update (2026-09-28, fundamental-operator Taylor limits):
- Applied the locally uniform jet convergence to the fundamental differential coefficients: at any nonzero limiting Wronskian, the Cramer coefficient vectors of the Taylor approximants converge at the center.
- Added both entire and local-ball versions, preserving the eventual nonzero-Wronskian condition through the proved continuity argument.
- This is the finite-dimensional coefficient-limit step before the paper's global coefficient estimates; the global growth estimate is still missing.

Update (2026-09-28, initial-basis continuity):
- Proved continuity of the initial-value basis under finite jet convergence: matrix inversion is handled through Mathlib's nonzero-determinant continuity theorem, and the finite basis sum is handled explicitly.
- The theorem separates jet convergence at the normalization center from value convergence at the evaluation point, so it does not conflate local uniform, pointwise, or measure convergence.

Update (2026-09-28, Taylor initial-basis limits):
- Specialized the initial-basis continuity theorem to entire Taylor approximants and to Taylor approximants on a local ball.
- The proof uses derivative convergence at the normalization center and value convergence separately at the evaluation point, with the center's ball membership supplied explicitly.

Update (2026-09-28, eventual nonvanishing of Taylor minors):
- Added the eventual nonzero Wronskian and arbitrary derivative-minor consequences of the proved Taylor-limit theorems. The nonvanishing is obtained from filter convergence to a genuinely nonzero limit, rather than inserted as a hypothesis for each approximant.

Update (2026-09-28, polynomial initial-basis majorant):
- Added the explicit Taylor-jet norm bound for every polynomial initial-basis coordinate, using the proved degree sum bound and polynomial Taylor reconstruction.
- This is the finite polynomial estimate needed before the paper's normalized-basis growth argument; no asymptotic estimate is hidden in it.

Update (2026-09-28, linear-factor Taylor coefficients):
- Proved the exact coefficient identity for a translated finite product of linear factors: the Taylor coefficient indexed by `M-s` is the elementary symmetric sum of the center-to-root displacements of size `s`.
- The proof uses the Taylor algebra homomorphism and Mathlib's Vieta coefficient theorem, giving a concrete polynomial model for the symmetric sums used in the universal-minor estimate.

Update (2026-09-28, reciprocal-root complement identity):
- Proved the finite complement identity expressing an elementary symmetric sum divided by the full product as the elementary symmetric sum of reciprocal entries.
- The proof uses an explicit complement bijection on `powersetCard` and keeps every entry's nonvanishing hypothesis in the theorem statement. This supplies the algebraic conversion used by reciprocal-root estimates; the paper's universal Plücker-coordinate expansion is still not formalized.

Update (2026-09-28, reciprocal Taylor coefficient bridge):
- Added the corresponding exact identity for a translated finite product of linear factors: a Taylor coefficient divided by the translated root product is the reciprocal-root elementary symmetric sum.
- This is a direct consequence of the proved Vieta and complement identities and is now available to the polynomial minor layer; it does not add any asymptotic or universal representation assumption.

Update (2026-09-28, common almost-everywhere subsequence):
- Proved the finite diagonal extraction lemma for two sequences converging in measure: one strictly increasing subsequence gives almost-everywhere pointwise convergence for both sequences.
- The proof composes the Mathlib subsequence extraction theorem and preserves the distinction between convergence in measure and almost-everywhere convergence needed in the rescaling argument.

Update (2026-09-28, finite-coordinate diagonal extraction):
- Extended the diagonal argument to any finite `Fin m` family of functions converging in measure, with one strictly increasing subsequence and a single almost-everywhere convergence statement for every coordinate.
- This is the exact finite-dimensional subsequence bookkeeping used before determinant and Wronskian limits; it does not identify convergence in measure with pointwise convergence without the extracted subsequence.

Update (2026-09-28, local uniform to restricted measure):
- Proved that uniform convergence on a measurable set yields convergence in measure for the restricted measure, by an explicit norm estimate and the Mathlib almost-everywhere characterization.
- This connects the Taylor/local-compactness layer to the paper's measure-convergence layer without imposing an ambient finite-measure assumption.

Update (2026-09-28, Taylor measure convergence):
- Instantiated the restricted-measure lemma for entire Taylor polynomials on closed disks and for local Taylor approximation on strict subdisks.
- These results connect the proved local uniform Taylor estimates to the convergence-in-measure/subsequence layer while keeping the disk restriction explicit.

Update (2026-09-28, derivative measure convergence):
- Added the strict-subdisk convergence-in-measure theorem for every fixed Taylor derivative order, obtained from local uniform derivative convergence and compactness of the closed subdisk.
- This supplies the measure-theoretic jet input used before finite Wronskian limits, with the radius gap retained in the statement.

Update (2026-09-28, local L1 seminorm control):
- Proved convergence of the extended `L¹` seminorm to zero from a nonnegative uniform scalar majorant tending to zero on a finite measure space.
- The estimate is explicit at the `eLpNorm'` level and is independent of the convergence-in-measure theorem, preserving the separate analytic modes required by the paper.

Update (2026-09-28, almost-everywhere determinant passage):
- Proved that almost-everywhere convergence of finite complex matrices implies almost-everywhere convergence of their determinants, using Mathlib's continuous determinant map.
- This supplies the finite-dimensional determinant/Wronskian passage after the extracted finite-coordinate subsequence; it does not assert the paper's missing global compactness or universal Plücker theorem.

Update (2026-09-28, almost-everywhere Wronskian passage):
- Specialized the finite matrix determinant limit to Wronskians: simultaneous almost-everywhere convergence of every finite derivative-jet entry gives almost-everywhere convergence of the Wronskian, with the finite intersection handled by `ae_all_iff`.

Update (2026-09-28, zero-free Poisson factor):
- Proved the exact fixed-radius logarithmic-derivative formula for an analytic function nonvanishing on a closed disk. An analytic logarithm, the harmonic Poisson formula, the open mapping theorem, and Mathlib's differentiated Herglotz kernel yield the boundary integral without an exceptional radius.
- This advances the fixed-radius proximity layer, while the general meromorphic logarithmic-derivative bound and the subsequent normalized limits remain open.

Update (2026-09-28, finite symmetric generating identity):
- Proved the finite generating identity expressing the sum of all elementary symmetric sums as the product of the linear factors `1 + t * x_i`. This is an exact finite algebraic input for later reciprocal-root majorants.

Update (2026-09-28, differentiated Poisson--Jensen decomposition):
- Proved the regular-boundary equality of the logarithmic boundary data for the extended canonical decomposition, its reduction to the ordinary decomposition when the boundary divisor vanishes, and the resulting exact eventual Poisson--Jensen formula for the logarithmic derivative.
- The formula retains the divisor sum, reflected boundary kernel, and codiscrete domain explicitly; it does not assert the missing uniform proximity estimate or normalized subsequential limit.

Update (2026-09-28, fixed-radius boundary estimates):
- Proved the norm estimate for the first differentiated Poisson kernel on the unit disk when `2 < R < 3`, and the corresponding boundary circle-average estimate for a meromorphic function.
- Proved the absolute boundary mean bound by twice the characteristic plus the central logarithm using the established proximity identity, inverse-characteristic identity, and nonnegativity of the counting terms.
- These are genuine fixed-radius inequalities; the global logarithmic-derivative estimate, subharmonic compactness, growth-index collapse, and the four universal non-radial frozen targets remain open. `FORMALIZATION_COMPLETE` remains absent.

Update (2026-09-28, finite-support logarithmic-derivative bound):
- Combined the exact Poisson--Jensen derivative formula with the proved canonical-kernel and boundary estimates into `norm_logDeriv_le_of_poisson_jensen_formula`.
- The theorem keeps a finite divisor support, a positive separation parameter, the radius range `2 < R < 3`, and the boundary meromorphicity assumption explicit. It is a genuine fixed-radius local estimate and does not assert the global exceptional-radius control, compactness, or growth-index arguments still needed for the universal targets.
- Added the characteristic version, replacing the absolute boundary mean by `12 * characteristic f ⊤ R + 6 * |log ‖f 0‖|` through the proved inverse-characteristic bookkeeping.

Update (2026-09-28, convergence-in-measure product control):
- Proved that convergence to zero in measure is preserved after multiplication by a sequence uniformly bounded in norm. The proof compares superlevel sets and keeps the measure filter explicit, providing the elementary product step used in the higher logarithmic-derivative limit argument.

Update (2026-09-28, convergence-in-measure quotient control):
- Added the corresponding quotient lemma when the denominator is uniformly bounded away from zero. It is proved by inverting the denominator and applying the product theorem, with the positive lower bound retained explicitly.

Update (2026-09-28, convergence-in-measure addition control):
- Proved closure under addition by an explicit superlevel-set union estimate and the measure subadditivity inequality. This supplies the finite algebra operations needed before passing determinant and Wronskian expressions to a synchronized subsequence.

Update (2026-09-28, convergence-in-measure finite sums):
- Iterated the addition estimate over finite index sets, proving convergence in measure of any finite sum whose summands converge to zero in measure. The empty and inserted cases are handled directly, preserving the filter and measure parameters.

Update (2026-09-28, absolute divisor counting):
- Proved the exact finite-support identity splitting the absolute divisor mass on the radius-three disk into positive and negative parts.
- Combined it with the existing divisor counting lemma to bound that absolute mass times `log (4/3)` by the positive and negative logarithmic counting functions. This is the signed-divisor bookkeeping needed before the characteristic bound; it does not assert the missing Hiong proximity estimate.
- Added the meromorphic specialization identifying the two parts with the pole counts of `f` and `1/f`, using the proved divisor-of-inverse and `logCounting_top` identities at a nonzero analytic center.

Update (2026-09-28, local divisor mass comparison):
- Proved that any finite set of nonzero local divisor entries in `ball 0 R`, for `R ≤ 3`, has absolute multiplicity sum bounded by the global radius-three divisor mass. The proof explicitly transports local divisor values to the global divisor and keeps the finite support in the `finsum` comparison.
- This bridges the finite-support fixed-radius logarithmic-derivative estimate to the characteristic divisor bound once a concrete Poisson--Jensen support and separation choice is supplied; the exceptional-radius selection and the four universal non-radial targets remain open.

Update (2026-09-28, characteristic mass combination):
- Combined the fixed-support Poisson--Jensen logarithmic-derivative estimate with the global absolute divisor mass and the two logarithmic counting functions. The resulting bound has the explicit factor `(δ⁻¹ + 1) / log (4/3)` and retains all support, separation, radius, and boundary hypotheses.
- This is the complete fixed-radius bookkeeping step before selecting exceptional radii; it does not supply the missing global exceptional-set, normalized-limit, growth-index, or universal Plücker arguments.

Update (2026-09-28, canonical decomposition to eventual bound):
- Composed Mathlib's proved canonical-decomposition Poisson--Jensen formula with the characteristic mass estimate. On the codiscrete filter of `ball 0 R`, the exact formula now yields the explicit characteristic bound whenever the evaluation point lies in the unit disk and stays at least `δ` from the finite support.
- The statement keeps the finite exceptional divisor set and all boundary hypotheses explicit; it does not claim the paper's missing radius selection or asymptotic compactness.

Update (2026-09-28, canonical finite divisor support):
- Added a direct finite-set extraction from `MeromorphicOn f (closedBall 0 R)`: the divisor support in `ball 0 R` is represented by a `Finset`, every selected multiplicity is nonzero, and every selected point satisfies the strict radius bound.
- This supplies the canonical support data for the preceding eventual estimate while leaving the point-separation and exceptional-radius choices explicit.

Update (2026-09-28, automatic support wrapper):
- Added the existential wrapper that chooses the canonical divisor support and returns the corresponding codiscrete eventual characteristic bound. The only remaining pointwise condition is the explicit unit-disk and `δ`-separation premise at the evaluation point.

Update (2026-09-28, separation-set topology):
- Proved that the finite-support `δ`-separation locus is closed and measurable. This records the exact geometry of the exceptional neighborhoods used by the fixed-radius estimate and is available for restricted-measure arguments.
- Identified the same locus exactly as the complement of the finite union of open `δ`-balls around the divisor support.
- Its intersection with the closed unit disk is compact, providing the compact domain needed for subsequent local uniform estimates.

Update (2026-09-28, differentiated Poisson--Jensen bridge):
- Used Mathlib's meromorphic codiscrete derivative theorem and the analytic Herglotz--Riesz boundary transform to differentiate the Poisson--Jensen logarithmic-derivative equality once. The new eventual equality is stated for the full kernel sum plus the explicit boundary term and preserves the codiscrete disk domain.
- This is the first genuine higher-derivative bridge; the full Hiong estimate and normalized limiting theorem remain open.
