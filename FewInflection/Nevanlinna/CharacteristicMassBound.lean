import FewInflection.Nevanlinna.PoissonLogDerivativeBound
import FewInflection.Nevanlinna.AbsoluteDivisorCount

/-!
# Characteristic control of the fixed-radius logarithmic derivative

This module combines the finite-support Poisson--Jensen estimate with the
absolute divisor mass comparison.  The analytic hypotheses are kept
explicit; no exceptional-radius or asymptotic theorem is packaged into the
statement.
-/

open scoped BigOperators ComplexConjugate Topology
open Complex Filter Function Function.locallyFinsuppWithin MeromorphicOn Metric Real Set
open ValueDistribution

namespace FewInflection

theorem norm_logDeriv_le_of_poisson_jensen_formula_characteristic_mass
    {f : ℂ → ℂ} {R δ : ℝ} {z : ℂ} (s : Finset ℂ)
    (hR2 : 2 < R) (hR3 : R < 3) (hz : ‖z‖ ≤ 1)
    (hfSphere : MeromorphicOn f (sphere 0 R))
    (hf : Meromorphic f) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hδ : 0 < δ)
    (hsupport : Function.support (divisor f (ball 0 R)) ⊆ (s : Set ℂ))
    (hsupport_ne : ∀ a ∈ s, divisor f (ball 0 R) a ≠ 0)
    (hinside : ∀ a ∈ s, ‖a‖ < R)
    (hsep : ∀ a ∈ s, δ ≤ ‖z - a‖)
    (hformula : logDeriv f z =
      (∑ᶠ a, (divisor f (ball 0 R) a : ℂ) *
        ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) +
      Real.circleAverage (fun ζ : ℂ =>
        (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R) :
    ‖logDeriv f z‖ ≤
      (δ⁻¹ + 1) / Real.log (4 / 3) *
          (ValueDistribution.logCounting f ⊤ 4 +
            ValueDistribution.logCounting (fun w : ℂ => (f w)⁻¹) ⊤ 4) +
        12 * ValueDistribution.characteristic f ⊤ R +
        6 * |Real.log ‖f 0‖| := by
  have hlocal := norm_logDeriv_le_of_poisson_jensen_formula_characteristic
    s hR2 hR3 hz hfSphere hf hfa h0 hδ hsupport hinside hsep hformula
  have hmass := finset_divisor_abs_sum_le_toClosedBall_natAbs_finsum hf
    (le_of_lt hR3) s hsupport_ne
  have hcount := meromorphic_toClosedBall_natAbs_finsum_mul_log_four_thirds_le_counts
    hf hfa h0
  have hlog : 0 < Real.log (4 / 3 : ℝ) := by
    apply Real.log_pos
    norm_num
  have hquot :
      (∑ᶠ w : ℂ, (((toClosedBall 3 (divisor f Set.univ)) w).natAbs : ℝ)) ≤
        (ValueDistribution.logCounting f ⊤ 4 +
          ValueDistribution.logCounting (fun w : ℂ => (f w)⁻¹) ⊤ 4) /
          Real.log (4 / 3) := by
    apply (le_div_iff₀ hlog).mpr
    exact hcount
  have hfactor : 0 ≤ δ⁻¹ + 1 := by
    have hδinv : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
    linarith
  have hscaled :
      (δ⁻¹ + 1) * ∑ a ∈ s, |(divisor f (ball 0 R) a : ℝ)| ≤
        (δ⁻¹ + 1) / Real.log (4 / 3) *
          (ValueDistribution.logCounting f ⊤ 4 +
            ValueDistribution.logCounting (fun w : ℂ => (f w)⁻¹) ⊤ 4) := by
    calc
      (δ⁻¹ + 1) * ∑ a ∈ s, |(divisor f (ball 0 R) a : ℝ)| ≤
          (δ⁻¹ + 1) *
            (∑ᶠ w : ℂ, (((toClosedBall 3 (divisor f Set.univ)) w).natAbs : ℝ)) :=
        mul_le_mul_of_nonneg_left hmass hfactor
      _ ≤ (δ⁻¹ + 1) *
          ((ValueDistribution.logCounting f ⊤ 4 +
            ValueDistribution.logCounting (fun w : ℂ => (f w)⁻¹) ⊤ 4) /
            Real.log (4 / 3)) :=
        mul_le_mul_of_nonneg_left hquot hfactor
      _ = (δ⁻¹ + 1) / Real.log (4 / 3) *
          (ValueDistribution.logCounting f ⊤ 4 +
            ValueDistribution.logCounting (fun w : ℂ => (f w)⁻¹) ⊤ 4) := by
        ring
  apply le_trans hlocal
  simpa [add_assoc] using add_le_add_right hscaled
    (12 * ValueDistribution.characteristic f ⊤ R + 6 * |Real.log ‖f 0‖|)

/-! The preceding bound can be fed the exact formula supplied by the
canonical-decomposition theorem.  The result is stated on the codiscrete
filter because the decomposition is exact away from the finite divisor set.
-/
theorem eventually_norm_logDeriv_le_of_poisson_jensen_formula_characteristic_mass
    {f : ℂ → ℂ} {R δ : ℝ} (s : Finset ℂ)
    (hR2 : 2 < R) (hR3 : R < 3)
    (hfClosed : MeromorphicOn f (closedBall 0 R))
    (hfSphere : MeromorphicOn f (sphere 0 R))
    (hf : Meromorphic f) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hboundary : ∀ w ∈ sphere 0 R, AnalyticAt ℂ f w ∧ f w ≠ 0)
    (hδ : 0 < δ)
    (hsupport : Function.support (divisor f (ball 0 R)) ⊆ (s : Set ℂ))
    (hsupport_ne : ∀ a ∈ s, divisor f (ball 0 R) a ≠ 0)
    (hinside : ∀ a ∈ s, ‖a‖ < R) :
    ∀ᶠ z in codiscreteWithin (ball 0 R),
      ‖z‖ ≤ 1 →
        (∀ a ∈ s, δ ≤ ‖z - a‖) →
          ‖logDeriv f z‖ ≤
            (δ⁻¹ + 1) / Real.log (4 / 3) *
                (ValueDistribution.logCounting f ⊤ 4 +
                  ValueDistribution.logCounting (fun w : ℂ => (f w)⁻¹) ⊤ 4) +
              12 * ValueDistribution.characteristic f ⊤ R +
              6 * |Real.log ‖f 0‖| := by
  have hformula := logDeriv_poisson_jensen_eventuallyEq (by linarith : 0 < R)
    hfClosed hfa h0
    hboundary
  filter_upwards [hformula] with z hz
  intro hzunit hzsep
  exact norm_logDeriv_le_of_poisson_jensen_formula_characteristic_mass s
    hR2 hR3 hzunit hfSphere hf hfa h0 hδ hsupport hsupport_ne hinside hzsep hz

/-! The finite set used above can be chosen canonically from the divisor. -/
theorem exists_finset_divisor_support_within_ball
    {f : ℂ → ℂ} {R : ℝ}
    (hfClosed : MeromorphicOn f (closedBall 0 R)) (hR : 0 < R) :
    ∃ s : Finset ℂ,
      Function.support (divisor f (ball 0 R)) ⊆ (s : Set ℂ) ∧
        (∀ a ∈ s, divisor f (ball 0 R) a ≠ 0) ∧
        (∀ a ∈ s, ‖a‖ < R) := by
  let D : locallyFinsuppWithin (ball (0 : ℂ) R) ℤ := divisor f (ball 0 R)
  have hfinite : D.support.Finite := hfClosed.divisor_ball_support_finite
  let s : Finset ℂ := hfinite.toFinset
  refine ⟨s, ?_, ?_, ?_⟩
  · intro a ha
    exact hfinite.mem_toFinset.2 (by simpa [D] using ha)
  · intro a ha
    have haD : D a ≠ 0 := by
      exact hfinite.mem_toFinset.1 ha
    simpa [D, Function.mem_support] using haD
  · intro a ha
    have haD : D a ≠ 0 := by
      exact hfinite.mem_toFinset.1 ha
    have haBall : a ∈ ball (0 : ℂ) R := D.supportWithinDomain haD
    simpa [mem_ball_zero_iff, abs_of_pos hR] using haBall

theorem exists_finset_eventual_norm_logDeriv_le_characteristic
    {f : ℂ → ℂ} {R δ : ℝ}
    (hR2 : 2 < R) (hR3 : R < 3)
    (hfClosed : MeromorphicOn f (closedBall 0 R))
    (hfSphere : MeromorphicOn f (sphere 0 R))
    (hf : Meromorphic f) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hboundary : ∀ w ∈ sphere 0 R, AnalyticAt ℂ f w ∧ f w ≠ 0)
    (hδ : 0 < δ) :
    ∃ s : Finset ℂ,
      Function.support (divisor f (ball 0 R)) ⊆ (s : Set ℂ) ∧
        (∀ a ∈ s, divisor f (ball 0 R) a ≠ 0) ∧
        (∀ a ∈ s, ‖a‖ < R) ∧
        ∀ᶠ z in codiscreteWithin (ball 0 R),
          ‖z‖ ≤ 1 →
            (∀ a ∈ s, δ ≤ ‖z - a‖) →
              ‖logDeriv f z‖ ≤
                (δ⁻¹ + 1) / Real.log (4 / 3) *
                    (ValueDistribution.logCounting f ⊤ 4 +
                      ValueDistribution.logCounting (fun w : ℂ => (f w)⁻¹) ⊤ 4) +
                  12 * ValueDistribution.characteristic f ⊤ R +
                  6 * |Real.log ‖f 0‖| := by
  obtain ⟨s, hs, hsne, hsinside⟩ :=
    exists_finset_divisor_support_within_ball hfClosed (by linarith : 0 < R)
  refine ⟨s, hs, hsne, hsinside, ?_⟩
  exact eventually_norm_logDeriv_le_of_poisson_jensen_formula_characteristic_mass
    s hR2 hR3 hfClosed hfSphere hf hfa h0 hboundary hδ hs hsne hsinside

theorem isClosed_finset_separation_set
    (s : Finset ℂ) (δ : ℝ) :
    IsClosed {z : ℂ | ∀ a ∈ s, δ ≤ ‖z - a‖} := by
  have hclosed : IsClosed (⋂ a ∈ (s : Set ℂ), {z : ℂ | δ ≤ ‖z - a‖}) := by
    apply isClosed_biInter
    intro a ha
    exact isClosed_Ici.preimage
      (continuous_norm.comp (continuous_id.sub continuous_const))
  convert hclosed using 1
  ext z
  simp

theorem measurableSet_finset_separation_set
    (s : Finset ℂ) (δ : ℝ) :
    MeasurableSet {z : ℂ | ∀ a ∈ s, δ ≤ ‖z - a‖} :=
  (isClosed_finset_separation_set s δ).measurableSet

theorem finset_separation_set_eq_compl_union_balls
    (s : Finset ℂ) (δ : ℝ) :
    {z : ℂ | ∀ a ∈ s, δ ≤ ‖z - a‖} =
      (⋃ a ∈ (s : Set ℂ), Metric.ball a δ)ᶜ := by
  ext z
  simp [Metric.mem_ball, dist_eq_norm, dist_comm]

theorem isCompact_unit_closedBall_inter_finset_separation
    (s : Finset ℂ) (δ : ℝ) :
    IsCompact (closedBall (0 : ℂ) 1 ∩
      {z : ℂ | ∀ a ∈ s, δ ≤ ‖z - a‖}) :=
  (isCompact_closedBall (0 : ℂ) (1 : ℝ)).inter_right
    (isClosed_finset_separation_set s δ)

end FewInflection
