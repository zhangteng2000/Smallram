import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The literal kernel in LaTeX `eq:envelope`. -/
noncomputable def envelopeIntegrand (α u : ℝ) : ℝ :=
  max 1 ((3 * u) ^ α) / (1 + u) ^ 2

/-- The literal constant I_alpha in LaTeX `lem:envelope`. -/
noncomputable def envelopeConstant (α : ℝ) : ℝ :=
  ∫ u in Ioi 0, envelopeIntegrand α u

theorem envelopeIntegrand_nonneg (α u : ℝ) : 0 ≤ envelopeIntegrand α u :=
  div_nonneg (le_trans zero_le_one (le_max_left _ _)) (sq_nonneg _)

theorem envelopeIntegrand_continuousOn {α : ℝ} (hα : 0 ≤ α) :
    ContinuousOn (envelopeIntegrand α) (Ici 0) := by
  have hnum : Continuous (fun u : ℝ => max 1 ((3 * u) ^ α)) :=
    continuous_const.max ((Real.continuous_rpow_const hα).comp (continuous_const.mul continuous_id))
  apply hnum.continuousOn.div (by fun_prop)
  intro u hu
  exact pow_ne_zero 2 (by change (0 : ℝ) ≤ u at hu; linarith)

theorem envelopeIntegrand_le_tail_power {α u : ℝ} (hα : 0 ≤ α) (hu : 1 ≤ u) :
    envelopeIntegrand α u ≤ (3 : ℝ) ^ α * u ^ (α - 2) := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  unfold envelopeIntegrand
  rw [max_eq_right (Real.one_le_rpow (by linarith : 1 ≤ 3 * u) hα),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hu0.le]
  calc
    _ ≤ ((3 : ℝ) ^ α * u ^ α) / u ^ 2 := div_le_div_of_nonneg_left (by positivity)
      (sq_pos_of_pos hu0) (by nlinarith)
    _ = (3 : ℝ) ^ α * u ^ (α - 2) := by
      rw [Real.rpow_sub hu0, Real.rpow_two, mul_div_assoc]

theorem envelope_integrand_integrable {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    IntegrableOn (envelopeIntegrand α) (Ioi 0) := by
  have hcont := envelopeIntegrand_continuousOn hα
  have hhead : IntegrableOn (envelopeIntegrand α) (Ioc (0 : ℝ) 1) :=
    ((hcont.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have htail : IntegrableOn (envelopeIntegrand α) (Ioi (1 : ℝ)) := by
    have hpower : IntegrableOn (fun u : ℝ => (3 : ℝ) ^ α * u ^ (α - 2)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : α - 2 < -1) zero_lt_one).const_mul _
    have hmeas : AEStronglyMeasurable (envelopeIntegrand α) (volume.restrict (Ioi (1 : ℝ))) :=
      (hcont.mono (fun u (hu : (1 : ℝ) < u) => (zero_lt_one.trans hu).le)).aestronglyMeasurable measurableSet_Ioi
    apply hpower.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (envelopeIntegrand_nonneg α u)]
    exact envelopeIntegrand_le_tail_power hα hu.le
  simpa only [Ioc_union_Ioi_eq_Ioi zero_le_one] using hhead.union htail

/-- Monotonicity of the envelope for nonnegative exponents, with the
small-base case handled by the maximum with one. -/
theorem envelopeIntegrand_mono_exponent {α β u : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hu : 0 < u) :
    envelopeIntegrand α u ≤ envelopeIntegrand β u := by
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  by_cases hb : 3 * u ≤ 1
  · rw [max_eq_left (Real.rpow_le_one (by positivity) hb hα),
      max_eq_left (Real.rpow_le_one (by positivity) hb (hα.trans hαβ))]
  · exact max_le_max le_rfl (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hb) hαβ)

end ModifiedCartan
#print axioms ModifiedCartan.envelope_integrand_integrable
