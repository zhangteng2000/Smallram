import ModifiedCartan.LocalConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-- The two-dimensional local integrability threshold used in the Cauchy
transform argument of `lem:logderivlimit`. -/
theorem integrableOn_norm_neg_rpow {p : ℝ} (hp : p < 2) (R : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ (-p)) (ball 0 R) := by
  refine integrableOn_ball_of_norm_le_rpow (E := ℂ) (C := 1) (α := p)
    (by norm_num [Complex.finrank_real_complex])
    (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using hp) ?_ ?_
  · filter_upwards [] with z
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) (-p)), one_mul]
    exact le_rfl
  · exact (measurable_norm.pow_const (-p)).aestronglyMeasurable

theorem integrableOn_shifted_norm_neg_rpow {p : ℝ} (hp : p < 2) (a : ℂ) (R : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z - a‖ ^ (-p)) (ball a R) := by
  have ht := (measurePreserving_sub_right (volume : Measure ℂ) a).integrableOn_comp_preimage
    (f := fun z : ℂ => ‖z‖ ^ (-p)) (s := ball 0 R) (measurableEmbedding_subRight a)
  have hball : (fun z : ℂ => z - a) ⁻¹' ball 0 R = ball a R := by
    ext z
    simp only [mem_preimage, mem_ball, dist_eq_norm, sub_zero]
  have h := ht.mpr (integrableOn_norm_neg_rpow hp R)
  simpa only [Function.comp_def, hball] using h

theorem memLp_cauchyKernel {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) (a : ℂ) (R : ℝ) :
    MemLp (fun z : ℂ => (z - a)⁻¹) (ENNReal.ofReal p) (volume.restrict (ball a R)) := by
  have hmeas : AEStronglyMeasurable (fun z : ℂ => (z - a)⁻¹)
      (volume.restrict (ball a R)) := by fun_prop
  apply (integrable_norm_rpow_iff hmeas (by simpa using hp0)
    ENNReal.ofReal_ne_top).mp
  simp only [ENNReal.toReal_ofReal hp0.le, norm_inv,
    Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
  exact integrableOn_shifted_norm_neg_rpow hp2 a R

theorem memLp_cauchyKernel_on_compact {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2)
    (a : ℂ) {K : Set ℂ} (hK : IsCompact K) :
    MemLp (fun z : ℂ => (z - a)⁻¹) (ENNReal.ofReal p) (volume.restrict K) := by
  obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_lt
  have hsub : K ⊆ ball a (R + ‖a‖) := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    linarith [norm_sub_le z a, hR z hz]
  exact (memLp_cauchyKernel hp0 hp2 a (R + ‖a‖)).mono_measure
    (Measure.restrict_mono hsub le_rfl)

theorem integral_shifted_norm_neg_rpow (p : ℝ) (a : ℂ) (R : ℝ) :
    (∫ z in ball a R, ‖z - a‖ ^ (-p)) = ∫ z : ℂ in ball 0 R, ‖z‖ ^ (-p) := by
  have hball : (fun z : ℂ => z - a) ⁻¹' ball 0 R = ball a R := by
    ext z
    simp only [mem_preimage, mem_ball, dist_eq_norm, sub_zero]
  have h := (measurePreserving_sub_right (volume : Measure ℂ) a).setIntegral_preimage_emb
    (measurableEmbedding_subRight a) (fun z : ℂ => ‖z‖ ^ (-p)) (ball 0 R)
  simpa only [hball] using h

/-- Vanishing of the discarded singular-kernel mass as its radius shrinks.
The translated integral is exactly independent of the centre. -/
theorem integral_norm_neg_rpow_tendsto_zero {p : ℝ} (hp : p < 2) :
    Tendsto (fun r : ℝ => ∫ z : ℂ in ball 0 r, ‖z‖ ^ (-p)) (𝓝 0) (𝓝 0) := by
  have hvol : Tendsto (fun r : ℝ => volume (ball (0 : ℂ) r)) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun r : ℝ => (ENNReal.ofReal r) ^ 2 * (NNReal.pi : ℝ≥0∞)) := by
      exact (ENNReal.continuous_mul_const ENNReal.coe_ne_top).comp
        ((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal)
    simpa only [Complex.volume_ball, ENNReal.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul] using hcont.tendsto 0
  have hmeasure : Tendsto (fun r : ℝ =>
      (volume.restrict (ball (0 : ℂ) 1)) (ball 0 r)) (𝓝 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvol (fun _ => bot_le)
    intro r
    exact Measure.restrict_le_self _
  have hlim := (integrableOn_norm_neg_rpow hp 1).tendsto_setIntegral_nhds_zero hmeasure
  apply hlim.congr'
  filter_upwards [gt_mem_nhds (by norm_num : (0 : ℝ) < 1)] with r hr
  rw [Measure.restrict_restrict measurableSet_ball,
    inter_eq_left.mpr (ball_subset_ball hr.le)]

end ModifiedCartan

