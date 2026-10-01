import ModifiedCartan.WeakGradientConvolution
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- A nonnegative distributional directional derivative becomes a
nonnegative classical directional derivative after positive smoothing. -/
theorem fderiv_convolution_nonneg_of_test {U : Set ℂ} {q χ : ℂ → ℝ}
    (hq : LocallyIntegrable q) (w : ℂ)
    (htest : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ z, 0 ≤ φ z) → (∫ z, q z * fderiv ℝ φ z w) ≤ 0)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (hχpos : ∀ z, 0 ≤ χ z)
    (x : ℂ) (hx : (fun z : ℂ => x - z) ⁻¹' tsupport χ ⊆ U) :
    0 ≤ fderiv ℝ (q ⋆[lsmul ℝ ℝ, volume] χ) x w := by
  rw [(hχc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hq hχ x).fderiv]
  rw [convolution_precompR_apply (lsmul ℝ ℝ) hq (hχc.fderiv ℝ)
    (hχ.continuous_fderiv one_ne_zero), convolution_def]
  change 0 ≤ ∫ z, q z * fderiv ℝ χ (x - z) w
  let φ : ℂ → ℝ := fun z => χ (x - z)
  have hφ : ContDiff ℝ 1 φ := hχ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := hχc.comp_homeomorph (IsometryEquiv.subLeft x).toHomeomorph
  have hφU : tsupport φ ⊆ U :=
    (tsupport_comp_subset_preimage χ (continuous_const.sub continuous_id)).trans hx
  have hderiv (z : ℂ) : fderiv ℝ φ z w = -fderiv ℝ χ (x - z) w := by
    have hd := ((hχ.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp z
      ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))).fderiv
    have hval := congrArg (fun L : ℂ →L[ℝ] ℝ => L w) hd
    simpa only [φ, Function.comp_def, Pi.sub_apply, id_eq,
      ContinuousLinearMap.comp_apply, sub_zero, zero_sub,
      neg_apply, ContinuousLinearMap.id_apply, map_neg] using hval
  have hh := htest φ hφ hφc hφU (fun z => hχpos (x - z))
  simp only [hderiv, mul_neg, integral_neg, neg_nonpos] at hh
  exact hh

theorem le_of_fderiv_nonneg_on_line {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (x w : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, 0 ≤ fderiv ℝ f (x + t • w) w) : f x ≤ f (x + T • w) := by
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa only [zero_add, one_smul, Pi.add_apply, id_eq] using!
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const w)
  have hderiv (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • w))
      (fderiv ℝ f (x + t • w) w) t := by
    exact ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt t (hline t))
  have hmono : MonotoneOn (fun t : ℝ => f (x + t • w)) (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
      (hf.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
      (fun t _ => (hderiv t).hasDerivWithinAt)
      (fun t ht => hd t (interior_subset ht))
  simpa only [zero_smul, add_zero] using hmono (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT

theorem convolution_le_along_line_of_tests {U : Set ℂ} {q χ : ℂ → ℝ}
    (hq : LocallyIntegrable q) (w : ℂ)
    (htest : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ z, 0 ≤ φ z) → (∫ z, q z * fderiv ℝ φ z w) ≤ 0)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (hχpos : ∀ z, 0 ≤ χ z)
    (x : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hx : ∀ t ∈ Icc 0 T, (fun z : ℂ => x + t • w - z) ⁻¹' tsupport χ ⊆ U) :
    (q ⋆[lsmul ℝ ℝ, volume] χ) x ≤ (q ⋆[lsmul ℝ ℝ, volume] χ) (x + T • w) := by
  apply le_of_fderiv_nonneg_on_line (hχc.contDiff_convolution_right (lsmul ℝ ℝ) hq hχ) x w hT
  intro t ht
  exact fderiv_convolution_nonneg_of_test hq w htest hχ hχc hχpos _ (hx t ht)

end ModifiedCartan
#print axioms ModifiedCartan.convolution_le_along_line_of_tests
