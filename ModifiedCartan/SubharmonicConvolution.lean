import ModifiedCartan.DiskConvolutionFubini
import ModifiedCartan.SubharmonicMeanCriterion
import ModifiedCartan.SmoothSubharmonicLaplacian
import Mathlib.Analysis.Calculus.ContDiff.Convolution

open scoped Topology Convolution ContDiff
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- A positive compact kernel preserves the literal disk submean property
where every translated point belongs to the original domain. -/
theorem IsSubharmonicOn.convolution {U V : Set ℂ} {f χ : ℂ → ℝ}
    (hu : IsSubharmonicOn U (fun z => (f z : EReal)))
    (hf : Continuous f) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχpos : ∀ w, 0 ≤ χ w)
    (hVU : ∀ x ∈ V, ∀ w ∈ tsupport χ, x - w ∈ U) :
    IsSubharmonicOn V (fun z => ((f ⋆[lsmul ℝ ℝ, volume] χ) z : EReal)) := by
  let F := f ⋆[lsmul ℝ ℝ, volume] χ
  have hF : Continuous F := hχc.continuous_convolution_right (lsmul ℝ ℝ) hf.locallyIntegrable hχ
  apply isSubharmonicOn_of_real_disk_means
    ((continuous_coe_real_ereal.comp hF).continuousOn.upperSemicontinuousOn)
    (fun z _ => EReal.coe_ne_top _) (hF.locallyIntegrable.locallyIntegrableOn V)
    (Eventually.of_forall (fun _ => rfl))
  intro c r hr hball
  simp only [Function.comp_apply, EReal.coe_le_coe_iff]
  have hi₁ : IntegrableOn (fun w => χ w * f (c - w)) (tsupport χ) :=
    (hχ.mul (hf.comp (continuous_const.sub continuous_id))).continuousOn.integrableOn_compact hχc
  have hi₂ := integrableOn_kernel_mul_disk_integral hf hχ hχc c r
  have hmean : (Real.pi * r ^ 2) * F c ≤ ∫ z in ball c r, F z := by
    change (Real.pi * r ^ 2) * (f ⋆[lsmul ℝ ℝ, volume] χ) c ≤
      ∫ z in ball c r, (f ⋆[lsmul ℝ ℝ, volume] χ) z
    rw [convolution_eq_integral_tsupport, integral_ball_convolution hf hχ hχc, ← integral_const_mul]
    apply integral_mono_ae (hi₁.const_mul _) hi₂
    filter_upwards [ae_restrict_mem (isClosed_tsupport χ).measurableSet] with w hw
    have htrans : closedBall (c - w) r ⊆ U := by
      intro z hz
      have hz' : z + w ∈ closedBall c r := by
        rw [mem_closedBall, dist_eq_norm] at hz ⊢
        convert hz using 1
        congr 1
        abel
      simpa only [add_sub_cancel_right] using hVU (z + w) (hball hz') w hw
    have hm := hu.mul_area_le_integral hr htrans (EReal.coe_ne_bot _)
    simp only [EReal.toReal_coe] at hm
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hm (hχpos w)
  have harea : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hq : F c ≤ (∫ z in ball c r, F z) / (Real.pi * r ^ 2) :=
    (le_div_iff₀ harea).mpr (by simpa only [mul_comm] using hmean)
  simpa only [div_eq_mul_inv, mul_comm] using hq

theorem IsSubharmonicOn.laplacian_convolution_nonneg {U V : Set ℂ} (hV : IsOpen V)
    {f χ : ℂ → ℝ} (hu : IsSubharmonicOn U (fun z => (f z : EReal)))
    (hf : Continuous f) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχpos : ∀ w, 0 ≤ χ w)
    (hVU : ∀ x ∈ V, ∀ w ∈ tsupport χ, x - w ∈ U) {c : ℂ} (hc : c ∈ V) :
    0 ≤ Laplacian.laplacian (f ⋆[lsmul ℝ ℝ, volume] χ) c := by
  exact (hu.convolution hf hχ.continuous hχc hχpos hVU).laplacian_nonneg_of_contDiff hV
    (hχc.contDiff_convolution_right (lsmul ℝ ℝ) hf.locallyIntegrable hχ) c hc

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.convolution
#print axioms ModifiedCartan.IsSubharmonicOn.laplacian_convolution_nonneg
