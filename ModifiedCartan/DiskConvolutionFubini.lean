import ModifiedCartan.DiskIsometry
import ModifiedCartan.WeakZeroCutoff
import Mathlib.MeasureTheory.Integral.Prod

open scoped Topology Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

theorem integral_ball_translate_sub (f : ℂ → ℝ) (c w : ℂ) (r : ℝ) :
    (∫ z in ball c r, f (z - w)) = ∫ z in ball (c - w) r, f z := by
  rw [← integral_ball_affine_isometry (LinearIsometryEquiv.refl ℝ ℂ) c r
    (fun z => f (z - w)),
    ← integral_ball_affine_isometry (LinearIsometryEquiv.refl ℝ ℂ) (c - w) r f]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => congrArg f (by simp; abel))

theorem integrable_disk_smoothing_integrand {f χ : ℂ → ℝ}
    (hf : Continuous f) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (c : ℂ) (r : ℝ) :
    Integrable (fun p : ℂ × ℂ => χ p.2 * f (p.1 - p.2))
      ((volume.restrict (ball c r)).prod (volume.restrict (tsupport χ))) := by
  rw [Measure.prod_restrict]
  change IntegrableOn _ (ball c r ×ˢ tsupport χ) (volume.prod volume)
  exact (((hχ.comp continuous_snd).mul
    (hf.comp (continuous_fst.sub continuous_snd))).continuousOn.integrableOn_compact
    ((isCompact_closedBall c r).prod hχc)).mono_set
    (prod_mono ball_subset_closedBall Subset.rfl)

theorem convolution_eq_integral_tsupport (f χ : ℂ → ℝ) (x : ℂ) :
    (f ⋆[lsmul ℝ ℝ, volume] χ) x = ∫ w in tsupport χ, χ w * f (x - w) := by
  rw [real_convolution_comm f χ, convolution_def]
  change (∫ w, χ w * f (x - w)) = _
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => by
    rw [image_eq_zero_of_notMem_tsupport hw, zero_mul])).symm

/-- Fubini for a continuous function smoothed by a compact kernel on a disk.
The compact restriction supplies all joint integrability hypotheses. -/
theorem integral_ball_convolution {f χ : ℂ → ℝ}
    (hf : Continuous f) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (c : ℂ) (r : ℝ) :
    (∫ z in ball c r, (f ⋆[lsmul ℝ ℝ, volume] χ) z) =
      ∫ w in tsupport χ, χ w * ∫ z in ball (c - w) r, f z := by
  simp_rw [convolution_eq_integral_tsupport]
  rw [integral_integral_swap (integrable_disk_smoothing_integrand hf hχ hχc c r)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  rw [integral_const_mul, integral_ball_translate_sub]

theorem integrableOn_kernel_mul_disk_integral {f χ : ℂ → ℝ}
    (hf : Continuous f) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (c : ℂ) (r : ℝ) :
    IntegrableOn (fun w => χ w * ∫ z in ball (c - w) r, f z) (tsupport χ) := by
  have hi := (integrable_disk_smoothing_integrand hf hχ hχc c r).integral_prod_right
  simpa only [IntegrableOn, integral_const_mul, integral_ball_translate_sub] using! hi

end ModifiedCartan
#print axioms ModifiedCartan.integral_ball_convolution
