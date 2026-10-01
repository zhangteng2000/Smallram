import ModifiedCartan.DiskIsometry

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem integral_norm_sq_ball_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ z in ball (0 : ℂ) r, ‖z‖ ^ 2 := by
  have hc : Continuous (fun z : ℂ => ‖z‖ ^ 2) := continuous_norm.pow 2
  have hi : IntegrableOn (fun z : ℂ => ‖z‖ ^ 2) (ball 0 r) :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  apply (setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall (fun z => sq_nonneg ‖z‖)) hi).mpr
  apply (hc.isOpen_support.inter isOpen_ball).measure_pos volume
  refine ⟨((r / 2 : ℝ) : ℂ), ?_, ?_⟩
  · change ‖((r / 2 : ℝ) : ℂ)‖ ^ 2 ≠ 0
    rw [Complex.norm_of_nonneg (half_pos hr).le]
    exact (sq_pos_of_pos (half_pos hr)).ne'
  · rw [mem_ball, dist_zero_right, Complex.norm_of_nonneg (half_pos hr).le]
    exact half_lt_self hr

/-- Integrating the four-direction difference gives four times the
ordinary disk submean difference. -/
theorem integral_quarter_difference {f : ℂ → ℝ} (hf : Continuous f) (c : ℂ) (r : ℝ) :
    (∫ z in ball (0 : ℂ) r,
      f (c + z) + f (c - z) + f (c + Complex.I * z) + f (c - Complex.I * z) - 4 * f c) =
      4 * ((∫ z in ball c r, f z) - (volume (ball (0 : ℂ) r)).toReal * f c) := by
  let a : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩
  let b : Circle := ⟨-Complex.I, mem_sphere_zero_iff_norm.mpr (by simp)⟩
  have h₁ : (∫ z in ball (0 : ℂ) r, f (c + z)) = ∫ z in ball c r, f z := by
    simpa using integral_ball_affine_isometry (LinearIsometryEquiv.refl ℝ ℂ) c r f
  have h₂ : (∫ z in ball (0 : ℂ) r, f (c - z)) = ∫ z in ball c r, f z := by
    simpa [sub_eq_add_neg] using integral_ball_affine_isometry (rotation (-1)) c r f
  have h₃ : (∫ z in ball (0 : ℂ) r, f (c + Complex.I * z)) = ∫ z in ball c r, f z := by
    simpa only [rotation_apply, a] using! integral_ball_affine_isometry (rotation a) c r f
  have h₄ : (∫ z in ball (0 : ℂ) r, f (c - Complex.I * z)) = ∫ z in ball c r, f z := by
    have hb (z : ℂ) : rotation b z = -Complex.I * z := rotation_apply b z
    simpa only [hb, neg_mul, sub_eq_add_neg] using!
      integral_ball_affine_isometry (rotation b) c r f
  have hi (b : ℂ) : IntegrableOn (fun z => f (c + b * z)) (ball (0 : ℂ) r) :=
    ((hf.comp (continuous_const.add (continuous_const.mul continuous_id))).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  have hi₁ : IntegrableOn (fun z => f (c + z)) (ball (0 : ℂ) r) := by simpa using hi 1
  have hi₂ : IntegrableOn (fun z => f (c - z)) (ball (0 : ℂ) r) := by simpa [sub_eq_add_neg] using hi (-1)
  have hi₃ := hi Complex.I
  have hi₄ : IntegrableOn (fun z => f (c - Complex.I * z)) (ball (0 : ℂ) r) := by
    simpa [sub_eq_add_neg] using hi (-Complex.I)
  have hiC : IntegrableOn (fun _ : ℂ => 4 * f c) (ball (0 : ℂ) r) :=
    (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  rw [integral_sub (f := fun z => f (c + z) + f (c - z) + f (c + Complex.I * z) + f (c - Complex.I * z))
      (((hi₁.add hi₂).add hi₃).add hi₄) hiC,
    integral_add (f := fun z => f (c + z) + f (c - z) + f (c + Complex.I * z)) ((hi₁.add hi₂).add hi₃) hi₄,
    integral_add (f := fun z => f (c + z) + f (c - z)) (hi₁.add hi₂) hi₃,
    integral_add hi₁ hi₂, h₁, h₂, h₃, h₄, setIntegral_const, smul_eq_mul]
  change _ - (volume (ball (0 : ℂ) r)).toReal * (4 * f c) = _
  ring

end ModifiedCartan
#print axioms ModifiedCartan.integral_quarter_difference
