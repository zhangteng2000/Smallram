import ModifiedCartan.SineHalfPower
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem circle_distance_rotated_im_lower {r : ℝ} (hr : 0 ≤ r) (a : ℂ) (θ : ℝ) :
    r * |Real.sin θ| ≤ ‖circleMap 0 r (θ + a.arg) - a‖ := by
  have he : circleMap 0 r (θ + a.arg) - a =
      (circleMap 0 r θ - (‖a‖ : ℂ)) * circleMap 0 1 a.arg := by
    rw [sub_mul, circleMap_zero_mul, mul_one]
    congr 1
    simpa only [circleMap_zero, Complex.ofReal_one, one_mul] using
      (Complex.norm_mul_exp_arg_mul_I a).symm
  rw [he, norm_mul, norm_circleMap_zero, abs_one, mul_one]
  have hi := Complex.abs_im_le_norm (circleMap 0 r θ - (‖a‖ : ℂ))
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, circleMap_zero_im,
    abs_mul, abs_of_nonneg hr] using hi

theorem circle_singular_half_power_rotated_bound {r : ℝ} (hr : 0 < r) (a : ℂ) :
    ∀ᵐ θ : ℝ,
      ‖circleMap 0 r (θ + a.arg) - a‖ ^ (-(1 / 2 : ℝ)) ≤
        r ^ (-(1 / 2 : ℝ)) * |Real.sin θ| ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [ae_sin_ne_zero] with θ hθ
  have hpos : 0 < r * |Real.sin θ| := mul_pos hr (abs_pos.mpr hθ)
  have h := Real.rpow_le_rpow_of_nonpos hpos (circle_distance_rotated_im_lower hr.le a θ)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  rwa [Real.mul_rpow hr.le (abs_nonneg _)] at h

theorem circle_singular_half_power_rotated_integrable {r : ℝ} (hr : 0 < r) (a : ℂ) :
    IntervalIntegrable (fun θ : ℝ =>
      ‖circleMap 0 r (θ + a.arg) - a‖ ^ (-(1 / 2 : ℝ))) volume 0 (2 * Real.pi) := by
  have hm : Measurable (fun θ : ℝ =>
      ‖circleMap 0 r (θ + a.arg) - a‖ ^ (-(1 / 2 : ℝ))) := by fun_prop
  apply ((sine_half_power_intervalIntegrable 0 (2 * Real.pi)).const_mul
    (r ^ (-(1 / 2 : ℝ)))).mono_fun' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_of_ae (circle_singular_half_power_rotated_bound hr a)] with θ hθ
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hθ

theorem circleIntegrable_of_shift {f : ℂ → ℝ} {r η : ℝ}
    (hf : IntervalIntegrable (fun θ : ℝ => f (circleMap 0 r (θ + η))) volume 0 (2 * Real.pi)) :
    CircleIntegrable f 0 r := by
  have hshift : IntervalIntegrable (fun θ : ℝ => f (circleMap 0 r θ)) volume η (η + 2 * Real.pi) := by
    have hh := (IntervalIntegrable.comp_add_right_iff
      (f := fun θ : ℝ => f (circleMap 0 r θ)) (c := η)).mp hf
    simpa only [zero_add, add_zero, add_comm] using hh
  have hp : Function.Periodic (fun θ : ℝ => f (circleMap 0 r θ)) (2 * Real.pi) :=
    (periodic_circleMap 0 r).comp f
  have hh := (hp.intervalIntegrable_iff (t₁ := η) (t₂ := 0)).mp hshift
  rw [circleIntegrable_def]
  simpa only [zero_add] using hh

theorem circle_singular_half_power_integrable {r : ℝ} (hr : 0 < r) (a : ℂ) :
    CircleIntegrable (fun z : ℂ => ‖z - a‖ ^ (-(1 / 2 : ℝ))) 0 r :=
  circleIntegrable_of_shift (circle_singular_half_power_rotated_integrable hr a)

/-- Uniform fractional singular-kernel mean, a dependency for LaTeX `lem:NH`. -/
theorem circle_singular_half_power_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → ∀ a : ℂ,
      Real.circleAverage (fun z : ℂ => ‖z - a‖ ^ (-(1 / 2 : ℝ))) 0 r ≤
        K * r ^ (-(1 / 2 : ℝ)) := by
  let I := ∫ θ in (0 : ℝ)..2 * Real.pi, |Real.sin θ| ^ (-(1 / 2 : ℝ))
  refine ⟨1 + (2 * Real.pi)⁻¹ * |I|, by positivity, fun r hr a => ?_⟩
  rw [Real.circleAverage_eq_integral_add a.arg]
  have hi := intervalIntegral.integral_mono_ae_restrict Real.two_pi_pos.le
    (circle_singular_half_power_rotated_integrable hr a)
    ((sine_half_power_intervalIntegrable 0 (2 * Real.pi)).const_mul (r ^ (-(1 / 2 : ℝ))))
    (ae_restrict_of_ae (circle_singular_half_power_rotated_bound hr a))
  rw [intervalIntegral.integral_const_mul] at hi
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr Real.two_pi_pos.le)
  change (2 * Real.pi)⁻¹ * _ ≤ _
  have hI : I ≤ |I| := le_abs_self I
  have hp := mul_le_mul_of_nonneg_left hI
    (mul_nonneg (inv_nonneg.mpr Real.two_pi_pos.le) (Real.rpow_nonneg hr.le (-(1 / 2 : ℝ))))
  have hn := Real.rpow_nonneg hr.le (-(1 / 2 : ℝ))
  dsimp only [I] at *
  nlinarith

end ModifiedCartan
#print axioms ModifiedCartan.circle_singular_half_power_integrable
#print axioms ModifiedCartan.circle_singular_half_power_bound
