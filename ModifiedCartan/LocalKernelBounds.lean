import FewInflection.Nevanlinna.PoissonBoundaryBounds
import Mathlib.Analysis.Complex.Liouville

open scoped Topology ComplexConjugate
open Filter Set Metric Complex MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem reflected_denominator_lower_bound {r R : ℝ} {a z : ℂ}
    (hr : 0 ≤ r) (hrR : r < R) (ha : ‖a‖ ≤ R) (hz : ‖z‖ ≤ r) :
    R * (R - r) ≤ ‖(R : ℂ) ^ 2 - conj a * z‖ := by
  have hR : 0 < R := hr.trans_lt hrR
  have hgeom := norm_sub_norm_le ((R : ℂ) ^ 2) (conj a * z)
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    norm_mul, norm_conj] at hgeom
  have hprod : ‖a‖ * ‖z‖ ≤ R * r := mul_le_mul ha hz (norm_nonneg _) hR.le
  nlinarith

theorem reflected_kernel_bound_general {r R : ℝ} {a z : ℂ}
    (hr : 0 ≤ r) (hrR : r < R) (ha : ‖a‖ ≤ R) (hz : ‖z‖ ≤ r) :
    ‖conj a / ((R : ℂ) ^ 2 - conj a * z)‖ ≤ (R - r)⁻¹ := by
  have hR : 0 < R := hr.trans_lt hrR
  have hgap := sub_pos.mpr hrR
  have hb := reflected_denominator_lower_bound hr hrR ha hz
  have hd : 0 < ‖(R : ℂ) ^ 2 - conj a * z‖ := (mul_pos hR hgap).trans_le hb
  rw [norm_div, norm_conj, inv_eq_one_div]
  apply (div_le_div_iff₀ hd hgap).mpr
  have hm := mul_le_mul_of_nonneg_right ha hgap.le
  nlinarith

theorem poisson_first_kernel_bound_general {r R : ℝ} {z ζ : ℂ}
    (hr : 0 ≤ r) (hrR : r < R) (hz : ‖z‖ ≤ r) (hζ : ζ ∈ sphere (0 : ℂ) R) :
    ‖2 * ζ / (ζ - z) ^ 2‖ ≤ 2 * R / (R - r) ^ 2 := by
  have hR : 0 < R := hr.trans_lt hrR
  have hζn : ‖ζ‖ = R := by simpa only [mem_sphere, dist_zero_right] using hζ
  have hd : R - r ≤ ‖ζ - z‖ := by
    have hh := norm_sub_norm_le ζ z
    rw [hζn] at hh
    linarith
  rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow, hζn]
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (sub_pos.mpr hrR))
    (pow_le_pow_left₀ (sub_pos.mpr hrR).le hd 2)

noncomputable def localPoissonLogDerivative (f : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  Real.circleAverage (fun ζ : ℂ =>
    (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R

theorem localPoissonLogDerivative_analytic {f : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f (sphere 0 |R|)) :
    AnalyticOnNhd ℂ (localPoissonLogDerivative f R) (ball 0 R) := by
  have hr := hf.circleIntegrable_log_norm
  have hc : CircleIntegrable (fun ζ : ℂ => (Real.log ‖f ζ‖ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hr ⊢
    exact Complex.ofRealCLM.integrable_comp hr
  have hH := analyticOnNhd_circleAverage_herglotzRieszKernel_smul hc
  apply (hH.deriv_of_isOpen isOpen_ball).congr isOpen_ball
  intro z hz
  exact (hasDerivAt_circleAverage_herglotzRieszKernel_smul hc hz).deriv

theorem localPoissonLogDerivative_bound {f : ℂ → ℂ} {r R : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hrR : r < R) (hz : ‖z‖ ≤ r)
    (hf : MeromorphicOn f (sphere 0 |R|)) :
    ‖localPoissonLogDerivative f R z‖ ≤
      (2 * R / (R - r) ^ 2) * Real.circleAverage (fun ζ => |Real.log ‖f ζ‖|) 0 R := by
  have hR := hr.trans_lt hrR
  have hi := hf.circleIntegrable_log_norm.abs
  have hb := FewInflection.norm_circleAverage_le_of_norm_le
    (F := fun ζ : ℂ => (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ))
    (b := (2 * R / (R - r) ^ 2) • fun ζ : ℂ => |Real.log ‖f ζ‖|)
    (CircleIntegrable.const_smul hi) (fun ζ hζ => ?_)
  · simpa only [localPoissonLogDerivative, Real.circleAverage_smul, smul_eq_mul] using hb
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (poisson_first_kernel_bound_general hr hrR hz (by simpa [abs_of_pos hR] using hζ))
      (abs_nonneg _)

theorem local_cauchy_derivative_bound {A : ℂ → ℂ} {r s R M : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) (hsR : s < R)
    (hA : AnalyticOnNhd ℂ A (ball 0 R))
    (hbound : ∀ w ∈ closedBall (0 : ℂ) s, ‖A w‖ ≤ M) (m : ℕ) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖iteratedDeriv m A z‖ ≤ (m.factorial : ℝ) * M / (s - r) ^ m := by
  have hsub : closedBall z (s - r) ⊆ closedBall (0 : ℂ) s := by
    intro w hw
    have hw' : ‖w - z‖ ≤ s - r := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have ht : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w - z) z
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hsubR : closedBall z (s - r) ⊆ ball (0 : ℂ) R :=
    hsub.trans (closedBall_subset_ball hsR)
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m (sub_pos.mpr hrs)
    (hA.differentiableOn.diffContOnCl_ball hsubR)
    (fun w hw => hbound w (hsub (sphere_subset_closedBall hw)))

end ModifiedCartan
#print axioms ModifiedCartan.localPoissonLogDerivative_bound
#print axioms ModifiedCartan.local_cauchy_derivative_bound
