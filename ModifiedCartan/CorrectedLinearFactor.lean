import ModifiedCartan.QuantitativeTaylor
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Polynomial approximation on a strictly smaller disk, directly from the
proved Taylor remainder bound. Dependency of the scalar `thm:A` lift. -/
theorem exists_polynomial_approx_on_closedBall {f : ℂ → ℂ} {r R ε : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    ∃ p : Polynomial ℂ, ∀ z ∈ closedBall (0 : ℂ) r, ‖p.eval z - f z‖ < ε := by
  have hR : 0 < R := hr.trans_lt hrR
  obtain ⟨M, hM0, hM⟩ :=
    ((isCompact_closedBall (0 : ℂ) R).image_of_continuousOn hf.continuousOn).isBounded.exists_pos_norm_le
  have hlim : Tendsto (fun N : ℕ => M * (r / R) ^ N / (1 - r / R)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr hR.le)
      ((div_lt_one hR).mpr hrR)).const_mul M).div_const (1 - r / R)
  obtain ⟨N, hN⟩ := (hlim.eventually_lt_const hε).exists
  refine ⟨FewInflection.taylorPolynomial f 0 N, fun z hz => ?_⟩
  exact (norm_taylorPolynomial_sub_le hR hr hrR hM0.le hf
    (fun w hw => hM _ (mem_image_of_mem f (sphere_subset_closedBall hw))) hz N).trans_lt hN

/-- A corrected linear factor is arbitrarily close to one on the half disk.
Its exponential correction creates no additional zero. No growth restriction
is imposed on the eventual divisor in the scalar `thm:A` construction. -/
theorem exists_corrected_linear_factor {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      ‖(1 - z) * Complex.exp (p.eval z) - 1‖ ≤ ε := by
  let L : ℂ → ℂ := fun z => -Complex.log (1 - z)
  have hslit {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ∈ Complex.slitPlane := by
    simpa only [norm_neg, sub_eq_add_neg] using
      Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa only [norm_neg] using hz)
  have hL : DifferentiableOn ℂ L (closedBall 0 (3 / 4)) := by
    apply DifferentiableOn.neg
    apply DifferentiableOn.clog (by fun_prop)
    intro z hz
    apply hslit
    have hzn : ‖z‖ ≤ 3 / 4 := by simpa only [mem_closedBall, dist_zero_right] using hz
    linarith
  obtain ⟨p, hp⟩ := exists_polynomial_approx_on_closedBall
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 3 / 4)
    (lt_min (by norm_num : (0 : ℝ) < 1) (half_pos hε)) hL
  refine ⟨p, fun z hz => ?_⟩
  have he := hp z (by simpa only [mem_closedBall, dist_zero_right] using hz)
  have hn : 1 - z ≠ 0 := Complex.slitPlane_ne_zero (hslit (by linarith))
  have hid : (1 - z) * Complex.exp (p.eval z) =
      Complex.exp (p.eval z - L z) := by
    dsimp only [L]
    rw [sub_neg_eq_add, Complex.exp_add, Complex.exp_log hn, mul_comm]
  rw [hid]
  exact (Complex.norm_exp_sub_one_le (he.le.trans (min_le_left _ _))).trans
    (by have hh := he.le.trans (min_le_right _ _); linarith)

end ModifiedCartan
#print axioms ModifiedCartan.exists_polynomial_approx_on_closedBall
#print axioms ModifiedCartan.exists_corrected_linear_factor
