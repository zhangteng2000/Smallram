import ModifiedCartan.HerglotzNormalization
import ModifiedCartan.BoundedWronskian
import ModifiedCartan.MonicCircleMean
import ModifiedCartan.RepresentationAsymptotics

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem representation_gauge_difference_re_le {n : ℕ} (f : Curve n) (t : ℝ)
    {H : ℂ → ℂ} {P : Polynomial ℂ} (hH : AnalyticOnNhd ℂ H (ball 0 64)) (hP : P.Monic)
    (hW : ∀ z ∈ ball (0 : ℂ) 64,
      FewInflection.wronskian n (rescaledRepresentation f t H) z = P.eval z)
    {z : ℂ} (hz : z ∈ closedBall 0 48) :
    (H z - rescaledHerglotz f t z).re ≤ Real.log (unitBoundWronskianConstant n) := by
  let L := rescaledHerglotz f t
  have hL : AnalyticOnNhd ℂ L (ball 0 256) := rescaledHerglotz_analytic f t
  have hsub : closedBall z 1 ⊆ ball (0 : ℂ) 64 := by
    intro w hw
    have hw' : ‖w-z‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hz' : ‖z‖ ≤ 48 := by simpa only [mem_closedBall, dist_zero_right] using hz
    have ht : ‖w‖ ≤ ‖w-z‖ + ‖z‖ := by simpa only [sub_add_cancel] using norm_add_le (w-z) z
    simpa only [mem_ball, dist_zero_right] using (show ‖w‖ < (64 : ℝ) by linarith)
  have h64256 : ball (0 : ℂ) 64 ⊆ ball 0 256 := ball_subset_ball (by norm_num)
  have hA : AnalyticOnNhd ℂ (fun w => (n + 1 : ℂ) * (H w - L w)) (closedBall z 1) := by
    intro w hw
    exact analyticAt_const.fun_mul ((hH w (hsub hw)).sub (hL w (h64256 (hsub hw))))
  have hM : 0 < unitBoundWronskianConstant n := lt_of_lt_of_le (by norm_num)
    (unitBoundWronskianConstant_ge_one n)
  have he := analytic_exp_factor_re_le_log_bound P hP hA hM (by
    intro w hw
    have hw64 := hsub (sphere_subset_closedBall hw)
    have heq := rescaledRepresentation_wronskian_gauge_change f t
      (hH w hw64) (hL w (h64256 hw64))
    rw [hW w hw64] at heq
    rw [← heq]
    exact norm_wronskian_le_of_unit_bound
      (fun j v hv => rescaledRepresentation_analyticAt f t (hL v hv) j)
      (fun v hv => rescaledHerglotz_normalization_norm_le_one f t hv) hw64)
  have he' : (n + 1 : ℝ) * (H z - L z).re ≤ Real.log (unitBoundWronskianConstant n) := by
    simpa using he
  have hlog : 0 ≤ Real.log (unitBoundWronskianConstant n) :=
    Real.log_nonneg (unitBoundWronskianConstant_ge_one n)
  by_cases ha : 0 ≤ (H z - L z).re
  · have hm := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) ha
    change (H z - L z).re ≤ _
    nlinarith
  · change (H z - L z).re ≤ _
    linarith

/-- Deterministic upper bound for the actual paper representation. Auxiliary
Herglotz normalization, a monic unit-circle mean, and Harnack replace the
logarithmic-derivative mean argument in Steps 2--3 of `prop:representation`. -/
theorem rescaledRepresentation_log_norm_upper {n : ℕ} (f : Curve n) (t : ℝ)
    {H : ℂ → ℂ} {P : Polynomial ℂ} (hH : AnalyticOnNhd ℂ H (ball 0 64)) (hP : P.Monic)
    (hW : ∀ z ∈ ball (0 : ℂ) 64,
      FewInflection.wronskian n (rescaledRepresentation f t H) z = P.eval z)
    {z : ℂ} (hz : z ∈ closedBall 0 32) :
    Real.log (euclideanNorm (fun j => rescaledRepresentation f t H j z)) ≤
      5 * characteristic f (256 * t) + 5 * Real.log (euclideanNorm (f.vector 0)) -
        5 * (H 0).re + 4 * Real.log (unitBoundWronskianConstant n) := by
  let L := rescaledHerglotz f t
  have hL : AnalyticOnNhd ℂ L (ball 0 256) := rescaledHerglotz_analytic f t
  have hv : InnerProductSpace.HarmonicOnNhd (fun w => (H w - L w).re) (closedBall 0 48) := by
    intro w hw
    exact ((hH w (closedBall_subset_ball (by norm_num : (48 : ℝ) < 64) hw)).sub
      (hL w (closedBall_subset_ball (by norm_num : (48 : ℝ) < 256) hw))).harmonicAt_re
  have hlower := harmonic_lower_bound_48_32 hv
    (fun w hw => representation_gauge_difference_re_le f t hH hP hW hw) hz
  have hmajor : Real.log (euclideanNorm (f.vector ((t : ℂ) * z))) ≤ (L z).re :=
    curve_log_norm_le_herglotz (f.dilate (t : ℂ))
      (closedBall_subset_ball (by norm_num : (32 : ℝ) < 256) hz)
  have hcenter := rescaledHerglotz_re_zero f t
  change (L 0).re = _ at hcenter
  simp only [Complex.sub_re] at hlower
  rw [rescaledRepresentation_log_norm]
  linarith

/-- The exact upper bound in LaTeX `eq:representationbounds`, for the same
analytic gauges and actual monic Wronskians supplied by Step 1. -/
theorem Paper.eq_representationbounds_norm {n : ℕ} (f : Curve n) {C : ℝ}
    {t s : ℕ → ℝ} {H : ℕ → ℂ → ℂ} {P : ℕ → Polynomial ℂ}
    (hs : Tendsto s atTop atTop)
    (hdata : ∀ᶠ ν in atTop, AnalyticOnNhd ℂ (H ν) (ball 0 64) ∧ (P ν).Monic ∧
      ∀ z ∈ ball (0 : ℂ) 64,
        FewInflection.wronskian n (rescaledRepresentation f (t ν) (H ν)) z = (P ν).eval z)
    (hT : ∀ᶠ ν in atTop, characteristic f (256 * t ν) ≤ C * s ν)
    (hcenter : Tendsto (fun ν => (H ν 0).re / s ν) atTop (𝓝 0)) :
    ∀ᶠ ν in atTop, ∀ z ∈ closedBall (0 : ℂ) 32,
      euclideanNorm (fun j => rescaledRepresentation f (t ν) (H ν) j z) ≤
        Real.exp ((5 * C + 1) * s ν) := by
  let D := 5 * Real.log (euclideanNorm (f.vector 0)) + 4 * Real.log (unitBoundWronskianConstant n)
  have hsmall : Tendsto (fun ν => (D - 5 * (H ν 0).re) / s ν) atTop (𝓝 0) := by
    have hl := ((tendsto_inv_atTop_zero.comp hs).const_mul D).sub (hcenter.const_mul (5 : ℝ))
    simp only [mul_zero, sub_zero] at hl
    convert! hl using 1
    funext ν
    simp only [Function.comp_apply]
    ring
  filter_upwards [hdata, hT, hs.eventually_gt_atTop 0,
    hsmall.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with ν hd hTν hsν hsmallν
  intro z hz
  have hu := rescaledRepresentation_log_norm_upper f (t ν) hd.1 hd.2.1 hd.2.2 hz
  have herror : D - 5 * (H ν 0).re < s ν := (div_lt_one hsν).mp hsmallν
  have hlog : Real.log (euclideanNorm (fun j => rescaledRepresentation f (t ν) (H ν) j z)) ≤
      (5 * C + 1) * s ν := by
    dsimp [D] at herror
    nlinarith
  have hn : 0 < euclideanNorm (fun j => rescaledRepresentation f (t ν) (H ν) j z) := by
    apply euclideanNorm_pos
    intro he
    obtain ⟨j, hj⟩ := rescaledRepresentation_reduced f (t ν) (H ν) z
    exact hj (congrFun he j)
  exact (Real.log_le_iff_le_exp hn).mp hlog

end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_representationbounds_norm
