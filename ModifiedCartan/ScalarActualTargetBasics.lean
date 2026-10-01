import ModifiedCartan.ScalarTargetLogData
import ModifiedCartan.ScalarNormNormalizedProfile

open scoped Topology Matrix
open Filter Set Metric Matrix
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- The normalized fixed-target form of the actual gauged representation. -/
def scalarActualTarget (f : Curve 1) (β : WithTop ℂ) (r : ℝ) (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((fun j => rescaledRepresentation f r H j z) ᵥ*
    (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ)) 0

theorem scalarActualTarget_analyticOnNhd (f : Curve 1) (β : WithTop ℂ) (r : ℝ)
    {H : ℂ → ℂ} {U : Set ℂ} (hH : AnalyticOnNhd ℂ H U) :
    AnalyticOnNhd ℂ (scalarActualTarget f β r H) U := by
  have hc (j : Index 1) : AnalyticOnNhd ℂ (rescaledRepresentation f r H j) U :=
    fun z hz => rescaledRepresentation_analyticAt f r (hH z hz) j
  have he : scalarActualTarget f β r H = fun z =>
      scalarTargetLinearForm β (rescaledRepresentation f r H 0 z)
        (rescaledRepresentation f r H 1 z) / (scalarTargetNormalizingSize β : ℂ) :=
    funext (fun z => scalarTargetUnitary_first β _)
  rw [he]
  induction β using WithTop.recTopCoe with
  | top =>
    change AnalyticOnNhd ℂ (fun z => rescaledRepresentation f r H 0 z / 1) U
    simpa only [div_one] using hc 0
  | coe b =>
    intro z hz
    exact ((hc 1 z hz).sub (analyticAt_const.mul (hc 0 z hz))).div_const

theorem scalarActualTarget_norm_le (f : Curve 1) (β : WithTop ℂ) (r : ℝ)
    (H : ℂ → ℂ) (z : ℂ) :
    ‖scalarActualTarget f β r H z‖ ≤
      euclideanNorm (fun j => rescaledRepresentation f r H j z) := by
  exact ((norm_le_pi_norm _ 0).trans (norm_le_euclideanNorm _)).trans_eq
    (euclideanNorm_vecMul_unitary (scalarTargetUnitary β) _)

theorem ArbitraryRadiusLimitData.scalar_norm_lt_explicit_bound
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 2) :
    (d.U z).toReal < (Real.pi / 2) * (2 : ℝ) ^ ρ := by
  by_cases hz0 : z = 0
  · rw [hz0, d.origin_zero, EReal.toReal_zero]
    positivity
  · obtain ⟨φ, hφ⟩ := d.scalar_norm_polar_profile hρ hr
    have hnorm : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
    have he : circleMap 0 ‖z‖ z.arg = z := by
      rw [circleMap_zero, Complex.norm_mul_exp_arg_mul_I]
    have hh := hφ ‖z‖ (norm_pos_iff.mpr hz0) hnorm z.arg
    rw [he] at hh
    rw [hh]
    calc
      _ ≤ (Real.pi / 2) * ‖z‖ ^ ρ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one (ρ * z.arg + φ)) (by positivity : 0 ≤ (Real.pi / 2) * ‖z‖ ^ ρ)
      _ < _ := mul_lt_mul_of_pos_left
        (Real.rpow_lt_rpow (norm_nonneg z) hnorm (lt_of_lt_of_le zero_lt_one hρ))
        (half_pos Real.pi_pos)

theorem PolynomialReplacementData.scalar_actual_target_approximation
    {f : Curve 1} {r s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index 1 → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f r s C A L H p a η) (β : WithTop ℂ) :
    ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 2,
      ‖scalarActualTarget f β (r ν) (H ν) z -
        (polynomialMatrixGauge (p ν) (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) 0).eval z‖ ≤
          scalarTargetLinearSize β * Real.exp (-A * s ν) := by
  filter_upwards [h.jet_error] with ν hν z hz
  have he := congrFun (polynomialMatrixGauge_eval_vecMul (p ν)
    (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) z) 0
  rw [scalarActualTarget, he, norm_sub_rev]
  apply scalarTargetUnitary_first_difference_bound β (Real.exp_pos _).le
  intro j
  simpa only [iteratedDeriv_zero] using hν j 0 (by omega) z
    ((closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 16)) (ball_subset_closedBall hz))

end
end ModifiedCartan
#print axioms ModifiedCartan.scalarActualTarget_analyticOnNhd
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_lt_explicit_bound
#print axioms ModifiedCartan.PolynomialReplacementData.scalar_actual_target_approximation
