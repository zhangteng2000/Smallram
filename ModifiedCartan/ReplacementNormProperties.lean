import ModifiedCartan.PolynomialReplacement
import ModifiedCartan.EuclideanTriangle

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem PolynomialReplacementData.taylor_center {n : ℕ} {f : Curve n}
    {t s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η)
    (hL : 0 < L) (hs : ∀ ν, 0 < s ν) (ν : ℕ) (j : Index n) :
    (p ν j).eval 0 = rescaledRepresentation f (t ν) (H ν) j 0 := by
  rw [h.taylor]
  have hN : 0 < Nat.ceil (L * s ν) := Nat.ceil_pos.mpr (mul_pos hL (hs ν))
  have he : Nat.ceil (L * s ν) = (Nat.ceil (L * s ν) - 1) + 1 := by omega
  rw [he, FewInflection.taylorPolynomial_eval_center]

theorem PolynomialReplacementData.norm_error {n : ℕ} {f : Curve n}
    {t s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η) :
    ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 4,
      |euclideanNorm (fun j => (p ν j).eval z) -
        euclideanNorm (fun j => rescaledRepresentation f (t ν) (H ν) j z)| ≤
          Real.sqrt (n + 1) * Real.exp (-A * s ν) := by
  filter_upwards [h.jet_error] with ν hν z hz
  apply euclideanNorm_difference_le_of_component_error _ _ (Real.exp_pos _).le
  intro j
  simpa only [iteratedDeriv_zero] using hν j 0 (by omega) z
    ((closedBall_subset_closedBall (by norm_num : (4 : ℝ) ≤ 16)) (ball_subset_closedBall hz))

theorem rescaledRepresentation_norm_pos {n : ℕ} (f : Curve n) (t : ℝ)
    (H : ℂ → ℂ) (z : ℂ) :
    0 < euclideanNorm (fun j => rescaledRepresentation f t H j z) := by
  apply euclideanNorm_pos
  obtain ⟨j, hj⟩ := rescaledRepresentation_reduced f t H z
  intro he
  exact hj (congrFun he j)

theorem PolynomialReplacementData.polynomial_coordinate_bound {n : ℕ} {f : Curve n}
    {t s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η)
    (hC : 0 < C) (hA : 0 < A) (hs : Tendsto s atTop atTop) :
    ∀ᶠ ν in atTop, ∀ j z, z ∈ ball (0 : ℂ) 4 →
      ‖(p ν j).eval z‖ ≤ Real.exp ((5 * C + 2) * s ν) := by
  filter_upwards [h.jet_error, h.gauge_norm, hs.eventually_ge_atTop 0,
    hs.eventually_ge_atTop (Real.log 2)] with ν he hg hs0 hs2 j z hz
  have herr : ‖(p ν j).eval z - rescaledRepresentation f (t ν) (H ν) j z‖ ≤
      Real.exp (-A * s ν) := by
    simpa only [iteratedDeriv_zero] using he j 0 (by omega) z
      ((closedBall_subset_closedBall (by norm_num : (4 : ℝ) ≤ 16)) (ball_subset_closedBall hz))
  have hbound : ‖rescaledRepresentation f (t ν) (H ν) j z‖ ≤
      Real.exp ((5 * C + 1) * s ν) :=
    (norm_le_pi_norm _ j).trans ((norm_le_euclideanNorm _).trans
      (hg z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 32)) hz)))
  have hexp : Real.exp (-A * s ν) ≤ Real.exp ((5 * C + 1) * s ν) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp (s ν) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hs2
  calc
    ‖(p ν j).eval z‖ = ‖rescaledRepresentation f (t ν) (H ν) j z +
        ((p ν j).eval z - rescaledRepresentation f (t ν) (H ν) j z)‖ := by congr 1; abel
    _ ≤ ‖rescaledRepresentation f (t ν) (H ν) j z‖ +
        ‖(p ν j).eval z - rescaledRepresentation f (t ν) (H ν) j z‖ := norm_add_le _ _
    _ ≤ Real.exp ((5 * C + 1) * s ν) + Real.exp (-A * s ν) := add_le_add hbound herr
    _ ≤ Real.exp ((5 * C + 1) * s ν) * 2 := by linarith
    _ ≤ Real.exp ((5 * C + 1) * s ν) * Real.exp (s ν) :=
      mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le
    _ = Real.exp ((5 * C + 2) * s ν) := by rw [← Real.exp_add]; congr 1; ring

end ModifiedCartan
#print axioms ModifiedCartan.PolynomialReplacementData.polynomial_coordinate_bound
