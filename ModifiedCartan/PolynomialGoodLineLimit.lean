import ModifiedCartan.ComplexRectangleIntegral
import ModifiedCartan.PolynomialGoodLine
import ModifiedCartan.FirstLogDerivLimit

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem polynomial_exists_ne_zero_on_open (P : Polynomial ℂ) (hP : P ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) : ∃ z ∈ U, P.eval z ≠ 0 := by
  have hglobal : ∃ z : ℂ, P.eval z ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hP (Polynomial.zero_of_eval_zero P hn)
  obtain ⟨c, hc⟩ := hUne
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hc
  have hA : AnalyticOnNhd ℂ (fun z => P.eval z) univ := AnalyticOnNhd.eval_polynomial P
  obtain ⟨b, hb, hbn⟩ := analytic_exists_ne_zero_on_ball isPreconnected_univ hA
    (by obtain ⟨z, hz⟩ := hglobal; exact ⟨z, mem_univ z, hz⟩)
    hε (subset_univ (ball c ε))
  exact ⟨b, hεU hb, hbn⟩

/-- Actual local log convergence supplies the planar derivative convergence
needed to construct good lines; there is no derivative-convergence premise. -/
theorem LocalLpConvergence.polynomial_logDerivative
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {P : ℕ → Polynomial ℂ} (hP : ∀ n, P n ≠ 0)
    {s : ℕ → ℝ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hlog : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖(P n).eval z‖) u)
    (hs : Tendsto s atTop atTop) (hg : HasWeakComplexGradient U u g) :
    LocalLpConvergence 1 U
      (fun n z => (P n).derivative.eval z / ((s n : ℂ) * (P n).eval z)) g := by
  have hA (n : ℕ) : AnalyticOnNhd ℂ (fun z => (P n).eval z) U :=
    (AnalyticOnNhd.eval_polynomial (P n)).mono (subset_univ U)
  have hN := fun n => polynomial_exists_ne_zero_on_open (P n) (hP n) hU hUne
  have hlim := hlog.logDeriv_localLpConvergence hU hUc hA hN hs hg
    (p := 1) le_rfl (by norm_num)
  simp only [ENNReal.ofReal_one] at hlim
  apply hlim.congr_ae _ EventuallyEq.rfl
  intro n
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [logDeriv_apply, (P n).hasDerivAt z |>.deriv]
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Uniform convergence on constructed zero-free horizontal lines follows from
actual local L1 log limits and the proved logarithmic derivative theorem.
Auxiliary to LaTeX `thm:A` (b), for rectangles in a smooth part of the limit. -/
theorem LocalLpConvergence.polynomial_good_horizontal_lines
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {P : ℕ → Polynomial ℂ} (hP : ∀ n, P n ≠ 0)
    {s : ℕ → ℝ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hlog : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖(P n).eval z‖) u)
    (hs : Tendsto s atTop atTop) (hg : HasWeakComplexGradient U u g)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hK : complexClosedRectangle a b c d ⊆ U)
    (hu : ∀ y ∈ Icc c d, ∀ x ∈ Icc a b,
      HasDerivAt (fun t : ℝ => u (⟨t, y⟩ : ℂ)) (g (⟨x, y⟩ : ℂ)).re x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ y ∈ Icc c d,
      (∀ x : ℝ, (P n).eval (⟨x, y⟩ : ℂ) ≠ 0) ∧
      ∀ x ∈ Icc a b, |polynomialLogError (P n) (s n) u (⟨x, y⟩ : ℂ)| < ε := by
  have hUne : U.Nonempty := ⟨(⟨a, c⟩ : ℂ), hK ⟨⟨le_rfl, hab.le⟩, ⟨le_rfl, hcd.le⟩⟩⟩
  have hgrad := hlog.polynomial_logDerivative hU hUc hUne hP hs hg
  have hEr := hlog.rectangle_integral_norm_sub hK
  have hGr := hgrad.rectangle_integral_norm_sub hK
  have hE : (∀ n, Integrable (fun v : ℝ × ℝ => |polynomialLogError (P n) (s n) u (⟨v.1, v.2⟩ : ℂ)|)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) ∧
      Tendsto (fun n => ∫ v : ℝ × ℝ, |polynomialLogError (P n) (s n) u (⟨v.1, v.2⟩ : ℂ)|
        ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) atTop (𝓝 0) := by
    simpa only [polynomialLogError, Real.norm_eq_abs] using hEr
  have hG : (∀ n, Integrable (fun v : ℝ × ℝ => ‖polynomialLogGradientError (P n) (s n) g (⟨v.1, v.2⟩ : ℂ)‖)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) ∧
      Tendsto (fun n => ∫ v : ℝ × ℝ, ‖polynomialLogGradientError (P n) (s n) g (⟨v.1, v.2⟩ : ℂ)‖
        ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) atTop (𝓝 0) := by
    exact hGr
  have hlim := ((hE.2.div_const (b - a)).add hG.2).div_const (d - c)
  simp only [zero_div, zero_add] at hlim
  filter_upwards [hlim.eventually_lt_const hε] with n hn
  obtain ⟨y, hy, hz, hb⟩ := polynomial_exists_good_horizontal_line (P n) (hP n)
    hab hcd hu (hE.1 n) (hG.1 n)
  exact ⟨y, hy, hz, fun x hx => (hb x hx).trans_lt hn⟩

end ModifiedCartan
#print axioms ModifiedCartan.LocalLpConvergence.polynomial_logDerivative
#print axioms ModifiedCartan.LocalLpConvergence.polynomial_good_horizontal_lines

