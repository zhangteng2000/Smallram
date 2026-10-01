import ModifiedCartan.SecondOrderTaylorBound
import ModifiedCartan.QuadraticTrace

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The sum over four perpendicular directions has the Laplacian as its
quadratic term, with an explicit uniform error bound. -/
theorem exists_quarter_mean_upper_bound {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ →
      f (c + z) + f (c - z) + f (c + Complex.I * z) + f (c - Complex.I * z) - 4 * f c ≤
        ‖z‖ ^ 2 * (Laplacian.laplacian f c + 4 * ε) := by
  obtain ⟨δ, hδ, hd⟩ := exists_second_order_taylor_error_bound hf c hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hupper (w : ℂ) (hw : ‖w‖ < δ) :
      f (c + w) ≤ f c + fderiv ℝ f c w +
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) c w w + ε * ‖w‖ ^ 2 := by
    have h := hd w hw
    rw [Real.norm_eq_abs] at h
    have hh := (le_abs_self _).trans h
    linarith
  have h₁ := hupper z hz
  have h₂ := hupper (-z) (by simpa only [norm_neg] using hz)
  have h₃ := hupper (Complex.I * z) (by simpa only [norm_mul, Complex.norm_I, one_mul] using hz)
  have h₄ := hupper (-(Complex.I * z)) (by simpa only [norm_neg, norm_mul, Complex.norm_I, one_mul] using hz)
  simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg, norm_neg, norm_mul,
    Complex.norm_I, one_mul, ← sub_eq_add_neg] at h₂ h₃ h₄
  have htrace := second_derivative_quarter_turn f c z
  simp only [iteratedFDeriv_two_apply] at htrace
  nlinarith

end ModifiedCartan
#print axioms ModifiedCartan.exists_quarter_mean_upper_bound
