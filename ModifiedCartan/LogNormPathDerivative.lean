import ModifiedCartan.ScalarSphericalSpeed
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The real derivative of the logarithmic modulus on a nonvanishing path.
The branch of the complex logarithm is chosen locally and eliminated. -/
theorem hasDerivAt_log_norm_complex {F : ℝ → ℂ} {F' : ℂ} {x : ℝ}
    (hF : HasDerivAt F F' x) (hne : F x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖F t‖) (F' / F x).re x := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hne with hp | hn
  · have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hF.clog_real hp)
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.log_re] using! hd
  · have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hF.neg.clog_real hn)
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.log_re, norm_neg,
      Pi.neg_apply, neg_div_neg_eq] using! hd

theorem hasDerivAt_horizontal_complex (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (⟨t, y⟩ : ℂ)) (1 : ℂ) x := by
  have hd := (hasDerivAt_id x).ofReal_comp.add_const ((y : ℂ) * Complex.I)
  have he : (fun t : ℝ => (⟨t, y⟩ : ℂ)) = (fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) := by
    funext t
    exact (Complex.re_add_im (⟨t, y⟩ : ℂ)).symm
  rw [he]
  simpa only [id_eq, Complex.ofReal_one] using! hd

theorem hasDerivAt_log_norm_horizontal {F : ℂ → ℂ} {F' : ℂ} {x y : ℝ}
    (hF : HasDerivAt F F' (⟨x, y⟩ : ℂ)) (hne : F (⟨x, y⟩ : ℂ) ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖F (⟨t, y⟩ : ℂ)‖)
      (F' / F (⟨x, y⟩ : ℂ)).re x := by
  have hd := complex_hasDerivAt_comp_real_path (γ := fun t : ℝ => (⟨t, y⟩ : ℂ)) (t := x)
    hF (hasDerivAt_horizontal_complex x y)
  rw [one_mul] at hd
  exact hasDerivAt_log_norm_complex hd hne

theorem scaled_complex_quotient_re (s : ℝ) (a b : ℂ) :
    s⁻¹ * (a / b).re = (a / ((s : ℂ) * b)).re := by
  have he : a / ((s : ℂ) * b) = (s⁻¹ : ℝ) * (a / b) := by
    simp only [Complex.ofReal_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Exact derivative of the normalized log error, for a zero-free real path. -/
theorem hasDerivAt_scaled_log_norm_sub {F : ℝ → ℂ} {F' : ℂ}
    {u : ℝ → ℝ} {u' x s : ℝ} (hF : HasDerivAt F F' x) (hne : F x ≠ 0)
    (hu : HasDerivAt u u' x) :
    HasDerivAt (fun t => s⁻¹ * Real.log ‖F t‖ - u t)
      (F' / ((s : ℂ) * F x) - (u' : ℂ)).re x := by
  have hd := ((hasDerivAt_log_norm_complex hF hne).const_mul s⁻¹).sub hu
  simpa only [scaled_complex_quotient_re, Complex.sub_re, Complex.ofReal_re] using! hd

end ModifiedCartan
#print axioms ModifiedCartan.hasDerivAt_log_norm_complex
#print axioms ModifiedCartan.hasDerivAt_scaled_log_norm_sub

