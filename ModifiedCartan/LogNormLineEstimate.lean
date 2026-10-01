import ModifiedCartan.GoodLineIntegral
import ModifiedCartan.LogNormPathDerivative

open scoped Topology
open Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Uniform log-modulus error along a zero-free line, controlled by the actual
function and logarithmic-derivative integrals. Auxiliary to LaTeX `thm:A` (b). -/
theorem scaled_log_norm_path_error_le {F F' g : ℝ → ℂ} {u : ℝ → ℝ}
    {a b s : ℝ} (hab : a < b)
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (F' t) t)
    (hne : ∀ t ∈ Icc a b, F t ≠ 0)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (g t).re t)
    (hG : IntervalIntegrable (fun t => ‖F' t / ((s : ℂ) * F t) - g t‖) volume a b)
    {x : ℝ} (hx : x ∈ Icc a b) :
    |s⁻¹ * Real.log ‖F x‖ - u x| ≤
      (∫ t in a..b, |s⁻¹ * Real.log ‖F t‖ - u t|) / (b - a) +
        ∫ t in a..b, ‖F' t / ((s : ℂ) * F t) - g t‖ := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun v => s⁻¹ * Real.log ‖F v‖ - u v)
        (F' t / ((s : ℂ) * F t) - g t).re t := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      hasDerivAt_scaled_log_norm_sub (s := s) (hF t ht) (hne t ht) (hu t ht)
  have hh := norm_le_integral_norm_add_derivative_bound hab hd hG
    (fun t _ => by simpa only [Real.norm_eq_abs] using
      Complex.abs_re_le_norm (F' t / ((s : ℂ) * F t) - g t)) hx
  simpa only [Real.norm_eq_abs] using hh

end ModifiedCartan
#print axioms ModifiedCartan.scaled_log_norm_path_error_le
