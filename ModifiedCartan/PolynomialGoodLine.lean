import ModifiedCartan.GoodLineSelection
import ModifiedCartan.LogNormLineEstimate
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Actual normalized polynomial log-modulus error, used for `thm:A` (b). -/
def polynomialLogError (P : Polynomial ℂ) (s : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  s⁻¹ * Real.log ‖P.eval z‖ - u z

/-- Actual normalized logarithmic derivative error, used for `thm:A` (b). -/
def polynomialLogGradientError (P : Polynomial ℂ) (s : ℝ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  P.derivative.eval z / ((s : ℂ) * P.eval z) - g z

/-- An actual zero-free horizontal line with uniform log-modulus error bounded
by the two planar error integrals. This proves the good-line construction rather
than assuming a uniform convergence or an exceptional-disk theorem. -/
theorem polynomial_exists_good_horizontal_line (P : Polynomial ℂ) (hP : P ≠ 0)
    {u : ℂ → ℝ} {g : ℂ → ℂ} {s a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hu : ∀ y ∈ Icc c d, ∀ x ∈ Icc a b,
      HasDerivAt (fun t : ℝ => u (⟨t, y⟩ : ℂ)) (g (⟨x, y⟩ : ℂ)).re x)
    (hE : Integrable (fun v : ℝ × ℝ => |polynomialLogError P s u (⟨v.1, v.2⟩ : ℂ)|)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hG : Integrable (fun v : ℝ × ℝ => ‖polynomialLogGradientError P s g (⟨v.1, v.2⟩ : ℂ)‖)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    ∃ y ∈ Icc c d, (∀ x : ℝ, P.eval (⟨x, y⟩ : ℂ) ≠ 0) ∧
      ∀ x ∈ Icc a b, |polynomialLogError P s u (⟨x, y⟩ : ℂ)| ≤
        ((∫ v : ℝ × ℝ, |polynomialLogError P s u (⟨v.1, v.2⟩ : ℂ)|
          ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) / (b - a) +
         ∫ v : ℝ × ℝ, ‖polynomialLogGradientError P s g (⟨v.1, v.2⟩ : ℂ)‖
          ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) / (d - c) := by
  let E : ℝ × ℝ → ℝ := fun v => |polynomialLogError P s u (⟨v.1, v.2⟩ : ℂ)|
  let G : ℝ × ℝ → ℝ := fun v => ‖polynomialLogGradientError P s g (⟨v.1, v.2⟩ : ℂ)‖
  let W : ℝ × ℝ → ℝ := fun v => E v / (b - a) + G v
  have hW : Integrable W ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) :=
    (hE.div_const (b - a)).add hG
  have hside : ∀ᵐ y ∂volume.restrict (Icc c d),
      (∀ x : ℝ, P.eval (⟨x, y⟩ : ℂ) ≠ 0) ∧
      IntegrableOn (fun x => E (x, y)) (Icc a b) ∧
      IntegrableOn (fun x => G (x, y)) (Icc a b) := by
    filter_upwards [ae_restrict_of_ae (polynomial_horizontal_zero_free_ae P hP),
      hE.prod_left_ae, hG.prod_left_ae] with y hy he hg
    exact ⟨hy, he, hg⟩
  obtain ⟨y, hy, hgood, _, hb⟩ := exists_good_horizontal_slice hcd hW hside
  have hi : (∫ x in Icc a b, W (x, y)) =
      (∫ x in Icc a b, E (x, y)) / (b - a) + ∫ x in Icc a b, G (x, y) := by
    exact (integral_add (hgood.2.1.div_const (b - a)) hgood.2.2).trans
      (by rw [integral_div])
  have htotal : (∫ v, W v ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) =
      (∫ v, E v ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) / (b - a) +
        ∫ v, G v ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) := by
    exact (integral_add (hE.div_const (b - a)) hG).trans (by rw [integral_div])
  rw [hi, htotal] at hb
  refine ⟨y, hy, hgood.1, ?_⟩
  intro x hx
  have hd (t : ℝ) (_ht : t ∈ Icc a b) :
      HasDerivAt (fun v : ℝ => P.eval (⟨v, y⟩ : ℂ)) (P.derivative.eval (⟨t, y⟩ : ℂ)) t := by
    simpa only [one_mul] using complex_hasDerivAt_comp_real_path
      (γ := fun v : ℝ => (⟨v, y⟩ : ℂ)) (t := t)
      (P.hasDerivAt (⟨t, y⟩ : ℂ)) (hasDerivAt_horizontal_complex t y)
  have hgi : IntervalIntegrable (fun t => G (t, y)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hgood.2.2
  have hh := scaled_log_norm_path_error_le (s := s) hab hd
    (fun t _ => hgood.1 t) (hu y hy) hgi hx
  have he : |polynomialLogError P s u (⟨x, y⟩ : ℂ)| ≤
      (∫ x in Icc a b, E (x, y)) / (b - a) + ∫ x in Icc a b, G (x, y) := by
    simpa only [polynomialLogError, polynomialLogGradientError, E, G,
      intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc] using hh
  exact he.trans hb

end
end ModifiedCartan
#print axioms ModifiedCartan.polynomial_exists_good_horizontal_line
