import ModifiedCartan.PolynomialGoodLineLimit

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem polynomial_vertical_zero_free_ae (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∀ᵐ x : ℝ, ∀ y : ℝ, P.eval (⟨x, y⟩ : ℂ) ≠ 0 := by
  have hz : {z : ℂ | P.eval z = 0}.Finite := Polynomial.finite_setOfPred_isRoot hP
  let N : Set ℝ := Complex.re '' {z : ℂ | P.eval z = 0}
  have hN : volume N = 0 := (hz.image Complex.re).measure_zero volume
  have he : ∀ᵐ x : ℝ, x ∉ N := by
    apply ae_iff.mpr
    simpa using hN
  filter_upwards [he] with x hx
  intro y hy
  exact hx ⟨(⟨x, y⟩ : ℂ), hy, rfl⟩

theorem hasDerivAt_vertical_complex (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (⟨x, t⟩ : ℂ)) Complex.I y := by
  have hd := ((hasDerivAt_id y).ofReal_comp.mul_const Complex.I).const_add (x : ℂ)
  have he : (fun t : ℝ => (⟨x, t⟩ : ℂ)) = (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) := by
    funext t
    exact (Complex.re_add_im (⟨x, t⟩ : ℂ)).symm
  rw [he]
  simpa only [id_eq, Complex.ofReal_one, one_mul] using! hd

theorem norm_I_logGradient_error (a b g : ℂ) :
    ‖Complex.I * a / b - Complex.I * g‖ = ‖a / b - g‖ := by
  rw [mul_div_assoc, ← mul_sub, norm_mul, Complex.norm_I, one_mul]

/-- Constructed vertical counterpart of the horizontal good-line estimate.
Here [a,b] is the vertical interval and [c,d] the horizontal interval. -/
theorem polynomial_exists_good_vertical_line (P : Polynomial ℂ) (hP : P ≠ 0)
    {u : ℂ → ℝ} {g : ℂ → ℂ} {s a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hu : ∀ x ∈ Icc c d, ∀ y ∈ Icc a b,
      HasDerivAt (fun t : ℝ => u (⟨x, t⟩ : ℂ)) (Complex.I * g (⟨x, y⟩ : ℂ)).re y)
    (hE : Integrable (fun v : ℝ × ℝ => |polynomialLogError P s u (⟨v.2, v.1⟩ : ℂ)|)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hG : Integrable (fun v : ℝ × ℝ => ‖polynomialLogGradientError P s g (⟨v.2, v.1⟩ : ℂ)‖)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    ∃ x ∈ Icc c d, (∀ y : ℝ, P.eval (⟨x, y⟩ : ℂ) ≠ 0) ∧
      ∀ y ∈ Icc a b, |polynomialLogError P s u (⟨x, y⟩ : ℂ)| ≤
        ((∫ v : ℝ × ℝ, |polynomialLogError P s u (⟨v.2, v.1⟩ : ℂ)|
          ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) / (b - a) +
         ∫ v : ℝ × ℝ, ‖polynomialLogGradientError P s g (⟨v.2, v.1⟩ : ℂ)‖
          ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) / (d - c) := by
  let E : ℝ × ℝ → ℝ := fun v => |polynomialLogError P s u (⟨v.2, v.1⟩ : ℂ)|
  let G : ℝ × ℝ → ℝ := fun v => ‖polynomialLogGradientError P s g (⟨v.2, v.1⟩ : ℂ)‖
  let W : ℝ × ℝ → ℝ := fun v => E v / (b - a) + G v
  have hW : Integrable W ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) :=
    (hE.div_const (b - a)).add hG
  have hside : ∀ᵐ x ∂volume.restrict (Icc c d),
      (∀ y : ℝ, P.eval (⟨x, y⟩ : ℂ) ≠ 0) ∧
      IntegrableOn (fun y => E (y, x)) (Icc a b) ∧
      IntegrableOn (fun y => G (y, x)) (Icc a b) := by
    filter_upwards [ae_restrict_of_ae (polynomial_vertical_zero_free_ae P hP),
      hE.prod_left_ae, hG.prod_left_ae] with x hx he hg
    exact ⟨hx, he, hg⟩
  obtain ⟨x, hx, hgood, _, hb⟩ := exists_good_horizontal_slice hcd hW hside
  have hi : (∫ y in Icc a b, W (y, x)) =
      (∫ y in Icc a b, E (y, x)) / (b - a) + ∫ y in Icc a b, G (y, x) := by
    exact (integral_add (hgood.2.1.div_const (b - a)) hgood.2.2).trans
      (by rw [integral_div])
  have htotal : (∫ v, W v ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) =
      (∫ v, E v ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) / (b - a) +
        ∫ v, G v ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) := by
    exact (integral_add (hE.div_const (b - a)) hG).trans (by rw [integral_div])
  rw [hi, htotal] at hb
  refine ⟨x, hx, hgood.1, ?_⟩
  intro y hy
  have hd (t : ℝ) (_ht : t ∈ Icc a b) :
      HasDerivAt (fun v : ℝ => P.eval (⟨x, v⟩ : ℂ))
        (Complex.I * P.derivative.eval (⟨x, t⟩ : ℂ)) t := by
    exact complex_hasDerivAt_comp_real_path
      (γ := fun v : ℝ => (⟨x, v⟩ : ℂ)) (t := t)
      (P.hasDerivAt (⟨x, t⟩ : ℂ)) (hasDerivAt_vertical_complex x t)
  have hgi : IntervalIntegrable (fun t => G (t, x)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hgood.2.2
  have hgrad : IntervalIntegrable (fun t =>
      ‖Complex.I * P.derivative.eval (⟨x, t⟩ : ℂ) / ((s : ℂ) * P.eval (⟨x, t⟩ : ℂ)) -
        Complex.I * g (⟨x, t⟩ : ℂ)‖) volume a b := by
    simpa only [norm_I_logGradient_error, G, polynomialLogGradientError] using hgi
  have hh := scaled_log_norm_path_error_le (s := s) hab hd
    (fun t _ => hgood.1 t) (hu x hx) hgrad hy
  have he : |polynomialLogError P s u (⟨x, y⟩ : ℂ)| ≤
      (∫ y in Icc a b, E (y, x)) / (b - a) + ∫ y in Icc a b, G (y, x) := by
    simpa only [polynomialLogError, polynomialLogGradientError, E, G,
      norm_I_logGradient_error,
      intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc] using hh
  exact he.trans hb

theorem LocalLpConvergence.rectangle_integral_norm_sub_swapped
    {E : Type*} [NormedAddCommGroup E] {F : ℕ → ℂ → E} {u : ℂ → E}
    {U : Set ℂ} (h : LocalLpConvergence 1 U F u)
    {a b c d : ℝ} (hK : complexClosedRectangle c d a b ⊆ U) :
    (∀ n, Integrable (fun v : ℝ × ℝ => ‖F n (⟨v.2, v.1⟩ : ℂ) - u (⟨v.2, v.1⟩ : ℂ)‖)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) ∧
    Tendsto (fun n => ∫ v : ℝ × ℝ, ‖F n (⟨v.2, v.1⟩ : ℂ) - u (⟨v.2, v.1⟩ : ℂ)‖
      ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) atTop (𝓝 0) := by
  have hh := h.rectangle_integral_norm_sub hK
  refine ⟨fun n => (hh.1 n).swap, ?_⟩
  apply hh.2.congr
  intro n
  exact (integral_prod_swap
    (fun v : ℝ × ℝ => ‖F n (⟨v.1, v.2⟩ : ℂ) - u (⟨v.1, v.2⟩ : ℂ)‖)).symm

/-- Actual local log limits also construct zero-free vertical good lines.
The parameter intervals follow the convention of the preceding estimate. -/
theorem LocalLpConvergence.polynomial_good_vertical_lines
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {P : ℕ → Polynomial ℂ} (hP : ∀ n, P n ≠ 0)
    {s : ℕ → ℝ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hlog : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖(P n).eval z‖) u)
    (hs : Tendsto s atTop atTop) (hg : HasWeakComplexGradient U u g)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hK : complexClosedRectangle c d a b ⊆ U)
    (hu : ∀ x ∈ Icc c d, ∀ y ∈ Icc a b,
      HasDerivAt (fun t : ℝ => u (⟨x, t⟩ : ℂ)) (Complex.I * g (⟨x, y⟩ : ℂ)).re y)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ x ∈ Icc c d,
      (∀ y : ℝ, (P n).eval (⟨x, y⟩ : ℂ) ≠ 0) ∧
      ∀ y ∈ Icc a b, |polynomialLogError (P n) (s n) u (⟨x, y⟩ : ℂ)| < ε := by
  have hUne : U.Nonempty := ⟨(⟨c, a⟩ : ℂ), hK ⟨⟨le_rfl, hcd.le⟩, ⟨le_rfl, hab.le⟩⟩⟩
  have hgrad := hlog.polynomial_logDerivative hU hUc hUne hP hs hg
  have hEr := hlog.rectangle_integral_norm_sub_swapped hK
  have hGr := hgrad.rectangle_integral_norm_sub_swapped hK
  have hE : (∀ n, Integrable (fun v : ℝ × ℝ => |polynomialLogError (P n) (s n) u (⟨v.2, v.1⟩ : ℂ)|)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) ∧
      Tendsto (fun n => ∫ v : ℝ × ℝ, |polynomialLogError (P n) (s n) u (⟨v.2, v.1⟩ : ℂ)|
        ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) atTop (𝓝 0) := by
    simpa only [polynomialLogError, Real.norm_eq_abs] using hEr
  have hG : (∀ n, Integrable (fun v : ℝ × ℝ => ‖polynomialLogGradientError (P n) (s n) g (⟨v.2, v.1⟩ : ℂ)‖)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) ∧
      Tendsto (fun n => ∫ v : ℝ × ℝ, ‖polynomialLogGradientError (P n) (s n) g (⟨v.2, v.1⟩ : ℂ)‖
        ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) atTop (𝓝 0) := by
    exact hGr
  have hlim := ((hE.2.div_const (b - a)).add hG.2).div_const (d - c)
  simp only [zero_div, zero_add] at hlim
  filter_upwards [hlim.eventually_lt_const hε] with n hn
  obtain ⟨x, hx, hz, hb⟩ := polynomial_exists_good_vertical_line (P n) (hP n)
    hab hcd hu (hE.1 n) (hG.1 n)
  exact ⟨x, hx, hz, fun y hy => (hb y hy).trans_lt hn⟩

theorem hasDerivAt_vertical_of_differentiableAt
    {u : ℂ → ℝ} {x y : ℝ} (hu : DifferentiableAt ℝ u (⟨x, y⟩ : ℂ)) :
    HasDerivAt (fun t : ℝ => u (⟨x, t⟩ : ℂ))
      (Complex.I * classicalComplexGradient u (⟨x, y⟩ : ℂ)).re y := by
  have he : (Complex.I * classicalComplexGradient u (⟨x, y⟩ : ℂ)).re =
      fderiv ℝ u (⟨x, y⟩ : ℂ) Complex.I := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      classicalComplexGradient_neg_im]
  rw [he]
  exact hu.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_vertical_complex x y)

end ModifiedCartan
#print axioms ModifiedCartan.polynomial_exists_good_vertical_line
#print axioms ModifiedCartan.LocalLpConvergence.polynomial_good_vertical_lines
