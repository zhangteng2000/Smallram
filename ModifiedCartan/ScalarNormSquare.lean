import ModifiedCartan.ScalarNormLocalAbsolute
import ModifiedCartan.SubsequenceRatios

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The absolute real part of a complex square root is determined by the
square itself. This avoids any choice of a branch in the scalar norm profile. -/
theorem re_sq_eq_norm_add_re_sq_half (b : ℂ) :
    b.re ^ 2 = (‖b ^ 2‖ + (b ^ 2).re) / 2 := by
  rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re]
  ring

/-- Branch-independent pointwise formula for the actual scalar norm limit. -/
theorem ArbitraryRadiusLimitData.scalar_norm_square
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2) :
    (d.U a).toReal ^ 2 =
      (‖-(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)‖ +
        (-(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)).re) / 2 := by
  obtain ⟨b, hb, hU⟩ := d.scalar_norm_value_root hρ ha ha2
  rw [hU, sq_abs, ← hb]
  exact re_sq_eq_norm_add_re_sq_half b

/-- The scalar canonical limit coefficient cannot vanish identically, since
the actual norm limit has circle average one. -/
theorem ArbitraryRadiusLimitData.scalar_coefficient_ne_zero
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) : d.coefficient 0 ≠ 0 := by
  intro hzero
  have hpoint (a : ℂ) (ha : ‖a‖ = 1) : (d.U a).toReal = 0 := by
    have ha0 : a ≠ 0 := by intro he; rw [he, norm_zero] at ha; norm_num at ha
    have ha2 : ‖a‖ < 2 := by rw [ha]; norm_num
    obtain ⟨b, hb, hU⟩ := d.scalar_norm_value_root hρ ha0 ha2
    have hb0 : b = 0 := by
      have hz : b ^ 2 = 0 := by simpa only [hzero, Pi.zero_apply, zero_mul, neg_zero] using hb
      exact eq_zero_of_pow_eq_zero hz
    simpa only [hb0, Complex.zero_re, abs_zero] using hU
  have hmean : Real.circleAverage (fun a => (d.U a).toReal) 0 1 = 0 := by
    calc
      _ = Real.circleAverage (fun _ : ℂ => (0 : ℝ)) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro a ha
        exact hpoint a (by simpa only [mem_sphere, dist_zero_right, abs_one] using ha)
      _ = 0 := Real.circleAverage_const _ _ _
  have hone := d.circleAverage_one (lt_of_lt_of_le zero_lt_one hρ) hr
  linarith

/-- The actual nonzero coefficient is a single monomial. In particular its
integer degree supplies the half-integer scalar order independently of choices. -/
theorem ArbitraryRadiusLimitData.scalar_coefficient_monomial_nonzero
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) :
    ∃ (k : ℕ) (c : ℂ), c ≠ 0 ∧ ρ = ((k : ℝ) + 2) / 2 ∧
      d.coefficient 0 = fun z => c * z ^ k := by
  have hn := d.scalar_coefficient_ne_zero hρ hr
  have hm := d.coefficient_monomial (0 : Fin 1)
  rcases hm with ⟨k, hk, c, hc⟩ | ⟨_, hz⟩
  · refine ⟨k, c, ?_, ?_, hc⟩
    · intro hz
      apply hn
      rw [hc, hz]
      ext z
      simp
    · norm_num only [Fin.val_zero, Nat.sub_zero, Nat.cast_add, Nat.cast_one] at hk
      linarith
  · exact (hn hz).elim

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_square
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_coefficient_monomial_nonzero

