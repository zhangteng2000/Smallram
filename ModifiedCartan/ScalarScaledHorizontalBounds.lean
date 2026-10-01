import ModifiedCartan.ScalarScaledLines

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Transfer actual horizontal bounds through varying ratios in [1,2], while
weakening the normalization scale by its proved pointwise comparison. -/
theorem scalar_horizontal_line_scale_eventually
    {f : Curve 1} {r s t c ε y : ℕ → ℝ} {a : ℕ → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hs : Tendsto s atTop atTop)
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) (hst : ∀ᶠ ν in atTop, s ν ≤ t ν)
    (hH : ∀ᶠ ν in atTop, y ν ∈ Icc ((a ν).im - ε ν) ((a ν).im + ε ν) ∧
      ∀ x ∈ Icc ((a ν).re - ε ν) ((a ν).re + ε ν),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨x, y ν⟩ : ℂ)) ≤ Real.exp (-δ * t ν)) :
    ∀ᶠ ν in atTop,
      (c ν)⁻¹ * y ν ∈ Icc
        (((((c ν)⁻¹ : ℝ) : ℂ) * a ν).im - (c ν)⁻¹ * ε ν)
        (((((c ν)⁻¹ : ℝ) : ℂ) * a ν).im + (c ν)⁻¹ * ε ν) ∧
      ∀ x ∈ Icc (((((c ν)⁻¹ : ℝ) : ℂ) * a ν).re - (c ν)⁻¹ * ε ν)
          (((((c ν)⁻¹ : ℝ) : ℂ) * a ν).re + (c ν)⁻¹ * ε ν),
        (c ν * r ν) * scalarSphericalSpeed f.coord
          (((c ν * r ν : ℝ) : ℂ) * (⟨x, (c ν)⁻¹ * y ν⟩ : ℂ)) ≤ Real.exp (-(δ / 2) * s ν) := by
  filter_upwards [hH, hst, constant_mul_exp_neg_le_half_eventually hs hδ
    (by norm_num : (0 : ℝ) ≤ 2)] with ν hHν hstν habsorb
  have hmono : Real.exp (-δ * t ν) ≤ Real.exp (-δ * s ν) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hstν (neg_nonpos.mpr hδ.le))
  exact scalar_horizontal_line_scaled_radius f (lt_of_lt_of_le zero_lt_one (hc ν).1)
    hHν.1 (fun x hx => (hHν.2 x hx).trans hmono)
    ((mul_le_mul_of_nonneg_right (hc ν).2 (Real.exp_pos _).le).trans habsorb)

end ModifiedCartan
#print axioms ModifiedCartan.scalar_horizontal_line_scale_eventually