import ModifiedCartan.ScalarMovingLines

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The same physical horizontal segment at a larger positive radius.
All center, height and width changes are retained exactly. -/
theorem scalar_horizontal_line_scaled_radius (f : Curve 1)
    {r s δ ε y c : ℝ} {a : ℂ} (hc : 0 < c)
    (hy : y ∈ Icc (a.im - ε) (a.im + ε))
    (hH : ∀ t ∈ Icc (a.re - ε) (a.re + ε),
      r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨t, y⟩ : ℂ)) ≤ Real.exp (-δ * s))
    (habsorb : c * Real.exp (-δ * s) ≤ Real.exp (-(δ / 2) * s)) :
    c⁻¹ * y ∈ Icc ((((c⁻¹ : ℝ) : ℂ) * a).im - c⁻¹ * ε) ((((c⁻¹ : ℝ) : ℂ) * a).im + c⁻¹ * ε) ∧
    ∀ t ∈ Icc ((((c⁻¹ : ℝ) : ℂ) * a).re - c⁻¹ * ε) ((((c⁻¹ : ℝ) : ℂ) * a).re + c⁻¹ * ε),
      (c * r) * scalarSphericalSpeed f.coord (((c * r : ℝ) : ℂ) * (⟨t, c⁻¹ * y⟩ : ℂ)) ≤
        Real.exp (-(δ / 2) * s) := by
  have hre : (((c⁻¹ : ℝ) : ℂ) * a).re = c⁻¹ * a.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have him : (((c⁻¹ : ℝ) : ℂ) * a).im = c⁻¹ * a.im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [hre, him]
  constructor
  · simpa only [mul_sub, mul_add, mem_Icc] using And.intro
      (mul_le_mul_of_nonneg_left hy.1 (inv_pos.mpr hc).le)
      (mul_le_mul_of_nonneg_left hy.2 (inv_pos.mpr hc).le)
  · intro t ht
    have h2t : c * t ∈ Icc (a.re - ε) (a.re + ε) := by
      have h1 := mul_le_mul_of_nonneg_left ht.1 hc.le
      have h2 := mul_le_mul_of_nonneg_left ht.2 hc.le
      have hl : c * (c⁻¹ * a.re - c⁻¹ * ε) = a.re - ε := by field_simp
      have hu : c * (c⁻¹ * a.re + c⁻¹ * ε) = a.re + ε := by field_simp
      rw [hl] at h1
      rw [hu] at h2
      exact ⟨h1, h2⟩
    have he : ((c * r : ℝ) : ℂ) * (⟨t, c⁻¹ * y⟩ : ℂ) =
        (r : ℂ) * (⟨c * t, y⟩ : ℂ) := by
      apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] <;> field_simp <;> ring
    rw [he, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (hH (c * t) h2t) hc.le).trans habsorb

theorem scalar_scaled_anchor_identity {c : ℝ} (hc : c ≠ 0) (r ε y : ℝ) (a : ℂ) :
    (((c * r : ℝ) : ℂ) * (⟨(((c⁻¹ : ℝ) : ℂ) * a).re - c⁻¹ * ε, c⁻¹ * y⟩ : ℂ)) =
      (r : ℂ) * (⟨a.re - ε, y⟩ : ℂ) := by
  have hre : (((c⁻¹ : ℝ) : ℂ) * a).re = c⁻¹ * a.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]
  apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] <;> field_simp <;> ring

end ModifiedCartan
#print axioms ModifiedCartan.scalar_horizontal_line_scaled_radius
#print axioms ModifiedCartan.scalar_scaled_anchor_identity