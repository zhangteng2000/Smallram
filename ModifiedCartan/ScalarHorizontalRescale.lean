import ModifiedCartan.ScalarSharpLocalTargetLines

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Change from the distant dyadic coordinates to the actual comparable
radius. A fixed horizontal half-width and twice that vertical tolerance
work uniformly for all comparable multipliers. -/
theorem scalar_horizontal_target_rescale {F : ℂ → ℝ} {b c L ε y B : ℝ} {z : ℂ}
    (hc : c ∈ Icc (1 : ℝ) 2) (hL : 0 < L) (hε : 0 ≤ ε)
    (hy : y ∈ Icc ((((c / L : ℝ) : ℂ) * z).im - 2 * ε / L)
      ((((c / L : ℝ) : ℂ) * z).im + 2 * ε / L))
    (hline : ∀ t ∈ Icc ((((c / L : ℝ) : ℂ) * z).re - 2 * ε / L)
      ((((c / L : ℝ) : ℂ) * z).re + 2 * ε / L),
        F (((L * b : ℝ) : ℂ) * (⟨t, y⟩ : ℂ)) ≤ B) :
    y / (c / L) ∈ Icc (z.im - 2 * ε) (z.im + 2 * ε) ∧
      ∀ t ∈ Icc (z.re - ε) (z.re + ε),
        F (((c * b : ℝ) : ℂ) * (⟨t, y / (c / L)⟩ : ℂ)) ≤ B := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc.1
  have hτ : 0 < c / L := div_pos hcpos hL
  have hlower : 2 * ε / L ≤ (c / L) * (2 * ε) := by
    have hh := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc.1 hL.le)
      (show 0 ≤ 2 * ε by positivity)
    calc
      _ = (1 / L) * (2 * ε) := by ring
      _ ≤ _ := hh
  have hupper : (c / L) * ε ≤ 2 * ε / L := by
    have hh := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc.2 hL.le) hε
    calc
      _ ≤ (2 / L) * ε := hh
      _ = _ := by ring
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hy
  constructor
  · constructor
    · apply (le_div_iff₀ hτ).2
      nlinarith [hy.1]
    · apply (div_le_iff₀ hτ).2
      nlinarith [hy.2]
  · intro t ht
    have hmem : (c / L) * t ∈ Icc ((((c / L : ℝ) : ℂ) * z).re - 2 * ε / L)
        ((((c / L : ℝ) : ℂ) * z).re + 2 * ε / L) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      constructor <;> nlinarith [ht.1, ht.2]
    have hh := hline ((c / L) * t) hmem
    have he : (((L * b : ℝ) : ℂ) * (⟨(c / L) * t, y⟩ : ℂ)) =
        (((c * b : ℝ) : ℂ) * (⟨t, y / (c / L)⟩ : ℂ)) := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        field_simp
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        field_simp
    rwa [he] at hh

end ModifiedCartan
#print axioms ModifiedCartan.scalar_horizontal_target_rescale
