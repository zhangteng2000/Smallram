import ModifiedCartan.TwoPhaseForms

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Homogeneity eliminates the affine intercept in every local two-phase
form. Only the two real radii on either side of one are needed in the proof. -/
theorem HasTwoPhaseFormOn.homogeneous_at_one {F : ℂ → ℝ} {b : ℂ} {s : ℝ}
    (hs : 0 < s) (h : HasTwoPhaseFormOn F b 1 (ball 1 s))
    (hrad : ∀ t : ℝ, 0 < t → (t : ℂ) ∈ ball (1 : ℂ) s → F (t : ℂ) = t * F 1) :
    EqOn F (fun w => (b * w).re) (ball 1 s) ∨
    EqOn F (fun w => -(b * w).re) (ball 1 s) ∨
    EqOn F (fun w => |(b * w).re|) (ball 1 s) := by
  let ε := min s 1 / 2
  have hε : 0 < ε := half_pos (lt_min hs zero_lt_one)
  have hεs : ε < s := (half_lt_self (lt_min hs zero_lt_one)).trans_le (min_le_left _ _)
  have hε1 : ε < 1 := (half_lt_self (lt_min hs zero_lt_one)).trans_le (min_le_right _ _)
  have hm : ((1 - ε : ℝ) : ℂ) ∈ ball (1 : ℂ) s := by
    rw [mem_ball, dist_eq_norm]
    have he : ((1 - ε : ℝ) : ℂ) - 1 = ((-ε : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hε]
    exact hεs
  have hp : ((1 + ε : ℝ) : ℂ) ∈ ball (1 : ℂ) s := by
    rw [mem_ball, dist_eq_norm]
    have he : ((1 + ε : ℝ) : ℂ) - 1 = (ε : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    exact hεs
  have hmF := hrad (1 - ε) (by linarith) hm
  have hpF := hrad (1 + ε) (by linarith) hp
  have hLm : (b * (((1 - ε : ℝ) : ℂ) - 1)).re = -ε * b.re := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero, mul_zero, sub_zero]
    ring
  have hLp : (b * (((1 + ε : ℝ) : ℂ) - 1)).re = ε * b.re := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero, mul_zero, sub_zero]
    ring
  have hL (w : ℂ) : (b * (w - 1)).re = (b * w).re - b.re := by
    rw [mul_sub, Complex.sub_re, mul_one]
  rcases h with h | h | h
  · have hh := h hm
    dsimp only at hh
    rw [hmF, hLm] at hh
    have hv : F 1 = b.re := mul_left_cancel₀ hε.ne' (show ε * F 1 = ε * b.re by nlinarith [hh])
    left
    intro w hw
    calc
      F w = F 1 + (b * (w - 1)).re := h hw
      _ = (b * w).re := by rw [hv, hL]; ring
  · have hh := h hm
    dsimp only at hh
    rw [hmF, hLm] at hh
    have hv : F 1 = -b.re := mul_left_cancel₀ hε.ne' (show ε * F 1 = ε * -b.re by nlinarith [hh])
    right; left
    intro w hw
    calc
      F w = F 1 - (b * (w - 1)).re := h hw
      _ = -(b * w).re := by rw [hv, hL]; ring
  · have hh := h hm
    have hh' := h hp
    dsimp only at hh hh'
    rw [hmF, hLm, abs_mul, abs_neg, abs_of_pos hε] at hh
    rw [hpF, hLp, abs_mul, abs_of_pos hε] at hh'
    have hv₁ : F 1 = -|b.re| := mul_left_cancel₀ hε.ne'
      (show ε * F 1 = ε * -|b.re| by nlinarith [hh])
    have hv₂ : F 1 = |b.re| := mul_left_cancel₀ hε.ne'
      (show ε * F 1 = ε * |b.re| by nlinarith [hh'])
    have hv : F 1 = 0 := by linarith
    have hb : b.re = 0 := abs_eq_zero.mp (by linarith)
    right; right
    intro w hw
    calc
      F w = F 1 + |(b * (w - 1)).re| := h hw
      _ = |(b * w).re| := by rw [hv, hL, hb, sub_zero, zero_add]

end ModifiedCartan
#print axioms ModifiedCartan.HasTwoPhaseFormOn.homogeneous_at_one
