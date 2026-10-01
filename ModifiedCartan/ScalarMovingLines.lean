import ModifiedCartan.ScalarUniformPeakCrosses
import ModifiedCartan.ScalarExponentialBounds

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Choose actual horizontal lines from the constructed moving crosses. -/
theorem exists_moving_horizontal_lines {f : Curve 1} {r s : ℕ → ℝ} {a : ℕ → ℂ}
    {ε δ : ℝ} (hε : 0 < ε)
    (h : ∀ᶠ ν in atTop, ScalarGoodCross f (r ν) (s ν) δ (ComplexRect.box (a ν) ε ε hε hε)) :
    ∃ y : ℕ → ℝ, ∀ᶠ ν in atTop,
      y ν ∈ Icc ((a ν).im - ε) ((a ν).im + ε) ∧
      ∀ t ∈ Icc ((a ν).re - ε) ((a ν).re + ε),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤ Real.exp (-δ * s ν) := by
  classical
  let P : ℕ → ℝ → Prop := fun ν y =>
    y ∈ Icc ((a ν).im - ε) ((a ν).im + ε) ∧
    ∀ t ∈ Icc ((a ν).re - ε) ((a ν).re + ε),
      r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, y⟩ : ℂ)) ≤ Real.exp (-δ * s ν)
  have he (ν : ℕ) : ∃ y, (∃ z, P ν z) → P ν y := by
    by_cases hh : ∃ y, P ν y
    · obtain ⟨y, hy⟩ := hh
      exact ⟨y, fun _ => hy⟩
    · exact ⟨(a ν).im, fun hh' => (hh hh').elim⟩
  choose y hy using he
  refine ⟨y, ?_⟩
  filter_upwards [h] with ν hν
  obtain ⟨_, _, z, hz, hH, _⟩ := hν
  exact hy ν ⟨z, hz, hH⟩

/-- The same physical horizontal line expressed at double radius. -/
theorem scalar_horizontal_line_double_radius (f : Curve 1)
    {r s δ ε y : ℝ} {a : ℂ}
    (hy : y ∈ Icc (a.im - ε) (a.im + ε))
    (hH : ∀ t ∈ Icc (a.re - ε) (a.re + ε),
      r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨t, y⟩ : ℂ)) ≤ Real.exp (-δ * s))
    (habsorb : 2 * Real.exp (-δ * s) ≤ Real.exp (-(δ / 2) * s)) :
    y / 2 ∈ Icc (((1 / 2 : ℂ) * a).im - ε / 2) (((1 / 2 : ℂ) * a).im + ε / 2) ∧
    ∀ t ∈ Icc (((1 / 2 : ℂ) * a).re - ε / 2) (((1 / 2 : ℂ) * a).re + ε / 2),
      (2 * r) * scalarSphericalSpeed f.coord (((2 * r : ℝ) : ℂ) * (⟨t, y / 2⟩ : ℂ)) ≤
        Real.exp (-(δ / 2) * s) := by
  have hre : ((1 / 2 : ℂ) * a).re = a.re / 2 := by norm_num [Complex.mul_re]; ring
  have him : ((1 / 2 : ℂ) * a).im = a.im / 2 := by norm_num [Complex.mul_im]; ring
  rw [hre, him]
  refine ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
  intro t ht
  have h2t : 2 * t ∈ Icc (a.re - ε) (a.re + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have he : ((2 * r : ℝ) : ℂ) * (⟨t, y / 2⟩ : ℂ) =
      (r : ℂ) * (⟨2 * t, y⟩ : ℂ) := by
    apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] <;> ring
  rw [he, mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hH (2 * t) h2t) (by norm_num)).trans habsorb

/-- Anchor coordinates represent the same physical point at double radius. -/
theorem scalar_doubled_anchor_identity (r ε y : ℝ) (a : ℂ) :
    (((2 * r : ℝ) : ℂ) * (⟨((1 / 2 : ℂ) * a).re - ε / 2, y / 2⟩ : ℂ)) =
      (r : ℂ) * (⟨a.re - ε, y⟩ : ℂ) := by
  have hre : ((1 / 2 : ℂ) * a).re = a.re / 2 := by norm_num [Complex.mul_re]; ring
  rw [hre]
  apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] <;> ring

end ModifiedCartan
#print axioms ModifiedCartan.exists_moving_horizontal_lines
#print axioms ModifiedCartan.scalar_horizontal_line_double_radius