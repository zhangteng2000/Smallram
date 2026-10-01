import ModifiedCartan.ScalarScaledHorizontalBounds
import ModifiedCartan.CharacteristicComparableBounds

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A good horizontal line at c*2^n, 1<=c<=2, expressed at the common larger
radius 2*2^n with normalization T(2^n). All transformations are exact. -/
theorem scalar_horizontal_line_at_dyadic_ceiling
    (f : Curve 1) (htrans : f.Transcendental)
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {c y : ℕ → ℝ} {b : ℕ → ℂ}
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) {ε δ : ℝ} (hδ : 0 < δ)
    (hH : ∀ᶠ ν in atTop, y ν ∈ Icc ((b ν).im - ε) ((b ν).im + ε) ∧
      ∀ t ∈ Icc ((b ν).re - ε) ((b ν).re + ε),
        (c ν * (2 : ℝ) ^ n ν) * scalarSphericalSpeed f.coord
          (((c ν * (2 : ℝ) ^ n ν : ℝ) : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤
            Real.exp (-δ * characteristic f (c ν * (2 : ℝ) ^ n ν))) :
    ∀ᶠ ν in atTop,
      (c ν / 2) * y ν ∈ Icc
        ((((c ν / 2 : ℝ) : ℂ) * b ν).im - (c ν / 2) * ε)
        ((((c ν / 2 : ℝ) : ℂ) * b ν).im + (c ν / 2) * ε) ∧
      ∀ t ∈ Icc ((((c ν / 2 : ℝ) : ℂ) * b ν).re - (c ν / 2) * ε)
          ((((c ν / 2 : ℝ) : ℂ) * b ν).re + (c ν / 2) * ε),
        (2 * (2 : ℝ) ^ n ν) * scalarSphericalSpeed f.coord
          (((2 * (2 : ℝ) ^ n ν : ℝ) : ℂ) * (⟨t, (c ν / 2) * y ν⟩ : ℂ)) ≤
            Real.exp (-(δ / 2) * characteristic f ((2 : ℝ) ^ n ν)) := by
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hs := (characteristic_tendsto_atTop_of_transcendental f htrans).comp (hpow.comp hn)
  have hst : ∀ᶠ ν in atTop,
      characteristic f ((2 : ℝ) ^ n ν) ≤ characteristic f (c ν * (2 : ℝ) ^ n ν) :=
    Eventually.of_forall (fun ν => (characteristic_comparable_mono f
      (pow_pos (by norm_num : (0 : ℝ) < 2) (n ν)) (hc ν)).1)
  have hh := scalar_horizontal_line_scale_eventually hδ hs
    (fun ν => two_div_mem_Icc_one_two (hc ν)) hst hH
  have he (ν : ℕ) : (2 / c ν) * (c ν * (2 : ℝ) ^ n ν) = 2 * (2 : ℝ) ^ n ν := by
    have hc0 : c ν ≠ 0 := (lt_of_lt_of_le zero_lt_one (hc ν).1).ne'
    field_simp
  simpa only [he, inv_div, Function.comp_def] using hh

end ModifiedCartan
#print axioms ModifiedCartan.scalar_horizontal_line_at_dyadic_ceiling