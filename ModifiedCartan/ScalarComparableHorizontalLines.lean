import ModifiedCartan.ScalarComparablePeaks
import ModifiedCartan.ScalarMovingLines

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual horizontal line choices at arbitrary comparable radii, with peaks
transported from the coherently numbered dyadic family. -/
theorem scalar_comparable_peaks_have_horizontal_lines
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {c : ℕ → ℝ}
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2)
    {ε : ℝ} (hε : 0 < ε)
    (hdisks : ∀ b : ℂ, ‖b‖ = 1 → closedBall b (4 * ε) ⊆ scalarFullSector b ρ) :
    ∃ δ > 0, ∃ y : ℕ → ℝ, ∀ᶠ ν in atTop,
      let b := scalarComparablePeakCenter f m ((2 : ℝ) ^ n ν) (c ν) (a (n ν))
      y ν ∈ Icc (b.im - ε) (b.im + ε) ∧
      ∀ t ∈ Icc (b.re - ε) (b.re + ε),
        (c ν * (2 : ℝ) ^ n ν) * scalarSphericalSpeed f.coord
          (((c ν * (2 : ℝ) ^ n ν : ℝ) : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤
            Real.exp (-δ * characteristic f (c ν * (2 : ℝ) ^ n ν)) := by
  have hm0 : m ≠ 0 := by intro hz; simp only [hz, Nat.cast_zero, zero_div] at hm; linarith
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hr : Tendsto (fun ν => c ν * (2 : ℝ) ^ n ν) atTop atTop := by
    apply tendsto_atTop_mono (fun ν => ?_) (hpow.comp hn)
    change (2 : ℝ) ^ n ν ≤ c ν * (2 : ℝ) ^ n ν
    have hh := mul_le_mul_of_nonneg_right (hc ν).1 (pow_pos (by norm_num : (0 : ℝ) < 2) (n ν)).le
    simpa only [one_mul] using hh
  let b : ℕ → ℂ := fun ν => scalarComparablePeakCenter f m ((2 : ℝ) ^ n ν) (c ν) (a (n ν))
  have hb (ν : ℕ) : ‖b ν‖ = 1 := scalarComparablePeakCenter_norm f m _ _ (ha (n ν))
  have hbpeak (ν : ℕ) : scalarPhaseCoefficient f m (c ν * (2 : ℝ) ^ n ν) * (b ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ) := scalarComparablePeakCenter_peak f hm0 _ _ (hpeak (n ν))
  obtain ⟨δ, hδ, hcross⟩ := scalar_phase_peak_moving_crosses f hlin htrans hsmall hρ hl hu hm
    hr hb hbpeak hε hdisks
  obtain ⟨y, hy⟩ := exists_moving_horizontal_lines hε hcross
  exact ⟨δ, hδ, y, hy⟩

end ModifiedCartan
#print axioms ModifiedCartan.scalar_comparable_peaks_have_horizontal_lines