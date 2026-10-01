import ModifiedCartan.ScalarComparableFixedTarget
import ModifiedCartan.ScalarComparableHorizontalLines

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The line choices and their convergence to the fixed target are both
constructed from the original curve at any sequence of comparable radii. -/
theorem scalar_comparable_peaks_have_fixed_target
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
    (q : ScalarDyadicPeakTargetData f a ρ)
    (hqRad : ∀ z : ℂ, ‖z‖ = 1 → ∀ t ∈ Icc (1 / 2 : ℝ) 1,
      closedBall ((t : ℂ) * z) (4 * q.width) ⊆ scalarFullSector z ρ) :
    ∃ δ > 0, ∃ y : ℕ → ℝ, ∃ η > 0, ∀ᶠ ν in atTop,
      let b := scalarComparablePeakCenter f m ((2 : ℝ) ^ n ν) (c ν) (a (n ν))
      (y ν ∈ Icc (b.im - q.width) (b.im + q.width) ∧
        ∀ t ∈ Icc (b.re - q.width) (b.re + q.width),
          (c ν * (2 : ℝ) ^ n ν) * scalarSphericalSpeed f.coord
            (((c ν * (2 : ℝ) ^ n ν : ℝ) : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤
              Real.exp (-δ * characteristic f (c ν * (2 : ℝ) ^ n ν))) ∧
      ‖scalarCurveSphere f (((c ν * (2 : ℝ) ^ n ν : ℝ) : ℂ) *
          (⟨b.re - q.width, y ν⟩ : ℂ)) - scalarSphereValue q.target‖ ≤
        Real.exp (-η * characteristic f (c ν * (2 : ℝ) ^ n ν)) := by
  obtain ⟨δ, hδ, y, hH⟩ := scalar_comparable_peaks_have_horizontal_lines
    f hlin htrans hsmall hρ hl hu hm ha hpeak hn hc q.width_pos
    (fun z hz => (q.sector_disks z hz).1)
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hb := scalarComparablePeakCenter_difference_tendsto_zero f hlin htrans hsmall
    hρ hl hu hm (hpow.comp hn) hc (fun ν => ha (n ν))
  obtain ⟨η, hη, hclose⟩ := scalar_comparable_anchor_fixed_target
    f hlin htrans hsmall hρ hl hu hm ha hpeak hn hc hb q hqRad hδ hH
  exact ⟨δ, hδ, y, η, hη, hH.and hclose⟩

end ModifiedCartan
#print axioms ModifiedCartan.scalar_comparable_peaks_have_fixed_target
