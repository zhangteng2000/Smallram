import ModifiedCartan.ScalarComparableLineTargets
import ModifiedCartan.ScalarDyadicDecomposition

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The coherent dyadic numbering extended to every real radius using its
exact dyadic decomposition and the actual phase correction. -/
noncomputable def scalarRadiusPeakCenter (f : Curve 1) (m : ℕ) (a : ℕ → ℂ) (r : ℝ) : ℂ :=
  scalarComparablePeakCenter f m ((2 : ℝ) ^ scalarDyadicIndex r)
    (scalarDyadicMultiplier r) (a (scalarDyadicIndex r))

theorem scalarRadiusPeakCenter_norm (f : Curve 1) (m : ℕ) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1) (r : ℝ) : ‖scalarRadiusPeakCenter f m a r‖ = 1 :=
  scalarComparablePeakCenter_norm f m _ _ (ha _)

theorem scalarRadiusPeakCenter_peak (f : Curve 1) {m : ℕ} (hm : m ≠ 0) {a : ℕ → ℂ}
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ)) (r : ℝ) :
    scalarPhaseCoefficient f m r * (scalarRadiusPeakCenter f m a r) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ) := by
  have hh := scalarComparablePeakCenter_peak f hm ((2 : ℝ) ^ scalarDyadicIndex r)
    (scalarDyadicMultiplier r) (hpeak (scalarDyadicIndex r))
  simpa only [scalarDyadicMultiplier_factor, scalarRadiusPeakCenter] using hh

/-- Every escaping radius sequence has actual good lines converging to the
same fixed target, with a positive exponential rate on its own characteristic.
There is no convergence assumption on the rotating phase or the radii ratios. -/
theorem scalar_arbitrary_radii_have_fixed_target
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (q : ScalarDyadicPeakTargetData f a ρ)
    (hqRad : ∀ z : ℂ, ‖z‖ = 1 → ∀ t ∈ Icc (1 / 2 : ℝ) 1,
      closedBall ((t : ℂ) * z) (4 * q.width) ⊆ scalarFullSector z ρ) :
    ∃ δ > 0, ∃ y : ℕ → ℝ, ∃ η > 0, ∀ᶠ ν in atTop,
      let b := scalarRadiusPeakCenter f m a (r ν)
      (y ν ∈ Icc (b.im - q.width) (b.im + q.width) ∧
        ∀ t ∈ Icc (b.re - q.width) (b.re + q.width),
          r ν * scalarSphericalSpeed f.coord
            ((r ν : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤ Real.exp (-δ * characteristic f (r ν))) ∧
      ‖scalarCurveSphere f ((r ν : ℂ) * (⟨b.re - q.width, y ν⟩ : ℂ)) -
          scalarSphereValue q.target‖ ≤ Real.exp (-η * characteristic f (r ν)) := by
  let R : ℕ → ℝ := fun ν => max 1 (r ν)
  have hR : Tendsto R atTop atTop := tendsto_atTop_mono (fun ν => le_max_right _ _) hr
  have hn := scalarDyadicIndex_tendsto.comp hR
  obtain ⟨δ, hδ, y, η, hη, hgood⟩ := scalar_comparable_peaks_have_fixed_target
    f hlin htrans hsmall hρ hl hu hm ha hpeak hn
    (fun ν => scalarDyadicMultiplier_mem (le_max_left 1 (r ν))) q hqRad
  refine ⟨δ, hδ, y, η, hη, ?_⟩
  filter_upwards [hgood, hr.eventually_ge_atTop 1] with ν hν hrν
  simpa only [Function.comp_def, scalarDyadicMultiplier_factor, R, max_eq_right hrν,
    scalarRadiusPeakCenter] using hν

end ModifiedCartan
#print axioms ModifiedCartan.scalarRadiusPeakCenter_peak
#print axioms ModifiedCartan.scalar_arbitrary_radii_have_fixed_target
