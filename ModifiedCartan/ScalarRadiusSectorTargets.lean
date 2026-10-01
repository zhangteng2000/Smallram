import ModifiedCartan.ScalarArbitraryRadiusTargets
import ModifiedCartan.ScalarDyadicTargetRefinement
import ModifiedCartan.ScalarDyadicSectorTargets

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The coherent numbering of all actual peaks at arbitrary radii. -/
noncomputable def scalarRadiusSectorCenter (f : Curve 1) (m : ℕ) (j : Fin m) (r : ℝ) : ℂ :=
  scalarRadiusPeakCenter f m (scalarDyadicSectorCenter f m j) r

theorem scalarRadiusSectorCenter_eq (f : Curve 1) (m : ℕ) (j : Fin m) (r : ℝ) :
    scalarRadiusSectorCenter f m j r =
      scalarSectorCenter (scalarRadiusPeakCenter f m (scalarDyadicPeakCenter f m) r) m j := by
  simp only [scalarRadiusSectorCenter, scalarRadiusPeakCenter, scalarComparablePeakCenter,
    scalarDyadicSectorCenter, scalarSectorCenter]
  ring

theorem scalarRadiusSectorCenter_norm (f : Curve 1) (m : ℕ) (j : Fin m) (r : ℝ) :
    ‖scalarRadiusSectorCenter f m j r‖ = 1 :=
  scalarRadiusPeakCenter_norm f m (scalarDyadicSectorCenter_norm f m j) r

theorem scalarRadiusSectorCenter_peak (f : Curve 1) {m : ℕ} (hm : m ≠ 0)
    (j : Fin m) (r : ℝ) :
    scalarPhaseCoefficient f m r * (scalarRadiusSectorCenter f m j r) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ) :=
  scalarRadiusPeakCenter_peak f hm (scalarDyadicSectorCenter_peak f hm j) r

/-- All numbered sectors have fixed target data with the geometric refinement
needed by the arbitrary-radius theorem. Every field is constructed from the
original curve; these are auxiliary data for LaTeX thm:A (b). -/
theorem scalar_exists_all_radial_sector_targets
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) :
    ∃ q : (j : Fin m) → ScalarDyadicPeakTargetData f (scalarDyadicSectorCenter f m j) ρ,
      ∀ j (z : ℂ), ‖z‖ = 1 → ∀ t ∈ Icc (1 / 2 : ℝ) 1,
        closedBall ((t : ℂ) * z) (4 * (q j).width) ⊆ scalarFullSector z ρ := by
  classical
  have hm0 : m ≠ 0 := by intro hz; simp only [hz, Nat.cast_zero, zero_div] at hm; linarith
  have hex (j : Fin m) := scalar_exists_dyadic_peak_target_radial
    f hlin htrans hsmall hρ hl hu hm
    (scalarDyadicSectorCenter_norm f m j) (scalarDyadicSectorCenter_peak f hm0 j)
    (scalarDyadicSectorCenter_steps_tendsto_zero f hlin htrans hsmall hρ hl hu hm j)
  choose q hq using hex
  exact ⟨q, hq⟩

end ModifiedCartan
#print axioms ModifiedCartan.scalarRadiusSectorCenter_peak
#print axioms ModifiedCartan.scalar_exists_all_radial_sector_targets
