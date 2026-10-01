import ModifiedCartan.ScalarDyadicTargets
import ModifiedCartan.ScalarSectorMultiplicity

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The coherent numbering of all m actual dyadic phase peaks. -/
noncomputable def scalarDyadicSectorCenter (f : Curve 1) (m : ℕ) (j : Fin m) (ν : ℕ) : ℂ :=
  scalarSectorCenter (scalarDyadicPeakCenter f m ν) m j

theorem scalarDyadicSectorCenter_norm (f : Curve 1) (m : ℕ) (j : Fin m) (ν : ℕ) :
    ‖scalarDyadicSectorCenter f m j ν‖ = 1 :=
  scalarSectorCenter_norm (scalarDyadicPeakCenter_norm f m ν) m j

theorem scalarDyadicSectorCenter_peak (f : Curve 1) {m : ℕ} (hm : m ≠ 0) (j : Fin m) (ν : ℕ) :
    scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (scalarDyadicSectorCenter f m j ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ) := by
  rw [scalarDyadicSectorCenter, scalarSectorCenter, mul_pow, scalarSectorRotation_pow hm, mul_one]
  exact scalarDyadicPeakCenter_peak f hm ν

theorem scalarDyadicSectorCenter_steps_tendsto_zero
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) (j : Fin m) :
    Tendsto (fun ν => scalarDyadicSectorCenter f m j (ν + 1) - scalarDyadicSectorCenter f m j ν)
      atTop (𝓝 0) := by
  have hh := (scalarDyadicPeakCenter_steps_tendsto_zero f hlin htrans hsmall hρ hl hu hm).mul_const
    (scalarSectorRotation m j.val)
  simpa only [scalarDyadicSectorCenter, scalarSectorCenter, sub_mul, zero_mul] using hh

/-- Every one of the m coherently tracked sectors has a fixed target with
actual exponentially convergent dyadic anchors. Auxiliary to thm:A (b). -/
theorem scalar_exists_all_dyadic_sector_targets
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) :
    Nonempty ((j : Fin m) → ScalarDyadicPeakTargetData f (scalarDyadicSectorCenter f m j) ρ) := by
  classical
  have hm0 : m ≠ 0 := by intro hz; simp only [hz, Nat.cast_zero, zero_div] at hm; linarith
  have he (j : Fin m) : Nonempty (ScalarDyadicPeakTargetData f (scalarDyadicSectorCenter f m j) ρ) :=
    scalar_exists_dyadic_peak_target f hlin htrans hsmall hρ hl hu hm
      (scalarDyadicSectorCenter_norm f m j) (scalarDyadicSectorCenter_peak f hm0 j)
      (scalarDyadicSectorCenter_steps_tendsto_zero f hlin htrans hsmall hρ hl hu hm j)
  exact ⟨fun j => Classical.choice (he j)⟩

/-- Integer multiplicities of these fixed dyadic targets total 2 rho.
Their identification with deficiencies is a separate analytic step. -/
theorem scalar_dyadic_target_multiplicities_hasSum {f : Curve 1} {m : ℕ} {ρ : ℝ}
    (hm : ρ = (m : ℝ) / 2)
    (q : (j : Fin m) → ScalarDyadicPeakTargetData f (scalarDyadicSectorCenter f m j) ρ) :
    HasSum (fun a => (scalarSectorMultiplicity (fun j => (q j).target) a : ℝ)) (2 * ρ) := by
  have he : (m : ℝ) = 2 * ρ := by linarith
  rw [← he]
  exact scalarSectorMultiplicity_hasSum _

end ModifiedCartan
#print axioms ModifiedCartan.scalar_exists_all_dyadic_sector_targets
#print axioms ModifiedCartan.scalar_dyadic_target_multiplicities_hasSum