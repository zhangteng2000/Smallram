import ModifiedCartan.ScalarProfileContinuity
import ModifiedCartan.ScalarPotentialSlowChange

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Every radius sequence has an actual physical-potential L1 subsequence
with a coefficient in the proved compact profile circle. -/
theorem scalar_potential_profile_subsequence
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ C : ℂ, ‖C‖ = (Real.pi / 2) ^ 2 ∧
      LocalLpConvergence 1 (ball (0 : ℂ) 2)
        (fun ν => scalarNormalizedSpherePotential f (r (ns ν))) (scalarQuadraticProfile m C) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  obtain ⟨A, hA, hAnorm, ⟨d⟩⟩ := Paper.exists_arbitrary_radius_limits f hlin htrans hsmall hρpos hl hu hr
  have hT := characteristic_matrixGauge_of_euclidean_isometry f A hA hAnorm
  have hN := FewInflection.Curve.matrixGauge_ramification_eq f A hA
  have hlinA := (f.matrixGauge_linearlyNonDegenerate_iff A hA).mp hlin
  have htransA := (f.matrixGauge_transcendental_iff A hA).mp htrans
  have hsmallA : SmallRamification (f.matrixGauge A hA) := by
    simpa only [SmallRamification, hT, hN] using hsmall
  have hlA : strongLowerIndex (characteristic (f.matrixGauge A hA)) = (ρ : EReal) := by
    simpa only [hT] using hl
  have huA : strongUpperIndex (characteristic (f.matrixGauge A hA)) = (ρ : EReal) := by
    simpa only [hT] using hu
  obtain ⟨C, hC, hprofile⟩ := d.scalar_exists_quadratic_profile hρ hr hm
  have hbase := (d.scalar_spherical_potential_localL1 hlinA htransA hsmallA hρpos hlA huA hr).restrict
    (ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4))
  rw [show (fun ν => scalarNormalizedSpherePotential (f.matrixGauge A hA) (r (d.subseq ν))) =
      (fun ν => scalarNormalizedSpherePotential f (r (d.subseq ν))) from by
    funext ν; exact scalarNormalizedSpherePotential_matrixGauge f A hA hAnorm _] at hbase
  refine ⟨d.subseq, d.strictMono, C, hC, hbase.congr_ae (fun _ => EventuallyEq.rfl) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact hprofile hz

end ModifiedCartan
#print axioms ModifiedCartan.scalar_potential_profile_subsequence
