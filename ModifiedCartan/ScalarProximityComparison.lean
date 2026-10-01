import ModifiedCartan.ScalarProximityMean

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Uniform comparison of the numerator/target norm mean with the Euclidean
norm mean. The comparison constant depends only on the fixed target. -/
theorem scalarProximityPairLog_abs_sub_mean_le (F : Curve 1) (β : WithTop ℂ) (r : ℝ) :
    |Real.circleAverage (fun z => Real.log (scalarProximityPairNorm β (F.vector z))) 0 r -
      Real.circleAverage (fun z => Real.log (euclideanNorm (F.vector z))) 0 r| ≤
        Real.log (2 * scalarTargetLinearSize β) := by
  let K := 2 * scalarTargetLinearSize β
  have hK : 0 < K := mul_pos (by norm_num) (scalarTargetLinearSize_pos β)
  have hpoint (z : ℂ) :
      Real.log (scalarProximityPairNorm β (F.vector z)) ≤ K.log + Real.log (euclideanNorm (F.vector z)) ∧
      Real.log (euclideanNorm (F.vector z)) ≤ K.log + Real.log (scalarProximityPairNorm β (F.vector z)) := by
    have hM := scalarProximityPairNorm_pos β (F.vector_ne_zero z)
    have hN := euclideanNorm_pos (F.vector_ne_zero z)
    obtain ⟨hMN, hNM⟩ := scalarProximityPairNorm_compare β (F.vector z)
    have h₁ := Real.log_le_log hM hMN
    have h₂ := Real.log_le_log hN hNM
    rw [Real.log_mul hK.ne' hN.ne'] at h₁
    rw [Real.log_mul hK.ne' hM.ne'] at h₂
    exact ⟨h₁, h₂⟩
  have hciM := (scalarProximityPairLog_continuous F β).continuousOn.circleIntegrable' (c := 0) (R := r)
  have hciN := (curve_log_euclideanNorm_continuous F).continuousOn.circleIntegrable' (c := 0) (R := r)
  have h₁ := Real.circleAverage_mono hciM ((circleIntegrable_const K.log 0 r).add hciN)
    (fun z _ => (hpoint z).1)
  have h₂ := Real.circleAverage_mono hciN ((circleIntegrable_const K.log 0 r).add hciM)
    (fun z _ => (hpoint z).2)
  rw [Real.circleAverage_add (circleIntegrable_const _ _ _) hciN, Real.circleAverage_const] at h₁
  rw [Real.circleAverage_add (circleIntegrable_const _ _ _) hciM, Real.circleAverage_const] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Classical and homogeneous proximity differ by a bounded amount, for
all finite targets and infinity and every nonzero radius. Auxiliary to `thm:A` (b). -/
theorem scalar_proximity_abs_sub_projective_le {f : ℂ → ℂ}
    (F : Curve 1) (hlin : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (β : WithTop ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, r ≠ 0 →
      |ValueDistribution.proximity f β r - scalarProjectiveProximity F β r| ≤ C := by
  let K := 2 * scalarTargetLinearSize β
  have hK : 1 ≤ K := by dsimp [K]; linarith [scalarTargetLinearSize_one_le β]
  refine ⟨Real.log K + |Real.log (scalarTargetNormalizingSize β)|,
    add_nonneg (Real.log_nonneg hK) (abs_nonneg _), ?_⟩
  intro r hr
  rw [scalar_proximity_eq_pair_log_means F hlin he β hr, scalarProjectiveProximity,
    scalarTargetFunction_circleAverage_log F hlin β hr]
  calc
    _ = |(Real.circleAverage (fun z => Real.log (scalarProximityPairNorm β (F.vector z))) 0 r -
        Real.circleAverage (fun z => Real.log (euclideanNorm (F.vector z))) 0 r) -
        Real.log (scalarTargetNormalizingSize β)| := by congr 1; ring
    _ ≤ |Real.circleAverage (fun z => Real.log (scalarProximityPairNorm β (F.vector z))) 0 r -
        Real.circleAverage (fun z => Real.log (euclideanNorm (F.vector z))) 0 r| +
        |Real.log (scalarTargetNormalizingSize β)| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le _ 0 (Real.log (scalarTargetNormalizingSize β))
    _ ≤ _ := add_le_add (scalarProximityPairLog_abs_sub_mean_le F β r) le_rfl

end ModifiedCartan
#print axioms ModifiedCartan.scalar_proximity_abs_sub_projective_le
