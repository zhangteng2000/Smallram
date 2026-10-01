import ModifiedCartan.ScalarTargetMatrixEquiv
import ModifiedCartan.ScalarTargetGaugeMean

open scoped Topology Matrix
open Filter Set Metric Matrix
set_option autoImplicit false
namespace ModifiedCartan

/-- Exact constant correction for projective proximity under an isometric
homogeneous coordinate change; target zeros are allowed at every location. -/
theorem scalarProjectiveProximity_matrixGauge (f : Curve 1) (hlin : f.linearlyNonDegenerate)
    (B : Matrix (Index 1) (Index 1) ℂ) (hB : IsUnit B.det)
    (hnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * B k j) = euclideanNorm x)
    {β γ : WithTop ℂ} {c : ℂ} (hc : c ≠ 0)
    (he : ∀ v : Index 1 → ℂ,
      scalarTargetCoordinateMap β (v ᵥ* B) = c * scalarTargetCoordinateMap γ v)
    {r : ℝ} (hr : r ≠ 0) :
    scalarProjectiveProximity (f.matrixGauge B hB) β r =
      scalarProjectiveProximity f γ r - Real.log ‖c‖ := by
  have hL := scalarTargetFunction_differentiable f γ
  have hLU : MeromorphicOn (scalarTargetFunction f γ) univ := fun z _ => (hL.analyticAt z).meromorphicAt
  have hLn := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hLU
    (fun z _ => entire_meromorphicOrder_ne_top hL (scalarTargetFunction_nontrivial f hlin γ) z)
  have hform (z : ℂ) : scalarTargetFunction (f.matrixGauge B hB) β z =
      c * scalarTargetFunction f γ z := by
    dsimp only [scalarTargetFunction]
    rw [FewInflection.Curve.matrixGauge_vector]
    exact he (f.vector z)
  have hlog : (fun z => Real.log ‖scalarTargetFunction (f.matrixGauge B hB) β z‖)
      =ᶠ[codiscreteWithin (univ : Set ℂ)]
      (fun z => Real.log ‖c‖ + Real.log ‖scalarTargetFunction f γ z‖) := by
    filter_upwards [hLn] with z hz
    rw [hform, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hz)]
  have hmean : Real.circleAverage
      (fun z => Real.log ‖scalarTargetFunction (f.matrixGauge B hB) β z‖) 0 r =
      Real.log ‖c‖ + Real.circleAverage (fun z => Real.log ‖scalarTargetFunction f γ z‖) 0 r := by
    rw [Real.circleAverage_congr_codiscreteWithin
      (hlog.filter_mono (codiscreteWithin_mono (subset_univ _))) hr,
      Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
        ((hLU.mono_set (subset_univ _)).circleIntegrable_log_norm), Real.circleAverage_const]
  have hN : (fun z => Real.log (euclideanNorm ((f.matrixGauge B hB).vector z))) =
      (fun z => Real.log (euclideanNorm (f.vector z))) := by
    funext z
    rw [FewInflection.Curve.matrixGauge_vector]
    exact congrArg Real.log (hnorm (f.vector z))
  simp only [scalarProjectiveProximity, hmean, hN]
  ring

/-- The proved correction vanishes after division by the actual diverging
characteristic, so normalized projective proximity limits transfer back. -/
theorem scalar_projective_proximity_limit_of_matrixGauge
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (B : Matrix (Index 1) (Index 1) ℂ) (hB : IsUnit B.det)
    (hnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * B k j) = euclideanNorm x)
    {β γ : WithTop ℂ} {c : ℂ} (hc : c ≠ 0)
    (he : ∀ v : Index 1 → ℂ,
      scalarTargetCoordinateMap β (v ᵥ* B) = c * scalarTargetCoordinateMap γ v)
    {L : ℝ} (hlim : Tendsto (fun r => scalarProjectiveProximity (f.matrixGauge B hB) β r /
      characteristic (f.matrixGauge B hB) r) atTop (𝓝 L)) :
    Tendsto (fun r => scalarProjectiveProximity f γ r / characteristic f r) atTop (𝓝 L) := by
  have hsmall := (characteristic_tendsto_atTop_of_transcendental f htrans).const_div_atTop (Real.log ‖c‖)
  have h := hlim.add hsmall
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [scalarProjectiveProximity_matrixGauge f hlin B hB hnorm hc he hr.ne',
    characteristic_matrixGauge_of_euclidean_isometry f B hB hnorm]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.scalarProjectiveProximity_matrixGauge
#print axioms ModifiedCartan.scalar_projective_proximity_limit_of_matrixGauge
