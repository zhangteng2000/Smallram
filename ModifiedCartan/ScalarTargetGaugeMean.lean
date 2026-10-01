import ModifiedCartan.ScalarActualTargetBasics
import ModifiedCartan.ScalarDistinctTargetBounds
import ModifiedCartan.ScalarRamificationBridge

open scoped Topology Matrix
open Filter Set Metric Matrix
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- The actual normalized homogeneous form for a fixed target. -/
def scalarTargetFunction (f : Curve 1) (β : WithTop ℂ) (z : ℂ) : ℂ :=
  scalarTargetCoordinateMap β (f.vector z)

theorem scalarTargetFunction_differentiable (f : Curve 1) (β : WithTop ℂ) :
    Differentiable ℂ (scalarTargetFunction f β) := by
  induction β using WithTop.recTopCoe with
  | top =>
    change Differentiable ℂ (fun z => f.coord 0 z / 1)
    simpa only [div_one] using f.holomorphic 0
  | coe b =>
    change Differentiable ℂ (fun z => (f.coord 1 z - b * f.coord 0 z) /
      (Real.sqrt (1 + ‖b‖ ^ 2) : ℂ))
    exact ((f.holomorphic 1).sub ((f.holomorphic 0).const_mul b)).div_const _

theorem scalarTargetFunction_nontrivial (f : Curve 1) (hlin : f.linearlyNonDegenerate)
    (β : WithTop ℂ) : ∃ z, scalarTargetFunction f β z ≠ 0 := by
  let V := scalarTargetUnitary β
  have hV : IsUnit (V : Matrix (Index 1) (Index 1) ℂ).det :=
    isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mp (by rw [norm_det_unitary]; norm_num))
  obtain ⟨z, hz⟩ := scalar_curve_coordinate_nontrivial (f.matrixGauge V hV)
    (f.matrixGauge_linearlyNonDegenerate V hV hlin) 0
  refine ⟨z, ?_⟩
  rw [scalarTargetFunction, scalarTargetCoordinateMap_apply]
  exact hz

theorem scalarActualTarget_eq_exp_mul (f : Curve 1) (β : WithTop ℂ) (r : ℝ)
    (H : ℂ → ℂ) (z : ℂ) :
    scalarActualTarget f β r H z =
      Complex.exp (-H z) * scalarTargetFunction f β ((r : ℂ) * z) := by
  rw [scalarActualTarget, ← scalarTargetCoordinateMap_apply]
  change scalarTargetCoordinateMap β
    (Complex.exp (-H z) • f.vector ((r : ℂ) * z)) = _
  exact (scalarTargetCoordinateMap β).map_smul (Complex.exp (-H z)) _

/-- The exponential gauge has exactly its harmonic center correction in the
fixed-target circle mean; target zeros, including at the origin, are allowed. -/
theorem scalarActualTarget_circleAverage_log (f : Curve 1)
    (hlin : f.linearlyNonDegenerate) (β : WithTop ℂ) {r : ℝ} (hr : r ≠ 0)
    {H : ℂ → ℂ} {B R : ℝ} (hH : AnalyticOnNhd ℂ H (ball 0 B))
    (hR : 0 < R) (hRB : R < B) :
    Real.circleAverage (fun z => Real.log ‖scalarActualTarget f β r H z‖) 0 R =
      Real.circleAverage (fun z => Real.log ‖scalarTargetFunction f β z‖) 0 (r * R) - (H 0).re := by
  let Q : ℂ → ℂ := fun z => scalarTargetFunction f β ((r : ℂ) * z)
  have hQ : Differentiable ℂ Q :=
    (scalarTargetFunction_differentiable f β).comp (differentiable_id.const_mul (r : ℂ))
  have hnQ : ∃ z, Q z ≠ 0 := by
    obtain ⟨z, hz⟩ := scalarTargetFunction_nontrivial f hlin β
    refine ⟨z / (r : ℂ), ?_⟩
    simpa only [Q, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr)] using hz
  have hQU : MeromorphicOn Q univ := fun z _ => (hQ.analyticAt z).meromorphicAt
  have hne := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hQU
    (fun z _ => entire_meromorphicOrder_ne_top hQ hnQ z)
  have he : (fun z => Real.log ‖scalarActualTarget f β r H z‖) =ᶠ[codiscreteWithin (univ : Set ℂ)]
      (fun z => Real.log ‖Q z‖ - (H z).re) := by
    filter_upwards [hne] with z hz
    rw [scalarActualTarget_eq_exp_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)) (norm_ne_zero_iff.mpr hz),
      Complex.norm_exp, Real.log_exp, Complex.neg_re]
    dsimp only [Q]
    ring
  have hh : InnerProductSpace.HarmonicOnNhd (fun z => (H z).re) (closedBall 0 |R|) := by
    intro z hz
    rw [abs_of_pos hR] at hz
    exact (hH z (closedBall_subset_ball hRB hz)).harmonicAt_re
  have hciQ : CircleIntegrable (fun z => Real.log ‖Q z‖) 0 R :=
    (hQU.mono_set (subset_univ _)).circleIntegrable_log_norm
  have hciH : CircleIntegrable (fun z => (H z).re) 0 R :=
    (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  rw [Real.circleAverage_congr_codiscreteWithin
    (he.filter_mono (codiscreteWithin_mono (subset_univ _))) hR.ne',
    Real.circleAverage_fun_sub hciQ hciH, hh.circleAverage_eq]
  exact congrArg (fun x => x - (H 0).re)
    (circleAverage_real_dilate (fun z => Real.log ‖scalarTargetFunction f β z‖) r R)

/-- Spherical homogeneous proximity, expressed by the actual fixed-target form. -/
def scalarProjectiveProximity (f : Curve 1) (β : WithTop ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z => Real.log (euclideanNorm (f.vector z))) 0 r -
    Real.circleAverage (fun z => Real.log ‖scalarTargetFunction f β z‖) 0 r

theorem scalarProjectiveProximity_eq_gauged_means (f : Curve 1)
    (hlin : f.linearlyNonDegenerate) (β : WithTop ℂ) {r : ℝ} (hr : r ≠ 0)
    {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H (ball 0 64)) :
    scalarProjectiveProximity f β r =
      Real.circleAverage (fun z => Real.log (euclideanNorm
        (fun j => rescaledRepresentation f r H j z))) 0 1 -
      Real.circleAverage (fun z => Real.log ‖scalarActualTarget f β r H z‖) 0 1 := by
  rw [Paper.eq_meanidentity f r hH (by norm_num) (by norm_num),
    scalarActualTarget_circleAverage_log f hlin β hr hH (by norm_num) (by norm_num)]
  simp only [one_mul, mul_one, characteristic, scalarProjectiveProximity]
  ring

end
end ModifiedCartan
#print axioms ModifiedCartan.scalarTargetFunction_nontrivial
#print axioms ModifiedCartan.scalarActualTarget_circleAverage_log
#print axioms ModifiedCartan.scalarProjectiveProximity_eq_gauged_means
