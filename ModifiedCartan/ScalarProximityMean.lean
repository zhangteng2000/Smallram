import ModifiedCartan.ScalarProximityPair

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Classical proximity equals the actual numerator/target pair log mean
minus the actual unnormalized target log mean, for every nonzero radius. -/
theorem scalar_proximity_eq_pair_log_means {f : ℂ → ℂ}
    (F : Curve 1) (hlin : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (β : WithTop ℂ) {r : ℝ} (hr : r ≠ 0) :
    ValueDistribution.proximity f β r =
      Real.circleAverage (fun z => Real.log (scalarProximityPairNorm β (F.vector z))) 0 r -
      Real.circleAverage (fun z => Real.log ‖scalarTargetRawFunction F β z‖) 0 r := by
  have hL := scalarTargetRawFunction_differentiable F β
  have hLU : MeromorphicOn (scalarTargetRawFunction F β) univ := fun z _ => (hL.analyticAt z).meromorphicAt
  have hLn := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hLU
    (fun z _ => entire_meromorphicOrder_ne_top hL (scalarTargetRawFunction_nontrivial F hlin β) z)
  have hqU : MeromorphicOn (F.coord 0) univ := fun z _ => ((F.holomorphic 0).analyticAt z).meromorphicAt
  have hqn := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hqU
    (fun z _ => entire_meromorphicOrder_ne_top (F.holomorphic 0)
      (scalar_curve_coordinate_nontrivial F hlin 0) z)
  have hciM := (scalarProximityPairLog_continuous F β).continuousOn.circleIntegrable' (c := 0) (R := r)
  have hciL := (hLU.mono_set (subset_univ (sphere (0 : ℂ) |r|))).circleIntegrable_log_norm
  have hrepl : ∀ G : ℂ → ℝ,
      G =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z =>
        Real.log (scalarProximityPairNorm β (F.vector z)) - Real.log ‖scalarTargetRawFunction F β z‖) →
      Real.circleAverage G 0 r =
        Real.circleAverage (fun z => Real.log (scalarProximityPairNorm β (F.vector z))) 0 r -
        Real.circleAverage (fun z => Real.log ‖scalarTargetRawFunction F β z‖) 0 r := by
    intro G hG
    rw [Real.circleAverage_congr_codiscreteWithin
      (hG.filter_mono (codiscreteWithin_mono (subset_univ _))) hr,
      Real.circleAverage_fun_sub hciM hciL]
  induction β using WithTop.recTopCoe with
  | top =>
    rw [ValueDistribution.proximity_top]
    apply hrepl
    filter_upwards [he, hqn] with z hz hzq
    rw [hz]
    have hh := log_max_norm_eq_posLog_div_add (F.coord 1 z) (F.coord 0 z) hzq
    change Real.posLog ‖F.coord 1 z / F.coord 0 z‖ =
      Real.log (max ‖F.coord 1 z‖ ‖F.coord 0 z‖) - Real.log ‖F.coord 0 z‖
    linarith
  | coe b =>
    rw [ValueDistribution.proximity_coe]
    apply hrepl
    filter_upwards [he, hqn, hLn] with z hz hzq hzL
    have hid : (f z - b)⁻¹ = F.coord 0 z / scalarTargetRawFunction F (b : WithTop ℂ) z := by
      rw [hz]
      change (F.coord 1 z / F.coord 0 z - b)⁻¹ = F.coord 0 z / (F.coord 1 z - b * F.coord 0 z)
      change F.coord 1 z - b * F.coord 0 z ≠ 0 at hzL
      field_simp
    rw [← norm_inv, hid]
    have hh := log_max_norm_eq_posLog_div_add (F.coord 0 z)
      (scalarTargetRawFunction F (b : WithTop ℂ) z) hzL
    change Real.posLog ‖F.coord 0 z / scalarTargetRawFunction F (b : WithTop ℂ) z‖ =
      Real.log (max ‖F.coord 0 z‖ ‖scalarTargetRawFunction F (b : WithTop ℂ) z‖) -
        Real.log ‖scalarTargetRawFunction F (b : WithTop ℂ) z‖
    linarith

/-- Exact circle-mean correction for the normalization of the target form. -/
theorem scalarTargetFunction_circleAverage_log (F : Curve 1)
    (hlin : F.linearlyNonDegenerate) (β : WithTop ℂ) {r : ℝ} (hr : r ≠ 0) :
    Real.circleAverage (fun z => Real.log ‖scalarTargetFunction F β z‖) 0 r =
      Real.circleAverage (fun z => Real.log ‖scalarTargetRawFunction F β z‖) 0 r -
        Real.log (scalarTargetNormalizingSize β) := by
  have hL := scalarTargetRawFunction_differentiable F β
  have hLU : MeromorphicOn (scalarTargetRawFunction F β) univ := fun z _ => (hL.analyticAt z).meromorphicAt
  have hLn := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hLU
    (fun z _ => entire_meromorphicOrder_ne_top hL (scalarTargetRawFunction_nontrivial F hlin β) z)
  have he : (fun z => Real.log ‖scalarTargetFunction F β z‖) =ᶠ[codiscreteWithin (univ : Set ℂ)]
      (fun z => Real.log ‖scalarTargetRawFunction F β z‖ - Real.log (scalarTargetNormalizingSize β)) := by
    filter_upwards [hLn] with z hz
    rw [scalarTargetFunction_eq_raw_div, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (scalarTargetNormalizingSize_pos β).le,
      Real.log_div (norm_ne_zero_iff.mpr hz) (scalarTargetNormalizingSize_pos β).ne']
  rw [Real.circleAverage_congr_codiscreteWithin
    (he.filter_mono (codiscreteWithin_mono (subset_univ _))) hr,
    Real.circleAverage_fun_sub
      ((hLU.mono_set (subset_univ _)).circleIntegrable_log_norm) (circleIntegrable_const _ _ _),
    Real.circleAverage_const]

end ModifiedCartan
#print axioms ModifiedCartan.scalar_proximity_eq_pair_log_means
#print axioms ModifiedCartan.scalarTargetFunction_circleAverage_log
