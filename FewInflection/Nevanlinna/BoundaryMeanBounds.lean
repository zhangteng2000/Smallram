import FewInflection.Nevanlinna.BoundaryMean
import FewInflection.Nevanlinna.CountingCharacteristic

/-!
# Absolute boundary means versus the characteristic

This is the scalar bookkeeping needed after the differentiated Poisson
formula. It keeps the inverse characteristic and the central logarithm
explicit, then uses nonnegativity of both proximity terms and the proved
counting estimate.
-/

open scoped Topology
open Filter MeromorphicAt MeromorphicOn MeasureTheory Metric Real Set
open ValueDistribution

namespace FewInflection

theorem circleAverage_abs_log_norm_le_two_characteristic_add_center
    {f : ℂ → ℂ} (hf : Meromorphic f) (hfa : AnalyticAt ℂ f 0)
    (h0 : f 0 ≠ 0) {r : ℝ} (hr : 1 ≤ r) :
    Real.circleAverage (fun z : ℂ => |Real.log ‖f z‖|) 0 r ≤
      2 * ValueDistribution.characteristic f ⊤ r +
        |Real.log ‖f 0‖| := by
  have hmean := circleAverage_abs_log_norm_eq_proximity_add_inv hf r
  have hinv := characteristic_inv_eq_sub_log_center hf hfa h0
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))
  have hp : 0 ≤ proximity f ⊤ r := proximity_nonneg (f := f) (a := (⊤ : WithTop ℂ)) r
  have hpi : 0 ≤ proximity (fun z => (f z)⁻¹) ⊤ r :=
    proximity_nonneg (f := fun z => (f z)⁻¹) (a := (⊤ : WithTop ℂ)) r
  have hc : 0 ≤ logCounting f ⊤ r :=
    logCounting_nonneg (f := f) (e := (⊤ : WithTop ℂ)) hr
  have hci : 0 ≤ logCounting (fun z => (f z)⁻¹) ⊤ r :=
    logCounting_nonneg (f := fun z => (f z)⁻¹)
      (e := (⊤ : WithTop ℂ)) hr
  have hinv' :
      proximity (fun z => (f z)⁻¹) ⊤ r +
          logCounting (fun z => (f z)⁻¹) ⊤ r =
        (proximity f ⊤ r + logCounting f ⊤ r) -
          Real.log ‖f 0‖ := by
    simpa [ValueDistribution.characteristic] using hinv
  change Real.circleAverage (fun z : ℂ => |Real.log ‖f z‖|) 0 r ≤
    2 * (proximity f ⊤ r + logCounting f ⊤ r) +
      |Real.log ‖f 0‖|
  calc
    Real.circleAverage (fun z : ℂ => |Real.log ‖f z‖|) 0 r =
        proximity f ⊤ r + proximity (fun z => (f z)⁻¹) ⊤ r := hmean
    _ ≤ 2 * (proximity f ⊤ r + logCounting f ⊤ r) +
          |Real.log ‖f 0‖| := by
      have hnonneg : 0 ≤ logCounting f ⊤ r +
          logCounting (fun z => (f z)⁻¹) ⊤ r +
          Real.log ‖f 0‖ + |Real.log ‖f 0‖| := by
        linarith [neg_le_abs (Real.log ‖f 0‖)]
      linarith [hinv']

end FewInflection
