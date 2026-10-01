import FewInflection.Nevanlinna.CountingBounds
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Characteristic/counting bookkeeping for the fixed-radius lemma

The paper first bounds the zero and pole counts by the characteristic of a
meromorphic function and of its inverse. These are exact consequences of the
First Main Theorem API; no growth estimate is hidden in this module.
-/

open scoped BigOperators Topology
open Filter Asymptotics MeromorphicAt MeromorphicOn MeasureTheory Metric Real Set
open ValueDistribution

namespace FewInflection

/-- At a non-pole, nonzero centre the characteristic of the inverse differs
from that of the original function by the logarithm of the central value. -/
theorem characteristic_inv_eq_sub_log_center
    {h : ℂ → ℂ} (hh : Meromorphic h) (hha : AnalyticAt ℂ h 0)
    (h0 : h 0 ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    ValueDistribution.characteristic (fun z => (h z)⁻¹) ⊤ r =
      ValueDistribution.characteristic h ⊤ r - Real.log ‖h 0‖ := by
  have hx := characteristic_sub_characteristic_inv_of_ne_zero (f := h) hh hr
  rw [hha.meromorphicTrailingCoeffAt_of_ne_zero h0] at hx
  have hx' : ValueDistribution.characteristic h ⊤ r -
      ValueDistribution.characteristic (fun z => (h z)⁻¹) ⊤ r =
      Real.log ‖h 0‖ := by
    change ValueDistribution.characteristic h ⊤ r -
      ValueDistribution.characteristic (fun z => (h z)⁻¹) ⊤ r =
      Real.log ‖h 0‖ at hx
    exact hx
  linarith

/-- At radii at least one, the total logarithmic count of zeros and poles is
bounded by twice the characteristic plus the central logarithmic term. -/
theorem logCounting_add_inv_le_two_characteristic
    {h : ℂ → ℂ} (hh : Meromorphic h) (hha : AnalyticAt ℂ h 0)
    (h0 : h 0 ≠ 0) {r : ℝ} (hr : 1 ≤ r) :
    ValueDistribution.logCounting h ⊤ r +
        ValueDistribution.logCounting (fun z => (h z)⁻¹) ⊤ r ≤
      2 * ValueDistribution.characteristic h ⊤ r + |Real.log ‖h 0‖| := by
  have hinv := characteristic_inv_eq_sub_log_center hh hha h0
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))
  have hp1 : 0 ≤ ValueDistribution.proximity h ⊤ r := by
    exact (proximity_nonneg (f := h) (a := (⊤ : WithTop ℂ))) r
  have hp2 : 0 ≤ ValueDistribution.proximity (fun z => (h z)⁻¹) ⊤ r := by
    exact (proximity_nonneg (f := fun z => (h z)⁻¹)
      (a := (⊤ : WithTop ℂ))) r
  have h1 : ValueDistribution.logCounting h ⊤ r ≤
      ValueDistribution.characteristic h ⊤ r :=
    le_add_of_nonneg_left hp1
  have h2 : ValueDistribution.logCounting (fun z => (h z)⁻¹) ⊤ r ≤
      ValueDistribution.characteristic (fun z => (h z)⁻¹) ⊤ r :=
    le_add_of_nonneg_left hp2
  have habs : -Real.log ‖h 0‖ ≤ |Real.log ‖h 0‖| := neg_le_abs _
  linarith [h1, h2, hinv, habs]

end FewInflection
