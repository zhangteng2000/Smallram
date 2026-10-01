import ModifiedCartan.Counting

open scoped Topology
open Filter Set Metric Function MeromorphicOn Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan

/-- The signed logarithmic count of an actual divisor on the closed disk.
This local definition avoids imposing global meromorphicity in LaTeX `lem:NH`. -/
noncomputable def closedDiskLogCounting {r : ℝ}
    (D : locallyFinsuppWithin (closedBall (0 : ℂ) |r|) ℤ) : ℝ :=
  (∑ᶠ z : ℂ, (D z : ℝ) * Real.log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * Real.log r

noncomputable def diskPoleCounting (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  closedDiskLogCounting (divisor f (closedBall 0 |r|))⁻

noncomputable def diskZeroCounting (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  closedDiskLogCounting (divisor f (closedBall 0 |r|))⁺

/-- The manuscript's scalar characteristic for a function meromorphic only
on a disk, with its actual local pole divisor. -/
noncomputable def diskCharacteristic (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ValueDistribution.proximity f ⊤ r + diskPoleCounting f r

theorem closedDiskLogCounting_toClosedBall (D : locallyFinsupp ℂ ℤ) (r : ℝ) :
    closedDiskLogCounting (toClosedBall r D) = D.logCounting r := by
  simp only [closedDiskLogCounting, Function.locallyFinsuppWithin.logCounting,
    toClosedBall_eval_within D (by simp : (0 : ℂ) ∈ closedBall 0 |r|)]
  rfl

theorem toClosedBall_negPart (D : locallyFinsupp ℂ ℤ) (r : ℝ) :
    toClosedBall r D⁻ = (toClosedBall r D)⁻ :=
  restrict_negPart D (Set.subset_univ _)

theorem toClosedBall_posPart (D : locallyFinsupp ℂ ℤ) (r : ℝ) :
    toClosedBall r D⁺ = (toClosedBall r D)⁺ :=
  restrict_posPart D (Set.subset_univ _)

theorem diskPoleCounting_eq_global {f : ℂ → ℂ} (hf : Meromorphic f) (r : ℝ) :
    diskPoleCounting f r = ValueDistribution.logCounting f ⊤ r := by
  rw [diskPoleCounting, toClosedBall_divisor hf, ← toClosedBall_negPart,
    closedDiskLogCounting_toClosedBall, ValueDistribution.logCounting_top]

theorem diskZeroCounting_eq_global {f : ℂ → ℂ} (hf : Meromorphic f) (r : ℝ) :
    diskZeroCounting f r = ValueDistribution.logCounting f (0 : WithTop ℂ) r := by
  rw [diskZeroCounting, toClosedBall_divisor hf, ← toClosedBall_posPart,
    closedDiskLogCounting_toClosedBall, ValueDistribution.logCounting_zero]

theorem diskCharacteristic_eq_global {f : ℂ → ℂ} (hf : Meromorphic f) (r : ℝ) :
    diskCharacteristic f r = ValueDistribution.characteristic f ⊤ r := by
  simp only [diskCharacteristic, diskPoleCounting_eq_global hf, ValueDistribution.characteristic,
    Pi.add_apply]

theorem closedDiskLogCounting_sub {r : ℝ}
    (D E : locallyFinsuppWithin (closedBall (0 : ℂ) |r|) ℤ) :
    closedDiskLogCounting (D - E) = closedDiskLogCounting D - closedDiskLogCounting E := by
  have hD : Function.HasFiniteSupport (fun z : ℂ => (D z : ℝ) * Real.log (r * ‖z‖⁻¹)) :=
    (D.finiteSupport (isCompact_closedBall ..)).subset (fun z hz => by
      intro hzero
      exact hz (by simp [hzero]))
  have hE : Function.HasFiniteSupport (fun z : ℂ => (E z : ℝ) * Real.log (r * ‖z‖⁻¹)) :=
    (E.finiteSupport (isCompact_closedBall ..)).subset (fun z hz => by
      intro hzero
      exact hz (by simp [hzero]))
  change (∑ᶠ z : ℂ, ((D z - E z : ℤ) : ℝ) * Real.log (r * ‖z‖⁻¹)) +
      ((D 0 - E 0 : ℤ) : ℝ) * Real.log r = _
  simp only [Int.cast_sub, sub_mul]
  rw [finsum_sub_distrib hD hE]
  unfold closedDiskLogCounting
  ring

theorem diskCounting_jensen {f : ℂ → ℂ} {r : ℝ} (hr : r ≠ 0)
    (hf : MeromorphicOn f (closedBall 0 |r|)) :
    diskZeroCounting f r - diskPoleCounting f r =
      Real.circleAverage (fun z => Real.log ‖f z‖) 0 r -
        Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  rw [diskZeroCounting, diskPoleCounting, ← closedDiskLogCounting_sub, posPart_sub_negPart]
  have hj := hf.circleAverage_log_norm hr
  simp only [zero_sub, norm_neg] at hj
  change closedDiskLogCounting _ = _
  unfold closedDiskLogCounting
  linarith

theorem closedDiskLogCounting_nonneg {r : ℝ} (hr : 0 < r)
    (D : locallyFinsuppWithin (closedBall (0 : ℂ) |r|) ℤ) (hD : 0 ≤ D) (h0 : D 0 = 0) :
    0 ≤ closedDiskLogCounting D := by
  rw [closedDiskLogCounting, h0, Int.cast_zero, zero_mul, add_zero]
  apply finsum_nonneg
  intro z
  by_cases hz : D z = 0
  · simp [hz]
  have hzr := D.supportWithinDomain hz
  have hn : ‖z‖ ≤ r := by
    simpa only [mem_closedBall, dist_zero_right, abs_of_pos hr] using hzr
  by_cases hz0 : z = 0
  · simp [hz0, h0]
  have hl : 0 ≤ Real.log (r * ‖z‖⁻¹) := by
    apply Real.log_nonneg
    rw [← div_eq_mul_inv]
    exact (one_le_div (norm_pos_iff.mpr hz0)).mpr hn
  exact mul_nonneg (Int.cast_nonneg (hD z)) hl

theorem diskCounting_nonneg_of_regular_center {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : MeromorphicOn f (closedBall 0 |r|)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    0 ≤ diskZeroCounting f r ∧ 0 ≤ diskPoleCounting f r := by
  have hD0 : divisor f (closedBall 0 |r|) 0 = 0 := by
    rw [hf.divisor_apply (by simp), hfa.meromorphicOrderAt_eq, hfa.analyticOrderAt_eq_zero.mpr h0]
    rfl
  constructor
  · exact closedDiskLogCounting_nonneg hr _ (posPart_nonneg _) (by simp [hD0])
  · exact closedDiskLogCounting_nonneg hr _ (negPart_nonneg _) (by simp [hD0])

end ModifiedCartan
#print axioms ModifiedCartan.diskCharacteristic_eq_global
#print axioms ModifiedCartan.diskCounting_jensen
#print axioms ModifiedCartan.diskCounting_nonneg_of_regular_center
