import ModifiedCartan.Counting
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import FewInflection.WronskianRegularity

open scoped BigOperators Topology
open Function Function.locallyFinsuppWithin MeasureTheory MeromorphicOn Metric Real Set

namespace ModifiedCartan

noncomputable section

theorem cutoff_set_inter {a R : ℝ} (ha : 0 < a) :
    Ici a ∩ Ioc 0 R = Icc a R := by
  ext t
  simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨h₁, _, h₂⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, ha.trans_le h₁, h₂⟩

theorem cutoff_inv_intervalIntegrable {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    IntervalIntegrable ((Ici a).indicator (fun t : ℝ => t⁻¹)) volume 0 R := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (ha.le.trans haR)]
  change Integrable _ (volume.restrict (Ioc 0 R))
  rw [integrable_indicator_iff measurableSet_Ici]
  change Integrable _ ((volume.restrict (Ioc 0 R)).restrict (Ici a))
  rw [Measure.restrict_restrict measurableSet_Ici, cutoff_set_inter ha]
  exact (continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne')).integrableOn_Icc

theorem integral_cutoff_inv {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    (∫ t in (0 : ℝ)..R, (Ici a).indicator (fun t : ℝ => t⁻¹) t) =
      Real.log (R / a) := by
  rw [intervalIntegral.integral_of_le (ha.le.trans haR),
    integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, cutoff_set_inter ha,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haR]
  exact integral_inv_of_pos ha (ha.trans_le haR)

def divisorCount (D : locallyFinsupp ℂ ℤ) (r : ℝ) : ℝ :=
  ∑ᶠ z : ℂ, ((toClosedBall r D) z : ℝ)

def diskSupport (D : locallyFinsupp ℂ ℤ) (R : ℝ) : Finset ℂ := by
  classical
  exact insert 0 ((toClosedBall R D).finiteSupport (isCompact_closedBall ..)).toFinset

theorem zero_mem_diskSupport (D : locallyFinsupp ℂ ℤ) (R : ℝ) :
    (0 : ℂ) ∈ diskSupport D R := by
  classical
  simp [diskSupport]

theorem mem_diskSupport_of_ne {D : locallyFinsupp ℂ ℤ} {R : ℝ} {z : ℂ}
    (hz : (toClosedBall R D) z ≠ 0) : z ∈ diskSupport D R := by
  classical
  simp [diskSupport, Function.mem_support, hz]

theorem norm_le_of_mem_diskSupport {D : locallyFinsupp ℂ ℤ} {R : ℝ}
    (hR : 0 ≤ R) {z : ℂ} (hz : z ∈ diskSupport D R) : ‖z‖ ≤ R := by
  classical
  simp only [diskSupport, Finset.mem_insert, Set.Finite.mem_toFinset,
    Function.mem_support] at hz
  rcases hz with rfl | hz
  · simpa using hR
  · by_contra hnot
    apply hz
    apply apply_eq_zero_of_notMem (toClosedBall R D)
    simpa [mem_closedBall, dist_zero_right, abs_of_nonneg hR] using hnot

theorem toClosedBall_cast_eq_if {D : locallyFinsupp ℂ ℤ} {t : ℝ}
    (ht : 0 ≤ t) (z : ℂ) :
    ((toClosedBall t D) z : ℝ) = if ‖z‖ ≤ t then (D z : ℝ) else 0 := by
  classical
  by_cases hz : ‖z‖ ≤ t
  · rw [toClosedBall_eval_within D (by
      simpa [mem_closedBall, dist_zero_right, abs_of_nonneg ht] using hz)]
    simp [hz]
  · rw [apply_eq_zero_of_notMem (toClosedBall t D) (by
      simpa [mem_closedBall, dist_zero_right, abs_of_nonneg ht] using hz)]
    simp [hz]

theorem divisorCount_eq_sum {D : locallyFinsupp ℂ ℤ} {t R : ℝ}
    (ht : 0 ≤ t) (htR : t ≤ R) :
    divisorCount D t =
      ∑ z ∈ diskSupport D R, if ‖z‖ ≤ t then (D z : ℝ) else 0 := by
  classical
  have hR : 0 ≤ R := ht.trans htR
  have hs : Function.support (fun z : ℂ => ((toClosedBall t D) z : ℝ)) ⊆
      (diskSupport D R : Set ℂ) := by
    intro z hz
    change ((toClosedBall t D) z : ℝ) ≠ 0 at hz
    have hzt : z ∈ closedBall (0 : ℂ) |t| := by
      by_contra hnot
      rw [apply_eq_zero_of_notMem (toClosedBall t D) hnot] at hz
      simp at hz
    have hzR : z ∈ closedBall (0 : ℂ) |R| :=
      closedBall_subset_closedBall (by simpa [abs_of_nonneg ht, abs_of_nonneg hR] using htR) hzt
    apply mem_diskSupport_of_ne
    rw [toClosedBall_eval_within D hzR]
    rw [toClosedBall_eval_within D hzt] at hz
    exact_mod_cast hz
  unfold divisorCount
  rw [finsum_eq_sum_of_support_subset _ hs]
  exact Finset.sum_congr rfl (fun z _ => toClosedBall_cast_eq_if ht z)

theorem divisorCount_zero (D : locallyFinsupp ℂ ℤ) :
    divisorCount D 0 = (D 0 : ℝ) := by
  unfold divisorCount
  rw [finsum_eq_single _ 0 (by
    intro z hz
    rw [toClosedBall_cast_eq_if (le_refl (0 : ℝ))]
    simp [hz])]
  rw [toClosedBall_cast_eq_if (le_refl (0 : ℝ))]
  simp

theorem divisorCount_sub_center_div_eq_sum {D : locallyFinsupp ℂ ℤ} {t R : ℝ}
    (ht : 0 ≤ t) (htR : t ≤ R) :
    (divisorCount D t - (D 0 : ℝ)) / t =
      ∑ z ∈ (diskSupport D R).erase 0,
        (D z : ℝ) * (Ici ‖z‖).indicator (fun t : ℝ => t⁻¹) t := by
  classical
  have h := divisorCount_eq_sum (D := D) ht htR
  rw [← Finset.sum_erase_add _ _ (zero_mem_diskSupport D R)] at h
  simp only [norm_zero, ite_eq_left ht] at h
  rw [h, add_sub_cancel_right, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : ‖z‖ ≤ t
  · simp [hz, div_eq_mul_inv]
  · simp [hz]

theorem integral_divisorCount {D : locallyFinsupp ℂ ℤ} {R : ℝ} (hR : 0 < R) :
    (∫ t in (0 : ℝ)..R, (divisorCount D t - (D 0 : ℝ)) / t) =
      ∑ z ∈ (diskSupport D R).erase 0, (D z : ℝ) * Real.log (R / ‖z‖) := by
  classical
  calc
    _ = ∫ t in (0 : ℝ)..R, ∑ z ∈ (diskSupport D R).erase 0,
        (D z : ℝ) * (Ici ‖z‖).indicator (fun t : ℝ => t⁻¹) t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hR.le] at ht
      exact divisorCount_sub_center_div_eq_sum ht.1 ht.2
    _ = ∑ z ∈ (diskSupport D R).erase 0, ∫ t in (0 : ℝ)..R,
        (D z : ℝ) * (Ici ‖z‖).indicator (fun t : ℝ => t⁻¹) t := by
      apply intervalIntegral.integral_finsetSum
      intro z hz
      exact (cutoff_inv_intervalIntegrable (norm_pos_iff.mpr (Finset.mem_erase.mp hz).1)
        (norm_le_of_mem_diskSupport hR.le (Finset.mem_of_mem_erase hz))).const_mul _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [intervalIntegral.integral_const_mul, integral_cutoff_inv
        (norm_pos_iff.mpr (Finset.mem_erase.mp hz).1)
        (norm_le_of_mem_diskSupport hR.le (Finset.mem_of_mem_erase hz))]

theorem divisor_logCounting_eq_sum {D : locallyFinsupp ℂ ℤ} {R : ℝ} (hR : 0 < R) :
    D.logCounting R =
      (∑ z ∈ (diskSupport D R).erase 0, (D z : ℝ) * Real.log (R / ‖z‖)) +
        (D 0 : ℝ) * Real.log R := by
  classical
  have hs : Function.support (fun z : ℂ =>
      ((toClosedBall R D) z : ℝ) * Real.log (R * ‖z‖⁻¹)) ⊆
      (diskSupport D R : Set ℂ) := by
    intro z hz
    apply mem_diskSupport_of_ne
    intro hzero
    apply hz
    simp [hzero]
  change (∑ᶠ z : ℂ, ((toClosedBall R D) z : ℝ) * Real.log (R * ‖z‖⁻¹)) + _ = _
  rw [finsum_eq_sum_of_support_subset _ hs,
    ← Finset.sum_erase_add _ _ (zero_mem_diskSupport D R)]
  simp only [norm_zero, inv_zero, mul_zero, Real.log_zero, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  have hnorm := norm_le_of_mem_diskSupport hR.le (Finset.mem_of_mem_erase hz)
  rw [toClosedBall_eval_within D (by
    simpa [mem_closedBall, dist_zero_right, abs_of_pos hR] using hnorm),
    ← div_eq_mul_inv]

theorem divisor_logCounting_eq_integral {D : locallyFinsupp ℂ ℤ} {R : ℝ}
    (hR : 0 < R) :
    D.logCounting R =
      (∫ t in (0 : ℝ)..R, (divisorCount D t - (D 0 : ℝ)) / t) +
        (D 0 : ℝ) * Real.log R := by
  rw [divisor_logCounting_eq_sum hR, integral_divisorCount hR]

/-- Literal integral in LaTeX label `eq:zero-count-definition`. -/
def integralZeroCounting (H : ℂ → ℂ) (r : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..r, (zeroCount H t - zeroCount H 0) / t) +
    zeroCount H 0 * Real.log r

namespace Paper

/-- LaTeX label `eq:zero-count-definition`: the manuscript's integral equals
mathlib's logarithmic counting function, including the central multiplicity. -/
theorem eq_zero_count_definition {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {r : ℝ} (hr : 0 < r) :
    ValueDistribution.logCounting H (0 : WithTop ℂ) r = integralZeroCounting H r := by
  have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hH
  have hc : zeroCount H 0 = (divisor H Set.univ 0 : ℝ) := divisorCount_zero _
  rw [ValueDistribution.logCounting_zero, posPart_eq_self.mpr ha.divisor_nonneg,
    integralZeroCounting, hc]
  exact divisor_logCounting_eq_integral hr

end Paper

theorem ramification_eq_integralZeroCounting {n : ℕ} (f : Curve n)
    {r : ℝ} (hr : 0 < r) :
    ramification f r =
      integralZeroCounting (fun z => FewInflection.wronskian n f.coord z) r :=
  Paper.eq_zero_count_definition (FewInflection.differentiable_wronskian f) hr

end
end ModifiedCartan

