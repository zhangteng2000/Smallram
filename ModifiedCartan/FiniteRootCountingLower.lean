import ModifiedCartan.WeightedZeroCounting

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_zero_analyticMultiplicity_pos {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hn : ∃ w, f w ≠ 0) {z : ℂ} (hz : f z = 0) :
    0 < (analyticOrderAt f z).toNat := by
  have ht : analyticOrderAt f z ≠ ⊤ := by
    intro ht
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (fun w => hf.analyticAt w)).mp ht
    obtain ⟨w, hw⟩ := hn
    exact hw (congrFun he w)
  have h0 : analyticOrderAt f z ≠ 0 := by
    intro h0
    exact ((hf.analyticAt z).analyticOrderAt_eq_zero.mp h0) hz
  cases ha : analyticOrderAt f z using ENat.recTopCoe <;> simp_all
  omega

theorem finite_distinct_roots_logCounting_lower {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hn : ∃ w, f w ≠ 0) {N : ℕ} (z : Fin N → ℂ)
    (hz : Function.Injective z) (hroot : ∀ j, f (z j) = 0)
    {R : ℝ} (hR : 1 ≤ R) :
    (∑ j : Fin N, rootCountingWeight R (z j)) ≤
      ValueDistribution.logCounting f (0 : WithTop ℂ) R := by
  classical
  let e : Fin N → entireZeroCopies f := fun j =>
    ⟨z j, ⟨0, entire_zero_analyticMultiplicity_pos hf hn (hroot j)⟩⟩
  have he : Function.Injective e := by
    intro i j hij
    exact hz (congrArg (fun a : entireZeroCopies f => a.1) hij)
  have hs : Summable (fun a : entireZeroCopies f => rootCountingWeight R a.1) :=
    summable_of_hasFiniteSupport (zeroCopy_weight_hasFiniteSupport hf (zero_le_one.trans hR))
  rw [entire_logCounting_eq_tsum_weights hf (zero_lt_one.trans_le hR)]
  calc
    (∑ j : Fin N, rootCountingWeight R (z j)) =
        ∑ a ∈ Finset.univ.image e, rootCountingWeight R a.1 := by
      rw [Finset.sum_image (fun _ _ _ _ hij => he hij)]
    _ ≤ _ := hs.sum_le_tsum _ (fun a _ => rootCountingWeight_nonneg hR a.1)

theorem logCounting_lower_of_exponentially_spaced_roots {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hn : ∃ w, f w ≠ 0) {z : ℕ → ℂ}
    (hz : Function.Injective z) (hroot : ∀ j, f (z j) = 0)
    (hz0 : ∀ j, z j ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ j, ‖z j‖ ≤ Real.exp ((j : ℝ) + b)) {R : ℝ} (hR : 1 ≤ R) :
    (Real.log R) ^ 2 / 2 - b * Real.log R - 1 ≤
      ValueDistribution.logCounting f (0 : WithTop ℂ) R := by
  let x := Real.log R
  let N := Nat.floor x
  have hx : 0 ≤ x := Real.log_nonneg hR
  have hfloor : (N : ℝ) ≤ x := Nat.floor_le hx
  have hfloor' : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hsum (M : ℕ) :
      (∑ j ∈ Finset.range M, (x - ((j : ℝ) + b))) =
        (M : ℝ) * x - (M : ℝ) * ((M : ℝ) - 1) / 2 - (M : ℝ) * b := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hl := finite_distinct_roots_logCounting_lower hf hn (fun j : Fin N => z j)
    (hz.comp Fin.val_injective) (fun j => hroot j) hR
  have hw (j : Fin N) : x - ((j : ℝ) + b) ≤ rootCountingWeight R (z j) := by
    rw [rootCountingWeight, if_neg (hz0 j)]
    have hlog : Real.log ‖z j‖ ≤ (j : ℝ) + b := by
      simpa only [Real.log_exp] using Real.log_le_log (norm_pos_iff.mpr (hz0 j)) (hbound j)
    have hpos : Real.log (R / ‖z j‖) ≤ Real.posLog (R / ‖z j‖) := le_max_right _ _
    rw [Real.log_div (ne_of_gt (zero_lt_one.trans_le hR)) (norm_ne_zero_iff.mpr (hz0 j))] at hpos
    dsimp only [x]
    linarith
  have hmain := (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hw j)).trans hl
  rw [Fin.sum_univ_eq_sum_range (fun j => x - ((j : ℝ) + b)), hsum] at hmain
  have hsq : (x - (N : ℝ)) ^ 2 ≤ 1 := by nlinarith
  have hp := mul_nonneg hb (sub_nonneg.mpr hfloor)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  change x ^ 2 / 2 - b * x - 1 ≤ _
  nlinarith

end ModifiedCartan
#print axioms ModifiedCartan.logCounting_lower_of_exponentially_spaced_roots
