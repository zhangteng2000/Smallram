import ModifiedCartan.ColumnPartitionMinorOrders
import ModifiedCartan.PolynomialAlternantTranslation

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Increasing orders after replacing row j by a row of order k>n. -/
def sortedReplacementOrders (n : ℕ) (j : Fin (n + 1)) (k : ℕ) (i : Fin (n + 1)) : ℕ :=
  if i.val < j.val then i.val else if i.val < n then i.val + 1 else k

theorem sortedReplacementOrders_strictMono {n k : ℕ} (j : Fin (n + 1)) (hk : n < k) :
    StrictMono (sortedReplacementOrders n j k) := by
  intro r s hrs
  have hr := r.isLt
  have hs := s.isLt
  have hj := j.isLt
  have hlt : r.val < s.val := hrs
  simp only [sortedReplacementOrders]
  split_ifs <;> omega

theorem sortedReplacementOrders_cycle {n : ℕ} (j i : Fin (n + 1)) (k : ℕ) :
    Function.update (fun r : Fin (n + 1) => r.val) j k
      (Fin.cycleIcc j (Fin.last n) i) = sortedReplacementOrders n j k i := by
  rw [sortedReplacementOrders]
  by_cases hij : i < j
  · rw [Fin.cycleIcc_of_lt hij, Function.update_of_ne hij.ne,
      ite_eq_left (show i.val < j.val from hij)]
  · by_cases hlast : i = Fin.last n
    · subst i
      rw [Fin.cycleIcc_of_last (Fin.le_last j), Function.update_self,
        ite_eq_right (by have hi := j.isLt; simp only [Fin.val_last]; omega)]
      simp only [Fin.val_last, lt_self_iff_false, ite_false]
    · have hil : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hlast
      have hval : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt hil
      have hne : i + 1 ≠ j := by
        intro hh
        have he := congrArg Fin.val hh
        rw [hval] at he
        have hge : j.val ≤ i.val := le_of_not_gt hij
        omega
      rw [Fin.cycleIcc_of_ge_of_lt (le_of_not_gt hij) hil,
        Function.update_of_ne hne, ite_eq_right (show ¬i.val < j.val from hij),
        ite_eq_left (show i.val < n from hil), hval]

theorem exists_partitionMinorOrders {n : ℕ} (e : Fin (n + 1) → ℕ) (he : StrictMono e) :
    ∃ μ : YoungDiagram, PartitionFits n μ ∧ partitionMinorOrders n μ = e := by
  obtain ⟨μ, hf, hm⟩ := exists_partitionAlternantExponent
    (fun i : Fin (n + 1) => e i.rev) (fun _ _ hij => he (Fin.rev_strictAnti hij))
  refine ⟨μ, (partitionFits_iff_height_le μ).mpr hf, ?_⟩
  funext i
  have hi := congrFun hm i.rev
  rw [partitionAlternantExponent_rev, Fin.rev_rev] at hi
  exact hi

theorem sum_partitionMinorOrders {n : ℕ} {μ : YoungDiagram} (hf : PartitionFits n μ) :
    (∑ i, partitionMinorOrders n μ i) = (∑ i : Fin (n + 1), i.val) + partitionSize μ := by
  simp only [partitionMinorOrders, Finset.sum_add_distrib]
  rw [partitionSize_eq_sum_rowLen hf]
  congr 1
  have he := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n + 1)))
    (fun i : Fin (n + 1) => μ.rowLen i.val)
  simpa only [Fin.revPerm_apply, Fin.val_rev, Nat.succ_sub_succ_eq_sub] using he

/-- The partition attached to the replaced row has exactly k-j boxes,
    as required in manuscript `prop:initial-basis`. -/
theorem sortedReplacementOrders_partitionSize {n k : ℕ} (j : Fin (n + 1))
    {μ : YoungDiagram} (hf : PartitionFits n μ)
    (he : partitionMinorOrders n μ = sortedReplacementOrders n j k) :
    partitionSize μ = k - j.val := by
  have hs : (∑ i, partitionMinorOrders n μ i) =
      ∑ i, Function.update (fun r : Fin (n + 1) => r.val) j k i := by
    rw [← Equiv.sum_comp (Fin.cycleIcc j (Fin.last n))
      (Function.update (fun r : Fin (n + 1) => r.val) j k)]
    apply Finset.sum_congr rfl
    intro i _
    rw [congrFun he i, sortedReplacementOrders_cycle]
  rw [sum_partitionMinorOrders hf, Finset.sum_update_of_mem (Finset.mem_univ j)] at hs
  have hb := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
    (fun i => i.val) (Finset.mem_univ j)
  rw [Finset.sdiff_singleton_eq_erase] at hs
  omega

end
end ModifiedCartan

#print axioms ModifiedCartan.sortedReplacementOrders_partitionSize