import ModifiedCartan.ColumnPartitions
import ModifiedCartan.PartitionMinorDerivative
import Mathlib.GroupTheory.Perm.Fin

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

theorem columnPartition_rowLen (q r : ℕ) :
    (columnPartition q).rowLen r = if r < q then 1 else 0 := by
  apply eq_of_forall_lt_iff
  intro k
  rw [← YoungDiagram.mem_iff_lt_rowLen]
  change ((r, k) ∈ Finset.range q ×ˢ {0}) ↔ k < if r < q then 1 else 0
  simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton]
  split_ifs with hr <;> omega

theorem columnPartition_fits {n q : ℕ} (hq : q ≤ n + 1) :
    PartitionFits n (columnPartition q) := by
  rw [PartitionFits, columnPartition_rowLen, ite_eq_right (by omega)]

theorem columnPartition_minorOrders {n : ℕ} (i k : Fin (n + 1)) :
    partitionMinorOrders n (columnPartition (n + 1 - i.val)) k =
      if k.val < i.val then k.val else k.val + 1 := by
  rw [partitionMinorOrders, columnPartition_rowLen]
  split_ifs <;> have hk := k.isLt <;> have hi := i.isLt <;> omega

/-- Cycling the replaced row to the end produces the increasing column
    partition orders. This fixes the sign in manuscript `eq:productformula`. -/
theorem columnPartition_order_cycle {n : ℕ} (i k : Fin (n + 1)) :
    Function.update (fun j : Fin (n + 1) => j.val) i (n + 1)
      (Fin.cycleIcc i (Fin.last n) k) =
        partitionMinorOrders n (columnPartition (n + 1 - i.val)) k := by
  rw [columnPartition_minorOrders]
  by_cases hki : k < i
  · rw [Fin.cycleIcc_of_lt hki, Function.update_of_ne hki.ne,
      ite_eq_left (show k.val < i.val from hki)]
  · by_cases hlast : k = Fin.last n
    · subst k
      rw [Fin.cycleIcc_of_last (Fin.le_last i), Function.update_self,
        ite_eq_right (by have hi := i.isLt; simp only [Fin.val_last]; omega)]
      rfl
    · have hkl : k < Fin.last n := lt_of_le_of_ne (Fin.le_last k) hlast
      have hval : (k + 1).val = k.val + 1 := Fin.val_add_one_of_lt hkl
      have hne : k + 1 ≠ i := by
        intro hh
        have he := congrArg Fin.val hh
        rw [hval] at he
        have hge : i.val ≤ k.val := le_of_not_gt hki
        omega
      rw [Fin.cycleIcc_of_ge_of_lt (le_of_not_gt hki) hkl,
        Function.update_of_ne hne, ite_eq_right (show ¬ k.val < i.val from hki), hval]

end
end ModifiedCartan

#print axioms ModifiedCartan.columnPartition_order_cycle