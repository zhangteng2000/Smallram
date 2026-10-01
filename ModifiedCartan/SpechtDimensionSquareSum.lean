import ModifiedCartan.UpwardTableauDimension

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The exact sum of squares of the actual standard-tableau dimensions. -/
theorem sum_youngTableauDimension_sq (n : ℕ) :
    (∑ μ : SizedYoungDiagram n, youngTableauDimension μ.val ^ 2) = n.factorial := by
  induction n with
  | zero =>
    rw [Fintype.sum_unique]
    change youngTableauDimension (⊥ : YoungDiagram) ^ 2 = Nat.factorial 0
    simp
  | succ n ih =>
    calc
      _ = ∑ ν : SizedYoungDiagram (n + 1),
          (∑ μ : SizedYoungDiagram n, if PartitionCovers ν.val μ.val then youngTableauDimension μ.val else 0) *
            youngTableauDimension ν.val := by
        apply Finset.sum_congr rfl
        intro ν _
        rw [pow_two]
        exact congrArg (fun k => k * youngTableauDimension ν.val)
          (youngTableauDimension_rank_rec n ν.val ν.property)
      _ = ∑ ν : SizedYoungDiagram (n + 1), ∑ μ : SizedYoungDiagram n,
          if PartitionCovers ν.val μ.val then youngTableauDimension μ.val * youngTableauDimension ν.val else 0 := by
        simp only [Finset.sum_mul, ite_mul, zero_mul]
      _ = ∑ μ : SizedYoungDiagram n, ∑ ν : SizedYoungDiagram (n + 1),
          if PartitionCovers ν.val μ.val then youngTableauDimension μ.val * youngTableauDimension ν.val else 0 :=
        Finset.sum_comm
      _ = ∑ μ : SizedYoungDiagram n, youngTableauDimension μ.val *
          (∑ ν : SizedYoungDiagram (n + 1), if PartitionCovers ν.val μ.val then youngTableauDimension ν.val else 0) := by
        simp only [Finset.mul_sum, mul_ite, mul_zero]
      _ = ∑ μ : SizedYoungDiagram n, youngTableauDimension μ.val * ((n + 1) * youngTableauDimension μ.val) := by
        apply Finset.sum_congr rfl
        intro μ _
        congr 1
        have hu := youngTableauDimension_upward μ.val
        rw [youngTableauDimension_successors_rank μ.val n μ.property] at hu
        simpa only [μ.property] using hu
      _ = (n + 1) * ∑ μ : SizedYoungDiagram n, youngTableauDimension μ.val ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro μ _
        ring
      _ = (n + 1) * n.factorial := by rw [ih]
      _ = (n + 1).factorial := (Nat.factorial_succ n).symm

theorem sum_specht_finrank_sq (n : ℕ) :
    (∑ μ : SizedYoungDiagram n, Module.finrank ℂ (YoungSpechtModule μ.val) ^ 2) = n.factorial := by
  simp only [← youngTableauDimension_eq_finrank]
  exact sum_youngTableauDimension_sq n

theorem sum_specht_finrank_sq_eq_card_perm (n : ℕ) :
    (∑ μ : SizedYoungDiagram n, Module.finrank ℂ (YoungSpechtModule μ.val) ^ 2) =
      Fintype.card (Equiv.Perm (Fin n)) := by
  rw [Fintype.card_perm, Fintype.card_fin]
  exact sum_specht_finrank_sq n

end
end ModifiedCartan


