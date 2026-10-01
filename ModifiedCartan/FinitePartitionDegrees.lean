import ModifiedCartan.YoungRowDegrees

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def partitionFiniteDegree (m : ℕ) (μ : YoungDiagram) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin m => μ.rowLen i.val)

theorem partitionFiniteDegree_apply (m : ℕ) (μ : YoungDiagram) (i : Fin m) :
    partitionFiniteDegree m μ i = μ.rowLen i.val := rfl

theorem partition_row_lt_of_height_le {m : ℕ} (μ : YoungDiagram) (hm : μ.colLen 0 ≤ m)
    (b : YoungBoxes μ) : b.val.1 < m :=
  (YoungDiagram.mem_iff_lt_colLen.mp b.property).trans_le
    ((μ.colLen_anti 0 b.val.2 (Nat.zero_le _)).trans hm)

def youngFiniteRowsEquiv {m : ℕ} (μ : YoungDiagram) (hm : μ.colLen 0 ≤ m) :
    YoungBoxes μ ≃ Σ i : Fin m, Fin (μ.rowLen i.val) where
  toFun b := ⟨⟨b.val.1, partition_row_lt_of_height_le μ hm b⟩,
    ⟨b.val.2, YoungDiagram.mem_iff_lt_rowLen.mp b.property⟩⟩
  invFun p := ⟨(p.1.val, p.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr p.2.isLt⟩
  left_inv b := rfl
  right_inv p := rfl

theorem finiteColorWeight_partitionFiniteDegree {m : ℕ} (μ : YoungDiagram)
    (hm : μ.colLen 0 ≤ m) :
    finiteColorWeight (partitionFiniteDegree m μ) = partitionRowWeight μ := by
  have h := (youngFiniteRowsEquiv μ hm).sum_comp (fun p => p.1.val)
  change (∑ b : YoungBoxes μ, b.val.1) =
    ∑ p : (Σ i : Fin m, Fin (μ.rowLen i.val)), p.1.val at h
  simpa [finiteColorWeight, partitionFiniteDegree, partitionRowWeight,
    Fintype.sum_sigma, mul_comm] using h.symm

theorem partitionFiniteDegree_mapDomain {m : ℕ} (μ : YoungDiagram) (hm : μ.colLen 0 ≤ m) :
    Finsupp.mapDomain Fin.val (partitionFiniteDegree m μ) = partitionRowDegree μ := by
  ext r
  rw [partitionRowDegree_apply]
  by_cases hr : r < m
  · have h := Finsupp.mapDomain_apply (f := Fin.val) Fin.val_injective
      (partitionFiniteDegree m μ) (⟨r, hr⟩ : Fin m)
    exact h
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by
      rintro ⟨i, hi⟩
      exact hr (hi ▸ i.isLt))]
    symm
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hrow : r < μ.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr hp)
    exact hr (hrow.trans_le hm)

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteColorWeight_partitionFiniteDegree
#print axioms ModifiedCartan.partitionFiniteDegree_mapDomain
