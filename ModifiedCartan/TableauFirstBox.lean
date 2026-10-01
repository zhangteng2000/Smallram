import ModifiedCartan.SkewTableaux

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

/-- Every proper predecessor of the box with label zero lies in the inner diagram. -/
theorem StandardSkewTableau.predecessor_mem_of_label_zero {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (c : SkewPartitionBoxes ν μ)
    (hc : (T.val c : ℕ) = 0) {d : ℕ × ℕ} (hd : d ≤ c.val)
    (hne : d ≠ c.val) : d ∈ μ := by
  by_contra hnot
  have hdν : d ∈ ν := ν.isLowerSet hd (Finset.mem_sdiff.mp c.property).1
  let d' : SkewPartitionBoxes ν μ := ⟨d, Finset.mem_sdiff.mpr ⟨hdν, hnot⟩⟩
  have hlt : d' < c := lt_iff_le_and_ne.mpr
    ⟨hd, fun heq => hne (congrArg Subtype.val heq)⟩
  have hval : (T.val d' : ℕ) < (T.val c : ℕ) := T.property hlt
  omega

theorem StandardSkewTableau.column_eq_rowLen_of_label_zero {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (c : SkewPartitionBoxes ν μ)
    (hc : (T.val c : ℕ) = 0) : c.val.2 = μ.rowLen c.val.1 := by
  have hnot : ¬ c.val.2 < μ.rowLen c.val.1 := by
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    exact (Finset.mem_sdiff.mp c.property).2
  by_contra heq
  have hlt : μ.rowLen c.val.1 < c.val.2 := by omega
  have hm := T.predecessor_mem_of_label_zero c hc
    (d := (c.val.1, μ.rowLen c.val.1)) ⟨le_rfl, hlt.le⟩ (by
      intro hh
      have := congrArg Prod.snd hh
      omega)
  rw [YoungDiagram.mem_iff_lt_rowLen] at hm
  exact lt_irrefl _ hm

theorem StandardSkewTableau.addable_of_label_zero {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (c : SkewPartitionBoxes ν μ)
    (hc : (T.val c : ℕ) = 0) : AddablePartitionRow μ c.val.1 := by
  by_cases hr : c.val.1 = 0
  · exact Or.inl hr
  · right
    have hm := T.predecessor_mem_of_label_zero c hc
      (d := (c.val.1 - 1, c.val.2)) ⟨by omega, le_rfl⟩ (by
        intro hh
        have := congrArg Prod.fst hh
        omega)
    rw [YoungDiagram.mem_iff_lt_rowLen] at hm
    rw [T.column_eq_rowLen_of_label_zero c hc] at hm
    exact hm

theorem StandardSkewTableau.addBox_le_of_label_zero {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (hμν : μ ≤ ν) (c : SkewPartitionBoxes ν μ)
    (hc : (T.val c : ℕ) = 0) :
    addPartitionBox μ c.val.1 (T.addable_of_label_zero c hc) ≤ ν := by
  intro d hd
  rcases (mem_addPartitionBox _ _ _ _).mp hd with hd | hd
  · rw [hd, ← T.column_eq_rowLen_of_label_zero c hc]
    exact (Finset.mem_sdiff.mp c.property).1
  · exact hμν hd

/-- The first box is selected by the actual bijective filling. -/
def StandardSkewTableau.firstBox {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (h : 0 < (ν.cells \ μ.cells).card) :
    SkewPartitionBoxes ν μ := T.val.symm ⟨0, h⟩

@[simp] theorem StandardSkewTableau.firstBox_label {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (h : 0 < (ν.cells \ μ.cells).card) :
    (T.val (T.firstBox h) : ℕ) = 0 := by
  simp [StandardSkewTableau.firstBox]

theorem StandardSkewTableau.firstBox_addable {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (h : 0 < (ν.cells \ μ.cells).card) :
    AddablePartitionRow μ (T.firstBox h).val.1 :=
  T.addable_of_label_zero _ (T.firstBox_label h)

end
end ModifiedCartan


