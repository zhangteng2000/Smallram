import ModifiedCartan.YoungPermutationSubgroups

open scoped Classical

namespace ModifiedCartan
noncomputable section

def IsPartitionCorner (μ : YoungDiagram) (b : YoungBoxes μ) : Prop :=
  ∀ c : ℕ × ℕ, c ∈ μ → b.val ≤ c → c = b.val

abbrev YoungCorner (μ : YoungDiagram) := {b : YoungBoxes μ // IsPartitionCorner μ b}

def removePartitionBox (μ : YoungDiagram) (b : YoungCorner μ) : YoungDiagram where
  cells := μ.cells.erase b.val.val
  isLowerSet := by
    intro c d hdc hc
    have hc' := Finset.mem_erase.mp hc
    apply Finset.mem_erase.mpr
    refine ⟨?_, μ.isLowerSet hdc hc'.2⟩
    intro he
    subst d
    exact hc'.1 (b.property c hc'.2 hdc)

@[simp] theorem mem_removePartitionBox (μ : YoungDiagram) (b : YoungCorner μ) (c : ℕ × ℕ) :
    c ∈ removePartitionBox μ b ↔ c ≠ b.val.val ∧ c ∈ μ := Finset.mem_erase

theorem removePartitionBox_le (μ : YoungDiagram) (b : YoungCorner μ) :
    removePartitionBox μ b ≤ μ := by
  intro c hc
  exact ((mem_removePartitionBox μ b c).mp hc).2

theorem partitionSize_removePartitionBox (μ : YoungDiagram) (b : YoungCorner μ) :
    partitionSize (removePartitionBox μ b) = partitionSize μ - 1 :=
  Finset.card_erase_of_mem b.val.property

theorem partitionSize_removePartitionBox_add_one (μ : YoungDiagram) (b : YoungCorner μ) :
    partitionSize (removePartitionBox μ b) + 1 = partitionSize μ :=
  Finset.card_erase_add_one b.val.property

theorem youngCorner_rowLen (μ : YoungDiagram) (b : YoungCorner μ) :
    μ.rowLen b.val.val.1 = b.val.val.2 + 1 := by
  have hb : b.val.val.2 < μ.rowLen b.val.val.1 :=
    YoungDiagram.mem_iff_lt_rowLen.mp b.val.property
  have hle : μ.rowLen b.val.val.1 ≤ b.val.val.2 + 1 := by
    by_contra h
    have hc : (b.val.val.1, b.val.val.2 + 1) ∈ μ :=
      YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have he := b.property _ hc ⟨le_rfl, Nat.le_succ _⟩
    have hh := congrArg Prod.snd he
    dsimp at hh
    omega
  omega

theorem youngCorner_colLen (μ : YoungDiagram) (b : YoungCorner μ) :
    μ.colLen b.val.val.2 = b.val.val.1 + 1 := by
  have hb : b.val.val.1 < μ.colLen b.val.val.2 :=
    YoungDiagram.mem_iff_lt_colLen.mp b.val.property
  have hle : μ.colLen b.val.val.2 ≤ b.val.val.1 + 1 := by
    by_contra h
    have hc : (b.val.val.1 + 1, b.val.val.2) ∈ μ :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have he := b.property _ hc ⟨Nat.le_succ _, le_rfl⟩
    have hh := congrArg Prod.fst he
    dsimp at hh
    omega
  omega

theorem youngCorner_row_injective (μ : YoungDiagram) :
    Function.Injective (fun b : YoungCorner μ => b.val.val.1) := by
  intro b c he
  change b.val.val.1 = c.val.val.1 at he
  have hb := youngCorner_rowLen μ b
  have hc := youngCorner_rowLen μ c
  rw [he] at hb
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext he (by omega)

theorem rowLen_removePartitionBox (μ : YoungDiagram) (b : YoungCorner μ) (i : ℕ) :
    (removePartitionBox μ b).rowLen i =
      if i = b.val.val.1 then μ.rowLen i - 1 else μ.rowLen i := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_removePartitionBox,
    YoungDiagram.mem_iff_lt_rowLen]
  change ((i, j) ≠ (b.val.val.1, b.val.val.2) ∧ j < μ.rowLen i) ↔
    j < if i = b.val.val.1 then μ.rowLen i - 1 else μ.rowLen i
  simp only [ne_eq, Prod.mk.injEq]
  by_cases hi : i = b.val.val.1
  · subst i
    simp only [ite_true, true_and, youngCorner_rowLen]
    omega
  · simp [hi]

theorem colLen_removePartitionBox (μ : YoungDiagram) (b : YoungCorner μ) (j : ℕ) :
    (removePartitionBox μ b).colLen j =
      if j = b.val.val.2 then μ.colLen j - 1 else μ.colLen j := by
  apply eq_of_forall_lt_iff
  intro i
  rw [← YoungDiagram.mem_iff_lt_colLen, mem_removePartitionBox,
    YoungDiagram.mem_iff_lt_colLen]
  change ((i, j) ≠ (b.val.val.1, b.val.val.2) ∧ i < μ.colLen j) ↔
    i < if j = b.val.val.2 then μ.colLen j - 1 else μ.colLen j
  simp only [ne_eq, Prod.mk.injEq]
  by_cases hj : j = b.val.val.2
  · subst j
    simp only [ite_true, and_true, youngCorner_colLen]
    omega
  · simp [hj]

end
end ModifiedCartan


