import ModifiedCartan.YoungPermutationSubgroups

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def garnirLeft (μ : YoungDiagram) (r j : ℕ) : Finset (YoungBoxes μ) :=
  Finset.univ.filter (fun b => b.val.2 = j ∧ r ≤ b.val.1)

def garnirRight (μ : YoungDiagram) (r j : ℕ) : Finset (YoungBoxes μ) :=
  Finset.univ.filter (fun b => b.val.2 = j + 1 ∧ b.val.1 ≤ r)

def garnirBelt (μ : YoungDiagram) (r j : ℕ) : Finset (YoungBoxes μ) :=
  garnirLeft μ r j ∪ garnirRight μ r j

@[simp] theorem mem_garnirLeft (μ : YoungDiagram) (r j : ℕ) (b : YoungBoxes μ) :
    b ∈ garnirLeft μ r j ↔ b.val.2 = j ∧ r ≤ b.val.1 := by simp [garnirLeft]

@[simp] theorem mem_garnirRight (μ : YoungDiagram) (r j : ℕ) (b : YoungBoxes μ) :
    b ∈ garnirRight μ r j ↔ b.val.2 = j + 1 ∧ b.val.1 ≤ r := by simp [garnirRight]

def garnirLeftEquiv (μ : YoungDiagram) (r j : ℕ) :
    Fin (μ.colLen j - r) ≃ (garnirLeft μ r j) where
  toFun k := ⟨⟨(r + k.val, j), YoungDiagram.mem_iff_lt_colLen.mpr (by have := k.isLt; omega)⟩,
    (mem_garnirLeft μ r j _).mpr ⟨rfl, by dsimp; omega⟩⟩
  invFun b := ⟨b.val.val.1 - r, by
    have hb := (mem_garnirLeft μ r j b.val).mp b.property
    have hh := YoungDiagram.mem_iff_lt_colLen.mp b.val.property
    rw [hb.1] at hh
    have hr : r ≤ b.val.val.1 := hb.2
    change b.val.val.1 - r < μ.colLen j - r
    exact Nat.sub_lt_sub_right hr hh⟩
  left_inv k := by
    apply Fin.ext
    dsimp
    omega
  right_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change r + (b.val.val.1 - r) = b.val.val.1
      have hb := (mem_garnirLeft μ r j b.val).mp b.property
      omega
    · exact ((mem_garnirLeft μ r j b.val).mp b.property).1.symm

def garnirRightEquiv (μ : YoungDiagram) (r j : ℕ) (hcell : (r, j + 1) ∈ μ) :
    Fin (r + 1) ≃ (garnirRight μ r j) where
  toFun k := ⟨⟨(k.val, j + 1), YoungDiagram.mem_iff_lt_colLen.mpr (by
      have hh := YoungDiagram.mem_iff_lt_colLen.mp hcell
      have hk := k.isLt
      omega)⟩, (mem_garnirRight μ r j _).mpr ⟨rfl, by have := k.isLt; dsimp; omega⟩⟩
  invFun b := ⟨b.val.val.1, by
    have hb := (mem_garnirRight μ r j b.val).mp b.property
    omega⟩
  left_inv k := rfl
  right_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((mem_garnirRight μ r j b.val).mp b.property).1.symm

theorem garnirLeft_card (μ : YoungDiagram) (r j : ℕ) :
    (garnirLeft μ r j).card = μ.colLen j - r := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (garnirLeftEquiv μ r j), Fintype.card_fin]

theorem garnirRight_card (μ : YoungDiagram) (r j : ℕ) (hcell : (r, j + 1) ∈ μ) :
    (garnirRight μ r j).card = r + 1 := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (garnirRightEquiv μ r j hcell), Fintype.card_fin]

theorem garnirLeft_disjoint_right (μ : YoungDiagram) (r j : ℕ) :
    Disjoint (garnirLeft μ r j) (garnirRight μ r j) := by
  apply Finset.disjoint_left.mpr
  intro b hl hr
  have hl' := (mem_garnirLeft μ r j b).mp hl
  have hr' := (mem_garnirRight μ r j b).mp hr
  omega

/-- A Garnir belt has one more box than the height of its left column. -/
theorem garnirBelt_card (μ : YoungDiagram) (r j : ℕ) (hcell : (r, j + 1) ∈ μ) :
    (garnirBelt μ r j).card = μ.colLen j + 1 := by
  rw [garnirBelt, Finset.card_union_of_disjoint (garnirLeft_disjoint_right μ r j),
    garnirLeft_card, garnirRight_card μ r j hcell]
  have hr : r < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (Nat.le_succ j) hcell)
  omega

end
end ModifiedCartan


