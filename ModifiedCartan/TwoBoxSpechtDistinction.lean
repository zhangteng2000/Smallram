import ModifiedCartan.RowColumnFiniteCharacters
import ModifiedCartan.CornerPredecessors

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem two_box_unique_corner_characters_ne {A : Type*} [Fintype A] [DecidableEq A]
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ) (hν : Fintype.card A = partitionSize ν)
    (b : YoungCorner μ) (c : YoungCorner ν)
    (hb : ∀ d : YoungCorner μ, d = b) (hc : ∀ d : YoungCorner ν, d = c)
    (hbcoord : b.val.val = (0, 1)) (hccoord : c.val.val = (1, 0)) :
    spechtCharacterOn μ hμ ≠ spechtCharacterOn ν hν := by
  have hrow (x : YoungBoxes μ) : x.val.1 = 0 := by
    have hh := (mem_iff_le_unique_corner μ b hb x.val).mp x.property
    rw [hbcoord] at hh
    exact Nat.eq_zero_of_le_zero hh.1
  have hcol (x : YoungBoxes ν) : x.val.2 = 0 := by
    have hh := (mem_iff_le_unique_corner ν c hc x.val).mp x.property
    rw [hccoord] at hh
    exact Nat.eq_zero_of_le_zero hh.2
  have hzero : (0, 0) ∈ μ := μ.isLowerSet ⟨Nat.zero_le _, Nat.zero_le _⟩ b.val.property
  let o : YoungBoxes μ := ⟨(0, 0), hzero⟩
  have hob : o ≠ b.val := by
    intro he
    have hh := congrArg (fun x : YoungBoxes μ => x.val) he
    change (0, 0) = b.val.val at hh
    rw [hbcoord] at hh
    norm_num at hh
  let e : YoungBoxes μ ≃ A := (youngBoxNumbering μ).trans (Fintype.equivFinOfCardEq hμ).symm
  exact spechtCharacterOn_row_column_ne μ ν hμ hν hrow hcol (e o) (e b.val)
    (fun he => hob (e.injective he))

end
end ModifiedCartan


