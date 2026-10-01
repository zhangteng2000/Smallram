import ModifiedCartan.RowColumnSpechtCharacters
import ModifiedCartan.SpechtCharacterLabels

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem spechtCharacterOn_single_row {A : Type*} [Fintype A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (hr : ∀ a : YoungBoxes μ, a.val.1 = 0) (g : Equiv.Perm A) :
    spechtCharacterOn μ h g = 1 := by
  let e : A ≃ YoungBoxes μ := (Fintype.equivFinOfCardEq h).trans (youngBoxNumbering μ).symm
  rw [spechtCharacterOn_eq_young μ h e]
  exact youngSpecht_character_single_row μ hr _

theorem spechtCharacterOn_single_column {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (hc : ∀ a : YoungBoxes μ, a.val.2 = 0) (g : Equiv.Perm A) :
    spechtCharacterOn μ h g = ((Equiv.Perm.sign g : ℤ) : ℂ) := by
  let e : A ≃ YoungBoxes μ := (Fintype.equivFinOfCardEq h).trans (youngBoxNumbering μ).symm
  rw [spechtCharacterOn_eq_young μ h e, youngSpecht_character_single_column μ hc]
  change ((Equiv.Perm.sign (e.permCongr g) : ℤ) : ℂ) = _
  rw [Equiv.Perm.sign_permCongr]

theorem spechtCharacterOn_row_column_ne {A : Type*} [Fintype A] [DecidableEq A]
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ) (hν : Fintype.card A = partitionSize ν)
    (hr : ∀ a : YoungBoxes μ, a.val.1 = 0) (hc : ∀ a : YoungBoxes ν, a.val.2 = 0)
    (a b : A) (hab : a ≠ b) : spechtCharacterOn μ hμ ≠ spechtCharacterOn ν hν := by
  intro he
  have hh := congrFun he (Equiv.swap a b)
  rw [spechtCharacterOn_single_row μ hμ hr, spechtCharacterOn_single_column ν hν hc,
    Equiv.Perm.sign_swap hab] at hh
  norm_num at hh

end
end ModifiedCartan


