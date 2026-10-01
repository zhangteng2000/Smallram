import ModifiedCartan.JucysMurphyBasisStep

open scoped Classical

namespace ModifiedCartan
noncomputable section

def simpleJucysMurphyBasisZero {A : Type*} [Fintype A] [LinearOrder A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) (hA : Fintype.card A = 0) :
    SimpleJucysMurphyBasis μ h := by
  have hs : μ.cells.card = 0 := h.symm.trans hA
  have hbot : μ = ⊥ := by
    apply YoungDiagram.ext
    exact (Finset.card_eq_zero.mp hs).trans YoungDiagram.cells_bot.symm
  have ht : Fintype.card (StandardYoungTableau μ) = 1 := by
    rw [standardYoungTableau_card, hbot, standardSkewTableauCount_self]
  letI : Subsingleton (StandardYoungTableau μ) := Fintype.card_le_one_iff_subsingleton.mp ht.le
  refine { basis := youngStandardPolytabloidBasis μ
           values := fun _ _ => 0
           values_injective := fun _ _ _ => Subsingleton.elim _ _
           eigen := ?_ }
  intro t i
  have hh : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨i⟩
  omega

end
end ModifiedCartan


