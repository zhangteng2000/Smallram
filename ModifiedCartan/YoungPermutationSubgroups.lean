import ModifiedCartan.SkewTableaux
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.RepresentationTheory.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Permutations preserving every fiber of a function. -/
def permutationFiberSubgroup {A B : Type*} (f : A → B) : Subgroup (Equiv.Perm A) where
  carrier := {g | ∀ a, f (g a) = f a}
  one_mem' := by intro a; rfl
  mul_mem' := by
    intro g h hg hh a
    exact (hg (h a)).trans (hh a)
  inv_mem' := by
    intro g hg a
    simpa using (hg (g⁻¹ a)).symm

@[simp] theorem mem_permutationFiberSubgroup {A B : Type*} (f : A → B)
    (g : Equiv.Perm A) : g ∈ permutationFiberSubgroup f ↔ ∀ a, f (g a) = f a := Iff.rfl

abbrev YoungBoxes (μ : YoungDiagram) := {c : ℕ × ℕ // c ∈ μ.cells}

def youngRowSubgroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (YoungBoxes μ)) :=
  permutationFiberSubgroup fun c => c.val.1

def youngColumnSubgroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (YoungBoxes μ)) :=
  permutationFiberSubgroup fun c => c.val.2

theorem young_perm_eq_one_of_row_column (μ : YoungDiagram)
    (g : Equiv.Perm (YoungBoxes μ)) (hr : g ∈ youngRowSubgroup μ)
    (hc : g ∈ youngColumnSubgroup μ) : g = 1 := by
  apply Equiv.ext
  intro c
  apply Subtype.ext
  exact Prod.ext (hr c) (hc c)

theorem young_row_column_inf (μ : YoungDiagram) :
    youngRowSubgroup μ ⊓ youngColumnSubgroup μ = ⊥ := by
  apply le_antisymm
  · intro g hg
    exact young_perm_eq_one_of_row_column μ g hg.1 hg.2
  · exact bot_le

/-- Row-equivalence classes of bijective fillings; the alphabet is the box set. -/
abbrev YoungTabloid (μ : YoungDiagram) :=
  Equiv.Perm (YoungBoxes μ) ⧸ youngRowSubgroup μ

def youngTabloid (μ : YoungDiagram) (g : Equiv.Perm (YoungBoxes μ)) : YoungTabloid μ :=
  QuotientGroup.mk g

theorem young_tabloid_eq_iff (μ : YoungDiagram) (g h : Equiv.Perm (YoungBoxes μ)) :
    youngTabloid μ g = youngTabloid μ h ↔ g⁻¹ * h ∈ youngRowSubgroup μ :=
  QuotientGroup.eq

theorem young_column_tabloid_injective (μ : YoungDiagram) :
    Function.Injective (fun g : youngColumnSubgroup μ => youngTabloid μ g.val) := by
  intro g h heq
  apply Subtype.ext
  apply eq_of_inv_mul_eq_one
  apply young_perm_eq_one_of_row_column μ
  · exact (young_tabloid_eq_iff μ g h).mp heq
  · exact (youngColumnSubgroup μ).mul_mem ((youngColumnSubgroup μ).inv_mem g.property) h.property

end
end ModifiedCartan


