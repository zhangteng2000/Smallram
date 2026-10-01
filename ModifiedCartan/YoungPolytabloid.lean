import ModifiedCartan.YoungPermutationSubgroups
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RepresentationTheory.Subrepresentation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- The permutation module on row tabloids of the actual Young diagram. -/
abbrev YoungPermutationModule (μ : YoungDiagram) := ℂ[YoungTabloid μ]

instance (μ : YoungDiagram) : FiniteDimensional ℂ (YoungPermutationModule μ) :=
  (MonoidAlgebra.basis (YoungTabloid μ) ℂ).finiteDimensional_of_finite

def youngTabloidRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (YoungBoxes μ)) (YoungPermutationModule μ) :=
  Representation.ofMulAction ℂ (Equiv.Perm (YoungBoxes μ)) (YoungTabloid μ)

/-- The ordinary sign character, cast to the complex numbers. -/
def youngPermutationSign (μ : YoungDiagram) : Equiv.Perm (YoungBoxes μ) →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

@[simp] theorem youngPermutationSign_one (μ : YoungDiagram) :
    youngPermutationSign μ 1 = 1 := map_one _

theorem youngPermutationSign_mul (μ : YoungDiagram) (g h : Equiv.Perm (YoungBoxes μ)) :
    youngPermutationSign μ (g * h) = youngPermutationSign μ g * youngPermutationSign μ h :=
  map_mul _ _ _

/-- The usual polytabloid of the identity filling: signed sum over column permutations. -/
def youngPolytabloid (μ : YoungDiagram) : YoungPermutationModule μ :=
  ∑ c : youngColumnSubgroup μ,
    MonoidAlgebra.single (youngTabloid μ c.val) (youngPermutationSign μ c.val)

theorem youngPolytabloid_column_coefficient (μ : YoungDiagram) (c : youngColumnSubgroup μ) :
    (youngPolytabloid μ).coeff (youngTabloid μ c.val) = youngPermutationSign μ c.val := by
  simp only [youngPolytabloid, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b hb hbc
    exact Finsupp.single_eq_of_ne' (fun h => hbc (young_column_tabloid_injective μ h))
  · simp

theorem youngPolytabloid_identity_coefficient (μ : YoungDiagram) :
    (youngPolytabloid μ).coeff (youngTabloid μ 1) = 1 := by
  simpa using youngPolytabloid_column_coefficient μ (1 : youngColumnSubgroup μ)

theorem youngPolytabloid_ne_zero (μ : YoungDiagram) : youngPolytabloid μ ≠ 0 := by
  intro h
  have hc := youngPolytabloid_identity_coefficient μ
  rw [h] at hc
  simpa using hc

end
end ModifiedCartan


