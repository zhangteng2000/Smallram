import ModifiedCartan.ColoringDegrees
import ModifiedCartan.FinitePermutationCharacter

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

attribute [local instance] coloringPermutationAction

abbrev WeightColoring (A : Type*) [Fintype A] {B : Type*} (d : B →₀ ℕ) :=
  {f : A → B // coloringDegree f = d}

instance weightColoringAction (A : Type*) [Fintype A] {B : Type*} (d : B →₀ ℕ) :
    MulAction (Equiv.Perm A) (WeightColoring A d) where
  smul σ f := ⟨σ • f.val, (coloringDegree_comp_equiv f.val σ.symm).trans f.property⟩
  one_smul f := Subtype.ext rfl
  mul_smul σ τ f := Subtype.ext rfl

def weightColoringRepresentation (A : Type*) [Fintype A] {B : Type*} (d : B →₀ ℕ) :
    Representation ℂ (Equiv.Perm A) ℂ[WeightColoring A d] :=
  Representation.ofMulAction ℂ (Equiv.Perm A) (WeightColoring A d)

theorem weightColoring_fixed_iff {A B : Type*} [Fintype A] (d : B →₀ ℕ)
    (σ : Equiv.Perm A) (f : WeightColoring A d) :
    σ • f = f ↔ ∀ a, f.val (σ a) = f.val a := by
  rw [Subtype.ext_iff]
  exact coloring_fixedBy_iff σ f.val

theorem weightColoringRepresentation_character {A B : Type*} [Fintype A] [Fintype B]
    (d : B →₀ ℕ) (σ : Equiv.Perm A) :
    (weightColoringRepresentation A d).character σ =
      ∑ f : WeightColoring A d, if ∀ a, f.val (σ a) = f.val a then (1 : ℂ) else 0 := by
  rw [weightColoringRepresentation, finitePermutationRepresentation_character]
  simp only [weightColoring_fixed_iff]

end
end ModifiedCartan


