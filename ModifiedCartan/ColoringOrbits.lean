import ModifiedCartan.ColoringMultisets
import ModifiedCartan.WeightedBurnside
import Mathlib.Data.Fintype.Vector

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The finite symmetric group acts on colorings by permuting positions. -/
@[instance_reducible]
def coloringPermutationAction (A B : Type*) : MulAction (Equiv.Perm A) (A → B) where
  smul σ f a := f (σ.symm a)
  one_smul f := rfl
  mul_smul σ τ f := rfl

attribute [local instance] coloringPermutationAction

abbrev ColoringOrbit (A B : Type*) := Quotient (MulAction.orbitRel (Equiv.Perm A) (A → B))

theorem coloringMultiset_smul {A B : Type*} [Fintype A] (σ : Equiv.Perm A) (f : A → B) :
    coloringMultiset (σ • f) = coloringMultiset f :=
  Subtype.ext (coloringMultiset_comp_equiv f σ.symm)

def coloringOrbitMultiset {A B : Type*} [Fintype A] : ColoringOrbit A B → Sym B (Fintype.card A) :=
  Quotient.lift coloringMultiset (by
    intro f g h
    obtain ⟨σ, rfl⟩ := h
    exact coloringMultiset_smul σ g)

theorem coloringOrbitMultiset_bijective {A B : Type*} [Fintype A] :
    Function.Bijective (coloringOrbitMultiset (A := A) (B := B)) := by
  constructor
  · intro q r h
    induction q using Quotient.inductionOn with | h f =>
      induction r using Quotient.inductionOn with | h g =>
        obtain ⟨σ, hσ⟩ := (coloringMultiset_eq_iff_permutation f g).mp h
        apply Quotient.sound
        refine ⟨σ⁻¹, ?_⟩
        change g ∘ ((σ⁻¹)⁻¹ : Equiv.Perm A) = f
        simpa only [inv_inv] using hσ
  · intro s
    obtain ⟨f, hf⟩ := coloringMultiset_surjective (A := A) s
    exact ⟨Quotient.mk _ f, hf⟩

def coloringOrbitEquivMultiset {A B : Type*} [Fintype A] :
    ColoringOrbit A B ≃ Sym B (Fintype.card A) :=
  Equiv.ofBijective coloringOrbitMultiset coloringOrbitMultiset_bijective

theorem coloringOrbitEquivMultiset_mk {A B : Type*} [Fintype A] (f : A → B) :
    coloringOrbitEquivMultiset (Quotient.mk _ f) = coloringMultiset f := rfl

theorem coloring_fixedBy_iff {A B : Type*} (σ : Equiv.Perm A) (f : A → B) :
    f ∈ MulAction.fixedBy (A → B) σ ↔ ∀ a, f (σ a) = f a := by
  change (f ∘ (σ⁻¹ : Equiv.Perm A) = f) ↔ _
  constructor
  · intro h a
    have ha := congrFun h (σ a)
    exact ha.symm.trans (congrArg f (σ.symm_apply_apply a))
  · intro h
    funext a
    exact (h (σ⁻¹ a)).symm.trans (congrArg f (σ.apply_symm_apply a))

end
end ModifiedCartan


