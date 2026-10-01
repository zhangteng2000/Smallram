import ModifiedCartan.PermutationCycleFibers
import ModifiedCartan.InvariantCycleSets
import Mathlib.Data.Fintype.BigOperators

open scoped Classical

namespace ModifiedCartan
noncomputable section

def cycleUnionSigmaEquiv {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (C : Finset (PermutationCycles σ)) :
    (Σ c : C, PermutationCycleFiber σ c.val) ≃ ↥(permutationCycleUnion σ C) where
  toFun p := ⟨p.2.val, (mem_permutationCycleUnion σ C p.2.val).mpr
    (p.2.property.symm ▸ p.1.property)⟩
  invFun x := ⟨⟨permutationCycleClass σ x.val, (mem_permutationCycleUnion σ C x.val).mp x.property⟩,
    ⟨x.val, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨c, hc⟩, ⟨a, ha⟩⟩
    cases ha
    rfl
  right_inv x := Subtype.ext rfl

theorem cycleUnionSigmaEquiv_apply {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (C : Finset (PermutationCycles σ)) (p : Σ c : C, PermutationCycleFiber σ c.val) :
    (cycleUnionSigmaEquiv σ C p).val = p.2.val := rfl

theorem cycleUnion_restriction_eq {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (C : Finset (PermutationCycles σ)) :
    σ.subtypePerm (permutationCycleUnion_invariant σ C) =
      (cycleUnionSigmaEquiv σ C).permCongr
        (Equiv.Perm.sigmaCongrRight (fun c : C => permutationCycleFiberPerm σ c.val)) := by
  apply Equiv.ext
  intro x
  obtain ⟨p, rfl⟩ := (cycleUnionSigmaEquiv σ C).surjective x
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  rfl

end
end ModifiedCartan

