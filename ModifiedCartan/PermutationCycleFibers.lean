import ModifiedCartan.CycleWeightedPowers

open scoped Classical

namespace ModifiedCartan
noncomputable section

def PermutationCycleFiber {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (c : PermutationCycles σ) := {a : A // permutationCycleClass σ a = c}

instance {A : Type*} [Fintype A] (σ : Equiv.Perm A) (c : PermutationCycles σ) :
    Fintype (PermutationCycleFiber σ c) := inferInstanceAs (Fintype {a : A // permutationCycleClass σ a = c})

instance {A : Type*} [Fintype A] (σ : Equiv.Perm A) (c : PermutationCycles σ) :
    Nonempty (PermutationCycleFiber σ c) := by
  refine Quotient.inductionOn c (fun a => ?_)
  exact ⟨⟨a, rfl⟩⟩

def permutationCycleFiberPerm {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (c : PermutationCycles σ) : Equiv.Perm (PermutationCycleFiber σ c) :=
  σ.subtypePerm (fun a => by simp only [permutationCycleClass_apply])

theorem permutationCycleFiberPerm_apply {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (c : PermutationCycles σ) (a : PermutationCycleFiber σ c) :
    (permutationCycleFiberPerm σ c a).val = σ a.val := rfl

theorem permutationCycleFiber_sameCycle {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (c : PermutationCycles σ) (a b : PermutationCycleFiber σ c) :
    (permutationCycleFiberPerm σ c).SameCycle a b := by
  apply Equiv.Perm.SameCycle.subtypePerm
  exact Quotient.exact (a.property.trans b.property.symm)

theorem permutationCycleFiber_card {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (c : PermutationCycles σ) :
    Fintype.card (PermutationCycleFiber σ c) = permutationCycleWeight σ (fun _ => 1) c := by
  change Fintype.card {a : A // permutationCycleClass σ a = c} = _
  rw [Fintype.card_subtype (fun a => permutationCycleClass σ a = c)]
  simp [permutationCycleWeight]

end
end ModifiedCartan

