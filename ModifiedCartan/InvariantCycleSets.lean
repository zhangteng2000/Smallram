import ModifiedCartan.CycleColorings

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Union of a chosen subset of the actual cycles, including fixed points. -/
def permutationCycleUnion (σ : Equiv.Perm A) (C : Finset (PermutationCycles σ)) : Finset A :=
  Finset.univ.filter (fun a => permutationCycleClass σ a ∈ C)

theorem mem_permutationCycleUnion (σ : Equiv.Perm A) (C : Finset (PermutationCycles σ))
    (a : A) : a ∈ permutationCycleUnion σ C ↔ permutationCycleClass σ a ∈ C := by
  simp [permutationCycleUnion]

theorem permutationCycleUnion_invariant (σ : Equiv.Perm A) (C : Finset (PermutationCycles σ))
    (a : A) : σ a ∈ permutationCycleUnion σ C ↔ a ∈ permutationCycleUnion σ C := by
  simp only [mem_permutationCycleUnion, permutationCycleClass_apply]

def permutationCycleImage (σ : Equiv.Perm A) (D : Finset A) : Finset (PermutationCycles σ) :=
  D.image (permutationCycleClass σ)

theorem mem_permutationCycleImage_iff (σ : Equiv.Perm A) (D : Finset A)
    (hD : ∀ a, σ a ∈ D ↔ a ∈ D) (a : A) :
    permutationCycleClass σ a ∈ permutationCycleImage σ D ↔ a ∈ D := by
  constructor
  · intro hm
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hm
    have hs : σ.SameCycle b a := Quotient.exact he
    have hp := coloring_sameCycle_eq σ (fun x => x ∈ D) (fun x => propext (hD x)) hs
    exact hp ▸ hb
  · intro hm
    exact Finset.mem_image_of_mem _ hm

theorem permutationCycleUnion_image (σ : Equiv.Perm A) (D : Finset A)
    (hD : ∀ a, σ a ∈ D ↔ a ∈ D) :
    permutationCycleUnion σ (permutationCycleImage σ D) = D := by
  ext a
  rw [mem_permutationCycleUnion, mem_permutationCycleImage_iff σ D hD]

theorem permutationCycleImage_union (σ : Equiv.Perm A) (C : Finset (PermutationCycles σ)) :
    permutationCycleImage σ (permutationCycleUnion σ C) = C := by
  ext c
  refine Quotient.inductionOn c (fun a => ?_)
  change permutationCycleClass σ a ∈ permutationCycleImage σ (permutationCycleUnion σ C) ↔ _
  rw [mem_permutationCycleImage_iff σ _ (permutationCycleUnion_invariant σ C),
    mem_permutationCycleUnion]
  rfl

/-- Exact correspondence between invariant supports and subsets of cycles. -/
def invariantFinsetCycleEquiv (σ : Equiv.Perm A) :
    Finset (PermutationCycles σ) ≃ {D : Finset A // ∀ a, σ a ∈ D ↔ a ∈ D} where
  toFun C := ⟨permutationCycleUnion σ C, permutationCycleUnion_invariant σ C⟩
  invFun D := permutationCycleImage σ D.val
  left_inv := permutationCycleImage_union σ
  right_inv D := Subtype.ext (permutationCycleUnion_image σ D.val D.property)

end
end ModifiedCartan

