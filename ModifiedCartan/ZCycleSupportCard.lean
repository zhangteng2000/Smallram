import ModifiedCartan.ZCycleSupportParameters
import ModifiedCartan.CompositionResidueTransport

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem zPrefixSet_union_card {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) :
    (zPrefixSet θ Z κ ∪ D).card = (∑ a : Z, ((κ a).val + 1)) + D.card := by
  have hd : Disjoint (zPrefixSet θ Z κ) D := by
    apply Finset.disjoint_left.mpr
    intro x hp hx
    exact (mem_zStripComplement_iff θ Z x).mp (hsub hx) (zPrefixSet_subset_union θ Z κ hp)
  rw [Finset.card_union_of_disjoint hd, zPrefixSet_card]

theorem zCycleSupport_card {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (C : ZComplementCycleParameters θ Z) :
    (zCycleSupport θ Z κ C).card = (∑ a : Z, ((κ a).val + 1)) +
      ∑ c ∈ C.val, permutationCycleWeight θ (fun _ => 1) c := by
  rw [zCycleSupport, zPrefixSet_union_card θ Z κ _ (zCycleSupport_complement_subset θ Z C),
    permutationCycleUnion_card]

theorem zComplementCycleWeight_sum {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :
    (∑ c ∈ permutationCycleImage θ (zStripComplement θ Z),
      permutationCycleWeight θ (fun _ => 1) c) = (zStripComplement θ Z).card := by
  rw [← permutationCycleUnion_card,
    permutationCycleUnion_image θ _ (zStripComplement_apply_iff θ Z)]

theorem zCycleSupport_laurentExponent {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (C : ZComplementCycleParameters θ Z) :
    ((zCycleSupport θ Z κ C).card : ℤ) - Z.card - Fintype.card A =
      compositionLaurentExponent (zStripLength θ Z) κ +
        (∑ c ∈ C.val, (permutationCycleWeight θ (fun _ => 1) c : ℤ)) -
        (∑ c ∈ permutationCycleImage θ (zStripComplement θ Z),
          (permutationCycleWeight θ (fun _ => 1) c : ℤ)) := by
  have hn : ((∑ a : Z, zStripLength θ Z a : ℕ) : ℤ) + (zStripComplement θ Z).card =
      (Fintype.card A : ℤ) := by
    exact_mod_cast zStripLengths_add_complement_card θ Z
  rw [zCycleSupport_card, compositionLaurentExponent_eq, Fintype.card_coe]
  have hc : (∑ c ∈ permutationCycleImage θ (zStripComplement θ Z),
      (permutationCycleWeight θ (fun _ => 1) c : ℤ)) = (zStripComplement θ Z).card := by
    exact_mod_cast zComplementCycleWeight_sum θ Z
  rw [hc]
  push_cast
  push_cast at hn
  omega

end
end ModifiedCartan

