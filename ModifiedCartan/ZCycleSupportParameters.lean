import ModifiedCartan.ZSupportParameters
import ModifiedCartan.InvariantCycleSubsets

open scoped Classical

namespace ModifiedCartan
noncomputable section

def ZComplementCycleParameters {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :=
  {C : Finset (PermutationCycles θ) // C ⊆ permutationCycleImage θ (zStripComplement θ Z)}

def zCycleSupport {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (C : ZComplementCycleParameters θ Z) : Finset A :=
  zPrefixSet θ Z κ ∪ permutationCycleUnion θ C.val

theorem zCycleSupport_complement_subset {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (C : ZComplementCycleParameters θ Z) :
    permutationCycleUnion θ C.val ⊆ zStripComplement θ Z :=
  (permutationCycleUnion_subset_iff θ _ (zStripComplement_apply_iff θ Z) C.val).mpr C.property

theorem zCycleSupport_isZAdmissible {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (C : ZComplementCycleParameters θ Z) :
    IsZAdmissible θ Z (zCycleSupport θ Z κ C) :=
  zPrefixSet_union_isZAdmissible θ Z κ _ (permutationCycleUnion_invariant θ C.val)

/-- Exact parameterization of all admissible supports by bounded positive
strip parts and a subset of the actual complement cycles. -/
def zAdmissibleCycleSupportEquiv {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :
    ((∀ a : Z, Fin (zStripLength θ Z a)) × ZComplementCycleParameters θ Z) ≃
      {Y : Finset A // IsZAdmissible θ Z Y} :=
  (Equiv.prodCongr (Equiv.refl _)
    (invariantSubsetCycleEquiv θ (zStripComplement θ Z) (zStripComplement_apply_iff θ Z))).trans
      (zAdmissibleSupportEquiv θ Z)

theorem zAdmissibleCycleSupportEquiv_apply {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (C : ZComplementCycleParameters θ Z) :
    (zAdmissibleCycleSupportEquiv θ Z (κ, C)).val = zCycleSupport θ Z κ C := rfl

end
end ModifiedCartan

