import ModifiedCartan.ZConstructedRightFactor

open scoped Classical

namespace ModifiedCartan
noncomputable section

def zSupportSplitEmbedding {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) : ((Σ a : Z, Fin ((κ a).val + 1)) ⊕ D) ↪ A where
  toFun := Sum.elim (zPrefixEmbedding θ Z κ) Subtype.val
  inj' := by
    rintro (p | d) (q | e) he
    · exact congrArg Sum.inl ((zPrefixEmbedding θ Z κ).injective he)
    · have hp : zPrefixEmbedding θ Z κ p ∈ zPrefixSet θ Z κ :=
        Finset.mem_map.mpr ⟨p, Finset.mem_univ p, rfl⟩
      change zPrefixEmbedding θ Z κ p = e.val at he
      exact False.elim (zComplementSubset_not_prefix θ Z κ D hsub e.val e.property (he ▸ hp))
    · have hq : zPrefixEmbedding θ Z κ q ∈ zPrefixSet θ Z κ :=
        Finset.mem_map.mpr ⟨q, Finset.mem_univ q, rfl⟩
      change d.val = zPrefixEmbedding θ Z κ q at he
      exact False.elim (zComplementSubset_not_prefix θ Z κ D hsub d.val d.property (he.symm ▸ hq))
    · exact congrArg Sum.inr (Subtype.ext he)

theorem zSupportSplitEmbedding_mem {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (p : (Σ a : Z, Fin ((κ a).val + 1)) ⊕ D) :
    zSupportSplitEmbedding θ Z κ D hsub p ∈ zPrefixSet θ Z κ ∪ D := by
  cases p with
  | inl p => exact Finset.mem_union_left D (Finset.mem_map.mpr ⟨p, Finset.mem_univ p, rfl⟩)
  | inr d => exact Finset.mem_union_right _ d.property

def zSupportSplitEquiv {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) :
    ((Σ a : Z, Fin ((κ a).val + 1)) ⊕ D) ≃ ↥(zPrefixSet θ Z κ ∪ D) :=
  Equiv.ofBijective (fun p => ⟨zSupportSplitEmbedding θ Z κ D hsub p,
    zSupportSplitEmbedding_mem θ Z κ D hsub p⟩) (by
    constructor
    · intro p q he
      exact (zSupportSplitEmbedding θ Z κ D hsub).injective (congrArg Subtype.val he)
    · intro x
      rcases Finset.mem_union.mp x.property with hp | hd
      · obtain ⟨a, i, hi⟩ := (mem_zPrefixSet_iff θ Z κ x.val).mp hp
        exact ⟨Sum.inl ⟨a, i⟩, Subtype.ext hi⟩
      · exact ⟨Sum.inr ⟨x.val, hd⟩, Subtype.ext rfl⟩)

theorem zSupportSplitEquiv_inl {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (p : Σ a : Z, Fin ((κ a).val + 1)) :
    (zSupportSplitEquiv θ Z κ D hsub (Sum.inl p)).val = zPrefixEmbedding θ Z κ p := rfl

theorem zSupportSplitEquiv_inr {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (d : D) :
    (zSupportSplitEquiv θ Z κ D hsub (Sum.inr d)).val = d.val := rfl

end
end ModifiedCartan

