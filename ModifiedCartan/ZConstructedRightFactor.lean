import ModifiedCartan.ZPrefixPermutations
import ModifiedCartan.InvariantSupportedPermutations

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem zComplementSubset_not_prefix {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hD : D ⊆ zStripComplement θ Z) (x : A) (hx : x ∈ D) : x ∉ zPrefixSet θ Z κ := by
  intro hp
  exact (mem_zStripComplement_iff θ Z x).mp (hD hx) (zPrefixSet_subset_union θ Z κ hp)

def zConstructedRightFactor {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hD : ∀ x, θ x ∈ D ↔ x ∈ D) (σ : Equiv.Perm Z) : Equiv.Perm A :=
  zPrefixPermutation θ Z κ σ * invariantSupportedPermutation θ D hD

theorem zConstructedRightFactor_support {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hD : ∀ x, θ x ∈ D ↔ x ∈ D) (σ : Equiv.Perm Z) :
    zConstructedRightFactor θ Z κ D hD σ ∈ supportedPermutationSubgroup (zPrefixSet θ Z κ ∪ D) := by
  intro x hx
  have hp : x ∉ zPrefixSet θ Z κ := fun h => hx (Finset.mem_union_left D h)
  have hd : x ∉ D := fun h => hx (Finset.mem_union_right _ h)
  change zPrefixPermutation θ Z κ σ (invariantSupportedPermutation θ D hD x) = x
  rw [invariantSupportedPermutation_mem θ D hD x hd, zPrefixPermutation_support θ Z κ σ x hp]

theorem zConstructedRightFactor_apply_prefix {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D)
    (σ : Equiv.Perm Z) (x : A) (hx : x ∈ zPrefixSet θ Z κ) :
    zConstructedRightFactor θ Z κ D hD σ x = zPrefixPermutation θ Z κ σ x := by
  have hn : x ∉ D := fun hd => zComplementSubset_not_prefix θ Z κ D hsub x hd hx
  change zPrefixPermutation θ Z κ σ (invariantSupportedPermutation θ D hD x) = _
  rw [invariantSupportedPermutation_mem θ D hD x hn]

theorem zConstructedRightFactor_apply_complement {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D)
    (σ : Equiv.Perm Z) (x : A) (hx : x ∈ D) :
    zConstructedRightFactor θ Z κ D hD σ x = θ x := by
  have hn := zComplementSubset_not_prefix θ Z κ D hsub (θ x) ((hD x).mpr hx)
  change zPrefixPermutation θ Z κ σ (invariantSupportedPermutation θ D hD x) = _
  rw [invariantSupportedPermutation_apply θ D hD x hx, zPrefixPermutation_support θ Z κ σ (θ x) hn]

theorem zConstructedRightFactor_isRight {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D) (σ : Equiv.Perm Z) :
    IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) (zConstructedRightFactor θ Z κ D hD σ) := by
  apply (isRightZFactor_iff θ Z _ _).mpr
  refine ⟨(zPrefixSet_union_isZAdmissible θ Z κ D hD).1,
    zConstructedRightFactor_support θ Z κ D hD σ, ?_⟩
  intro x hx
  obtain ⟨hm, hn⟩ := Finset.mem_sdiff.mp hx
  have he : zConstructedRightFactor θ Z κ D hD σ (θ⁻¹ x) = x := by
    rcases Finset.mem_union.mp hm with hp | hd
    · have hps := Finset.mem_sdiff.mpr ⟨hp, hn⟩
      rw [zConstructedRightFactor_apply_prefix θ Z κ D hsub hD σ _
        (zPrefixSet_predecessor θ Z κ x hps)]
      exact zPrefixPermutation_predecessor θ Z κ σ x hps
    · have hd' : θ⁻¹ x ∈ D := (hD (θ⁻¹ x)).mp (by simpa using hd)
      rw [zConstructedRightFactor_apply_complement θ Z κ D hsub hD σ _ hd']
      simp
  apply (zConstructedRightFactor θ Z κ D hD σ).injective
  simpa using he.symm

end
end ModifiedCartan

