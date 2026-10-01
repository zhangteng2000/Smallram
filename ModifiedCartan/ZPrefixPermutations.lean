import ModifiedCartan.ZSupportReconstruction
import ModifiedCartan.BlockInflation

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The actual ambient permutation obtained by joining the chosen strip
prefixes according to sigma. Letters outside the prefixes are fixed. -/
def zPrefixPermutation {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (σ : Equiv.Perm Z) : Equiv.Perm A :=
  (blockInflation (fun a => (κ a).val) σ).viaFintypeEmbedding (zPrefixEmbedding θ Z κ)

theorem zPrefixPermutation_apply_embedding {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (σ : Equiv.Perm Z)
    (p : Σ a : Z, Fin ((κ a).val + 1)) :
    zPrefixPermutation θ Z κ σ (zPrefixEmbedding θ Z κ p) =
      zPrefixEmbedding θ Z κ (blockInflation (fun a => (κ a).val) σ p) :=
  Equiv.Perm.viaFintypeEmbedding_apply_image _ _ p

theorem zPrefixPermutation_support {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (σ : Equiv.Perm Z) :
    zPrefixPermutation θ Z κ σ ∈ supportedPermutationSubgroup (zPrefixSet θ Z κ) := by
  intro x hx
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨p, hp⟩
  apply hx
  exact Finset.mem_map.mpr ⟨p, Finset.mem_univ p, hp⟩

theorem zPrefixPermutation_internal {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (σ : Equiv.Perm Z)
    (a : Z) (i : ℕ) (hi : i < (κ a).val) :
    zPrefixPermutation θ Z κ σ ((θ ^ i) a.val) = (θ ^ (i + 1)) a.val := by
  have h := zPrefixPermutation_apply_embedding θ Z κ σ ⟨a, ⟨i, by omega⟩⟩
  rw [blockInflation_internal (fun a => (κ a).val) σ a i hi] at h
  exact h

theorem zPrefixPermutation_last {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (σ : Equiv.Perm Z) (a : Z) :
    zPrefixPermutation θ Z κ σ ((θ ^ (κ a).val) a.val) = (σ a).val := by
  have h := zPrefixPermutation_apply_embedding θ Z κ σ ⟨a, Fin.last ((κ a).val)⟩
  rw [blockInflation_last] at h
  exact h

theorem zPrefixPermutation_predecessor {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (σ : Equiv.Perm Z)
    (x : A) (hx : x ∈ zPrefixSet θ Z κ \ Z) :
    zPrefixPermutation θ Z κ σ (θ⁻¹ x) = x := by
  obtain ⟨hm, hn⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨a, i, hi⟩ := (mem_zPrefixSet_iff θ Z κ x).mp hm
  have hpos : 0 < i.val := by
    by_contra h
    have he : i.val = 0 := by omega
    have hax : a.val = x := by simpa [he] using hi
    exact hn (hax ▸ a.property)
  have he : i.val = (i.val - 1) + 1 := by omega
  have hp : θ⁻¹ ((θ ^ i.val) a.val) = (θ ^ (i.val - 1)) a.val := by
    conv_lhs => rw [he, pow_succ', Equiv.Perm.mul_apply]
    simp
  rw [← hi, hp, zPrefixPermutation_internal θ Z κ σ a (i.val - 1)
    (by have := i.isLt; omega), ← he]

end
end ModifiedCartan

