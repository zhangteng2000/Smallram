import ModifiedCartan.RightZFactorExistence

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem rightZFactor_forward {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A)
    (π : Equiv.Perm A) (hπ : IsRightZFactor θ Z Y π) (x : A) (hx : θ x ∈ Y \ Z) :
    π x = θ x := by
  have h := ((isRightZFactor_iff θ Z Y π).mp hπ).2.2 (θ x) hx
  have he := congrArg π h
  simpa using he.symm

theorem rightZFactor_prefix_internal {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (π : Equiv.Perm A) (hπ : IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) π)
    (a : Z) (i : ℕ) (hi : i < (κ a).val) :
    π ((θ ^ i) a.val) = (θ ^ (i + 1)) a.val := by
  have he : θ ((θ ^ i) a.val) = (θ ^ (i + 1)) a.val := by
    rw [pow_succ', Equiv.Perm.mul_apply]
  rw [← he]
  apply rightZFactor_forward θ Z _ π hπ
  rw [he]
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left D ?_, ?_⟩
  · exact (mem_zPrefixSet_iff θ Z κ _).mpr ⟨a, ⟨i + 1, by omega⟩, rfl⟩
  · exact zStripLength_minimal θ Z a (i + 1) (by omega) (by have := (κ a).isLt; omega)

theorem rightZFactor_complement {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D)
    (π : Equiv.Perm A) (hπ : IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) π)
    (x : A) (hx : x ∈ D) : π x = θ x := by
  have hm := (hD x).mpr hx
  apply rightZFactor_forward θ Z _ π hπ
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hm,
    zStripComplement_not_mem_Z θ Z (θ x) (hsub hm)⟩

theorem rightZFactor_endpoint_mem_Z {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (π : Equiv.Perm A)
    (hπ : IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) π) (a : Z) :
    π ((θ ^ (κ a).val) a.val) ∈ Z := by
  let x := (θ ^ (κ a).val) a.val
  have hx : x ∈ zPrefixSet θ Z κ ∪ D :=
    Finset.mem_union_left D ((mem_zPrefixSet_iff θ Z κ x).mpr ⟨a, Fin.last ((κ a).val), rfl⟩)
  have hpy := supportedPermutation_apply_mem _
    ⟨π, ((isRightZFactor_iff θ Z _ π).mp hπ).2.1⟩ hx
  change π x ∈ Z
  by_contra hn
  have hp := ((isRightZFactor_iff θ Z _ π).mp hπ).2.2 (π x) (Finset.mem_sdiff.mpr ⟨hpy, hn⟩)
  have hpx : θ x = π x := by simpa using congrArg θ hp
  have he : θ x = (θ ^ ((κ a).val + 1)) a.val := by
    dsimp [x]
    rw [pow_succ', Equiv.Perm.mul_apply]
  by_cases hlt : (κ a).val + 1 < zStripLength θ Z a
  · have hm : (θ ^ ((κ a).val + 1)) a.val ∈ zPrefixSet θ Z κ ∪ D := by
      rw [← he, hpx]
      exact hpy
    exact (Nat.lt_irrefl _) ((zPrefixSet_union_strip_mem_iff θ Z κ D hsub a _ hlt).mp hm)
  · have hlen : (κ a).val + 1 = zStripLength θ Z a := by have := (κ a).isLt; omega
    apply hn
    rw [← hpx, he, hlen]
    exact zStripLength_return θ Z a

def rightZFactorEndMap {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (π : Equiv.Perm A)
    (hπ : IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) π) (a : Z) : Z :=
  ⟨π ((θ ^ (κ a).val) a.val), rightZFactor_endpoint_mem_Z θ Z κ D hsub π hπ a⟩

theorem rightZFactorEndMap_injective {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (π : Equiv.Perm A)
    (hπ : IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) π) :
    Function.Injective (rightZFactorEndMap θ Z κ D hsub π hπ) := by
  intro a b hab
  have he : π ((θ ^ (κ a).val) a.val) = π ((θ ^ (κ b).val) b.val) := congrArg Subtype.val hab
  exact ((zStrip_pow_eq_iff θ Z a b _ _ (κ a).isLt (κ b).isLt).mp (π.injective he)).1

def rightZFactorEndPermutation {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (π : Equiv.Perm A)
    (hπ : IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) π) : Equiv.Perm Z :=
  Equiv.ofBijective (rightZFactorEndMap θ Z κ D hsub π hπ)
    ⟨rightZFactorEndMap_injective θ Z κ D hsub π hπ,
      Finite.surjective_of_injective (rightZFactorEndMap_injective θ Z κ D hsub π hπ)⟩

end
end ModifiedCartan

