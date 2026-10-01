import ModifiedCartan.RightZFactorEndpoints

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem rightZFactor_reconstruction {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D)
    (π : Equiv.Perm A) (hπ : IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) π) :
    zConstructedRightFactor θ Z κ D hD (rightZFactorEndPermutation θ Z κ D hsub π hπ) = π := by
  apply Equiv.ext
  intro x
  by_cases hp : x ∈ zPrefixSet θ Z κ
  · rw [zConstructedRightFactor_apply_prefix θ Z κ D hsub hD _ x hp]
    obtain ⟨a, i, hi⟩ := (mem_zPrefixSet_iff θ Z κ x).mp hp
    rw [← hi]
    by_cases hlt : i.val < (κ a).val
    · rw [zPrefixPermutation_internal θ Z κ _ a i.val hlt,
        rightZFactor_prefix_internal θ Z κ D π hπ a i.val hlt]
    · have he : i.val = (κ a).val := by have := i.isLt; omega
      rw [he, zPrefixPermutation_last]
      rfl
  · by_cases hd : x ∈ D
    · rw [zConstructedRightFactor_apply_complement θ Z κ D hsub hD _ x hd,
        rightZFactor_complement θ Z κ D hsub hD π hπ x hd]
    · have hn : x ∉ zPrefixSet θ Z κ ∪ D := by
        simpa only [Finset.mem_union, not_or] using And.intro hp hd
      rw [zConstructedRightFactor_support θ Z κ D hD _ x hn,
        ((isRightZFactor_iff θ Z _ π).mp hπ).2.1 x hn]

theorem zConstructedRightFactor_endPermutation {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D) (σ : Equiv.Perm Z) :
    rightZFactorEndPermutation θ Z κ D hsub (zConstructedRightFactor θ Z κ D hD σ)
      (zConstructedRightFactor_isRight θ Z κ D hsub hD σ) = σ := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  change zConstructedRightFactor θ Z κ D hD σ ((θ ^ (κ a).val) a.val) = (σ a).val
  have hp : (θ ^ (κ a).val) a.val ∈ zPrefixSet θ Z κ :=
    (mem_zPrefixSet_iff θ Z κ _).mpr ⟨a, Fin.last ((κ a).val), rfl⟩
  rw [zConstructedRightFactor_apply_prefix θ Z κ D hsub hD σ ((θ ^ (κ a).val) a.val) hp,
    zPrefixPermutation_last]

/-- Exact bijection in KP source Section 4.1.3: the free choices in a right
factor are precisely the permutations of the selected strip prefixes.
Auxiliary to the manuscript's LaTeX `lem:KP-correspondence`. -/
def rightZFactorEquiv {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D) :
    Equiv.Perm Z ≃ {π : Equiv.Perm A // IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) π} where
  toFun σ := ⟨zConstructedRightFactor θ Z κ D hD σ,
    zConstructedRightFactor_isRight θ Z κ D hsub hD σ⟩
  invFun π := rightZFactorEndPermutation θ Z κ D hsub π.val π.property
  left_inv := zConstructedRightFactor_endPermutation θ Z κ D hsub hD
  right_inv π := Subtype.ext (rightZFactor_reconstruction θ Z κ D hsub hD π.val π.property)

end
end ModifiedCartan

