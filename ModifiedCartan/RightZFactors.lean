import ModifiedCartan.ZFactorSets
import ModifiedCartan.SupportedPermutations

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- Actual supported factorizations used in KP source Section 4.1.2,
auxiliary to LaTeX `lem:KP-correspondence`. -/
def IsZFactorization {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z X Y : Finset A)
    (σ π : Equiv.Perm A) : Prop :=
  X ∪ Y = Finset.univ ∧ X ∩ Y = Z ∧ σ ∈ supportedPermutationSubgroup X ∧
    π ∈ supportedPermutationSubgroup Y ∧ σ * π = θ

def IsRightZFactor {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A)
    (π : Equiv.Perm A) : Prop := ∃ X σ, IsZFactorization θ Z X Y σ π

theorem permutation_mul_inv_fixes_iff {A : Type*} (θ π : Equiv.Perm A) (a : A) :
    (θ * π⁻¹) a = a ↔ π⁻¹ a = θ⁻¹ a := by
  constructor
  · intro h
    exact θ.injective (h.trans (θ.apply_symm_apply a).symm)
  · intro h
    change θ (π⁻¹ a) = a
    rw [h]
    exact θ.apply_symm_apply a

theorem isRightZFactor_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A)
    (π : Equiv.Perm A) :
    IsRightZFactor θ Z Y π ↔ Z ⊆ Y ∧ π ∈ supportedPermutationSubgroup Y ∧
      ∀ a ∈ Y \ Z, π⁻¹ a = θ⁻¹ a := by
  constructor
  · rintro ⟨X, σ, hu, hi, hσ, hπ, he⟩
    have hZY : Z ⊆ Y := by
      rw [← hi]
      exact Finset.inter_subset_right
    refine ⟨hZY, hπ, ?_⟩
    intro a ha
    have hX : a ∉ X := by
      intro hx
      apply (Finset.mem_sdiff.mp ha).2
      rw [← hi]
      exact Finset.mem_inter.mpr ⟨hx, (Finset.mem_sdiff.mp ha).1⟩
    have hs : σ = θ * π⁻¹ := by rw [← he, mul_assoc, mul_inv_cancel, mul_one]
    have hf := hσ a hX
    rw [hs] at hf
    exact (permutation_mul_inv_fixes_iff θ π a).mp hf
  · rintro ⟨hZY, hπ, h⟩
    refine ⟨zFactorLeftSet Z Y, θ * π⁻¹, zFactorLeftSet_union Z Y,
      zFactorLeftSet_inter Z Y hZY, ?_, hπ, ?_⟩
    · intro a ha
      apply (permutation_mul_inv_fixes_iff θ π a).mpr
      exact h a (Finset.mem_sdiff.mpr ((not_mem_zFactorLeftSet Z Y a).mp ha))
    · simp [mul_assoc]

theorem zFactorization_left_unique {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z X Y : Finset A) (σ π : Equiv.Perm A) (h : IsZFactorization θ Z X Y σ π) :
    X = zFactorLeftSet Z Y ∧ σ = θ * π⁻¹ := by
  refine ⟨zFactorLeftSet_unique X Z Y h.1 h.2.1, ?_⟩
  rw [← h.2.2.2.2, mul_assoc, mul_inv_cancel, mul_one]

theorem rightZFactor_predecessor_mem {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (π : Equiv.Perm A) (h : IsRightZFactor θ Z Y π)
    (a : A) (ha : a ∈ Y \ Z) : θ⁻¹ a ∈ Y := by
  obtain ⟨hZY, hπ, hp⟩ := (isRightZFactor_iff θ Z Y π).mp h
  rw [← hp a ha]
  exact supportedPermutation_apply_mem Y
    ⟨π⁻¹, (supportedPermutationSubgroup Y).inv_mem hπ⟩ (Finset.mem_sdiff.mp ha).1

end
end ModifiedCartan

