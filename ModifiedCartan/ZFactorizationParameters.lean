import ModifiedCartan.RightZFactors
import Mathlib.Data.Fintype.Powerset

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- A support is part of the data, including its fixed points. KP Section 4.1.2;
auxiliary to LaTeX `lem:KP-correspondence`. -/
abbrev SupportedPermutationData (A : Type*) :=
  Σ X : Finset A, supportedPermutationSubgroup X

abbrev ZFactorizationParameters {A : Type*} [Fintype A]
    (θ : Equiv.Perm A) (Z : Finset A) :=
  {p : SupportedPermutationData A × SupportedPermutationData A //
    p.1.1 ∪ p.2.1 = Finset.univ ∧ p.1.1 ∩ p.2.1 = Z ∧
    p.1.2.val * p.2.2.val = θ}

theorem rightZFactor_canonicalFactorization {A : Type*} [Fintype A]
    (θ : Equiv.Perm A) (Z Y : Finset A) (π : Equiv.Perm A)
    (hπ : IsRightZFactor θ Z Y π) :
    IsZFactorization θ Z (zFactorLeftSet Z Y) Y (θ * π⁻¹) π := by
  obtain ⟨X, σ, h⟩ := hπ
  obtain ⟨hX, hσ⟩ := zFactorization_left_unique θ Z X Y σ π h
  simpa only [hX, hσ] using h

/-- Removes the uniquely determined left support and left permutation from an
actual supported factorization. No existence assumption is added. -/
def zFactorizationRightEquiv {A : Type*} [Fintype A]
    (θ : Equiv.Perm A) (Z : Finset A) :
    ZFactorizationParameters θ Z ≃
      Σ Y : Finset A, {π : Equiv.Perm A // IsRightZFactor θ Z Y π} where
  toFun p := ⟨p.val.2.1, p.val.2.2.val, p.val.1.1, p.val.1.2.val,
    p.property.1, p.property.2.1, p.val.1.2.property, p.val.2.2.property,
    p.property.2.2⟩
  invFun p :=
    let h := rightZFactor_canonicalFactorization θ Z p.1 p.2.val p.2.property
    ⟨(⟨zFactorLeftSet Z p.1, θ * p.2.val⁻¹, h.2.2.1⟩,
      ⟨p.1, p.2.val, h.2.2.2.1⟩), h.1, h.2.1, h.2.2.2.2⟩
  left_inv := by
    rintro ⟨⟨⟨X, σ, hσ⟩, ⟨Y, π, hπ⟩⟩, hu, hi, he⟩
    obtain ⟨hX, hs⟩ := zFactorization_left_unique θ Z X Y σ π
      ⟨hu, hi, hσ, hπ, he⟩
    apply Subtype.ext
    dsimp
    subst X
    subst σ
    rfl
  right_inv := by
    rintro ⟨Y, π, hπ⟩
    rfl

end
end ModifiedCartan

