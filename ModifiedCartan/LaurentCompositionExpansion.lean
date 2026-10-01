import ModifiedCartan.NormalizedGeometricLaurent
import Mathlib.Data.Fintype.Pi

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem laurent_prod_T {A R : Type*} [CommSemiring R] (s : Finset A) (e : A → ℤ) :
    (∏ a ∈ s, LaurentPolynomial.T (e a) : LaurentPolynomial R) =
      LaurentPolynomial.T (∑ a ∈ s, e a) := by
  induction s using Finset.induction_on with
  | empty => simp [LaurentPolynomial.T_zero]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, LaurentPolynomial.T_add]

theorem normalizedGeometricLaurent_mul_T {R : Type*} [CommRing R]
    (n : ℕ) (z : LaurentPolynomial R) :
    normalizedGeometricLaurent n (LaurentPolynomial.T 1 * z) =
      ∑ r : Fin n, LaurentPolynomial.T (((r.val + 1 : ℕ) : ℤ) - (n : ℤ) - 1) * z ^ (r.val + 1) := by
  rw [normalizedGeometricLaurent, positiveGeometricSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_pow, LaurentPolynomial.T_pow, mul_one, ← mul_assoc, ← LaurentPolynomial.T_add]
  apply congrArg (fun q : ℤ => LaurentPolynomial.T q * z ^ (r.val + 1))
  omega

def compositionLaurentExponent {A : Type*} [Fintype A] (ℓ : A → ℕ)
    (κ : (a : A) → Fin (ℓ a)) : ℤ :=
  ∑ a : A, ((((κ a).val + 1 : ℕ) : ℤ) - (ℓ a : ℤ) - 1)

def weightedCompositionLaurent {A B R : Type*} [Fintype A] [Fintype B] [CommRing R]
    (ℓ : A → ℕ) (x : B → LaurentPolynomial R) : LaurentPolynomial R :=
  ∑ κ : (a : A) → Fin (ℓ a), LaurentPolynomial.T (compositionLaurentExponent ℓ κ) *
    ∑ f : A ↪ B, ∏ a : A, x (f a) ^ ((κ a).val + 1)

theorem weightedCompositionLaurent_eq {A B R : Type*} [Fintype A] [Fintype B] [CommRing R]
    (ℓ : A → ℕ) (x : B → LaurentPolynomial R) :
    weightedCompositionLaurent ℓ x =
      ∑ f : A ↪ B, ∏ a : A, normalizedGeometricLaurent (ℓ a) (LaurentPolynomial.T 1 * x (f a)) := by
  rw [weightedCompositionLaurent]
  simp only [compositionLaurentExponent, ← laurent_prod_T, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  simp only [normalizedGeometricLaurent_mul_T]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro κ hκ
  exact (Finset.prod_mul_distrib).symm

end
end ModifiedCartan

