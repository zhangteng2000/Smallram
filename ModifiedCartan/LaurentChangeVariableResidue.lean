import ModifiedCartan.LaurentDerivation
import Mathlib.Algebra.CharZero.Defs

open scoped BigOperators LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem laurentDerivative_pow_succ {R : Type*} [CommRing R]
    (s : LaurentPolynomial R) (n : ℕ) :
    laurentDerivative (s ^ (n + 1)) = (n + 1) • (s ^ n * laurentDerivative s) := by
  simpa only [laurentDerivation_apply, Nat.add_sub_cancel, smul_eq_mul,
    nsmul_eq_mul, mul_assoc] using (laurentDerivation R).leibniz_pow s (n + 1)

theorem laurent_residue_pow_mul_derivative {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] (s : LaurentPolynomial R) (n : ℕ) :
    (s ^ n * laurentDerivative s).coeff (-1) = 0 := by
  have h : ((n + 1 : ℕ) : R) * (s ^ n * laurentDerivative s).coeff (-1) = 0 := by
    calc
      _ = ((n + 1) • (s ^ n * laurentDerivative s)).coeff (-1) := by
        rw [AddMonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]
      _ = (laurentDerivative (s ^ (n + 1))).coeff (-1) := by
        rw [laurentDerivative_pow_succ]
      _ = 0 := laurentDerivative_residue _
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (by omega))

/-- Finite formal substitution formula: the residue of P(s) ds is zero.
This will be applied over the actual polynomial ring in the marker variables. -/
theorem laurent_residue_aeval_mul_derivative {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] (P : Polynomial R) (s : LaurentPolynomial R) :
    (Polynomial.aeval s P * laurentDerivative s).coeff (-1) = 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_zero]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, ← LaurentPolynomial.C_eq_algebraMap, mul_assoc,
      ← LaurentPolynomial.smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply,
      laurent_residue_pow_mul_derivative, smul_zero]

theorem laurent_residue_derivative_mul_affine_product {B R : Type*}
    [Fintype B] [CommRing R] [IsDomain R] [CharZero R]
    (s : LaurentPolynomial R) (x c : B → R) :
    (laurentDerivative s * ∏ b : B,
      (LaurentPolynomial.C (c b) - LaurentPolynomial.C (x b) * s)).coeff (-1) = 0 := by
  let P : Polynomial R := ∏ b : B, (Polynomial.C (c b) - Polynomial.C (x b) * Polynomial.X)
  have hp : Polynomial.aeval s P = ∏ b : B,
      (LaurentPolynomial.C (c b) - LaurentPolynomial.C (x b) * s) := by
    simp only [P, map_prod, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      LaurentPolynomial.C_eq_algebraMap]
  rw [mul_comm, ← hp]
  exact laurent_residue_aeval_mul_derivative P s

end
end ModifiedCartan

