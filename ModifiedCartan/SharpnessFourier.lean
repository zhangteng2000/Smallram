import ModifiedCartan.IntegrableSystem
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Intervals

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def sharpnessRoot (q : ℕ) (j : Fin q) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) ^ j.val

theorem sharpnessRoot_injective {q : ℕ} (hq : 1 ≤ q) :
    Function.Injective (sharpnessRoot q) := by
  intro i j hij
  apply Fin.ext
  exact (Complex.isPrimitiveRoot_exp q (by omega)).pow_inj i.isLt j.isLt hij

theorem sharpnessRoot_pow {q : ℕ} (hq : 1 ≤ q) (j : Fin q) :
    sharpnessRoot q j ^ q = 1 := by
  unfold sharpnessRoot
  rw [← pow_mul, Nat.mul_comm, pow_mul,
    (Complex.isPrimitiveRoot_exp q (by omega)).pow_eq_one, one_pow]

theorem sharpnessRoot_ne_zero {q : ℕ} (j : Fin q) : sharpnessRoot q j ≠ 0 :=
  pow_ne_zero _ (Complex.exp_ne_zero _)

theorem sharpnessRoot_norm {q : ℕ} (hq : 1 ≤ q) (j : Fin q) :
    ‖sharpnessRoot q j‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (sharpnessRoot_pow hq j) (by omega)

theorem sharpnessRoot_exp {q : ℕ} (j : Fin q) :
    sharpnessRoot q j = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / q) := by
  unfold sharpnessRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem root_ratio_geometric_sum {q : ℕ} (hq : 1 ≤ q) (i j : Fin q) :
    (∑ l : Fin q, (sharpnessRoot q j / sharpnessRoot q i) ^ l.val) =
      if i = j then (q : ℂ) else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [sharpnessRoot_ne_zero]
  · rw [ite_eq_right hij, Fin.sum_univ_eq_sum_range]
    have hratio : sharpnessRoot q j / sharpnessRoot q i ≠ 1 := by
      intro he
      have hr := (div_eq_one_iff_eq (sharpnessRoot_ne_zero i)).mp he
      exact hij ((sharpnessRoot_injective hq hr).symm)
    rw [geom_sum_eq hratio, div_pow, sharpnessRoot_pow hq,
      sharpnessRoot_pow hq, div_one, sub_self, zero_div]

noncomputable def sharpnessFourier (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j => sharpnessRoot q j ^ i.val

noncomputable def sharpnessFourierInverse (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j => (q : ℂ)⁻¹ * (sharpnessRoot q i ^ j.val)⁻¹

theorem sharpnessFourierInverse_mul {q : ℕ} (hq : 1 ≤ q) :
    sharpnessFourierInverse q * sharpnessFourier q = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have he (l : Fin q) : sharpnessFourierInverse q i l * sharpnessFourier q l j =
      (q : ℂ)⁻¹ * (sharpnessRoot q j / sharpnessRoot q i) ^ l.val := by
    unfold sharpnessFourierInverse sharpnessFourier
    rw [div_pow]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, root_ratio_geometric_sum hq]
  split_ifs
  · exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
  · exact mul_zero _

theorem sharpnessFourier_mul_inverse {q : ℕ} (hq : 1 ≤ q) :
    sharpnessFourier q * sharpnessFourierInverse q = 1 :=
  mul_eq_one_comm.mp (sharpnessFourierInverse_mul hq)

end ModifiedCartan
#print axioms ModifiedCartan.sharpnessRoot_injective
#print axioms ModifiedCartan.sharpnessFourierInverse_mul
#print axioms ModifiedCartan.sharpnessFourier_mul_inverse

