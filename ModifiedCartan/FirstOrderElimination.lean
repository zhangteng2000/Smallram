import ModifiedCartan.IntegrableSystem
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open scoped Topology BigOperators
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def firstOrderEliminator {ι : Type*} [DecidableEq ι]
    (lam : ι → ℂ) (B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if i = j then 0 else -B i j / (lam i - lam j)

theorem firstOrderEliminator_commutator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℂ) (hlam : Function.Injective lam) (B : Matrix ι ι ℂ)
    (b : ℂ) (hB : ∀ i, B i i = b) :
    Matrix.diagonal lam * firstOrderEliminator lam B -
      firstOrderEliminator lam B * Matrix.diagonal lam + B = b • (1 : Matrix ι ι ℂ) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, firstOrderEliminator]
  by_cases hij : i = j
  · subst j
    simp [hB]
  · simp only [hij, ite_false, mul_zero]
    have hd : lam i - lam j ≠ 0 := sub_ne_zero.mpr (fun hh => hij (hlam hh))
    field_simp
    ring

theorem firstOrderGauge_identity {A : Type*} [Ring A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (L B C : A) (b s : ℝ) (hc : L * C - C * L + B = b • (1 : A)) :
    (L + s • B) * (1 + s • C) - (s * b) • (1 + s • C) + s ^ 2 • C =
      (1 + s • C) * L + s ^ 2 • ((B - b • (1 : A)) * C + C) := by
  have he : L * C + B - b • (1 : A) = C * L := by
    calc
      _ = (L * C - C * L + B - b • (1 : A)) + C * L := by abel
      _ = C * L := by rw [hc, sub_self, zero_add]
  calc
    _ = L + s • (L * C + B - b • (1 : A)) +
        s ^ 2 • ((B - b • (1 : A)) * C + C) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        sub_mul, smul_add, smul_sub, smul_smul]
      module
    _ = _ := by rw [he]; simp only [add_mul, one_mul, smul_mul_assoc]

end ModifiedCartan
#print axioms ModifiedCartan.firstOrderEliminator_commutator
#print axioms ModifiedCartan.firstOrderGauge_identity

