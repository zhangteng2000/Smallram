import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Each coefficient of a vector-valued polynomial lies in the linear span
    of its values. Only scalar polynomial extensionality is needed. -/
theorem polynomialCombination_coeff_mem {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V] (w : ι → Polynomial ℂ) (v : ι → V)
    (S : Submodule ℂ V) (h : ∀ a : ℂ, (∑ i, (w i).eval a • v i) ∈ S) (k : ℕ) :
    (∑ i, (w i).coeff k • v i) ∈ S := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
  intro φ hφ
  let p : Polynomial ℂ := ∑ i, Polynomial.C (φ (v i)) * w i
  have hp : p = 0 := by
    apply Polynomial.funext
    intro a
    have hh := (S.mem_dualAnnihilator φ).mp hφ _ (h a)
    simpa only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_zero, map_sum, map_smul, smul_eq_mul, mul_comm] using hh
  have hh := congrArg (fun q : Polynomial ℂ => q.coeff k) hp
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_zero] at hh
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using hh

/-- Finite coefficient expansion for a vector-valued polynomial. -/
theorem polynomialCombination_eval_eq_sum {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V] (w : ι → Polynomial ℂ) (v : ι → V)
    (D : ℕ) (hD : ∀ i, (w i).natDegree < D) (a : ℂ) :
    (∑ i, (w i).eval a • v i) =
      ∑ k ∈ Finset.range D, a ^ k • ∑ i, (w i).coeff k • v i := by
  simp_rw [Polynomial.eval_eq_sum_range' (hD _), Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, mul_comm]

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialCombination_coeff_mem