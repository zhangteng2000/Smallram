import ModifiedCartan.KPPolynomialCoefficientAction
import ModifiedCartan.KPParameterBetheAlgebra
import ModifiedCartan.KPJointCoefficientSpace
import Mathlib.Algebra.Polynomial.OfFn


namespace ModifiedCartan
noncomputable section
open scoped Classical BigOperators MonoidAlgebra IsMulCommutative
attribute [local instance] kpParameterBetheAlgebra_isMulCommutative

theorem kpBetaPowerCoefficient_empty {N : ℕ} (z : Fin N → ℂ) (k : ℕ) :
    kpBetaPowerCoefficient (⊥ : YoungDiagram) z k =
      (kpWeightPolynomial z ∅).coeff k • (1 : ℂ[Equiv.Perm (Fin N)]) := by
  apply polynomialCombination_coeff_eq_smul
  intro a
  rw [← kpBeta_eq_polynomialCombination, kpBeta_empty, kpWeightPolynomial_eval]
  simp only [Finset.sdiff_empty]

theorem kpParameterWeight_coeff_zero_of_gt {N : ℕ} (I : Finset (Fin N))
    (k : ℕ) (hk : N < k) : (kpParameterWeight I).coeff k = 0 := by
  apply MvPolynomial.funext
  intro z
  have he := congrArg (fun p : Polynomial ℂ => p.coeff k) (kpParameterWeight_map z I)
  rw [Polynomial.coeff_map] at he
  have hd : (kpWeightPolynomial z I).natDegree < k := by
    apply lt_of_le_of_lt (kpWeightPolynomial_natDegree_le z I)
    have hc := Finset.card_le_card (Finset.sdiff_subset (s := Finset.univ) (t := I))
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  have he' : MvPolynomial.eval z ((kpParameterWeight I).coeff k) =
      (kpWeightPolynomial z I).coeff k := he
  rw [he', Polynomial.coeff_eq_zero_of_natDegree_lt hd, map_zero]

theorem kpParameterBetaCoefficient_empty {N : ℕ} (k : ℕ) :
    kpParameterBetaCoefficient (N := N) (⊥ : YoungDiagram) k =
      algebraMap (MvPolynomial (Fin N) ℂ) (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)]
        ((kpParameterWeight ∅).coeff k) := by
  apply kpParameterEvaluation_ext
  intro z
  rw [kpParameterBetaCoefficient_evaluation, kpParameterEvaluation_algebraMap,
    kpBetaPowerCoefficient_empty, Algebra.algebraMap_eq_smul_one]
  congr 1
  have he := congrArg (fun p : Polynomial ℂ => p.coeff k) (kpParameterWeight_map z ∅)
  rw [Polynomial.coeff_map] at he
  exact he.symm

def kpParameterColumnCoefficient (N q k : ℕ) : kpParameterBetheAlgebra N :=
  ⟨kpParameterBetaCoefficient (columnPartition q) k, Algebra.subset_adjoin ⟨(q, k), rfl⟩⟩

theorem kpParameterColumnCoefficient_zero (N k : ℕ) :
    kpParameterColumnCoefficient N 0 k =
      algebraMap (MvPolynomial (Fin N) ℂ) (kpParameterBetheAlgebra N)
        ((kpParameterWeight ∅).coeff k) := by
  apply Subtype.ext
  simp only [kpParameterColumnCoefficient, Subalgebra.coe_algebraMap,
    columnPartition_zero_eq_bot]
  exact kpParameterBetaCoefficient_empty k

def kpParameterColumnPolynomial (N q : ℕ) : Polynomial (kpParameterBetheAlgebra N) :=
  Polynomial.ofFn (N + 1) (fun k => kpParameterColumnCoefficient N q k.val)

theorem kpParameterColumnPolynomial_zero (N : ℕ) :
    kpParameterColumnPolynomial N 0 =
      (kpParameterWeight ∅).map
        (algebraMap (MvPolynomial (Fin N) ℂ) (kpParameterBetheAlgebra N)) := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map]
  by_cases hk : k < N + 1
  · rw [kpParameterColumnPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
    exact kpParameterColumnCoefficient_zero N k
  · rw [kpParameterColumnPolynomial, Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega),
      kpParameterWeight_coeff_zero_of_gt _ k (by omega), map_zero]

def kpParameterDifferentialCoefficients (N : ℕ) (i : Fin (N + 1)) :
    Polynomial (kpParameterBetheAlgebra N) :=
  Polynomial.C ((-1 : kpParameterBetheAlgebra N) ^ (N - i.val)) *
    kpParameterColumnPolynomial N (N - i.val)

theorem kpParameterDifferentialCoefficients_leading (N : ℕ) :
    kpParameterDifferentialCoefficients N (Fin.last N) =
      (kpParameterWeight ∅).map
        (algebraMap (MvPolynomial (Fin N) ℂ) (kpParameterBetheAlgebra N)) := by
  simp only [kpParameterDifferentialCoefficients, Fin.val_last, Nat.sub_self,
    pow_zero, Polynomial.C_1, one_mul, kpParameterColumnPolynomial_zero]

end
end ModifiedCartan

#print axioms ModifiedCartan.kpParameterColumnPolynomial_zero
#print axioms ModifiedCartan.kpParameterDifferentialCoefficients_leading
