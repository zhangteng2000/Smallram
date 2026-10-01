import ModifiedCartan.KPPolynomialParameters
import ModifiedCartan.BetheAlgebra

open scoped Classical BigOperators MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- The subset weight polynomial with formal root parameters. -/
def kpParameterWeight {N : ℕ} (I : Finset (Fin N)) : Polynomial (MvPolynomial (Fin N) ℂ) :=
  ∏ i ∈ Finset.univ \ I, (Polynomial.X + Polynomial.C (MvPolynomial.X i))

theorem kpParameterWeight_map {N : ℕ} (z : Fin N → ℂ) (I : Finset (Fin N)) :
    (kpParameterWeight I).map (MvPolynomial.aeval z).toRingHom = kpWeightPolynomial z I := by
  simp only [kpParameterWeight, kpWeightPolynomial, Polynomial.map_prod,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, MvPolynomial.aeval_X]

/-- The literal polynomial-parameter lift of the coefficient of a KP operator. -/
def kpParameterBetaCoefficient {N : ℕ} (μ : YoungDiagram) (k : ℕ) :
    (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)] :=
  ∑ I : SizedLetterSubset (Fin N) (partitionSize μ),
    (kpParameterWeight I.val).coeff k • kpParameterLift (kpAlpha μ I.val)

theorem kpParameterBetaCoefficient_evaluation {N : ℕ} (μ : YoungDiagram)
    (k : ℕ) (z : Fin N → ℂ) :
    kpParameterEvaluation z (kpParameterBetaCoefficient μ k) = kpBetaPowerCoefficient μ z k := by
  unfold kpParameterBetaCoefficient kpBetaPowerCoefficient
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [kpParameterEvaluation_smul, kpParameterEvaluation_lift]
  congr 1
  have he := congrArg (fun p : Polynomial ℂ => p.coeff k) (kpParameterWeight_map z I.val)
  rw [Polynomial.coeff_map] at he
  exact he

theorem kpBetaPowerCoefficient_zero (μ : YoungDiagram) {N : ℕ} (z : Fin N → ℂ) :
    kpBetaPowerCoefficient μ z 0 = kpBeta μ z 0 := by
  rw [kpBeta_eq_polynomialCombination]
  simp only [kpBetaPowerCoefficient, ← Polynomial.coeff_zero_eq_eval_zero]

/-- The traditional universal single-column algebra over the root-parameter
    polynomial ring. The arbitrary-partition generators are not included. -/
def kpParameterBetheAlgebra (N : ℕ) :
    Subalgebra (MvPolynomial (Fin N) ℂ) (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)] :=
  Algebra.adjoin (MvPolynomial (Fin N) ℂ)
    (Set.range fun qk : ℕ × ℕ => kpParameterBetaCoefficient (columnPartition qk.1) qk.2)

theorem kpParameterEvaluation_algebraMap {N : ℕ} (z : Fin N → ℂ)
    (r : MvPolynomial (Fin N) ℂ) :
    kpParameterEvaluation z (algebraMap (MvPolynomial (Fin N) ℂ)
      (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)] r) =
      algebraMap ℂ ℂ[Equiv.Perm (Fin N)] (MvPolynomial.eval z r) := by
  rw [Algebra.algebraMap_eq_smul_one]
  rw [kpParameterEvaluation_smul, map_one]
  exact (Algebra.algebraMap_eq_smul_one _).symm

theorem kpParameterBetheAlgebra_evaluation_mem {N : ℕ} (z : Fin N → ℂ)
    {x : (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)]} (hx : x ∈ kpParameterBetheAlgebra N) :
    kpParameterEvaluation z x ∈ betheAlgebra z := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨q, k⟩, rfl⟩ := hx
    rw [kpParameterBetaCoefficient_evaluation]
    exact kpBetaPowerCoefficient_column_mem_bethe z q k
  | algebraMap r =>
    rw [kpParameterEvaluation_algebraMap]
    exact (betheAlgebra z).algebraMap_mem _
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact (betheAlgebra z).add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [map_mul]
    exact (betheAlgebra z).mul_mem ihx ihy

theorem kpParameterBetheAlgebra_isMulCommutative (N : ℕ) :
    IsMulCommutative (kpParameterBetheAlgebra N) := by
  apply Algebra.isMulCommutative_adjoin (MvPolynomial (Fin N) ℂ)
  rintro x ⟨⟨q, k⟩, rfl⟩ y ⟨⟨r, l⟩, rfl⟩
  apply kpParameterEvaluation_ext
  intro z
  rw [map_mul, map_mul, kpParameterBetaCoefficient_evaluation, kpParameterBetaCoefficient_evaluation]
  exact congrArg Subtype.val (kpGeneratedAlgebra_elements_commute z
    ⟨_, betheAlgebra_le_kpGeneratedAlgebra z (kpBetaPowerCoefficient_column_mem_bethe z q k)⟩
    ⟨_, betheAlgebra_le_kpGeneratedAlgebra z (kpBetaPowerCoefficient_column_mem_bethe z r l)⟩)

end
end ModifiedCartan

#print axioms ModifiedCartan.kpParameterBetheAlgebra_isMulCommutative