import ModifiedCartan.AlternantCauchyExpansion
import ModifiedCartan.FrobeniusAlternantTriangularity
import ModifiedCartan.WeightedOrthogonalTriangularity

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def frobeniusAlternantCoefficient (m : ℕ) (ν μ : YoungDiagram) : ℂ :=
  MvPolynomial.coeff (partitionFiniteDegree m ν + finiteStaircaseDegree m)
    (finiteVandermondeAlternant m * finiteFrobeniusPolynomial (Fin m) μ)

theorem mvPolynomial_coeff_right_constant {B R : Type*} [CommSemiring R]
    (d : B →₀ ℕ) (P : MvPolynomial B R) (c : R) :
    MvPolynomial.coeff d (P * MvPolynomial.C c) = MvPolynomial.coeff d P * c := by
  rw [mul_comm P, MvPolynomial.coeff_C_mul, mul_comm]

/-- The exact orthogonal coefficient relation from the Cauchy determinant.
    Auxiliary to the Schur identification for paper `lem:KP-correspondence`. -/
theorem frobeniusAlternantCoefficient_orthogonality {m n : ℕ}
    (μ ν : SizedYoungDiagram n) (hμ : μ.val.colLen 0 ≤ m) (hν : ν.val.colLen 0 ≤ m) :
    (∑ κ : SizedYoungDiagram n,
      frobeniusAlternantCoefficient m μ.val κ.val * frobeniusAlternantCoefficient m ν.val κ.val) =
        if μ = ν then 1 else 0 := by
  have hd : (partitionFiniteDegree m ν.val + finiteStaircaseDegree m).degree =
      (finiteStaircaseDegree m).degree + n := by
    rw [partitionAlternantExponent_degree ν.val hν, ν.property]
  have h := finiteAlternant_frobenius_expansion n
    (partitionFiniteDegree m ν.val + finiteStaircaseDegree m) hd
  change finiteAlternant (partitionAlternantExponent m ν.val) = _ at h
  have hc := congrArg (MvPolynomial.coeff (partitionFiniteDegree m μ.val + finiteStaircaseDegree m)) h
  rw [finiteAlternant_partition_coeff ν.val μ.val hν hμ] at hc
  simp only [Finset.mul_sum, MvPolynomial.coeff_sum, ← mul_assoc,
    mvPolynomial_coeff_right_constant] at hc
  simpa only [frobeniusAlternantCoefficient, Subtype.ext_iff, eq_comm] using hc.symm

theorem sizedYoung_height_le_of_size_le {m n : ℕ} (h : n ≤ m) (μ : SizedYoungDiagram n) :
    μ.val.colLen 0 ≤ m := by
  calc
    μ.val.colLen 0 ≤ partitionSize μ.val := partition_colLen_le_size μ.val 0
    _ = n := μ.property
    _ ≤ m := h

theorem frobeniusAlternantCoefficient_identity_of_size_le {m n : ℕ} (hm : n ≤ m)
    (μ ν : SizedYoungDiagram n) :
    frobeniusAlternantCoefficient m μ.val ν.val = if μ = ν then 1 else 0 := by
  refine weighted_triangular_orthogonal_identity
    (fun τ : SizedYoungDiagram n => partitionRowWeight τ.val)
    (fun ρ τ : SizedYoungDiagram n => frobeniusAlternantCoefficient m ρ.val τ.val) ?_ ?_ ?_ μ ν
  · intro ρ τ hw hne
    exact finiteVandermondeFrobenius_coeff_zero_of_le_ne τ.val ρ.val
      (sizedYoung_height_le_of_size_le hm ρ) hw (fun he => hne (Subtype.ext he))
  · intro ρ τ
    exact frobeniusAlternantCoefficient_orthogonality ρ τ
      (sizedYoung_height_le_of_size_le hm ρ) (sizedYoung_height_le_of_size_le hm τ)
  · intro ρ
    exact finiteVandermondeFrobenius_diagonal_nat ρ.val (sizedYoung_height_le_of_size_le hm ρ)

end
end ModifiedCartan

#print axioms ModifiedCartan.frobeniusAlternantCoefficient_orthogonality
#print axioms ModifiedCartan.frobeniusAlternantCoefficient_identity_of_size_le
