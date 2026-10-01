import ModifiedCartan.ZFactorizationLaurentSeries
import ModifiedCartan.ComplementMarkerDegrees

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

def supportedPowerSumLaurentWeight {A : Type*} [Fintype A] (B : Type*) [Fintype B]
    (p : SupportedPermutationData A × SupportedPermutationData A) :
    LaurentPolynomial (MvPolynomial B ℂ) :=
  LaurentPolynomial.T (-(p.1.1.card : ℤ)) *
    LaurentPolynomial.C
      (MvPolynomial.C (((Equiv.Perm.sign p.1.2.val : ℤ) : ℂ) * (-1 : ℂ) ^ p.1.1.card) *
       permutationFixedColoringSum
        (supportedPermutationRestriction p.2.1 p.2.2.val p.2.2.property)
        (fun b : B => (MvPolynomial.X b : MvPolynomial B ℂ)))

/-- The actual supported-permutation expression in KP equation (4.3), with
independent marker variables and finite-alphabet cycle power sums. Its bridge
to Schur coefficients of the previously defined KP operators is separate. -/
def supportedPowerSumQuadratic (A B : Type*) [Fintype A] [Fintype B] :
    MonoidAlgebra (MvPolynomial A (LaurentPolynomial (MvPolynomial B ℂ))) (Equiv.Perm A) :=
  ∑ p : SupportedPermutationData A × SupportedPermutationData A,
    MonoidAlgebra.single (p.1.2.val * p.2.2.val)
      (MvPolynomial.monomial (complementMarkerDegree p.1.1 p.2.1)
        (supportedPowerSumLaurentWeight B p))

theorem supportedPowerSumQuadratic_squarefree_coeff {A B : Type*}
    [Fintype A] [Fintype B] (θ : Equiv.Perm A) (Z : Finset A) :
    MvPolynomial.coeff (markerSquarefreeDegree (Finset.univ \ Z))
      ((supportedPowerSumQuadratic A B).coeff θ) =
        zFactorizationLaurentSeries B θ Z := by
  rw [supportedPowerSumQuadratic]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MvPolynomial.coeff_sum]
  calc
    _ = ∑ p : SupportedPermutationData A × SupportedPermutationData A,
        if h : p.1.1 ∪ p.2.1 = Finset.univ ∧ p.1.1 ∩ p.2.1 = Z ∧
            p.1.2.val * p.2.2.val = θ then
          zFactorizationLaurentTerm B ⟨p, h⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hm : p.1.2.val * p.2.2.val = θ
      · rw [MonoidAlgebra.coeff_single_apply, if_pos hm, MvPolynomial.coeff_monomial]
        by_cases hd : complementMarkerDegree p.1.1 p.2.1 =
            markerSquarefreeDegree (Finset.univ \ Z)
        · obtain ⟨hu, hi⟩ := (complementMarkerDegree_squarefree_iff p.1.1 p.2.1 Z).mp hd
          rw [if_pos hd, dif_pos ⟨hu, hi, hm⟩]
          rfl
        · rw [if_neg hd, dif_neg]
          rintro ⟨hu, hi, _⟩
          exact hd ((complementMarkerDegree_squarefree_iff p.1.1 p.2.1 Z).mpr ⟨hu, hi⟩)
      · rw [MonoidAlgebra.coeff_single_apply, if_neg hm, MvPolynomial.coeff_zero, dif_neg]
        exact fun h => hm h.2.2
    _ = _ := sum_dite_eq_sum_subtype _ _

end
end ModifiedCartan

