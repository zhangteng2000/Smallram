import ModifiedCartan.ZFactorizationParameters
import ModifiedCartan.RightZFactorLaurentSeries

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

/-- One literal summand of KP equation (4.3), after fixing its permutation
coefficient and a squarefree marker coefficient. -/
def zFactorizationLaurentTerm {A : Type*} [Fintype A] (B : Type*) [Fintype B]
    {θ : Equiv.Perm A} {Z : Finset A} (p : ZFactorizationParameters θ Z) :
    LaurentPolynomial (MvPolynomial B ℂ) :=
  LaurentPolynomial.T (-(p.val.1.1.card : ℤ)) *
    LaurentPolynomial.C
      (MvPolynomial.C (((Equiv.Perm.sign p.val.1.2.val : ℤ) : ℂ) *
        (-1 : ℂ) ^ p.val.1.1.card) *
       permutationFixedColoringSum
        (supportedPermutationRestriction p.val.2.1 p.val.2.2.val p.val.2.2.property)
        (fun b : B => (MvPolynomial.X b : MvPolynomial B ℂ)))

def zFactorizationLaurentSeries {A : Type*} [Fintype A] (B : Type*) [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) : LaurentPolynomial (MvPolynomial B ℂ) :=
  ∑ p : ZFactorizationParameters θ Z, zFactorizationLaurentTerm B p

theorem zFactorizationLaurentSeries_eq {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) :
    zFactorizationLaurentSeries B θ Z =
      LaurentPolynomial.C (MvPolynomial.C (((Equiv.Perm.sign θ : ℤ) : ℂ))) *
        rightZFactorLaurentSeries B θ Z := by
  rw [zFactorizationLaurentSeries,
    ← Equiv.sum_comp (zFactorizationRightEquiv θ Z).symm (zFactorizationLaurentTerm B),
    Fintype.sum_sigma]
  simp only [rightZFactorLaurentSeries, zSupportLaurentTerm, rightZFactorPolynomial,
    map_sum, Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro Y hY
  apply Finset.sum_congr (by ext; simp)
  intro π hπ
  dsimp [zFactorizationLaurentTerm, zFactorizationRightEquiv]
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Units.val_mul, Int.cast_mul]
  simp only [map_mul]
  ring

end
end ModifiedCartan

