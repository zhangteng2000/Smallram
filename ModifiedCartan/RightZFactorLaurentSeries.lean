import ModifiedCartan.RightZFactorPolynomial
import ModifiedCartan.CycleSubsetLaurentProduct
import ModifiedCartan.ZCycleSupportFiniteness

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem rightZFactorPolynomial_zero {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z Y : Finset A) (h : ¬ IsZAdmissible θ Z Y) :
    rightZFactorPolynomial B θ Z Y = 0 := by
  letI : IsEmpty {π : Equiv.Perm A // IsRightZFactor θ Z Y π} :=
    ⟨fun π => h (rightZFactor_isZAdmissible θ Z Y π.val π.property)⟩
  simp [rightZFactorPolynomial]

def zSupportLaurentTerm {A : Type*} [Fintype A] (B : Type*) [Fintype B]
    (θ : Equiv.Perm A) (Z Y : Finset A) : LaurentPolynomial (MvPolynomial B ℂ) :=
  LaurentPolynomial.T (-((zFactorLeftSet Z Y).card : ℤ)) *
    LaurentPolynomial.C (MvPolynomial.C ((-1 : ℂ) ^ (zFactorLeftSet Z Y).card) *
      rightZFactorPolynomial B θ Z Y)

/-- The actual supported-right-factor Laurent sum, without the common sign
of theta. Its identification with a KP group-algebra coefficient is separate. -/
def rightZFactorLaurentSeries {A : Type*} [Fintype A] (B : Type*) [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) : LaurentPolynomial (MvPolynomial B ℂ) :=
  ∑ Y : Finset A, zSupportLaurentTerm B θ Z Y

theorem zSupportLaurentTerm_zero {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z Y : Finset A) (h : ¬ IsZAdmissible θ Z Y) :
    zSupportLaurentTerm B θ Z Y = 0 := by
  simp [zSupportLaurentTerm, rightZFactorPolynomial_zero θ Z Y h]

theorem rightZFactorLaurentSeries_admissible {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) :
    rightZFactorLaurentSeries B θ Z =
      ∑ Y : {Y : Finset A // IsZAdmissible θ Z Y}, zSupportLaurentTerm B θ Z Y.val := by
  unfold rightZFactorLaurentSeries
  calc
    _ = ∑ Y : Finset A, if h : IsZAdmissible θ Z Y then zSupportLaurentTerm B θ Z Y else 0 := by
      apply Finset.sum_congr rfl
      intro Y hY
      by_cases h : IsZAdmissible θ Z Y
      · simp [h]
      · simp [h, zSupportLaurentTerm_zero θ Z Y h]
    _ = _ := sum_dite_eq_sum_subtype (fun Y : Finset A => IsZAdmissible θ Z Y)
      (fun Y _ => zSupportLaurentTerm B θ Z Y)

theorem rightZFactorLaurentSeries_parameters {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) :
    rightZFactorLaurentSeries B θ Z =
      ∑ κ : ∀ a : Z, Fin (zStripLength θ Z a), ∑ C : ZComplementCycleParameters θ Z,
        zSupportLaurentTerm B θ Z (zCycleSupport θ Z κ C) := by
  rw [rightZFactorLaurentSeries_admissible,
    ← Equiv.sum_comp (zAdmissibleCycleSupportEquiv θ Z) (fun Y => zSupportLaurentTerm B θ Z Y.val)]
  rw [Fintype.sum_prod_type]
  rfl

end
end ModifiedCartan

