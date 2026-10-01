import ModifiedCartan.CompositionResidueTransport
import ModifiedCartan.ScaledMonomialEvaluation
import ModifiedCartan.FiniteBernstein

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def finiteBernsteinComposition {A : Type*} [Fintype A] [DecidableEq A]
    (B : Type*) [Fintype B] (ℓ : A → ℕ) : LaurentPolynomial (MvPolynomial B ℂ) :=
  ∑ κ : (a : A) → Fin (ℓ a), LaurentPolynomial.T (compositionLaurentExponent ℓ κ) *
    finiteBernstein B (scaledMonomialPolynomial (Option B) (fun a => (κ a).val + 1))

theorem finiteBernsteinComposition_eq {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (ℓ : A → ℕ) :
    finiteBernsteinComposition B ℓ = finiteElementaryLaurent B *
      weightedCompositionLaurent ℓ (shiftedCompositionAlphabet (fun b : B => MvPolynomial.X b)) := by
  have hx (b : Option B) : finiteAlphabetShift B (MvPolynomial.X b) =
      shiftedCompositionAlphabet (fun b : B => MvPolynomial.X b) b := by
    cases b with
    | none => exact finiteAlphabetShift_none B
    | some b => exact finiteAlphabetShift_some B b
  rw [finiteBernsteinComposition, weightedCompositionLaurent, Finset.mul_sum]
  simp only [finiteBernstein, scaledMonomialPolynomial_map, hx]
  apply Finset.sum_congr (by ext; simp)
  intro κ hκ
  exact mul_left_comm _ _ _

/-- Auxiliary for LaTeX `lem:KP-correspondence`: the exact finite-variable
composition residue identity of KP source Lemma 2.25. No positivity condition
is needed because a zero bound gives an empty finite sum. -/
theorem finiteBernsteinComposition_residue {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (ℓ : A → ℕ) : (finiteBernsteinComposition B ℓ).coeff (-1) = 0 := by
  rw [finiteBernsteinComposition_eq]
  exact weightedCompositionLaurent_residue ℓ (fun b : B => MvPolynomial.X b)

theorem finiteBernstein_bounded_composition_residue {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (ℓ : A → ℕ) :
    (∑ κ : (a : A) → Fin (ℓ a),
      LaurentPolynomial.T (((∑ a : A, ((κ a).val + 1) : ℕ) : ℤ) -
        ((∑ a : A, ℓ a : ℕ) : ℤ) - (Fintype.card A : ℤ)) *
      finiteBernstein B (scaledMonomialPolynomial (Option B) (fun a => (κ a).val + 1))).coeff (-1) = 0 := by
  have h := finiteBernsteinComposition_residue (B := B) ℓ
  simp only [finiteBernsteinComposition, compositionLaurentExponent_eq] at h
  exact h

end
end ModifiedCartan

