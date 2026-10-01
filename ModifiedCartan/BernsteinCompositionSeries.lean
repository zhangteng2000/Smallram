import ModifiedCartan.FiniteBernsteinLaurent
import ModifiedCartan.BernsteinCompositionResidue

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

/-- The literal finite-variable series phi_ell(t) in KP source Lemma 2.25. -/
def finiteCompositionSeries {A : Type*} [Fintype A] [DecidableEq A]
    (B : Type*) [Fintype B] (ℓ : A → ℕ) : LaurentPolynomial (MvPolynomial B ℂ) :=
  ∑ κ : (a : A) → Fin (ℓ a), LaurentPolynomial.T (compositionLaurentExponent ℓ κ) *
    LaurentPolynomial.C (scaledMonomialPolynomial B (fun a => (κ a).val + 1))

theorem finiteBernsteinLaurent_composition {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (ℓ : A → ℕ) :
    finiteBernsteinLaurent B (finiteCompositionSeries (Option B) ℓ) = finiteBernsteinComposition B ℓ := by
  rw [finiteCompositionSeries, finiteBernsteinLaurent_sum]
  simp only [finiteBernsteinLaurent_T_mul, finiteBernsteinLaurent_C, finiteBernsteinComposition]

/-- Auxiliary for LaTeX `lem:KP-correspondence`: KP source Lemma 2.25 with
the Laurent-linear extension of the finite-alphabet Bernstein operator. -/
theorem finiteCompositionSeries_Bernstein_residue {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (ℓ : A → ℕ) :
    (finiteBernsteinLaurent B (finiteCompositionSeries (Option B) ℓ)).coeff (-1) = 0 := by
  rw [finiteBernsteinLaurent_composition]
  exact finiteBernsteinComposition_residue ℓ

end
end ModifiedCartan

