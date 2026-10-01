import ModifiedCartan.GeneralMarkerEvaluation
import ModifiedCartan.SupportedQuadraticResidue
import ModifiedCartan.SupportedPowerSumProduct

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteBernstein_residue_evaluateMarkers {A B : Type*} [Fintype B]
    (z : A → ℂ) (F : MvPolynomial A (LaurentPolynomial (MvPolynomial (Option B) ℂ)))
    (hF : ∀ d, (finiteBernsteinLaurent B (MvPolynomial.coeff d F)).coeff (-1) = 0) :
    (finiteBernsteinLaurent B (evaluateSupportedMarkers z F)).coeff (-1) = 0 := by
  rw [evaluateSupportedMarkers_expansion, finiteBernsteinLaurent_sum]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  exact finiteBernsteinLaurent_scalar_residue B _ _ (hF d)

/-- The literal KP supported-permutation quadratic identity after substituting
arbitrary complex parameters, including collisions. KP Section 4.1.4;
auxiliary to LaTeX `lem:KP-correspondence`. -/
theorem supportedPowerSumQuadratic_evaluated_residue {A B : Type*} [Fintype A] [Fintype B]
    (z : A → ℂ) (θ : Equiv.Perm A) :
    (finiteBernsteinLaurent B
      (evaluateSupportedMarkers z ((supportedPowerSumQuadratic A (Option B)).coeff θ))).coeff (-1) = 0 :=
  finiteBernstein_residue_evaluateMarkers z _ (fun d => supportedPowerSumQuadratic_residue θ d)

/-- KP equation (4.3), as the product of the two actual finite group-algebra
series, after arbitrary marker substitution. -/
theorem supportedPowerSumProduct_evaluated_residue {A B : Type*} [Fintype A] [Fintype B]
    (z : A → ℂ) (θ : Equiv.Perm A) :
    (finiteBernsteinLaurent B
      (((MonoidAlgebra.mapRingHom (Equiv.Perm A) (evaluateSupportedMarkers z))
        (supportedColumnLaurentSeries A (Option B)) *
       (MonoidAlgebra.mapRingHom (Equiv.Perm A) (evaluateSupportedMarkers z))
        (supportedPowerSumSeries A (Option B))).coeff θ)).coeff (-1) = 0 := by
  rw [← map_mul, MonoidAlgebra.coeff_mapRingHom,
    ← supportedPowerSumQuadratic_eq_product]
  exact supportedPowerSumQuadratic_evaluated_residue z θ

end
end ModifiedCartan


