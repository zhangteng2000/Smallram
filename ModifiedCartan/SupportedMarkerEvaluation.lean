import ModifiedCartan.SquarefreeMarkerEvaluation
import ModifiedCartan.SupportedPowerSumProduct

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def evaluateSupportedMarkers {A B : Type*} (z : A → ℂ) :
    MvPolynomial A (LaurentPolynomial (MvPolynomial B ℂ)) →+*
      LaurentPolynomial (MvPolynomial B ℂ) :=
  MvPolynomial.eval₂Hom (RingHom.id _) (fun a => LaurentPolynomial.C (MvPolynomial.C (z a)))

theorem evaluateSupportedMarkers_monomial {A B : Type*} (z : A → ℂ) (s : Finset A)
    (c : LaurentPolynomial (MvPolynomial B ℂ)) :
    evaluateSupportedMarkers z (MvPolynomial.monomial (markerSquarefreeDegree s) c) =
      c * LaurentPolynomial.C (MvPolynomial.C (∏ a ∈ s, z a)) := by
  rw [evaluateSupportedMarkers, markerSquarefreeMonomial_eval₂]
  simp only [RingHom.id_apply, map_prod]

end
end ModifiedCartan

