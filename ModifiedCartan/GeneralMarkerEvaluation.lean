import ModifiedCartan.SupportedMarkerEvaluation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem evaluateSupportedMarkers_monomial_general {A B : Type*} (z : A → ℂ)
    (d : A →₀ ℕ) (c : LaurentPolynomial (MvPolynomial B ℂ)) :
    evaluateSupportedMarkers z (MvPolynomial.monomial d c) =
      c * LaurentPolynomial.C (MvPolynomial.C (d.prod (fun a k => z a ^ k))) := by
  rw [evaluateSupportedMarkers, MvPolynomial.eval₂Hom_monomial]
  simp only [RingHom.id_apply, Finsupp.prod, map_prod, map_pow]

theorem evaluateSupportedMarkers_expansion {A B : Type*} (z : A → ℂ)
    (F : MvPolynomial A (LaurentPolynomial (MvPolynomial B ℂ))) :
    evaluateSupportedMarkers z F = ∑ d ∈ F.support,
      LaurentPolynomial.C (MvPolynomial.C (d.prod (fun a k => z a ^ k))) * MvPolynomial.coeff d F := by
  calc
    _ = evaluateSupportedMarkers z (∑ d ∈ F.support, MvPolynomial.monomial d (MvPolynomial.coeff d F)) :=
      congrArg (evaluateSupportedMarkers z) (MvPolynomial.as_sum F)
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [evaluateSupportedMarkers_monomial_general, mul_comm]

end
end ModifiedCartan


