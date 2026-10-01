import ModifiedCartan.KPParameterAdjugateReconstruction
import ModifiedCartan.KPJointInitialBasis

namespace ModifiedCartan
noncomputable section
open scoped Classical BigOperators MonoidAlgebra IsMulCommutative
attribute [local instance] kpParameterBetheAlgebra_isMulCommutative

/-- Every actual joint character satisfies the universal denominator-cleared
    minor identity. Auxiliary to manuscript `lem:KP-correspondence`(i). -/
theorem kpParameterAdjugateMinor_character {n : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin (n + 1)) = partitionSize τ)
    (z : Fin (n + 1) → ℂ) (χ : YoungDiagram → ℂ)
    (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) (hz : (∏ i, z i) ≠ 0)
    (φ : kpGeneratedAlgebra z →ₐ[ℂ] ℂ)
    (hφ : ∀ x : kpGeneratedAlgebra z, ∀ v ∈ kpJointEigenspace τ hτ z χ,
      (spechtRepresentationOn τ hτ).asAlgebraHom x.val v = φ x • v)
    (μ : YoungDiagram) :
    MvPolynomial.eval z (kpParameterODEDeterminant (n + 1) (2 * (n + 1))) ^ (n + 1) * χ μ =
      (∏ i, z i) * (φ.comp (kpParameterBetheEvaluation z))
        (partitionCoefficientMinor (R := kpParameterBetheAlgebra (n + 1)) μ
          (kpParameterAdjugatePolynomial (n + 1) (2 * (n + 1)))) := by
  obtain ⟨V, hV, b, hb, hc, _⟩ := kpJoint_identityBasis_exists τ hτ z χ hne hz
  have hs : partitionSize τ = n + 1 := hτ.symm.trans (Fintype.card_fin _)
  have hL : n + partitionSize τ < 2 * (n + 1) := by omega
  have he := schubert_columnValues_adjugate_minor hV b hb
    (kpJointValuePolynomial (n + 1) χ) hc hL μ
  have hne' := (kpJointEigenspace_ne_bot_decidableEq_iff
    (inferInstance : DecidableEq (Fin (n + 1))) (Classical.decEq _) τ hτ z χ).mp hne
  have hμ : (kpJointValuePolynomial (n + 1) χ μ).eval 0 = χ μ := by
    simpa only [Fintype.card_fin] using
      kpJointValuePolynomial_eval_zero τ hτ z χ hne' μ
  have hbot : (kpJointValuePolynomial (n + 1) χ ⊥).eval 0 = ∏ i, z i := by
    have hw := kpJointValuePolynomial_bot τ hτ z χ hne
    simp only [Fintype.card_fin] at hw
    rw [hw]
    simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, zero_add]
  rw [kpParameterScalarODEJetMatrix_det τ hτ z χ hne φ hφ, hμ, hbot] at he
  change _ = (∏ i, z i) * (φ.comp (kpParameterBetheEvaluation z)).toRingHom
    (partitionCoefficientMinor (R := kpParameterBetheAlgebra (n + 1)) μ
      (kpParameterAdjugatePolynomial (n + 1) (2 * (n + 1))))
  rw [partitionCoefficientMinor_map (R := kpParameterBetheAlgebra (n + 1))]
  simp_rw [kpParameterAdjugatePolynomial_character τ hτ z χ hne φ hφ]
  exact he

end
end ModifiedCartan

#print axioms ModifiedCartan.kpParameterAdjugateMinor_character
