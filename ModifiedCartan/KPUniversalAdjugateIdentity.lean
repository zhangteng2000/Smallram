import ModifiedCartan.KPAdjugateMinorCharacters
import ModifiedCartan.KPRealJointActionExt

namespace ModifiedCartan
noncomputable section
open scoped Classical BigOperators MonoidAlgebra IsMulCommutative
attribute [local instance] kpParameterBetheAlgebra_isMulCommutative

/-- The actual Specht decomposition proves the cleared reconstruction identity
    at positive real parameters, including collisions. -/
theorem kpParameterAdjugateMinor_positive {n : ℕ}
    (z : Fin (n + 1) → ℝ) (hz : ∀ i, 0 < z i) (μ : YoungDiagram) :
    kpParameterEvaluation (fun i => (z i : ℂ))
      (kpParameterODEDeterminant (n + 1) (2 * (n + 1)) ^ (n + 1) •
        kpParameterBetaCoefficient (N := n + 1) μ 0) =
      kpParameterEvaluation (fun i => (z i : ℂ))
        ((kpParameterWeight (N := n + 1) ∅).coeff 0 •
          (partitionCoefficientMinor (R := kpParameterBetheAlgebra (n + 1)) μ
            (kpParameterAdjugatePolynomial (n + 1) (2 * (n + 1)))).val) := by
  let zc : Fin (n + 1) → ℂ := fun i => (z i : ℂ)
  let δ : ℂ := MvPolynomial.eval zc
    (kpParameterODEDeterminant (n + 1) (2 * (n + 1)))
  let Q : kpParameterBetheAlgebra (n + 1) :=
    partitionCoefficientMinor (R := kpParameterBetheAlgebra (n + 1)) μ (kpParameterAdjugatePolynomial (n + 1) (2 * (n + 1)))
  have hz0 : (∏ i, zc i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    dsimp only [zc]
    exact_mod_cast (hz i).ne'
  change kpParameterEvaluation zc _ = kpParameterEvaluation zc _
  rw [kpParameterEvaluation_smul, map_pow, kpParameterBetaCoefficient_evaluation,
    kpBetaPowerCoefficient_zero, kpParameterEvaluation_smul, kpParameterWeight_zero_eval]
  change δ ^ (n + 1) • kpBeta μ zc 0 = (∏ i, zc i) • kpParameterEvaluation zc Q.val
  apply kpRealJointAction_ext z
  intro τ χ hne v hv
  obtain ⟨φ, _, hφ⟩ := exists_kpJointCharacter τ.val τ.property.symm zc χ hne
  have hβ := (mem_kpJointEigenspace_iff τ.val τ.property.symm zc χ v).mp hv μ
  have hQ : (spechtRepresentationOn τ.val τ.property.symm).asAlgebraHom
      (kpParameterEvaluation zc Q.val) v = φ (kpParameterBetheEvaluation zc Q) • v :=
    hφ (kpParameterBetheEvaluation zc Q) v hv
  rw [map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hβ, hQ,
    smul_smul, smul_smul]
  apply congrArg (fun c : ℂ => c • v)
  exact kpParameterAdjugateMinor_character τ.val τ.property.symm zc χ hne hz0 φ hφ μ

/-- A universal polynomial-parameter identity. Its proof uses real spectral
    decomposition only to prove a polynomial identity, so specialization to
    arbitrary complex parameters needs no diagonalizability assumption. -/
theorem kpParameterAdjugateMinor_identity (n : ℕ) (μ : YoungDiagram) :
    kpParameterODEDeterminant (n + 1) (2 * (n + 1)) ^ (n + 1) •
      kpParameterBetaCoefficient (N := n + 1) μ 0 =
      (kpParameterWeight (N := n + 1) ∅).coeff 0 •
        (partitionCoefficientMinor (R := kpParameterBetheAlgebra (n + 1)) μ
          (kpParameterAdjugatePolynomial (n + 1) (2 * (n + 1)))).val := by
  apply kpParameterEvaluation_ext_pos_real
  intro z hz
  exact kpParameterAdjugateMinor_positive z hz μ

end
end ModifiedCartan

#print axioms ModifiedCartan.kpParameterAdjugateMinor_positive
#print axioms ModifiedCartan.kpParameterAdjugateMinor_identity
