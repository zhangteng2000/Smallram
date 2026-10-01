import ModifiedCartan.KPUniversalAdjugateIdentity
import ModifiedCartan.KPGeneratedShift

namespace ModifiedCartan
noncomputable section
open scoped Classical BigOperators MonoidAlgebra IsMulCommutative
attribute [local instance] kpParameterBetheAlgebra_isMulCommutative

/-- Clearing the explicit nonzero scalar determinant places every KP
    generator in the traditional Bethe algebra away from zero parameters. -/
theorem kpBeta_zero_mem_bethe_of_prod_ne_zero {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hz : (∏ i, z i) ≠ 0) (μ : YoungDiagram) : kpBeta μ z 0 ∈ betheAlgebra z := by
  let δ : ℂ := MvPolynomial.eval z
    (kpParameterODEDeterminant (n + 1) (2 * (n + 1)))
  let Q : kpParameterBetheAlgebra (n + 1) :=
    partitionCoefficientMinor (R := kpParameterBetheAlgebra (n + 1)) μ
      (kpParameterAdjugatePolynomial (n + 1) (2 * (n + 1)))
  have hδ : δ ≠ 0 := kpParameterODEDeterminant_eval_ne_zero z hz
  have he := congrArg (kpParameterEvaluation z) (kpParameterAdjugateMinor_identity n μ)
  rw [kpParameterEvaluation_smul, map_pow, kpParameterBetaCoefficient_evaluation,
    kpBetaPowerCoefficient_zero, kpParameterEvaluation_smul, kpParameterWeight_zero_eval] at he
  change δ ^ (n + 1) • kpBeta μ z 0 = (∏ i, z i) • kpParameterEvaluation z Q.val at he
  have hm : δ ^ (n + 1) • kpBeta μ z 0 ∈ betheAlgebra z := by
    rw [he]
    exact Subalgebra.smul_mem _ (kpParameterBetheAlgebra_evaluation_mem z Q.property) _
  have hi := Subalgebra.smul_mem (betheAlgebra z) hm ((δ ^ (n + 1))⁻¹)
  simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hδ), one_smul] using hi

theorem kpGeneratedAlgebra_eq_betheAlgebra_of_prod_ne_zero {n : ℕ}
    (z : Fin (n + 1) → ℂ) (hz : (∏ i, z i) ≠ 0) :
    kpGeneratedAlgebra z = betheAlgebra z := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x ⟨μ, rfl⟩
    exact kpBeta_zero_mem_bethe_of_prod_ne_zero z hz μ
  · exact betheAlgebra_le_kpGeneratedAlgebra z

theorem exists_complex_shift_prod_ne_zero {N : ℕ} (z : Fin N → ℂ) :
    ∃ t : ℂ, (∏ i, (z i + t)) ≠ 0 := by
  obtain ⟨t, ht⟩ := (Set.finite_range (fun i => -z i)).exists_notMem
  refine ⟨t, Finset.prod_ne_zero_iff.mpr ?_⟩
  intro i _
  intro h
  apply ht
  exact ⟨i, by linear_combination -h⟩

/-- The exact traditional Bethe-algebra identification for every complex
    parameter tuple, including zero and repeated parameters.
    This is the missing identification in manuscript `lem:KP-correspondence`(i). -/
theorem kpGeneratedAlgebra_eq_betheAlgebra {M : ℕ} (hM : 0 < M) (z : Fin M → ℂ) :
    kpGeneratedAlgebra z = betheAlgebra z := by
  cases M with
  | zero => omega
  | succ n =>
    obtain ⟨t, ht⟩ := exists_complex_shift_prod_ne_zero z
    have he := kpGeneratedAlgebra_eq_betheAlgebra_of_prod_ne_zero (fun i => z i + t) ht
    simpa only [kpGeneratedAlgebra_shift, betheAlgebra_shift] using he

end
end ModifiedCartan

#print axioms ModifiedCartan.kpBeta_zero_mem_bethe_of_prod_ne_zero
#print axioms ModifiedCartan.kpGeneratedAlgebra_eq_betheAlgebra
