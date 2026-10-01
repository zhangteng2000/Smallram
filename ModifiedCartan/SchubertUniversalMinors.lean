import ModifiedCartan.KPExpectationExpansion
import ModifiedCartan.KPSchubertConstantVector
import ModifiedCartan.SchubertMinorRatios
import FewInflection.PluckerBounds

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

/-- Universal derivative-minor expansion for an actual Schubert space.
    This is the representation-theoretic core of manuscript `lem:universal-minors`,
    including constant Wronskians and repeated roots. The vector is fixed for
    the space and works for every basis, partition and admissible center. -/
theorem schubertUniversalMinors {M n D : ℕ} (τ : YoungDiagram)
    (hτ : Fintype.card (Fin M) = partitionSize τ) (roots : Fin M → ℂ)
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ)
    (hW : schubertMonicWronskian hV = ∏ i, (Polynomial.X - Polynomial.C (roots i))) :
    ∃ v : YoungSpechtModule τ, ‖v‖ = 1 ∧
      (∀ (b : Module.Basis (Fin (n + 1)) ℂ V) (μ : YoungDiagram) (a : ℂ),
        (schubertMonicWronskian hV).eval a ≠ 0 →
        (partitionPolynomialMinor μ (fun j => (b j).val)).eval a /
          (FewInflection.polynomialWronskian (fun j => (b j).val)).eval a =
          ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard (partitionSize μ),
            inner ℂ v ((spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ I) v) /
              (∏ i ∈ I, (a - roots i))) ∧
      ∀ (μ : YoungDiagram) (I : Finset (Fin M)),
        ‖inner ℂ v ((spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ I) v)‖ ≤
          ((partitionSize μ).factorial : ℝ) := by
  have hW' : schubertMonicWronskian hV =
      ∏ i, (Polynomial.X + Polynomial.C (-roots i)) := by
    simpa only [map_neg, sub_eq_add_neg] using hW
  obtain ⟨v, hv, he⟩ := schubertWronskiFibre_exists_unit_kpEigenvector_all
    τ hτ (fun i => -roots i) hV hW'
  refine ⟨v, hv, ?_, ?_⟩
  · intro b μ a ha
    have hr : ∀ i, a + -roots i ≠ 0 := by
      rw [hW', Polynomial.eval_prod] at ha
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at ha
      exact fun i => Finset.prod_ne_zero_iff.mp ha i (Finset.mem_univ i)
    have hex : inner ℂ v ((spechtRepresentationOn τ hτ).asAlgebraHom
        (kpBeta μ (fun i => -roots i) a) v) = normalizedSchubertCoordinate hV μ a := by
      rw [he]
      calc
        inner ℂ v (normalizedSchubertCoordinate hV μ a • v) =
            normalizedSchubertCoordinate hV μ a * inner ℂ v v :=
          inner_smul_right v v _
        _ = normalizedSchubertCoordinate hV μ a := by
          rw [inner_self_eq_norm_sq_to_K, hv]
          simp
    rw [← normalizedSchubertCoordinate_div_bot hV b μ a,
      normalizedSchubertCoordinate_bot hV a, hW', Polynomial.eval_prod]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [← hex, kpBeta_expectation_div_product _ μ _ a hr v]
    simp only [sub_eq_add_neg]
  · intro μ I
    exact kpAlpha_expectation_bound _ (spechtRepresentationOn_unitary τ hτ) μ I v hv

/-- LaTeX `eq:minor-es-bound` for an actual Schubert space, with every
    normalization and coefficient bound discharged. -/
theorem schubertMinor_norm_le {M n D : ℕ} (τ : YoungDiagram)
    (hτ : Fintype.card (Fin M) = partitionSize τ) (roots : Fin M → ℂ)
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ)
    (hW : schubertMonicWronskian hV = ∏ i, (Polynomial.X - Polynomial.C (roots i)))
    (b : Module.Basis (Fin (n + 1)) ℂ V) (μ : YoungDiagram) (a : ℂ)
    (ha : (schubertMonicWronskian hV).eval a ≠ 0) :
    ‖(partitionPolynomialMinor μ (fun j => (b j).val)).eval a /
        (FewInflection.polynomialWronskian (fun j => (b j).val)).eval a‖ ≤
      ((partitionSize μ).factorial : ℝ) *
        FewInflection.elementarySymmetric (fun i => ‖a - roots i‖⁻¹) (partitionSize μ) := by
  obtain ⟨v, hv, he, hb⟩ := schubertUniversalMinors τ hτ roots hV hW
  rw [he b μ a ha]
  simp only [div_eq_mul_inv]
  simpa only [norm_inv, Finset.prod_inv_distrib] using
    FewInflection.norm_sum_coeff_mul_inv_product_le_factorial_mul_elementarySymmetric
      (fun I => inner ℂ v ((spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ I) v))
      (fun i => a - roots i) (fun I _ => hb μ I)

end
end ModifiedCartan

#print axioms ModifiedCartan.schubertUniversalMinors
#print axioms ModifiedCartan.schubertMinor_norm_le