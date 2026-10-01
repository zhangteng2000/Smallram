import ModifiedCartan.PolynomialSpaceSchubert
import ModifiedCartan.SchubertUniversalMinors

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

namespace Paper

/-- LaTeX `lem:universal-minors`, `eq:universal-minors`, and
    `eq:projectionbound`. The Hermitian space is the actual finite-dimensional
    Specht module displayed by the existential witness. Its unitary representation
    and one unit vector work for every basis of V, partition and admissible center.
    The only space hypothesis is an actual basis of size n+1; no Schubert profile
    or spectral hypothesis is supplied as an input. This includes M=0. -/
theorem lem_universal_minors {M n : ℕ} {V : Submodule ℂ (Polynomial ℂ)}
    (b₀ : Module.Basis (Fin (n + 1)) ℂ V) (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b₀ j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) :
    ∃ (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ),
      IsUnitaryRepresentation (spechtRepresentationOn τ hτ) ∧
      ∃ v : YoungSpechtModule τ, ‖v‖ = 1 ∧
        (∀ (b : Module.Basis (Fin (n + 1)) ℂ V) (μ : YoungDiagram) (a : ℂ),
          (∏ i, (a - roots i)) ≠ 0 →
          (partitionPolynomialMinor μ (fun j => (b j).val)).eval a /
            (FewInflection.polynomialWronskian (fun j => (b j).val)).eval a =
            ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard (partitionSize μ),
              inner ℂ v ((spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ I) v) /
                (∏ i ∈ I, (a - roots i))) ∧
        ∀ (μ : YoungDiagram) (I : Finset (Fin M)),
          ‖inner ℂ v ((spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ I) v)‖ ≤
            ((partitionSize μ).factorial : ℝ) := by
  obtain ⟨τ, hV⟩ := polynomialSpace_exists_schubertFrame b₀
  have hW' : schubertMonicWronskian hV =
      ∏ i, (Polynomial.X - Polynomial.C (roots i)) :=
    (schubertMonicWronskian_eq_basis hV b₀).trans hW
  have hτ : Fintype.card (Fin M) = partitionSize τ :=
    (Fintype.card_fin M).trans (schubertWronskiFibre_partitionSize roots hV hW').symm
  obtain ⟨v, hv, he, hb⟩ := schubertUniversalMinors τ hτ roots hV hW'
  refine ⟨τ, hτ, spechtRepresentationOn_unitary τ hτ, v, hv, ?_, hb⟩
  intro b μ a ha
  apply he b μ a
  simpa only [hW', Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] using ha

/-- LaTeX `eq:minor-es-bound`, for an arbitrary polynomial space and basis,
    with roots counted with multiplicity and the constant case included. -/
theorem eq_minor_es_bound {M n : ℕ} {V : Submodule ℂ (Polynomial ℂ)}
    (b : Module.Basis (Fin (n + 1)) ℂ V) (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i)))
    (μ : YoungDiagram) (a : ℂ) (ha : (∏ i, (a - roots i)) ≠ 0) :
    ‖(partitionPolynomialMinor μ (fun j => (b j).val)).eval a /
        (FewInflection.polynomialWronskian (fun j => (b j).val)).eval a‖ ≤
      ((partitionSize μ).factorial : ℝ) *
        FewInflection.elementarySymmetric (fun i => ‖a - roots i‖⁻¹) (partitionSize μ) := by
  obtain ⟨τ, hV⟩ := polynomialSpace_exists_schubertFrame b
  have hW' : schubertMonicWronskian hV =
      ∏ i, (Polynomial.X - Polynomial.C (roots i)) :=
    (schubertMonicWronskian_eq_basis hV b).trans hW
  have hτ : Fintype.card (Fin M) = partitionSize τ :=
    (Fintype.card_fin M).trans (schubertWronskiFibre_partitionSize roots hV hW').symm
  apply schubertMinor_norm_le τ hτ roots hV hW' b μ a
  simpa only [hW', Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] using ha

end Paper
end
end ModifiedCartan

#print axioms ModifiedCartan.Paper.lem_universal_minors
#print axioms ModifiedCartan.Paper.eq_minor_es_bound