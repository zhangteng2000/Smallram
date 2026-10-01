import ModifiedCartan.BetheAlgebraIdentification
import ModifiedCartan.KPCorrespondenceEigenspaces

namespace ModifiedCartan.Paper
noncomputable section
open scoped Classical BigOperators

/-- LaTeX `lem:KP-correspondence`, both parts, with the actual traditional
    single-column Bethe algebra and the exact normalized Schubert coordinates.
    The algebra identification uses the proved finite adjugate reconstruction
    and polynomial-parameter identity instead of an external FDO inverse. -/
theorem lem_KP_correspondence {M n D : ℕ} (hM : 0 < M)
    (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ)
    (hf : PartitionFits n τ) (hD : n + 1 + τ.rowLen 0 ≤ D) (z : Fin M → ℂ) :
    (∀ μ ν : YoungDiagram, ∀ a b : ℂ,
      kpBeta μ z a * kpBeta ν z b = kpBeta ν z b * kpBeta μ z a) ∧
    (∀ μ : YoungDiagram, ∀ a : ℂ, kpBeta μ z a ∈ kpGeneratedAlgebra z) ∧
    kpGeneratedAlgebra z = betheAlgebra z ∧
    (∀ μ : YoungDiagram, ∀ a t : ℂ,
      kpBeta μ z (a + t) = ∑ ν : Subpartition (partitionSquare (Fintype.card (Fin M))),
        ((standardSkewTableauCount ν.val μ : ℂ) /
          ((partitionSize ν.val - partitionSize μ).factorial : ℂ) *
            t ^ (partitionSize ν.val - partitionSize μ)) • kpBeta ν.val z a) ∧
    (∀ E : Submodule ℂ (YoungSpechtModule τ),
      IsCommonEigenspace (spechtRepresentationOn τ hτ).asAlgebraHom (kpGeneratedAlgebra z) E →
      ∃ (V : Submodule ℂ (Polynomial ℂ)) (hV : V ∈ polynomialSchubertCell n D τ),
        (∀ μ v, v ∈ E → (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z 0) v =
          normalizedSchubertCoordinate hV μ 0 • v) ∧
        schubertMonicWronskian hV = ∏ i, (Polynomial.X + Polynomial.C (z i))) ∧
    (∀ (V : Submodule ℂ (Polynomial ℂ)) (hV : V ∈ polynomialSchubertCell n D τ),
      schubertMonicWronskian hV = ∏ i, (Polynomial.X + Polynomial.C (z i)) →
      ∃ E : Submodule ℂ (YoungSpechtModule τ),
        IsCommonEigenspace (spechtRepresentationOn τ hτ).asAlgebraHom (kpGeneratedAlgebra z) E ∧
        ∀ μ v, v ∈ E → (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z 0) v =
          normalizedSchubertCoordinate hV μ 0 • v) :=
  ⟨fun μ ν a b => (kpBeta_commute z μ ν a b).eq,
    fun μ a => kpBeta_mem_generated μ z a,
    kpGeneratedAlgebra_eq_betheAlgebra hM z,
    fun μ a t => kpBeta_translation μ z a t,
    (lem_KP_correspondence_ii hM τ hτ hf hD z).1,
    (lem_KP_correspondence_ii hM τ hτ hf hD z).2⟩

end
end ModifiedCartan.Paper

#print axioms ModifiedCartan.Paper.lem_KP_correspondence
