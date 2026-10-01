import ModifiedCartan.CommonEigenspaceAlgebra
import ModifiedCartan.KPInverseCorrespondence

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Forward Wronski correspondence with the canonical finite-index instances. -/
theorem kpJointWronskiFibre_exists_fin {M n D : ℕ} (hM : 0 < M)
    (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ)
    (hf : PartitionFits n τ) (hD : n + 1 + τ.rowLen 0 ≤ D) (z : Fin M → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    ∃ (V : Submodule ℂ (Polynomial ℂ)) (hV : V ∈ polynomialSchubertCell n D τ),
      (∀ μ, normalizedSchubertCoordinate hV μ 0 = χ μ) ∧
      schubertMonicWronskian hV = ∏ i, (Polynomial.X + Polynomial.C (z i)) := by
  apply kpJointWronskiFibre_exists (by simpa using hM) τ hτ hf hD z χ
  exact (kpJointEigenspace_ne_bot_decidableEq_iff
    (inferInstance : DecidableEq (Fin M)) (Classical.decEq _) τ hτ z χ).mp hne

/-- Inverse Wronski correspondence with an independently named number of roots. -/
theorem kpJointEigenspace_of_schubertWronskiFibre_fin {M n D : ℕ} (hM : 0 < M)
    (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ)
    (z : Fin M → ℂ) {V : Submodule ℂ (Polynomial ℂ)}
    (hV : V ∈ polynomialSchubertCell n D τ)
    (hW : schubertMonicWronskian hV = ∏ i, (Polynomial.X + Polynomial.C (z i))) :
    kpJointEigenspace τ hτ z (fun μ => normalizedSchubertCoordinate hV μ 0) ≠ ⊥ := by
  have hsize : M = partitionSize τ := (Fintype.card_fin M).symm.trans hτ
  subst M
  exact kpJointEigenspace_of_schubertWronskiFibre τ hM z hV hW

theorem kpCommonEigenspace_schubertWronskiFibre {M n D : ℕ} (hM : 0 < M)
    (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ)
    (hf : PartitionFits n τ) (hD : n + 1 + τ.rowLen 0 ≤ D) (z : Fin M → ℂ)
    (E : Submodule ℂ (YoungSpechtModule τ))
    (hE : IsCommonEigenspace (spechtRepresentationOn τ hτ).asAlgebraHom
      (kpGeneratedAlgebra z) E) :
    ∃ (V : Submodule ℂ (Polynomial ℂ)) (hV : V ∈ polynomialSchubertCell n D τ),
      (∀ μ v, v ∈ E → (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z 0) v =
        normalizedSchubertCoordinate hV μ 0 • v) ∧
      schubertMonicWronskian hV = ∏ i, (Polynomial.X + Polynomial.C (z i)) := by
  obtain ⟨hne, χ, hχ⟩ := (kp_isCommonEigenspace_iff τ hτ z E).mp hE
  have hj : kpJointEigenspace τ hτ z χ ≠ ⊥ :=
    fun he => hne (le_antisymm (hχ.trans_eq he) bot_le)
  obtain ⟨V, hV, hc, hW⟩ := kpJointWronskiFibre_exists_fin hM τ hτ hf hD z χ hj
  refine ⟨V, hV, ?_, hW⟩
  intro μ v hv
  rw [hc]
  exact (mem_kpJointEigenspace_iff τ hτ z χ v).mp (hχ hv) μ

theorem schubertWronskiFibre_exists_kpCommonEigenspace {M n D : ℕ} (hM : 0 < M)
    (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ) (z : Fin M → ℂ)
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ)
    (hW : schubertMonicWronskian hV = ∏ i, (Polynomial.X + Polynomial.C (z i))) :
    ∃ E : Submodule ℂ (YoungSpechtModule τ),
      IsCommonEigenspace (spechtRepresentationOn τ hτ).asAlgebraHom (kpGeneratedAlgebra z) E ∧
      ∀ μ v, v ∈ E → (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z 0) v =
        normalizedSchubertCoordinate hV μ 0 • v := by
  let χ := fun μ => normalizedSchubertCoordinate hV μ 0
  refine ⟨kpJointEigenspace τ hτ z χ, ?_, ?_⟩
  · exact kpJointEigenspace_isCommonEigenspace τ hτ z χ
      (kpJointEigenspace_of_schubertWronskiFibre_fin hM τ hτ z hV hW)
  · intro μ v hv
    exact (mem_kpJointEigenspace_iff τ hτ z χ v).mp hv μ

namespace Paper

/-- LaTeX `lem:KP-correspondence`(ii), both directions, for exactly the
    manuscript's nonzero scalar-action subspaces and all root multiplicities.
    The separate Bethe algebra identification in part (i) is not asserted here. -/
theorem lem_KP_correspondence_ii {M n D : ℕ} (hM : 0 < M)
    (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ)
    (hf : PartitionFits n τ) (hD : n + 1 + τ.rowLen 0 ≤ D) (z : Fin M → ℂ) :
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
  ⟨kpCommonEigenspace_schubertWronskiFibre hM τ hτ hf hD z,
    fun _ hV hW => schubertWronskiFibre_exists_kpCommonEigenspace hM τ hτ z hV hW⟩

end Paper
end
end ModifiedCartan

#print axioms ModifiedCartan.Paper.lem_KP_correspondence_ii