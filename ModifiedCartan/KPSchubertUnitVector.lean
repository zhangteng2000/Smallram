import ModifiedCartan.KPCorrespondenceEigenspaces
import ModifiedCartan.KPJointWronskian

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

/-- The common eigenvalue polynomial is the coordinate of the prescribed
    actual Schubert space at every center. -/
theorem kpJointValuePolynomial_eq_schubertCoordinate {M n D : ℕ} (hM : 0 < M)
    (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ)
    (z : Fin M → ℂ) {V : Submodule ℂ (Polynomial ℂ)}
    (hV : V ∈ polynomialSchubertCell n D τ)
    (hne : kpJointEigenspace τ hτ z (fun μ => normalizedSchubertCoordinate hV μ 0) ≠ ⊥)
    (μ : YoungDiagram) (a : ℂ) :
    (kpJointValuePolynomial (Fintype.card (Fin M))
      (fun ν => normalizedSchubertCoordinate hV ν 0) μ).eval a =
        normalizedSchubertCoordinate hV μ a := by
  have hne' := (kpJointEigenspace_ne_bot_decidableEq_iff
    (inferInstance : DecidableEq (Fin M)) (Classical.decEq _) τ hτ z _).mp hne
  obtain ⟨W, hW, hc⟩ := kpJointSchubertSpace_exists
    (by simpa using hM) τ hτ hV.1 hV.2.1 z _ hne'
  have he : W = V := polynomialSchubertSpace_eq_of_coordinates hW hV (fun ν => by
    rw [hc, kpJointValuePolynomial_eval_zero τ hτ z _ hne'])
  subst W
  exact (hc μ a).symm

/-- LaTeX `eq:KP-eigenvalue-at-center`: one unit vector is chosen before
    either the partition or the center, and works for all of them. -/
theorem schubertWronskiFibre_exists_unit_kpEigenvector {M n D : ℕ} (hM : 0 < M)
    (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ)
    (z : Fin M → ℂ) {V : Submodule ℂ (Polynomial ℂ)}
    (hV : V ∈ polynomialSchubertCell n D τ)
    (hW : schubertMonicWronskian hV = ∏ i, (Polynomial.X + Polynomial.C (z i))) :
    ∃ v : YoungSpechtModule τ, ‖v‖ = 1 ∧
      ∀ μ a, (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z a) v =
        normalizedSchubertCoordinate hV μ a • v := by
  let χ := fun μ => normalizedSchubertCoordinate hV μ 0
  have hne := kpJointEigenspace_of_schubertWronskiFibre_fin hM τ hτ z hV hW
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨v, hv, he⟩ := (commonEigenvector_exists_unit_iff
    (fun μ => (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z 0)) χ).mp
      ⟨u, hu0, (mem_kpJointEigenspace_iff τ hτ z χ u).mp hu⟩
  have hm := (mem_kpJointEigenspace_iff τ hτ z χ v).mpr he
  refine ⟨v, hv, ?_⟩
  intro μ a
  rw [kpJointValuePolynomial_action τ hτ z χ v hm,
    kpJointValuePolynomial_eq_schubertCoordinate hM τ hτ z hV hne]

end
end ModifiedCartan

#print axioms ModifiedCartan.schubertWronskiFibre_exists_unit_kpEigenvector