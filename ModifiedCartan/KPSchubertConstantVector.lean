import ModifiedCartan.KPSchubertUnitVector

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

/-- The constant-Wronskian case of the unit-vector construction is proved
    directly with the trivial symmetric group. -/
theorem schubert_unit_kpEigenvector_zero {n D : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin 0) = partitionSize τ)
    (z : Fin 0 → ℂ) {V : Submodule ℂ (Polynomial ℂ)}
    (hV : V ∈ polynomialSchubertCell n D τ) :
    ∃ v : YoungSpechtModule τ, ‖v‖ = 1 ∧
      ∀ μ a, (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z a) v =
        normalizedSchubertCoordinate hV μ a • v := by
  have hbot : τ = ⊥ := partition_eq_bot_of_size_zero τ (by simpa using hτ.symm)
  subst τ
  obtain ⟨χ, u, hu0, hu⟩ := specht_exists_kpJointEigenvector ⊥ hτ z
  obtain ⟨v, hv, _⟩ := (commonEigenvector_exists_unit_iff
    (fun μ => (spechtRepresentationOn ⊥ hτ).asAlgebraHom (kpBeta μ z 0)) χ).mp
      ⟨u, hu0, (mem_kpJointEigenspace_iff ⊥ hτ z χ u).mp hu⟩
  refine ⟨v, hv, ?_⟩
  intro μ a
  by_cases hμ : μ = ⊥
  · subst μ
    rw [kpBeta_empty, normalizedSchubertCoordinate_top]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul, map_one,
      Module.End.one_apply, partitionSize_bot, Nat.factorial_zero, Nat.cast_one,
      standardSkewTableauCount_self, div_one]
  · have hs : Fintype.card (Fin 0) < partitionSize μ := by
      have hn : partitionSize μ ≠ 0 := fun hz => hμ (partition_eq_bot_of_size_zero μ hz)
      simpa using Nat.pos_of_ne_zero hn
    rw [kpBeta_of_size_gt μ z a hs, map_zero, LinearMap.zero_apply,
      normalizedSchubertCoordinate_eq_zero_of_not_le hV μ (by simpa using hμ), zero_smul]

/-- A fixed unit vector for every Wronski fibre, including degree zero. -/
theorem schubertWronskiFibre_exists_unit_kpEigenvector_all {M n D : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ)
    (z : Fin M → ℂ) {V : Submodule ℂ (Polynomial ℂ)}
    (hV : V ∈ polynomialSchubertCell n D τ)
    (hW : schubertMonicWronskian hV = ∏ i, (Polynomial.X + Polynomial.C (z i))) :
    ∃ v : YoungSpechtModule τ, ‖v‖ = 1 ∧
      ∀ μ a, (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z a) v =
        normalizedSchubertCoordinate hV μ a • v := by
  by_cases hM : M = 0
  · subst M
    exact schubert_unit_kpEigenvector_zero τ hτ z hV
  · exact schubertWronskiFibre_exists_unit_kpEigenvector (Nat.pos_of_ne_zero hM) τ hτ z hV hW

end
end ModifiedCartan

#print axioms ModifiedCartan.schubertWronskiFibre_exists_unit_kpEigenvector_all