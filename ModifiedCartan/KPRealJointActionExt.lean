import ModifiedCartan.KPRealJointDecomposition
import ModifiedCartan.SpechtAlgebraFaithful

open scoped Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- Equality on all actual real-parameter joint eigenspaces detects equality
    in the symmetric-group algebra. Auxiliary to `lem:KP-correspondence`. -/
theorem kpRealJointAction_ext {N : ℕ} (z : Fin N → ℝ)
    (x y : ℂ[Equiv.Perm (Fin N)])
    (h : ∀ τ : SizedYoungDiagram (Fintype.card (Fin N)),
      ∀ χ : YoungDiagram → ℂ,
      kpJointEigenspace τ.val τ.property.symm (fun i => (z i : ℂ)) χ ≠ ⊥ →
      ∀ v ∈ kpJointEigenspace τ.val τ.property.symm (fun i => (z i : ℂ)) χ,
        (spechtRepresentationOn τ.val τ.property.symm).asAlgebraHom x v =
          (spechtRepresentationOn τ.val τ.property.symm).asAlgebraHom y v) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_all_specht_actions_zero
  intro τ
  let L := (spechtRepresentationOn τ.val τ.property.symm).asAlgebraHom (x - y)
  change L = 0
  have hk : (⨆ χ : YoungDiagram → ℂ,
      kpJointEigenspace τ.val τ.property.symm (fun i => (z i : ℂ)) χ) ≤
      LinearMap.ker L := by
    apply iSup_le
    intro χ v hv
    by_cases hne : kpJointEigenspace τ.val τ.property.symm (fun i => (z i : ℂ)) χ = ⊥
    · rw [hne] at hv
      have hv0 : v = 0 := hv
      subst v
      exact (LinearMap.ker L).zero_mem
    · change (spechtRepresentationOn τ.val τ.property.symm).asAlgebraHom (x - y) v = 0
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
      exact h τ χ hne v hv
  have ht : ⊤ ≤ LinearMap.ker L := by
    rw [← kpJointEigenspaces_real_iSup τ.val τ.property.symm z]
    exact hk
  apply LinearMap.ext
  intro v
  exact ht (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ (YoungSpechtModule τ.val)))

end
end ModifiedCartan

#print axioms ModifiedCartan.kpRealJointAction_ext
