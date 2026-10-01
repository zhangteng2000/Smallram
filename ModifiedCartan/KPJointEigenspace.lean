import ModifiedCartan.KPBetaCommutation
import ModifiedCartan.CommonEigenvectors

open scoped Classical

namespace ModifiedCartan
noncomputable section

def kpJointEigenspace {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) : Submodule ℂ (YoungSpechtModule τ) :=
  ⨅ μ : YoungDiagram, ((spechtRepresentationOn τ h).asAlgebraHom (kpBeta μ z 0)).eigenspace (χ μ)

theorem mem_kpJointEigenspace_iff {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (v : YoungSpechtModule τ) :
    v ∈ kpJointEigenspace τ h z χ ↔
      ∀ μ, (spechtRepresentationOn τ h).asAlgebraHom (kpBeta μ z 0) v = χ μ • v := by
  simp only [kpJointEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem specht_exists_kpJointEigenvector {N : ℕ} (τ : YoungDiagram)
    (h : Fintype.card (Fin N) = partitionSize τ) (z : Fin N → ℂ) :
    ∃ (χ : YoungDiagram → ℂ) (v : YoungSpechtModule τ), v ≠ 0 ∧ v ∈ kpJointEigenspace τ h z χ := by
  let e : YoungSpechtModule τ := ⟨youngPolytabloid τ, youngPolytabloid_mem_specht τ⟩
  have he : e ≠ 0 := fun he => youngPolytabloid_ne_zero τ (congrArg Subtype.val he)
  letI : Nontrivial (YoungSpechtModule τ) := ⟨⟨e, 0, he⟩⟩
  obtain ⟨χ, v, hv, heig⟩ := exists_commonEigenvector
    (fun μ => (spechtRepresentationOn τ h).asAlgebraHom (kpBeta μ z 0))
    (fun μ ν => (kpBeta_commute z μ ν 0 0).map (spechtRepresentationOn τ h).asAlgebraHom)
  exact ⟨χ, v, hv, (mem_kpJointEigenspace_iff τ h z χ v).mpr heig⟩

theorem specht_exists_kpJointEigenspace {N : ℕ} (τ : YoungDiagram)
    (h : Fintype.card (Fin N) = partitionSize τ) (z : Fin N → ℂ) :
    ∃ χ : YoungDiagram → ℂ, kpJointEigenspace τ h z χ ≠ ⊥ := by
  obtain ⟨χ, v, hv, hm⟩ := specht_exists_kpJointEigenvector τ h z
  refine ⟨χ, ?_⟩
  intro he
  rw [he] at hm
  exact hv hm

end
end ModifiedCartan


