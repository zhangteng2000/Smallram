import ModifiedCartan.ScalarActionCharacter
import ModifiedCartan.KPJointEigenvalues

open scoped Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Each actual nonzero joint eigenspace determines a character of the entire
generated algebra, with the prescribed beta eigenvalues. -/
theorem exists_kpJointCharacter (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ h z χ ≠ ⊥) :
    ∃ φ : kpGeneratedAlgebra z →ₐ[ℂ] ℂ,
      (∀ μ : YoungDiagram, φ ⟨kpBeta μ z 0, kpBeta_zero_mem_generated μ z⟩ = χ μ) ∧
      ∀ x : kpGeneratedAlgebra z, ∀ v ∈ kpJointEigenspace τ h z χ,
        (spechtRepresentationOn τ h).asAlgebraHom x.val v = φ x • v := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let ρ := (spechtRepresentationOn τ h).asAlgebraHom.comp (kpGeneratedAlgebra z).val
  have hall (x : kpGeneratedAlgebra z) : ∃ c : ℂ, ρ x v = c • v := by
    obtain ⟨c, hc⟩ := kpJointEigenspace_generated_scalar τ h z χ x
    exact ⟨c, hc v hv⟩
  let φ := scalarActionCharacter ρ v hv0 hall
  have hp (x : kpGeneratedAlgebra z) (w : YoungSpechtModule τ)
      (hw : w ∈ kpJointEigenspace τ h z χ) :
      (spechtRepresentationOn τ h).asAlgebraHom x.val w = φ x • w := by
    obtain ⟨c, hc⟩ := kpJointEigenspace_generated_scalar τ h z χ x
    have he : φ x = c := scalarActionValue_eq ρ v hv0 hall x c (hc v hv)
    rw [he]
    exact hc w hw
  refine ⟨φ, ?_, hp⟩
  intro μ
  apply smul_left_injective ℂ hv0
  exact (hp ⟨kpBeta μ z 0, kpBeta_zero_mem_generated μ z⟩ v hv).symm.trans
    ((mem_kpJointEigenspace_iff τ h z χ v).mp hv μ)

theorem kpJointEigenspace_inf_eq_bot_of_ne (τ : YoungDiagram)
    (h : Fintype.card A = partitionSize τ) (z : A → ℂ) (χ ψ : YoungDiagram → ℂ) (hne : χ ≠ ψ) :
    kpJointEigenspace τ h z χ ⊓ kpJointEigenspace τ h z ψ = ⊥ := by
  apply bot_unique
  intro v hv
  by_cases hz : v = 0
  · exact hz
  · apply False.elim
    apply hne
    funext μ
    apply smul_left_injective ℂ hz
    exact ((mem_kpJointEigenspace_iff τ h z χ v).mp hv.1 μ).symm.trans
      ((mem_kpJointEigenspace_iff τ h z ψ v).mp hv.2 μ)

end
end ModifiedCartan


