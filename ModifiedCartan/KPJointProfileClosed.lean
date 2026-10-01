import ModifiedCartan.ClosedJointEigenprofiles
import ModifiedCartan.KPRealJointDecomposition

open scoped Classical BigOperators Topology

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

theorem continuous_kpWeight {A : Type*} [Fintype A] (a : ℂ) (I : Finset A) :
    Continuous (fun z : A → ℂ => kpWeight z a I) := by
  apply continuous_finsetProd
  intro i hi
  exact continuous_const.add (continuous_apply i)

/-- The actual KP action varies continuously with the parameters and vector.
    Auxiliary to the collision argument in manuscript `lem:KP-correspondence`. -/
theorem continuous_specht_kpBeta_action {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (μ : YoungDiagram) (a : ℂ) :
    Continuous (fun x : (A → ℂ) × YoungSpechtModule τ =>
      (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ x.1 a) x.2) := by
  simp only [kpBeta_eq_sum_all_subsets, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply]
  apply continuous_finsetSum
  intro I hI
  exact ((continuous_kpWeight a I).comp continuous_fst).smul
    (((spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ I)).continuous_of_finiteDimensional.comp
      continuous_snd)

theorem kpJointEigenspace_ne_bot_iff {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ) :
    kpJointEigenspace τ hτ z χ ≠ ⊥ ↔
      ∃ v : YoungSpechtModule τ, v ≠ 0 ∧
        ∀ μ, (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z 0) v = χ μ • v := by
  constructor
  · intro h
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact ⟨v, hv0, (mem_kpJointEigenspace_iff τ hτ z χ v).mp hv⟩
  · rintro ⟨v, hv0, hv⟩ he
    have hm := (mem_kpJointEigenspace_iff τ hτ z χ v).mpr hv
    rw [he] at hm
    exact hv0 hm

set_option maxHeartbeats 800000 in
/-- Closedness of actual KP joint profiles, including colliding parameters.
    This proves the eigenvalue-limit step of manuscript `lem:KP-correspondence`. -/
theorem isClosed_kpJointProfiles {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) :
    IsClosed {q : (A → ℂ) × (YoungDiagram → ℂ) |
      kpJointEigenspace τ hτ q.1 q.2 ≠ ⊥} := by
  simp only [kpJointEigenspace_ne_bot_iff]
  apply isClosed_commonEigenvector_parameters
    (fun q : (A → ℂ) × (YoungDiagram → ℂ) => fun μ =>
      (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ q.1 0))
    (fun q : (A → ℂ) × (YoungDiagram → ℂ) => q.2)
  · intro μ
    have hc : Continuous (fun x : ((A → ℂ) × (YoungDiagram → ℂ)) × YoungSpechtModule τ =>
        (x.1.1, x.2)) :=
      (continuous_fst.comp continuous_fst).prodMk continuous_snd
    have ht := (continuous_specht_kpBeta_action τ hτ μ 0).comp hc
    exact ht
  · intro μ
    exact (continuous_apply μ).comp continuous_snd

/-- A convergent family of actual KP profiles retains a nonzero joint eigenspace.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem kpJointEigenspace_ne_bot_of_tendsto {A B : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    {l : Filter B} [l.NeBot] {q : B → (A → ℂ) × (YoungDiagram → ℂ)}
    {q₀ : (A → ℂ) × (YoungDiagram → ℂ)} (hq : Filter.Tendsto q l (𝓝 q₀))
    (hne : ∀ᶠ b in l, kpJointEigenspace τ hτ (q b).1 (q b).2 ≠ ⊥) :
    kpJointEigenspace τ hτ q₀.1 q₀.2 ≠ ⊥ :=
  (isClosed_kpJointProfiles τ hτ).mem_of_tendsto hq hne

end
end ModifiedCartan

#print axioms ModifiedCartan.isClosed_kpJointProfiles
#print axioms ModifiedCartan.kpJointEigenspace_ne_bot_of_tendsto
