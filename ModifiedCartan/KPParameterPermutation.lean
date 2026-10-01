import ModifiedCartan.KPJointProfileClosed
import ModifiedCartan.PermutationStar

open scoped Classical BigOperators MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem kpWeight_permute {A : Type*} [Fintype A] (z : A → ℂ)
    (a : ℂ) (I : Finset A) (u : Equiv.Perm A) :
    kpWeight (z ∘ u) a I = kpWeight z a (I.image u) := by
  have hu : (Finset.univ : Finset A).image u = Finset.univ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact u.surjective i
  have hs : (Finset.univ \ I).image u = Finset.univ \ I.image u := by
    rw [Finset.image_sdiff _ _ u.injective, hu]
  rw [kpWeight, kpWeight, ← hs, Finset.prod_image]
  · rfl
  · exact fun i hi j hj he => u.injective he

/-- Relabeling the roots conjugates the actual KP operators. -/
theorem kpBeta_parameter_conjugate {A : Type*} [Fintype A]
    (μ : YoungDiagram) (z : A → ℂ) (a : ℂ) (u : Equiv.Perm A) :
    permutationElement u * kpBeta μ (z ∘ u) a * permutationElement u⁻¹ = kpBeta μ z a := by
  rw [kpBeta_eq_sum_all_subsets, kpBeta_eq_sum_all_subsets,
    Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ I : Finset A, kpWeight z a (I.image u) • kpAlpha μ (I.image u) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [mul_smul_comm, smul_mul_assoc, kpWeight_permute]
      exact congrArg (fun q => kpWeight z a (I.image u) • q) (kpAlpha_conjugate μ I u)
    _ = _ := by
      simpa only [Equiv.finsetCongr_apply, Finset.map_eq_image, Equiv.coe_toEmbedding] using
        Equiv.sum_comp u.finsetCongr (fun I : Finset A => kpWeight z a I • kpAlpha μ I)

theorem commonEigenvector_iff_of_intertwining {K ι V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (T S : ι → Module.End K V) (χ : ι → K)
    (f : Module.End K V) (hf : Function.Bijective f)
    (h : ∀ i v, f (T i v) = S i (f v)) :
    (∃ v : V, v ≠ 0 ∧ ∀ i, T i v = χ i • v) ↔
      ∃ v : V, v ≠ 0 ∧ ∀ i, S i v = χ i • v := by
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨f v, ?_, ?_⟩
    · intro hz
      exact hv (hf.1 (hz.trans (map_zero f).symm))
    · intro i
      rw [← h, he i, map_smul]
  · rintro ⟨w, hw, he⟩
    obtain ⟨v, rfl⟩ := hf.2 w
    refine ⟨v, ?_, ?_⟩
    · intro hz
      exact hw (hz ▸ map_zero f)
    · intro i
      apply hf.1
      rw [h, he i, map_smul]

/-- The joint profile is unchanged by any permutation of the root parameters,
    including coincident roots. Auxiliary to `lem:KP-correspondence`. -/
theorem kpJointEigenspace_permute_ne_bot_iff {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ) (u : Equiv.Perm A) :
    kpJointEigenspace τ hτ (z ∘ u) χ ≠ ⊥ ↔ kpJointEigenspace τ hτ z χ ≠ ⊥ := by
  rw [kpJointEigenspace_ne_bot_iff, kpJointEigenspace_ne_bot_iff]
  apply commonEigenvector_iff_of_intertwining _ _ χ
    ((spechtRepresentationOn τ hτ) u) ((spechtRepresentationOn τ hτ).apply_bijective u)
  intro μ v
  have he := permutationElement_conjugation_cancel u _ _ (kpBeta_parameter_conjugate μ z 0 u)
  have haction := congrArg (fun q => (spechtRepresentationOn τ hτ).asAlgebraHom q v) he
  simpa only [map_mul, Module.End.mul_apply, permutationElement,
    Representation.asAlgebraHom_single_one] using haction

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointEigenspace_permute_ne_bot_iff
