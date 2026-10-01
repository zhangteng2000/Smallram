import ModifiedCartan.KPParameterDifferentialCoefficients
import ModifiedCartan.KPJointCharacter

namespace ModifiedCartan
noncomputable section
open scoped Classical BigOperators MonoidAlgebra IsMulCommutative
attribute [local instance] kpParameterBetheAlgebra_isMulCommutative

/-- Parameter evaluation lands in the actual generated KP algebra through
    the traditional single-column algebra. -/
def kpParameterBetheEvaluation {N : ℕ} (z : Fin N → ℂ) :
    kpParameterBetheAlgebra N →ₐ[ℂ] kpGeneratedAlgebra z :=
  ((kpParameterEvaluation z).comp
    ((kpParameterBetheAlgebra N).val.restrictScalars ℂ)).codRestrict
      (kpGeneratedAlgebra z) (fun x =>
        betheAlgebra_le_kpGeneratedAlgebra z
          (kpParameterBetheAlgebra_evaluation_mem z x.property))

theorem kpParameterBetheEvaluation_val {N : ℕ} (z : Fin N → ℂ)
    (x : kpParameterBetheAlgebra N) :
    (kpParameterBetheEvaluation z x).val = kpParameterEvaluation z x.val := rfl

theorem kpBetaPowerCoefficient_eq_zero_of_gt {N : ℕ} (μ : YoungDiagram)
    (z : Fin N → ℂ) (k : ℕ) (hk : N < k) : kpBetaPowerCoefficient μ z k = 0 := by
  unfold kpBetaPowerCoefficient
  apply Finset.sum_eq_zero
  intro I _
  have hd : (kpWeightPolynomial z I.val).natDegree < k := by
    apply lt_of_le_of_lt (kpWeightPolynomial_natDegree_le z I.val)
    have hc := Finset.card_le_card (Finset.sdiff_subset (s := Finset.univ) (t := I.val))
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd, zero_smul]

theorem kpJointValuePolynomial_coeff_zero_of_gt {N : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin N) = partitionSize τ)
    (z : Fin N → ℂ) (χ : YoungDiagram → ℂ)
    (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) (μ : YoungDiagram)
    (k : ℕ) (hk : N < k) : (kpJointValuePolynomial N χ μ).coeff k = 0 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply smul_left_injective ℂ hv0
  have he := kpBetaPowerCoefficient_action τ hτ z χ v hv μ k
  rw [kpBetaPowerCoefficient_eq_zero_of_gt μ z k hk, map_zero, LinearMap.zero_apply] at he
  simpa only [Fintype.card_fin, zero_smul] using he.symm

theorem kpParameterColumnCoefficient_character {N : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin N) = partitionSize τ)
    (z : Fin N → ℂ) (χ : YoungDiagram → ℂ)
    (hne : kpJointEigenspace τ hτ z χ ≠ ⊥)
    (φ : kpGeneratedAlgebra z →ₐ[ℂ] ℂ)
    (hφ : ∀ x : kpGeneratedAlgebra z, ∀ v ∈ kpJointEigenspace τ hτ z χ,
      (spechtRepresentationOn τ hτ).asAlgebraHom x.val v = φ x • v)
    (q k : ℕ) :
    (φ.comp (kpParameterBetheEvaluation z)) (kpParameterColumnCoefficient N q k) =
      (kpJointValuePolynomial N χ (columnPartition q)).coeff k := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply smul_left_injective ℂ hv0
  change φ (kpParameterBetheEvaluation z (kpParameterColumnCoefficient N q k)) • v = _
  rw [← hφ _ v hv]
  change (spechtRepresentationOn τ hτ).asAlgebraHom
    (kpParameterEvaluation z (kpParameterBetaCoefficient (columnPartition q) k)) v = _
  rw [kpParameterBetaCoefficient_evaluation]
  simpa only [Fintype.card_fin] using
    kpBetaPowerCoefficient_action τ hτ z χ v hv (columnPartition q) k

theorem kpParameterColumnPolynomial_character {N : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin N) = partitionSize τ)
    (z : Fin N → ℂ) (χ : YoungDiagram → ℂ)
    (hne : kpJointEigenspace τ hτ z χ ≠ ⊥)
    (φ : kpGeneratedAlgebra z →ₐ[ℂ] ℂ)
    (hφ : ∀ x : kpGeneratedAlgebra z, ∀ v ∈ kpJointEigenspace τ hτ z χ,
      (spechtRepresentationOn τ hτ).asAlgebraHom x.val v = φ x • v)
    (q : ℕ) :
    (kpParameterColumnPolynomial N q).map
      (φ.comp (kpParameterBetheEvaluation z)).toRingHom =
        kpJointValuePolynomial N χ (columnPartition q) := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map]
  by_cases hk : k < N + 1
  · rw [kpParameterColumnPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
    exact kpParameterColumnCoefficient_character τ hτ z χ hne φ hφ q k
  · rw [kpParameterColumnPolynomial, Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega),
      map_zero, kpJointValuePolynomial_coeff_zero_of_gt τ hτ z χ hne _ k (by omega)]

theorem kpParameterDifferentialCoefficients_character {N : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin N) = partitionSize τ)
    (z : Fin N → ℂ) (χ : YoungDiagram → ℂ)
    (hne : kpJointEigenspace τ hτ z χ ≠ ⊥)
    (φ : kpGeneratedAlgebra z →ₐ[ℂ] ℂ)
    (hφ : ∀ x : kpGeneratedAlgebra z, ∀ v ∈ kpJointEigenspace τ hτ z χ,
      (spechtRepresentationOn τ hτ).asAlgebraHom x.val v = φ x • v)
    (i : Fin (N + 1)) :
    (kpParameterDifferentialCoefficients N i).map
      (φ.comp (kpParameterBetheEvaluation z)).toRingHom =
      Polynomial.C ((-1 : ℂ) ^ (N - i.val)) *
        kpJointValuePolynomial N χ (columnPartition (N - i.val)) := by
  unfold kpParameterDifferentialCoefficients
  rw [Polynomial.map_mul, Polynomial.map_C,
    kpParameterColumnPolynomial_character τ hτ z χ hne φ hφ]
  have hs : (φ.comp (kpParameterBetheEvaluation z)).toRingHom
      ((-1 : kpParameterBetheAlgebra N) ^ (N - i.val)) = (-1 : ℂ) ^ (N - i.val) := by
    rw [map_pow]
    have hm := (φ.comp (kpParameterBetheEvaluation z)).toRingHom.map_neg
      (1 : kpParameterBetheAlgebra N)
    rw [(φ.comp (kpParameterBetheEvaluation z)).toRingHom.map_one] at hm
    exact congrArg (fun x : ℂ => x ^ (N - i.val)) hm
  rw [hs]

end
end ModifiedCartan

#print axioms ModifiedCartan.kpParameterDifferentialCoefficients_character
