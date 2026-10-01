import ModifiedCartan.KPJointWronskiFibre
import ModifiedCartan.SchubertDimensionTransfer

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Actual joint eigenvalues give a space in every allowed Schubert dimension,
    with the exact normalized coordinates at every center. This is the forward
    direction of manuscript `lem:KP-correspondence`, with no dimension equality
    between the polynomial space and the parameter index set assumed. -/
theorem kpJointSchubertSpace_exists {A : Type*} [Fintype A]
    (hA : 0 < Fintype.card A) {n D : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (hf : PartitionFits n τ) (hD : n + 1 + τ.rowLen 0 ≤ D) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    ∃ (V : Submodule ℂ (Polynomial ℂ)) (hV : V ∈ polynomialSchubertCell n D τ),
      ∀ μ a, normalizedSchubertCoordinate hV μ a =
        (kpJointValuePolynomial (Fintype.card A) χ μ).eval a := by
  let k := Fintype.card A - 1
  have hk : Fintype.card A = k + 1 := by dsimp [k]; omega
  obtain ⟨V, hV, hc⟩ := kpJointSchubertSpace_exists_card_dimension
    (D := k + 1 + τ.rowLen 0) hk τ hτ le_rfl z χ hne
  obtain ⟨W, G, hG⟩ := polynomialSchubertFrame_exists_dimension hV.1 hf (schubertFrame hV)
  let hW : W ∈ polynomialSchubertCell n D τ := ⟨hf, hD, ⟨G⟩⟩
  refine ⟨W, hW, ?_⟩
  intro μ a
  rw [normalizedSchubertCoordinate_eq_basis hW G.basis]
  change normalizedPartitionMinor τ G.polynomials μ a = _
  rw [hG]
  exact hc μ a

/-- Forward part of LaTeX `lem:KP-correspondence`(ii), including its monic
    Wronskian and exact normalization, for every permitted ambient dimension
    and all parameter tuples, including repeated parameters. -/
theorem kpJointWronskiFibre_exists {A : Type*} [Fintype A]
    (hA : 0 < Fintype.card A) {n D : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (hf : PartitionFits n τ) (hD : n + 1 + τ.rowLen 0 ≤ D) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    ∃ (V : Submodule ℂ (Polynomial ℂ)) (hV : V ∈ polynomialSchubertCell n D τ),
      (∀ μ, normalizedSchubertCoordinate hV μ 0 = χ μ) ∧
      schubertMonicWronskian hV = ∏ i : A, (Polynomial.X + Polynomial.C (z i)) := by
  obtain ⟨V, hV, hc⟩ := kpJointSchubertSpace_exists hA τ hτ hf hD z χ hne
  refine ⟨V, hV, ?_, ?_⟩
  · intro μ
    rw [hc, kpJointValuePolynomial_eval_zero τ hτ z χ hne μ]
  · apply Polynomial.funext
    intro a
    rw [← normalizedSchubertCoordinate_bot hV a, hc,
      kpJointValuePolynomial_bot τ hτ z χ hne]

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointSchubertSpace_exists
#print axioms ModifiedCartan.kpJointWronskiFibre_exists