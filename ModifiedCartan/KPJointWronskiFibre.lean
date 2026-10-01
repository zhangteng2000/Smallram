import ModifiedCartan.KPJointSchubertSpace
import ModifiedCartan.SchubertMonicWronskian

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Forward Wronski-fibre correspondence in parameter-cardinality dimension.
    All parameters, including repeated ones, are covered. Auxiliary to
    manuscript `lem:KP-correspondence`; the dimension transfer and converse
    are separate obligations. -/
theorem kpJointWronskiFibre_exists_card_dimension {A : Type*} [Fintype A]
    {n D : ℕ} (hn : Fintype.card A = n + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (hD : n + 1 + τ.rowLen 0 ≤ D) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    ∃ (V : Submodule ℂ (Polynomial ℂ)) (hV : V ∈ polynomialSchubertCell n D τ),
      (∀ μ, normalizedSchubertCoordinate hV μ 0 = χ μ) ∧
      schubertMonicWronskian hV = ∏ i : A, (Polynomial.X + Polynomial.C (z i)) := by
  obtain ⟨V, hV, hc⟩ := kpJointSchubertSpace_exists_card_dimension hn τ hτ hD z χ hne
  refine ⟨V, hV, ?_, ?_⟩
  · intro μ
    rw [hc, kpJointValuePolynomial_eval_zero τ hτ z χ hne μ]
  · apply Polynomial.funext
    intro a
    rw [← normalizedSchubertCoordinate_bot hV a, hc,
      kpJointValuePolynomial_bot τ hτ z χ hne]

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointWronskiFibre_exists_card_dimension