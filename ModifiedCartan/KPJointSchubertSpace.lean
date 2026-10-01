import ModifiedCartan.KPJointPolynomialTuple
import ModifiedCartan.SchubertFrameReconstruction

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Every actual nonzero joint eigenspace produces a Schubert space in the
    parameter-cardinality dimension, with all exact normalized coordinates.
    This is a proved direction of manuscript `lem:KP-correspondence`; transfer
    to arbitrary allowed dimensions and the converse fibre direction remain
    separate obligations. -/
theorem kpJointSchubertSpace_exists_card_dimension {A : Type*} [Fintype A]
    {n D : ℕ} (hn : Fintype.card A = n + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (hD : n + 1 + τ.rowLen 0 ≤ D) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    ∃ (V : Submodule ℂ (Polynomial ℂ)) (hV : V ∈ polynomialSchubertCell n D τ),
      ∀ μ a, normalizedSchubertCoordinate hV μ a =
        (kpJointValuePolynomial (Fintype.card A) χ μ).eval a := by
  obtain ⟨p, c, hp, hc, hm⟩ := kpJointPolynomialTuple_exists hn τ hτ z χ hne
  have ht : PartitionFits n τ := (partitionFits_iff_height_le τ).mpr
    ((partition_colLen_le_size τ 0).trans_eq (hτ.symm.trans hn))
  have hs : ∀ μ : YoungDiagram, ¬ μ ≤ τ → (partitionPolynomialMinor μ p).eval 0 = 0 := by
    intro μ hμ
    have h := hm μ 0
    rw [kpJointValuePolynomial_eq_zero_of_not_le τ hτ z χ hne μ hμ,
      Polynomial.eval_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  obtain ⟨V, F, hF⟩ := polynomialSchubertFrame_exists_of_minor_support τ ht p
    (kpJointPolynomialTuple_top_ne_zero τ hτ z χ hne p c hm 0) hs
  let hV : V ∈ polynomialSchubertCell n D τ := ⟨ht, hD, ⟨F⟩⟩
  refine ⟨V, hV, ?_⟩
  intro μ a
  rw [normalizedSchubertCoordinate_eq_basis hV F.basis]
  change normalizedPartitionMinor τ F.polynomials μ a = _
  rw [hF]
  exact kpJointPolynomialTuple_normalized τ hτ z χ hne p c hm μ a

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointSchubertSpace_exists_card_dimension