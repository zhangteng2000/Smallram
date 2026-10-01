import ModifiedCartan.SchubertDegreeInitialCoefficients
import ModifiedCartan.KPCorrespondenceEigenspaces
import ModifiedCartan.PolynomialInitialBasisExistence

namespace ModifiedCartan
noncomputable section
open scoped Classical BigOperators

/-- The forward correspondence supplies an actual normalized polynomial basis
    for every nonzero joint space away from zero root parameters. All centers
    of the normalized-coordinate identity are retained. -/
theorem kpJoint_identityBasis_exists {n : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin (n + 1)) = partitionSize τ)
    (z : Fin (n + 1) → ℂ) (χ : YoungDiagram → ℂ)
    (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) (hz : (∏ i, z i) ≠ 0) :
    ∃ (V : Submodule ℂ (Polynomial ℂ))
      (hV : V ∈ polynomialSchubertCell n (2 * (n + 1)) τ)
      (b : Module.Basis (Fin (n + 1)) ℂ V),
      (∀ i j : Fin (n + 1),
        (Polynomial.derivative^[i.val] (b j).val).eval 0 = if i = j then 1 else 0) ∧
      (∀ μ a, (kpJointValuePolynomial (n + 1) χ μ).eval a =
        normalizedSchubertCoordinate hV μ a) ∧
      (∀ j, (b j).val.natDegree < 2 * (n + 1)) := by
  have hs : partitionSize τ = n + 1 := hτ.symm.trans (Fintype.card_fin _)
  have hf : PartitionFits n τ :=
    (partitionFits_iff_height_le τ).mpr ((partition_colLen_le_size τ 0).trans_eq hs)
  have hD : n + 1 + τ.rowLen 0 ≤ 2 * (n + 1) := by
    have hr := partition_rowLen_le_size τ 0
    omega
  have hne' := (kpJointEigenspace_ne_bot_decidableEq_iff
    (inferInstance : DecidableEq (Fin (n + 1))) (Classical.decEq _) τ hτ z χ).mp hne
  obtain ⟨V, hV, hc⟩ := kpJointSchubertSpace_exists
    (by simp) τ hτ hf hD z χ hne'
  have hW : normalize (FewInflection.polynomialWronskian
      (fun j => ((schubertFrame hV).basis j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (-z i)) := by
    rw [← schubertMonicWronskian_eq_basis hV (schubertFrame hV).basis]
    apply Polynomial.funext
    intro a
    rw [← normalizedSchubertCoordinate_bot, hc, kpJointValuePolynomial_bot τ hτ z χ hne]
    simp only [Polynomial.C_neg, sub_neg_eq_add]
  have ha : (∏ i, (0 - -z i)) ≠ 0 := by simpa only [zero_sub, neg_neg] using hz
  obtain ⟨b, hb⟩ := polynomialBasis_exists_identity_jets (schubertFrame hV).basis 0
    (polynomialWronskian_eval_ne_zero_of_roots (schubertFrame hV).basis
      (fun i => -z i) hW 0 ha)
  refine ⟨V, hV, b, hb, ?_, ?_⟩
  · intro μ a
    simpa only [Fintype.card_fin] using (hc μ a).symm
  · intro j
    have hd := polynomialSchubertCell_natDegree_le hV (b j)
    omega

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJoint_identityBasis_exists
