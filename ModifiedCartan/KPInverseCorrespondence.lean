import ModifiedCartan.KPPolynomialEquationTransfer
import ModifiedCartan.KPEquationPolynomials

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Every point of the Schubert chart in the prescribed Wronski fibre gives
    a nonzero actual KP joint eigenspace, including repeated roots.
    This is the inverse direction of manuscript `lem:KP-correspondence`(ii). -/
theorem kpJointEigenspace_chart_of_wronskian {n : ℕ} (τ : YoungDiagram)
    (hM : 0 < partitionSize τ) (hτ : PartitionFits n τ)
    (z : Fin (partitionSize τ) → ℂ) (x : SchubertChartSlot n τ → ℂ)
    (hW : schubertMonicWronskian (schubertChartSpace_mem τ hτ le_rfl x) =
      ∏ i, (Polynomial.X + Polynomial.C (z i))) :
    kpJointEigenspace τ (Fintype.card_fin _) z
      (fun μ => MvPolynomial.eval x (schubertCoordinatePolynomial τ μ)) ≠ ⊥ := by
  apply (kpJointEigenspace_ne_bot_decidableEq_iff
    (inferInstance : DecidableEq (Fin (partitionSize τ))) (Classical.decEq _)
    τ (Fintype.card_fin _) z _).mpr
  apply (kpJointEigenspace_chart_ne_bot_iff_finite_det τ (Fintype.card_fin _) hτ z x).mpr
  intro g
  rw [← kpEquationDeterminantPolynomial_eval₂ τ (Fintype.card_fin _) g x z]
  apply kpPolynomialEquation_vanishes_on_wronskiFibre τ hM hτ
    (kpEquationDeterminantPolynomial τ (Fintype.card_fin _) g) ?_ z x hW
  intro z' x' hW' hχ
  rw [kpEquationDeterminantPolynomial_eval₂]
  have hχ' := (kpJointEigenspace_ne_bot_decidableEq_iff
    (inferInstance : DecidableEq (Fin (partitionSize τ))) (Classical.decEq _)
    τ (Fintype.card_fin _) z'
    (fun μ => MvPolynomial.eval x' (schubertCoordinatePolynomial τ μ))).mp hχ
  exact (kpJointEigenspace_chart_ne_bot_iff_finite_det τ (Fintype.card_fin _) hτ z' x').mp hχ' g

theorem schubertMonicWronskian_eq_of_same_space {n D E : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)}
    (hV : V ∈ polynomialSchubertCell n D τ) (hW : V ∈ polynomialSchubertCell n E τ) :
    schubertMonicWronskian hV = schubertMonicWronskian hW := by
  apply Polynomial.funext
  intro a
  rw [← normalizedSchubertCoordinate_bot, ← normalizedSchubertCoordinate_bot,
    normalizedSchubertCoordinate_eq_basis hV (schubertFrame hW).basis]
  rfl

/-- Exact inverse KP correspondence for actual Schubert spaces, with no
    generic-root restriction or fibre-count assumption.
    LaTeX `lem:KP-correspondence`(ii), final sentence. -/
theorem kpJointEigenspace_of_schubertWronskiFibre {n D : ℕ} (τ : YoungDiagram)
    (hM : 0 < partitionSize τ) (z : Fin (partitionSize τ) → ℂ)
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ)
    (hW : schubertMonicWronskian hV = ∏ i, (Polynomial.X + Polynomial.C (z i))) :
    kpJointEigenspace τ (Fintype.card_fin _) z
      (fun μ => normalizedSchubertCoordinate hV μ 0) ≠ ⊥ := by
  obtain ⟨x, hx⟩ := polynomialSchubertSpace_exists_chart hV
  subst V
  have hc : (fun μ => normalizedSchubertCoordinate hV μ 0) =
      (fun μ => MvPolynomial.eval x (schubertCoordinatePolynomial τ μ)) := by
    funext μ
    exact normalizedSchubertCoordinate_chart τ μ hV.1 hV.2.1 x
  rw [hc]
  apply kpJointEigenspace_chart_of_wronskian τ hM hV.1 z x
  exact (schubertMonicWronskian_eq_of_same_space
    (schubertChartSpace_mem τ hV.1 le_rfl x) hV).trans hW

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointEigenspace_of_schubertWronskiFibre
