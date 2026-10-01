import ModifiedCartan.SchubertCoordinatePolynomials
import ModifiedCartan.MonicPolynomialParameters
import ModifiedCartan.SchubertChartSurjectivity
import ModifiedCartan.KPForwardCorrespondence
import ModifiedCartan.PolynomialMapDensity

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

set_option maxHeartbeats 1000000 in
/-- At least one actual KP joint profile lies in the explicit Schubert chart
    over every root tuple. This is obtained from the proved forward direction. -/
theorem kpJointSchubertChart_exists {n : ℕ} (τ : YoungDiagram)
    (hM : 0 < partitionSize τ) (hτ : PartitionFits n τ)
    (z : Fin (partitionSize τ) → ℂ) :
    ∃ x : SchubertChartSlot n τ → ℂ,
      schubertMonicWronskian (schubertChartSpace_mem τ hτ le_rfl x) =
        ∏ i, (Polynomial.X + Polynomial.C (z i)) ∧
      kpJointEigenspace τ (Fintype.card_fin _) z
        (fun μ => MvPolynomial.eval x (schubertCoordinatePolynomial (n := n) τ μ)) ≠ ⊥ := by
  obtain ⟨χ, hχ⟩ := specht_exists_kpJointEigenspace τ (Fintype.card_fin _) z
  have hd : (inferInstance : DecidableEq (Fin (partitionSize τ))) = Classical.decEq _ :=
    Subsingleton.elim _ _
  have hχ' : @kpJointEigenspace (Fin (partitionSize τ)) _ (Classical.decEq _)
      τ (Fintype.card_fin _) z χ ≠ ⊥ := by
    rw [← hd]
    exact hχ
  obtain ⟨V, hV, hc, hW⟩ := kpJointWronskiFibre_exists
    (n := n) (D := n + 1 + τ.rowLen 0)
    (by simpa only [Fintype.card_fin] using hM) τ (Fintype.card_fin _) hτ le_rfl z χ hχ'
  obtain ⟨x, hx⟩ := polynomialSchubertSpace_exists_chart hV
  subst V
  refine ⟨x, hW, ?_⟩
  have he : (fun μ => MvPolynomial.eval x (schubertCoordinatePolynomial τ μ)) = χ := by
    funext μ
    rw [← normalizedSchubertCoordinate_chart τ μ hτ (le_refl _) x]
    exact hc μ
  rw [he]
  exact hχ

def schubertChartSlotEquiv {n : ℕ} (τ : YoungDiagram) (hτ : PartitionFits n τ) :
    SchubertChartSlot n τ ≃ Fin (partitionSize τ) :=
  Fintype.equivFinOfCardEq (schubertChartSlot_card τ hτ)

/-- The coefficient map of the monic Wronskian, with source and target
    indexed by the same finite set of chart slots. -/
def schubertWronskiMapPolynomial {n : ℕ} (τ : YoungDiagram) (hτ : PartitionFits n τ)
    (s : SchubertChartSlot n τ) : MvPolynomial (SchubertChartSlot n τ) ℂ :=
  schubertWronskiCoefficientPolynomial τ (schubertChartSlotEquiv τ hτ s).val

set_option maxHeartbeats 1000000 in
/-- Polynomial equations that hold on all actual KP chart points hold on the
    whole Schubert chart. This proves the density step of the alternative
    inverse-correspondence argument without a Schubert fibre-degree formula.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomial_eq_zero_of_kpJointSchubertCharts {n : ℕ} (τ : YoungDiagram)
    (hM : 0 < partitionSize τ) (hτ : PartitionFits n τ)
    (p : MvPolynomial (SchubertChartSlot n τ) ℂ)
    (hp : ∀ (z : Fin (partitionSize τ) → ℂ) (x : SchubertChartSlot n τ → ℂ),
      schubertMonicWronskian (schubertChartSpace_mem τ hτ le_rfl x) =
        ∏ i, (Polynomial.X + Polynomial.C (z i)) →
      kpJointEigenspace τ (Fintype.card_fin _) z
        (fun μ => MvPolynomial.eval x (schubertCoordinatePolynomial τ μ)) ≠ ⊥ →
      MvPolynomial.eval x p = 0) : p = 0 := by
  apply polynomial_eq_zero_of_zero_on_every_fibre (schubertWronskiMapPolynomial τ hτ) p
  intro y
  let e := schubertChartSlotEquiv τ hτ
  let c : Fin (partitionSize τ) → ℂ := fun i => y (e.symm i)
  let q := monicPolynomialFromCoefficients c
  obtain ⟨z, hz⟩ := complex_monic_eq_prod_linear q
    (monicPolynomialFromCoefficients_monic c) (monicPolynomialFromCoefficients_natDegree c)
  obtain ⟨x, hxW, hx⟩ := kpJointSchubertChart_exists τ hM hτ z
  refine ⟨x, ?_, hp z x hxW hx⟩
  funext s
  rw [schubertWronskiMapPolynomial,
    schubertWronskiCoefficientPolynomial_eval τ hτ (le_refl _) x,
    hxW, ← hz, monicPolynomialFromCoefficients_coeff]
  exact congrArg y (e.symm_apply_apply s)

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointSchubertChart_exists
#print axioms ModifiedCartan.polynomial_eq_zero_of_kpJointSchubertCharts
