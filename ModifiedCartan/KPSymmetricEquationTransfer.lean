import ModifiedCartan.SymmetricPolynomialSpecialization
import ModifiedCartan.KPWronskiMapDominance

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Every symmetric polynomial equation that holds on actual KP profiles
    holds throughout the corresponding Wronski fibre. This is the precise
    descent step in the alternative proof of `lem:KP-correspondence`. -/
theorem kpSymmetricEquation_vanishes_on_wronskiFibre {n : ℕ} (τ : YoungDiagram)
    (hM : 0 < partitionSize τ) (hτ : PartitionFits n τ)
    (p : MvPolynomial (Fin (partitionSize τ)) (MvPolynomial (SchubertChartSlot n τ) ℂ))
    (hs : p.IsSymmetric)
    (hp : ∀ (z : Fin (partitionSize τ) → ℂ) (x : SchubertChartSlot n τ → ℂ),
      schubertMonicWronskian (schubertChartSpace_mem τ hτ le_rfl x) =
        ∏ i, (Polynomial.X + Polynomial.C (z i)) →
      kpJointEigenspace τ (Fintype.card_fin _) z
        (fun μ => MvPolynomial.eval x (schubertCoordinatePolynomial τ μ)) ≠ ⊥ →
      MvPolynomial.eval₂ (MvPolynomial.eval x) z p = 0) :
    ∀ (z : Fin (partitionSize τ) → ℂ) (x : SchubertChartSlot n τ → ℂ),
      schubertMonicWronskian (schubertChartSpace_mem τ hτ le_rfl x) =
        ∏ i, (Polynomial.X + Polynomial.C (z i)) →
      MvPolynomial.eval₂ (MvPolynomial.eval x) z p = 0 := by
  let w : Fin (Fintype.card (Fin (partitionSize τ))) → MvPolynomial (SchubertChartSlot n τ) ℂ :=
    fun i => schubertWronskiCoefficientPolynomial τ (partitionSize τ - (i.val + 1))
  obtain ⟨q, hq⟩ := symmetricPolynomial_exists_specialization p hs w
  have hvalues (z : Fin (partitionSize τ) → ℂ) (x : SchubertChartSlot n τ → ℂ)
      (hW : schubertMonicWronskian (schubertChartSpace_mem τ hτ le_rfl x) =
        ∏ i, (Polynomial.X + Polynomial.C (z i)))
      (i : Fin (Fintype.card (Fin (partitionSize τ)))) :
      MvPolynomial.eval x (w i) = MvPolynomial.eval₂ (MvPolynomial.eval x) z
        (MvPolynomial.esymm (Fin (partitionSize τ)) (MvPolynomial (SchubertChartSlot n τ) ℂ)
          (i.val + 1)) := by
    change MvPolynomial.eval x (schubertWronskiCoefficientPolynomial τ _) = _
    rw [schubertWronskiCoefficientPolynomial_eval τ hτ (le_refl _) x, hW]
    exact (eval₂_esymm_eq_linearProduct_coeff x z
      ⟨i.val, by simpa only [Fintype.card_fin] using i.isLt⟩).symm
  have hzero : q = 0 := by
    apply polynomial_eq_zero_of_kpJointSchubertCharts τ hM hτ q
    intro z x hW hχ
    rw [hq x z (hvalues z x hW)]
    exact hp z x hW hχ
  intro z x hW
  rw [← hq x z (hvalues z x hW), hzero, map_zero]

end
end ModifiedCartan

#print axioms ModifiedCartan.kpSymmetricEquation_vanishes_on_wronskiFibre
