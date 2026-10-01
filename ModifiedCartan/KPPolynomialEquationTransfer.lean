import ModifiedCartan.KPSymmetricEquationTransfer
import ModifiedCartan.KPParameterPermutation
import ModifiedCartan.SymmetricOrbitPolynomial

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

theorem kpJointEigenspace_ne_bot_decidableEq_iff {A : Type*} [Fintype A]
    (d e : DecidableEq A) (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ) :
    (@kpJointEigenspace A _ d τ hτ z χ ≠ ⊥) ↔
      (@kpJointEigenspace A _ e τ hτ z χ ≠ ⊥) := by
  have he : d = e := Subsingleton.elim _ _
  cases he
  rfl

theorem kpJointEigenspace_fin_permute_ne_bot_iff {M : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin M) = partitionSize τ)
    (z : Fin M → ℂ) (χ : YoungDiagram → ℂ) (u : Equiv.Perm (Fin M)) :
    kpJointEigenspace τ hτ (z ∘ u) χ ≠ ⊥ ↔ kpJointEigenspace τ hτ z χ ≠ ⊥ := by
  let d : DecidableEq (Fin M) := inferInstance
  let e : DecidableEq (Fin M) := Classical.decEq _
  exact (kpJointEigenspace_ne_bot_decidableEq_iff d e τ hτ (z ∘ u) χ).trans
    ((kpJointEigenspace_permute_ne_bot_iff τ hτ z χ u).trans
      (kpJointEigenspace_ne_bot_decidableEq_iff d e τ hτ z χ).symm)

/-- Polynomial equations valid on actual KP joint profiles hold at every
    polynomial Schubert space with the given Wronskian, including collisions.
    Root relabeling and symmetric orbit equations turn the proved density
    statement into this full-fibre assertion. Auxiliary to `lem:KP-correspondence`. -/
theorem kpPolynomialEquation_vanishes_on_wronskiFibre {n : ℕ} (τ : YoungDiagram)
    (hM : 0 < partitionSize τ) (hτ : PartitionFits n τ)
    (p : MvPolynomial (Fin (partitionSize τ)) (MvPolynomial (SchubertChartSlot n τ) ℂ))
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
  intro z x hW
  apply eval₂_eq_zero_of_symmetricOrbitPolynomial (MvPolynomial.eval x)
    (fun c => ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩) z p
  intro c
  apply kpSymmetricEquation_vanishes_on_wronskiFibre τ hM hτ
    (symmetricOrbitPolynomial p c) (symmetricOrbitPolynomial_isSymmetric p c) ?_ z x hW
  intro z' x' hW' hχ
  apply symmetricOrbitPolynomial_eval₂_eq_zero
  intro u
  apply hp (z' ∘ u) x'
  · exact hW'.trans (Equiv.prod_comp u
      (fun i => Polynomial.X + Polynomial.C (z' i))).symm
  · exact (kpJointEigenspace_fin_permute_ne_bot_iff τ (Fintype.card_fin _) z'
      (fun μ => MvPolynomial.eval x' (schubertCoordinatePolynomial τ μ)) u).mpr hχ

end
end ModifiedCartan

#print axioms ModifiedCartan.kpPolynomialEquation_vanishes_on_wronskiFibre
