import ModifiedCartan.PolynomialSpechtFourier
import ModifiedCartan.FiniteCyclePolynomials

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The actual normalized finite character transform of cycle power sums.
Its identification with determinantal Schur polynomials is not part of this definition. -/
def finiteFrobeniusPolynomialOn {A : Type*} [Fintype A] (B : Type*) [Fintype B]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) : MvPolynomial B ℂ :=
  MvPolynomial.C ((Nat.card (Equiv.Perm A) : ℂ)⁻¹) *
    ∑ g : Equiv.Perm A, MvPolynomial.C (spechtCharacterOn μ h g⁻¹) * finiteCyclePolynomial B g

def finiteFrobeniusPolynomial (B : Type*) [Fintype B] (μ : YoungDiagram) : MvPolynomial B ℂ :=
  finiteFrobeniusPolynomialOn (A := Fin (partitionSize μ)) B μ (Fintype.card_fin _)

theorem finiteFrobeniusPolynomialOn_relabel {A C B : Type*}
    [Fintype A] [Fintype C] [Fintype B] (μ : YoungDiagram)
    (hA : Fintype.card A = partitionSize μ) (hC : Fintype.card C = partitionSize μ) (e : A ≃ C) :
    finiteFrobeniusPolynomialOn B μ hA = finiteFrobeniusPolynomialOn B μ hC := by
  unfold finiteFrobeniusPolynomialOn
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_perm, hA, hC]
  apply congrArg (fun P : MvPolynomial B ℂ => MvPolynomial.C ((↑(partitionSize μ).factorial : ℂ)⁻¹) * P)
  rw [← Equiv.sum_comp e.permCongr
    (fun g : Equiv.Perm C => MvPolynomial.C (spechtCharacterOn μ hC g⁻¹) * finiteCyclePolynomial B g)]
  apply Finset.sum_congr (by ext; simp)
  intro g hg
  have hinv : (e.permCongr g)⁻¹ = e.permCongr g⁻¹ := (map_inv e.permCongrHom g).symm
  rw [hinv, spechtCharacterOn_relabel μ hA hC e, finiteCyclePolynomial_relabel]

theorem finiteFrobeniusPolynomialOn_eq {A B : Type*} [Fintype A] [Fintype B]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) :
    finiteFrobeniusPolynomialOn B μ h = finiteFrobeniusPolynomial B μ :=
  finiteFrobeniusPolynomialOn_relabel μ h (Fintype.card_fin _) (Fintype.equivFinOfCardEq h)

/-- Exact cycle-power expansion in the finite character transforms of the
constructed Specht representations. Auxiliary to `lem:KP-correspondence`.
The later Schur-determinant identification is still a separate theorem. -/
theorem finiteCyclePolynomial_frobenius {A B : Type*} [Fintype A] [Fintype B]
    (g : Equiv.Perm A) :
    finiteCyclePolynomial B g = ∑ μ : SizedYoungDiagram (Fintype.card A),
      MvPolynomial.C (spechtCharacterOn μ.val μ.property.symm g) * finiteFrobeniusPolynomial B μ.val := by
  rw [polynomial_specht_fourier (finiteCyclePolynomial B)
    (fun σ h => finiteCyclePolynomial_conjugate σ h)]
  apply Finset.sum_congr rfl
  intro μ hμ
  change MvPolynomial.C (spechtCharacterOn μ.val μ.property.symm g) *
      finiteFrobeniusPolynomialOn B μ.val μ.property.symm = _
  rw [finiteFrobeniusPolynomialOn_eq]

end
end ModifiedCartan

