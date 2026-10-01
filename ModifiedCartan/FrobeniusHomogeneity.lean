import ModifiedCartan.FiniteFrobeniusPolynomials
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteCyclePolynomial_isHomogeneous {A B : Type*} [Fintype A] [Fintype B]
    (σ : Equiv.Perm A) : (finiteCyclePolynomial B σ).IsHomogeneous (Fintype.card A) := by
  unfold finiteCyclePolynomial permutationFixedColoringSum
  apply MvPolynomial.IsHomogeneous.sum
  intro f hf
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun a : A => (MvPolynomial.X (f.val a) : MvPolynomial B ℂ)) (fun _ => 1)
    (fun a _ => MvPolynomial.isHomogeneous_X ℂ (f.val a))
  simpa using h

theorem finiteFrobeniusPolynomial_isHomogeneous {B : Type*} [Fintype B] (μ : YoungDiagram) :
    (finiteFrobeniusPolynomial B μ).IsHomogeneous (partitionSize μ) := by
  unfold finiteFrobeniusPolynomial finiteFrobeniusPolynomialOn
  apply MvPolynomial.IsHomogeneous.C_mul
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  apply MvPolynomial.IsHomogeneous.C_mul
  simpa only [Fintype.card_fin] using finiteCyclePolynomial_isHomogeneous (B := B) σ

end
end ModifiedCartan


