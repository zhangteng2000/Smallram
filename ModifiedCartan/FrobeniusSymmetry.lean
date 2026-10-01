import ModifiedCartan.FiniteFrobeniusPolynomials
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finitePowerSumPolynomial_isSymmetric {B : Type*} [Fintype B] (j : ℕ) :
    (finitePowerSumPolynomial B j).IsSymmetric := by
  intro e
  simp only [finitePowerSumPolynomial, map_sum, map_pow, MvPolynomial.rename_X]
  exact Equiv.sum_comp e (fun b => (MvPolynomial.X b : MvPolynomial B ℂ) ^ j)

theorem finiteCyclePolynomial_isSymmetric {A B : Type*} [Fintype A] [Fintype B]
    (σ : Equiv.Perm A) : (finiteCyclePolynomial B σ).IsSymmetric := by
  intro e
  rw [finiteCyclePolynomial_cycles, map_prod]
  apply Finset.prod_congr rfl
  intro c hc
  exact finitePowerSumPolynomial_isSymmetric _ e

theorem finiteFrobeniusPolynomial_isSymmetric {B : Type*} [Fintype B] (μ : YoungDiagram) :
    (finiteFrobeniusPolynomial B μ).IsSymmetric := by
  intro e
  unfold finiteFrobeniusPolynomial finiteFrobeniusPolynomialOn
  simp only [map_mul, map_sum, MvPolynomial.rename_C, finiteCyclePolynomial_isSymmetric _ e]

end
end ModifiedCartan


