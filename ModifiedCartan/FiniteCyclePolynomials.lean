import ModifiedCartan.FixedColoringTransport
import ModifiedCartan.FiniteAlphabetShift

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def finiteCyclePolynomial {A : Type*} [Fintype A] (B : Type*) [Fintype B]
    (σ : Equiv.Perm A) : MvPolynomial B ℂ :=
  permutationFixedColoringSum σ (fun b : B => (MvPolynomial.X b : MvPolynomial B ℂ))

theorem finiteCyclePolynomial_cycles {A B : Type*} [Fintype A] [Fintype B] (σ : Equiv.Perm A) :
    finiteCyclePolynomial B σ =
      ∏ c : PermutationCycles σ, finitePowerSumPolynomial B (permutationCycleWeight σ (fun _ => 1) c) :=
  permutationFixedColoringSum_cycles σ _

theorem finiteCyclePolynomial_relabel {A C B : Type*} [Fintype A] [Fintype C] [Fintype B]
    (e : A ≃ C) (σ : Equiv.Perm A) :
    finiteCyclePolynomial B (e.permCongr σ) = finiteCyclePolynomial B σ :=
  permutationFixedColoringSum_conjugate e σ _

theorem finiteCyclePolynomial_conjugate {A B : Type*} [Fintype A] [Fintype B]
    (σ h : Equiv.Perm A) : finiteCyclePolynomial B (h * σ * h⁻¹) = finiteCyclePolynomial B σ := by
  have he : h.permCongr σ = h * σ * h⁻¹ := by
    apply Equiv.ext
    intro a
    rfl
  rw [← he, finiteCyclePolynomial_relabel]

end
end ModifiedCartan

