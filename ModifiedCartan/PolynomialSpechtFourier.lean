import ModifiedCartan.SpechtFourierExpansion
import Mathlib.Algebra.MvPolynomial.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def polynomialSpechtCoefficient {A B : Type*} [Fintype A]
    (F : Equiv.Perm A → MvPolynomial B ℂ) (μ : SizedYoungDiagram (Fintype.card A)) :
    MvPolynomial B ℂ :=
  MvPolynomial.C ((Nat.card (Equiv.Perm A) : ℂ)⁻¹) *
    ∑ g : Equiv.Perm A, MvPolynomial.C ((sizedSpechtRepresentation μ).character g⁻¹) * F g

theorem polynomialSpechtCoefficient_coeff {A B : Type*} [Fintype A]
    (F : Equiv.Perm A → MvPolynomial B ℂ) (μ : SizedYoungDiagram (Fintype.card A)) (d : B →₀ ℕ) :
    MvPolynomial.coeff d (polynomialSpechtCoefficient F μ) =
      classFunctionFourierCoefficient (fun g => MvPolynomial.coeff d (F g)) (sizedSpechtRepresentation μ) := by
  simp only [polynomialSpechtCoefficient, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_sum, classFunctionFourierCoefficient]
  apply congrArg (fun c : ℂ => (Nat.card (Equiv.Perm A) : ℂ)⁻¹ * c)
  apply Finset.sum_congr rfl
  intro g hg
  exact mul_comm _ _

theorem polynomial_specht_fourier {A B : Type*} [Fintype A]
    (F : Equiv.Perm A → MvPolynomial B ℂ)
    (hF : ∀ g h, F (h * g * h⁻¹) = F g) (g : Equiv.Perm A) :
    F g = ∑ μ : SizedYoungDiagram (Fintype.card A),
      MvPolynomial.C ((sizedSpechtRepresentation μ).character g) * polynomialSpechtCoefficient F μ := by
  ext d
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, polynomialSpechtCoefficient_coeff]
  exact classFunction_specht_fourier (fun g => MvPolynomial.coeff d (F g))
    (fun g h => congrArg (MvPolynomial.coeff d) (hF g h)) g

end
end ModifiedCartan

