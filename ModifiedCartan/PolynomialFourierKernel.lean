import ModifiedCartan.PolynomialSpechtFourier
import Mathlib.Algebra.MvPolynomial.Rename

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem polynomialSpechtCoefficient_inverse_sum {A B : Type*} [Fintype A]
    (F : Equiv.Perm A → MvPolynomial B ℂ) (μ : SizedYoungDiagram (Fintype.card A)) :
    polynomialSpechtCoefficient F μ =
      MvPolynomial.C ((Nat.card (Equiv.Perm A) : ℂ)⁻¹) *
        ∑ g : Equiv.Perm A, MvPolynomial.C ((sizedSpechtRepresentation μ).character g) * F g⁻¹ := by
  unfold polynomialSpechtCoefficient
  apply congrArg (fun P : MvPolynomial B ℂ => MvPolynomial.C ((Nat.card (Equiv.Perm A) : ℂ)⁻¹) * P)
  symm
  simpa only [Equiv.inv_apply, inv_inv] using
    Equiv.sum_comp (Equiv.inv (Equiv.Perm A))
      (fun g => MvPolynomial.C ((sizedSpechtRepresentation μ).character g⁻¹) * F g)

/-- The finite character Fourier expansion gives its bilinear reproducing kernel. -/
theorem polynomial_specht_kernel {A B : Type*} [Fintype A]
    (F G : Equiv.Perm A → MvPolynomial B ℂ)
    (hF : ∀ g h, F (h * g * h⁻¹) = F g) :
    MvPolynomial.C ((Nat.card (Equiv.Perm A) : ℂ)⁻¹) *
      (∑ g : Equiv.Perm A, F g * G g⁻¹) =
        ∑ μ : SizedYoungDiagram (Fintype.card A),
          polynomialSpechtCoefficient F μ * polynomialSpechtCoefficient G μ := by
  calc
    _ = MvPolynomial.C ((Nat.card (Equiv.Perm A) : ℂ)⁻¹) *
        ∑ g : Equiv.Perm A, ∑ μ : SizedYoungDiagram (Fintype.card A),
          (MvPolynomial.C ((sizedSpechtRepresentation μ).character g) *
            polynomialSpechtCoefficient F μ) * G g⁻¹ := by
      congr 1
      apply Finset.sum_congr rfl
      intro g hg
      rw [polynomial_specht_fourier F hF g, Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [polynomialSpechtCoefficient_inverse_sum G μ]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      ring

theorem polynomialSpechtCoefficient_rename {A B C : Type*} [Fintype A]
    (F : Equiv.Perm A → MvPolynomial B ℂ) (f : B → C)
    (μ : SizedYoungDiagram (Fintype.card A)) :
    polynomialSpechtCoefficient (fun g => MvPolynomial.rename f (F g)) μ =
      MvPolynomial.rename f (polynomialSpechtCoefficient F μ) := by
  simp only [polynomialSpechtCoefficient, map_mul, map_sum, MvPolynomial.rename_C]

end
end ModifiedCartan


