import ModifiedCartan.StaircaseWeights
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteExponent_monomial {R : Type*} [CommSemiring R] {m : ℕ}
    (e : Fin m → ℕ) (c : R) :
    MvPolynomial.monomial (finiteExponent e) c =
      MvPolynomial.C c * ∏ i : Fin m, (MvPolynomial.X i : MvPolynomial (Fin m) R) ^ e i := by
  rw [MvPolynomial.monomial_eq, (finiteExponent e).prod_fintype _ (fun _ => pow_zero _)]
  rfl

/-- The literal finite alternant, auxiliary to paper `lem:KP-correspondence`. -/
def finiteAlternant {m : ℕ} (e : Fin m → ℕ) : MvPolynomial (Fin m) ℂ :=
  ∑ σ : Equiv.Perm (Fin m),
    MvPolynomial.monomial (finiteExponent (e ∘ σ)) ((Equiv.Perm.sign σ : ℤ) : ℂ)

theorem finiteAlternant_eq_det {m : ℕ} (e : Fin m → ℕ) :
    finiteAlternant e = Matrix.det (fun i j : Fin m =>
      (MvPolynomial.X j : MvPolynomial (Fin m) ℂ) ^ e i) := by
  erw [Matrix.det_apply']
  simp only [finiteAlternant, finiteExponent_monomial,
    Function.comp_apply, map_intCast]

theorem finiteAlternant_coeff_mul {m : ℕ} (e : Fin m → ℕ)
    (d : Fin m →₀ ℕ) (F : MvPolynomial (Fin m) ℂ) :
    MvPolynomial.coeff d (finiteAlternant e * F) =
      ∑ σ : Equiv.Perm (Fin m), if finiteExponent (e ∘ σ) ≤ d then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          MvPolynomial.coeff (d - finiteExponent (e ∘ σ)) F else 0 := by
  simp only [finiteAlternant, Finset.sum_mul, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial_mul']

def finiteVandermondeAlternant (m : ℕ) : MvPolynomial (Fin m) ℂ :=
  finiteAlternant (fun i => i.rev.val)

theorem finiteVandermondeAlternant_coeff_mul {m : ℕ}
    (d : Fin m →₀ ℕ) (F : MvPolynomial (Fin m) ℂ) :
    MvPolynomial.coeff d (finiteVandermondeAlternant m * F) =
      ∑ σ : Equiv.Perm (Fin m), if finitePermutedStaircaseDegree σ ≤ d then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          MvPolynomial.coeff (d - finitePermutedStaircaseDegree σ) F else 0 :=
  finiteAlternant_coeff_mul _ _ _

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteAlternant_eq_det
