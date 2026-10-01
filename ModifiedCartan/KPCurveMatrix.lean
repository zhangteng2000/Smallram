import ModifiedCartan.KPCurvePolynomial
import ModifiedCartan.MatrixCyclic

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {N : ℕ} {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]

def kpCurveMatrixPolynomial (B : Module.Basis ι ℂ V) (ρ : Representation ℂ (Equiv.Perm (Fin N)) V)
    (μ : YoungDiagram) (z : Fin N → ℂ) (a : ℂ) : Matrix ι ι (Polynomial ℂ) := fun r c =>
  ∑ I : Finset (Fin N), kpCurveWeightPolynomial z a I *
    Polynomial.C (LinearMap.toMatrixAlgEquiv B (ρ.asAlgebraHom (kpAlpha μ I)) r c)

theorem kpCurveMatrixPolynomial_eval (B : Module.Basis ι ℂ V)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) (μ : YoungDiagram) (z : Fin N → ℂ)
    (a s : ℂ) (r c : ι) :
    (kpCurveMatrixPolynomial B ρ μ z a r c).eval s =
      LinearMap.toMatrixAlgEquiv B (ρ.asAlgebraHom (kpBeta μ (kpPolynomialParameters z s) a)) r c := by
  rw [kpBeta_eq_sum_all_subsets]
  simp only [kpCurveMatrixPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, kpCurveWeightPolynomial_eval, map_sum, map_smul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

def kpCurveCommutatorPolynomial (B : Module.Basis ι ℂ V)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) (μ ν : YoungDiagram) (z : Fin N → ℂ)
    (a b : ℂ) (r c : ι) : Polynomial ℂ :=
  (∑ k : ι, kpCurveMatrixPolynomial B ρ μ z a r k * kpCurveMatrixPolynomial B ρ ν z b k c) -
    ∑ k : ι, kpCurveMatrixPolynomial B ρ ν z b r k * kpCurveMatrixPolynomial B ρ μ z a k c

theorem kpCurveCommutatorPolynomial_eval (B : Module.Basis ι ℂ V)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) (μ ν : YoungDiagram) (z : Fin N → ℂ)
    (a b s : ℂ) (r c : ι) :
    (kpCurveCommutatorPolynomial B ρ μ ν z a b r c).eval s =
      LinearMap.toMatrixAlgEquiv B
        (ρ.asAlgebraHom (kpBeta μ (kpPolynomialParameters z s) a) *
          ρ.asAlgebraHom (kpBeta ν (kpPolynomialParameters z s) b) -
         ρ.asAlgebraHom (kpBeta ν (kpPolynomialParameters z s) b) *
          ρ.asAlgebraHom (kpBeta μ (kpPolynomialParameters z s) a)) r c := by
  simp only [kpCurveCommutatorPolynomial, Polynomial.eval_sub, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, kpCurveMatrixPolynomial_eval, map_sub, map_mul, Matrix.sub_apply,
    Matrix.mul_apply]

end
end ModifiedCartan


