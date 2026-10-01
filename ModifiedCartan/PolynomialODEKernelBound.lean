import ModifiedCartan.WronskianNontrivial
import FewInflection.PolynomialJets
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Dimension.Finite

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def polynomialFunctionLinear : Polynomial ℂ →ₗ[ℂ] (ℂ → ℂ) where
  toFun p z := p.eval z
  map_add' p q := by ext z; simp
  map_smul' c p := by ext z; simp

theorem polynomialFunctionLinear_injective : Function.Injective polynomialFunctionLinear := by
  intro p q h
  exact Polynomial.funext (fun z => congrFun h z)

theorem polynomialWronskian_ne_zero_of_linearIndependent {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (hp : LinearIndependent ℂ p) :
    FewInflection.polynomialWronskian p ≠ 0 := by
  have hfun := hp.map' polynomialFunctionLinear
    (LinearMap.ker_eq_bot.mpr polynomialFunctionLinear_injective)
  obtain ⟨z, hz⟩ := exists_wronskian_ne_zero_of_linearIndependent
    (g := fun j z => (p j).eval z) (fun j => (p j).differentiable) hfun
  intro hzero
  apply hz
  have he := congrArg (Polynomial.eval z) hzero
  simpa only [FewInflection.polynomialWronskian_eval, Polynomial.eval_zero,
    FewInflection.derivativeMinor, FewInflection.wronskian] using he

def polynomialDifferentialApply {n : ℕ} (a : Fin (n + 1) → Polynomial ℂ)
    (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ i : Fin (n + 1), a i * Polynomial.derivative^[i.val] p

/-- An order-at-most-n differential expression annihilating n+1 independent
    polynomials has all coefficients zero. Auxiliary to the differential-kernel
    argument in paper `lem:KP-correspondence`. -/
theorem polynomialDifferential_coeff_zero_of_linearIndependent {n : ℕ}
    (a : Fin (n + 1) → Polynomial ℂ) (p : Fin (n + 1) → Polynomial ℂ)
    (hp : LinearIndependent ℂ p) (ha : ∀ j, polynomialDifferentialApply a (p j) = 0) :
    a = 0 := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℂ) :=
    fun i j => Polynomial.derivative^[i.val] (p j)
  have hM : M.det ≠ 0 := polynomialWronskian_ne_zero_of_linearIndependent p hp
  apply Matrix.eq_zero_of_vecMul_eq_zero hM
  funext j
  exact ha j

/-- Exact polynomial-kernel dimension bound required by KP Proposition 2.11.
    This uses the previously proved analytic Wronskian criterion as an
    alternative proof. Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomialDifferential_subspace_finrank_le {n : ℕ}
    (a : Fin (n + 1) → Polynomial ℂ) (ha : a (Fin.last n) ≠ 0)
    (V : Submodule ℂ (Polynomial ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ p ∈ V, polynomialDifferentialApply a p = 0) :
    Module.finrank ℂ V ≤ n := by
  by_contra hn
  obtain ⟨p, hp⟩ := exists_linearIndependent_of_le_finrank
    (R := ℂ) (M := V) (show n + 1 ≤ Module.finrank ℂ V by omega)
  have hlin := hp.map' V.subtype V.ker_subtype
  have hz := polynomialDifferential_coeff_zero_of_linearIndependent a
    (fun j => (p j).val) hlin (fun j => hV (p j).val (p j).property)
  apply ha
  exact congrFun hz (Fin.last n)

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialDifferential_subspace_finrank_le
