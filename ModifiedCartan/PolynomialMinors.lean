import FewInflection.PolynomialJets
import FewInflection.FundamentalAnalytic

open scoped BigOperators

namespace ModifiedCartan

noncomputable section

/-- Polynomial form of the determinant in LaTeX `eq:derivative-minor`. -/
def polynomialDerivativeMinor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (orders : ι → ℕ) (p : ι → Polynomial ℂ) : Polynomial ℂ :=
  (Matrix.of fun i j => Polynomial.derivative^[orders i] (p j)).det

/-- Increase a single derivative order. -/
def raiseMinorOrder {ι : Type*} [DecidableEq ι] (orders : ι → ℕ) (i : ι) : ι → ℕ :=
  Function.update orders i (orders i + 1)

@[simp] theorem raiseMinorOrder_self {ι : Type*} [DecidableEq ι]
    (orders : ι → ℕ) (i : ι) : raiseMinorOrder orders i i = orders i + 1 := by
  simp [raiseMinorOrder]

@[simp] theorem raiseMinorOrder_of_ne {ι : Type*} [DecidableEq ι]
    (orders : ι → ℕ) {i j : ι} (h : j ≠ i) :
    raiseMinorOrder orders i j = orders j := by
  simp [raiseMinorOrder, h]

theorem polynomialDerivativeMinor_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (orders : ι → ℕ) (p : ι → Polynomial ℂ) (z : ℂ) :
    (polynomialDerivativeMinor orders p).eval z =
      (Matrix.of fun i j => (Polynomial.derivative^[orders i] (p j)).eval z).det := by
  exact RingHom.map_det (Polynomial.evalRingHom z) _

theorem polynomialDerivativeMinor_eval_eq_derivativeMinor {n : ℕ}
    (orders : Fin (n + 1) → ℕ) (p : Fin (n + 1) → Polynomial ℂ) (z : ℂ) :
    (polynomialDerivativeMinor orders p).eval z =
      FewInflection.derivativeMinor orders (fun j w => (p j).eval w) z := by
  rw [polynomialDerivativeMinor_eval, FewInflection.derivativeMinor_polynomial_eval]
  rfl

theorem polynomialDerivativeMinor_wronskian {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) :
    polynomialDerivativeMinor (fun i : Fin (n + 1) => (i : ℕ)) p =
      FewInflection.polynomialWronskian p := rfl

theorem polynomialDerivativeMinor_eq_zero_of_collision {ι : Type*}
    [Fintype ι] [DecidableEq ι] (orders : ι → ℕ) (p : ι → Polynomial ℂ)
    {i j : ι} (hij : i ≠ j) (horders : orders i = orders j) :
    polynomialDerivativeMinor orders p = 0 := by
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp only [Matrix.of_apply, horders]

theorem polynomialDerivativeMinor_raised_eq_zero_of_collision {ι : Type*}
    [Fintype ι] [DecidableEq ι] (orders : ι → ℕ) (p : ι → Polynomial ℂ)
    {i j : ι} (hij : i ≠ j) (horders : orders i + 1 = orders j) :
    polynomialDerivativeMinor (raiseMinorOrder orders i) p = 0 := by
  apply polynomialDerivativeMinor_eq_zero_of_collision _ _ hij
  simpa [hij.symm] using horders

/-- Differentiating a minor raises one row at a time, with coefficient one. -/
theorem derivative_polynomialDerivativeMinor {ι : Type*}
    [Fintype ι] [DecidableEq ι] (orders : ι → ℕ) (p : ι → Polynomial ℂ) :
    (polynomialDerivativeMinor orders p).derivative =
      ∑ i : ι, polynomialDerivativeMinor (raiseMinorOrder orders i) p := by
  apply Polynomial.funext
  intro z
  rw [← Polynomial.deriv]
  have hfun : (fun w => (polynomialDerivativeMinor orders p).eval w) =
      (fun w => (Matrix.of fun i j =>
        (Polynomial.derivative^[orders i] (p j)).eval w).det) := by
    funext w
    exact polynomialDerivativeMinor_eval orders p w
  rw [hfun]
  have hd := FewInflection.deriv_det_updateRow
    (M := fun w => Matrix.of fun i j =>
      (Polynomial.derivative^[orders i] (p j)).eval w)
    (M' := fun w => Matrix.of fun i j =>
      (Polynomial.derivative^[orders i + 1] (p j)).eval w)
    (z := z) (fun i j => by
      simpa only [Function.iterate_succ_apply', Matrix.of_apply] using
        (Polynomial.derivative^[orders i] (p j)).hasDerivAt z)
  rw [hd, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [polynomialDerivativeMinor_eval]
  congr 1
  ext k j
  by_cases hki : k = i
  · subst k
    simp [Matrix.updateRow_apply]
  · simp [Matrix.updateRow_apply, hki]

end
end ModifiedCartan


