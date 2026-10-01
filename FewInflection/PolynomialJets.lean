import FewInflection.DerivativeMinors
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Polynomial jets

This file records the elementary jet identity needed when a polynomial basis
is inserted into a derivative minor.  The identity is proved from mathlib's
analytic derivative theorem for polynomial evaluation; no polynomial
approximation or analytic statement is hidden in a definition.
-/

open scoped BigOperators

namespace FewInflection

noncomputable section

def polynomialWronskian {n : ℕ} (p : Index n → Polynomial ℂ) : Polynomial ℂ :=
  Matrix.det (fun (i j : Index n) => Polynomial.derivative^[i] (p j))

theorem iteratedDeriv_polynomial_eval
    (p : Polynomial ℂ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w : ℂ => p.eval w) z =
      (Polynomial.derivative^[k] p).eval z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv k (fun w : ℂ => p.eval w) =
            (fun w : ℂ => (Polynomial.derivative^[k] p).eval w) := by
        funext w
        exact ih w
      rw [hfun]
      simp [Function.iterate_succ_apply']

theorem iteratedDeriv_polynomial_eval_zero
    (p : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun w : ℂ => p.eval w) 0 =
      (Nat.factorial k : ℂ) * p.coeff k := by
  rw [iteratedDeriv_polynomial_eval, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

theorem polynomial_coeff_eq_jet
    (p : Polynomial ℂ) (k : ℕ) :
    p.coeff k = iteratedDeriv k (fun w : ℂ => p.eval w) 0 /
      (Nat.factorial k : ℂ) := by
  rw [iteratedDeriv_polynomial_eval_zero]
  have hk : (Nat.factorial k : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp

theorem polynomial_taylor_coeff_eq_jet
    (p : Polynomial ℂ) (a : ℂ) (k : ℕ) :
    (p.taylor a).coeff k =
      iteratedDeriv k (fun w : ℂ => p.eval w) a /
        (Nat.factorial k : ℂ) := by
  rw [polynomial_coeff_eq_jet]
  simp only [Polynomial.taylor_eval]
  rw [iteratedDeriv_comp_add_const k (fun w : ℂ => p.eval w) a]
  simp only [zero_add]

theorem factorial_mul_polynomial_taylor_coeff_eq_jet
    (p : Polynomial ℂ) (a : ℂ) (k : ℕ) :
    (Nat.factorial k : ℂ) * (p.taylor a).coeff k =
      iteratedDeriv k (fun w : ℂ => p.eval w) a := by
  rw [polynomial_taylor_coeff_eq_jet]
  have hk : (Nat.factorial k : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- Exact Taylor reconstruction for a polynomial of degree at most `d`. -/
theorem polynomial_eval_eq_jet_sum
    (p : Polynomial ℂ) {d : ℕ} (hd : p.natDegree ≤ d) (a z : ℂ) :
    p.eval z = ∑ k ∈ Finset.range (d + 1),
      (iteratedDeriv k (fun w : ℂ => p.eval w) a /
        (Nat.factorial k : ℂ)) * (z - a) ^ k := by
  rw [← Polynomial.taylor_eval_sub a p z]
  rw [Polynomial.eval_eq_sum_range' (n := d + 1) (by
    rw [Polynomial.natDegree_taylor]
    omega)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [polynomial_taylor_coeff_eq_jet]

theorem norm_polynomial_eval_le_jet_sum
    (p : Polynomial ℂ) {d : ℕ} (hd : p.natDegree ≤ d)
    {a z : ℂ} {R : ℝ} (hR : ‖z - a‖ ≤ R) :
    ‖p.eval z‖ ≤
      ∑ k ∈ Finset.range (d + 1),
        ‖iteratedDeriv k (fun w : ℂ => p.eval w) a‖ /
            (Nat.factorial k : ℝ) * R ^ k := by
  rw [polynomial_eval_eq_jet_sum p hd a z]
  calc
    ‖∑ k ∈ Finset.range (d + 1),
          (iteratedDeriv k (fun w : ℂ => p.eval w) a /
            (Nat.factorial k : ℂ)) * (z - a) ^ k‖
        ≤ ∑ k ∈ Finset.range (d + 1),
          ‖(iteratedDeriv k (fun w : ℂ => p.eval w) a /
            (Nat.factorial k : ℂ)) * (z - a) ^ k‖ := by
      exact norm_sum_le (Finset.range (d + 1)) _
    _ ≤ ∑ k ∈ Finset.range (d + 1),
          ‖iteratedDeriv k (fun w : ℂ => p.eval w) a‖ /
            (Nat.factorial k : ℝ) * R ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, norm_div, norm_natCast, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hR k)
        (div_nonneg (norm_nonneg _) (by positivity))

theorem norm_polynomial_combination_eval_le_jet_sum
    {n : ℕ} (p : Index n → Polynomial ℂ) (c : Index n → ℂ)
    {d : ℕ} (hd : ∀ j : Index n, (p j).natDegree ≤ d)
    {a z : ℂ} {R : ℝ} (hR : ‖z - a‖ ≤ R) :
    ‖∑ j : Index n, c j * (p j).eval z‖ ≤
      ∑ j : Index n, ‖c j‖ *
        (∑ k ∈ Finset.range (d + 1),
          ‖iteratedDeriv k (fun w : ℂ => (p j).eval w) a‖ /
            (Nat.factorial k : ℝ) * R ^ k) := by
  calc
    ‖∑ j : Index n, c j * (p j).eval z‖ ≤
        ∑ j : Index n, ‖c j * (p j).eval z‖ := by
      exact norm_sum_le (Finset.univ : Finset (Index n)) _
    _ = ∑ j : Index n, ‖c j‖ * ‖(p j).eval z‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul]
    _ ≤ ∑ j : Index n, ‖c j‖ *
        (∑ k ∈ Finset.range (d + 1),
          ‖iteratedDeriv k (fun w : ℂ => (p j).eval w) a‖ /
            (Nat.factorial k : ℝ) * R ^ k) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (norm_polynomial_eval_le_jet_sum (p j) (hd j) hR)
        (norm_nonneg _)

theorem derivativeMinor_polynomial_eval
    {n : ℕ} (orders : Index n → ℕ)
    (p : Index n → Polynomial ℂ) (z : ℂ) :
    derivativeMinor orders (fun j w => (p j).eval w) z =
      Matrix.det (fun (i j : Index n) =>
        (Polynomial.derivative^[orders i] (p j)).eval z) := by
  simp only [derivativeMinor]
  congr 1
  funext i j
  exact iteratedDeriv_polynomial_eval (p j) (orders i) z

theorem polynomialWronskian_eval
    {n : ℕ} (p : Index n → Polynomial ℂ) (z : ℂ) :
    (polynomialWronskian p).eval z =
      derivativeMinor (fun i : Index n => (i : ℕ))
        (fun j w => (p j).eval w) z := by
  let M : Matrix (Index n) (Index n) (Polynomial ℂ) :=
    fun i j => Polynomial.derivative^[i] (p j)
  calc
    (polynomialWronskian p).eval z = (Polynomial.evalRingHom z) M.det := by
      rfl
    _ = ((Polynomial.evalRingHom z).mapMatrix M).det :=
      RingHom.map_det (Polynomial.evalRingHom z) M
    _ = Matrix.det (fun i j => (Polynomial.evalRingHom z) (M i j)) := by
      rfl
    _ = derivativeMinor (fun i : Index n => (i : ℕ))
        (fun j w => (p j).eval w) z := by
      simp [derivativeMinor, M]
      congr 1
      funext i j
      exact (iteratedDeriv_polynomial_eval (p j) (i : ℕ) z).symm

theorem polynomialWronskian_natDegree_le
    {n : ℕ} (p : Index n → Polynomial ℂ) :
    (polynomialWronskian p).natDegree ≤ ∑ j : Index n, (p j).natDegree := by
  classical
  let M : Matrix (Index n) (Index n) (Polynomial ℂ) :=
    fun i j => Polynomial.derivative^[i] (p j)
  change M.det.natDegree ≤ _
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  simp only [M]
  calc
    (Equiv.Perm.sign σ • ∏ i : Index n,
        Polynomial.derivative^[σ i] (p i)).natDegree
        ≤ (∏ i : Index n, Polynomial.derivative^[σ i] (p i)).natDegree :=
      Polynomial.natDegree_smul_le _ _
    _ ≤ ∑ i : Index n,
        (Polynomial.derivative^[σ i] (p i)).natDegree := by
      simpa using (Polynomial.natDegree_prod_le
        (s := (Finset.univ : Finset (Index n)))
        (f := fun i : Index n => Polynomial.derivative^[σ i] (p i)))
    _ ≤ ∑ i : Index n, (p i).natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Polynomial.natDegree_iterate_derivative (p i) (σ i : ℕ)).trans
        (Nat.sub_le _ _)

end

end FewInflection
