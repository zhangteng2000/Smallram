import FewInflection.InitialBasis

/-!
# Constant matrix changes of polynomial bases

The derivative-minor invariance already holds for functions.  This file gives
the corresponding polynomial identity before evaluation: a constant change of
polynomial basis multiplies the polynomial Wronskian by the determinant of the
change-of-basis matrix.  It is a direct determinant calculation.
-/

open scoped BigOperators

namespace FewInflection

noncomputable section

def polynomialMatrixGauge {n : ℕ} (A : Matrix (Index n) (Index n) ℂ)
    (p : Index n → Polynomial ℂ) : Index n → Polynomial ℂ :=
  fun j => ∑ k : Index n, Polynomial.C (A k j) * p k

def polynomialJetMatrix {n : ℕ} (p : Index n → Polynomial ℂ) (a : ℂ) :
    Matrix (Index n) (Index n) ℂ :=
  fun i j => (Polynomial.derivative^[(i : ℕ)] (p j)).eval a

def polynomialInitialBasis {n : ℕ} (p : Index n → Polynomial ℂ) (a : ℂ)
    (j : Index n) : Polynomial ℂ :=
  polynomialMatrixGauge (polynomialJetMatrix p a)⁻¹ p j

theorem polynomialJetMatrix_eq_jetMatrix_eval
    {n : ℕ} (p : Index n → Polynomial ℂ) (a : ℂ) :
    polynomialJetMatrix p a =
      jetMatrix (fun j z => (p j).eval z) a := by
  ext i j
  exact (iteratedDeriv_polynomial_eval (p j) (i : ℕ) a).symm

theorem polynomialInitialBasis_eval
    {n : ℕ} (p : Index n → Polynomial ℂ) (a z : ℂ) (j : Index n) :
    (polynomialInitialBasis p a j).eval z =
      initialBasis (fun k w => (p k).eval w) a j z := by
  rw [polynomialInitialBasis, initialBasis]
  rw [polynomialJetMatrix_eq_jetMatrix_eval]
  simp [polynomialMatrixGauge, initialBasisCoeff, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem polynomialInitialBasis_derivative
    {n : ℕ} (p : Index n → Polynomial ℂ) {a : ℂ}
    (hW : (polynomialWronskian p).eval a ≠ 0) :
    ∀ i j : Index n,
      iteratedDeriv (i : ℕ)
          (fun z => (polynomialInitialBasis p a j).eval z) a =
        if i = j then 1 else 0 := by
  have hEq : (polynomialWronskian p).eval a =
      wronskian n (fun j z => (p j).eval z) a := by
    simpa [wronskian, derivativeMinor] using polynomialWronskian_eval p a
  have hW' : wronskian n (fun j z => (p j).eval z) a ≠ 0 := by
    rw [← hEq]
    exact hW
  have hcont : ∀ i j : Index n,
      ContDiffAt ℂ (i : ℕ) (fun z => (p j).eval z) a := by
    intro i j
    exact (p j).differentiable.contDiff.contDiffAt
  intro i j
  have heq : (fun z => (polynomialInitialBasis p a j).eval z) =
      initialBasis (fun k z => (p k).eval z) a j := by
    funext z
    exact polynomialInitialBasis_eval p a z j
  rw [heq]
  exact initialBasis_derivative hW' hcont i j

theorem polynomialInitialBasis_natDegree_le
    {n : ℕ} (p : Index n → Polynomial ℂ) (a : ℂ) (j : Index n) :
    (polynomialInitialBasis p a j).natDegree ≤
      ∑ k : Index n, (p k).natDegree := by
  unfold polynomialInitialBasis polynomialMatrixGauge
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  calc
    (Polynomial.C ((polynomialJetMatrix p a)⁻¹ k j) * p k).natDegree ≤
        (p k).natDegree := by
      rw [← Polynomial.smul_eq_C_mul]
      exact Polynomial.natDegree_smul_le _ _
    _ ≤ ∑ l : Index n, (p l).natDegree := by
      simpa using (Finset.single_le_sum
        (s := (Finset.univ : Finset (Index n)))
        (f := fun l : Index n => (p l).natDegree)
        (fun l hl => Nat.zero_le _) (Finset.mem_univ k))

theorem norm_polynomialInitialBasis_eval_le_jet_sum
    {n : ℕ} (p : Index n → Polynomial ℂ) (a z : ℂ) (j : Index n)
    {d : ℕ} (hd : (∑ k : Index n, (p k).natDegree) ≤ d)
    {R : ℝ} (hR : ‖z - a‖ ≤ R) :
    ‖(polynomialInitialBasis p a j).eval z‖ ≤
      ∑ k ∈ Finset.range (d + 1),
        ‖iteratedDeriv k
          (fun w : ℂ => (polynomialInitialBasis p a j).eval w) a‖ /
            (Nat.factorial k : ℝ) * R ^ k := by
  apply norm_polynomial_eval_le_jet_sum
  · exact (polynomialInitialBasis_natDegree_le p a j).trans hd
  · exact hR

theorem iterate_derivative_polynomialMatrixGauge
    {n : ℕ} (A : Matrix (Index n) (Index n) ℂ)
    (p : Index n → Polynomial ℂ) (k : ℕ) (j : Index n) :
    Polynomial.derivative^[k] (polynomialMatrixGauge A p j) =
      ∑ l : Index n,
        Polynomial.C (A l j) * Polynomial.derivative^[k] (p l) := by
  simp [polynomialMatrixGauge, Polynomial.iterate_derivative_sum,
    Polynomial.iterate_derivative_C_mul]

theorem polynomialWronskian_matrixGauge
    {n : ℕ} (A : Matrix (Index n) (Index n) ℂ)
    (p : Index n → Polynomial ℂ) :
    polynomialWronskian (polynomialMatrixGauge A p) =
      polynomialWronskian p * Polynomial.C A.det := by
  classical
  let P : Matrix (Index n) (Index n) (Polynomial ℂ) :=
    fun i j => Polynomial.derivative^[i] (p j)
  let B : Matrix (Index n) (Index n) (Polynomial ℂ) :=
    fun i j => Polynomial.C (A i j)
  have hmat :
      (fun (i j : Index n) => Polynomial.derivative^[(i : ℕ)]
        (polynomialMatrixGauge A p j)) = P * B := by
    funext i j
    rw [iterate_derivative_polynomialMatrixGauge A p (i : ℕ) j]
    change (∑ l : Index n,
      Polynomial.C (A l j) * Polynomial.derivative^[(i : ℕ)] (p l)) =
      ∑ l : Index n, P i l * B l j
    simp [P, B, mul_comm]
  have hdetB : B.det = Polynomial.C A.det := by
    have hmap := RingHom.map_det (Polynomial.C : ℂ →+* Polynomial ℂ) A
    calc
      B.det = ((Polynomial.C : ℂ →+* Polynomial ℂ).mapMatrix A).det := by
        rfl
      _ = Polynomial.C A.det := hmap.symm
  calc
    polynomialWronskian (polynomialMatrixGauge A p) =
        Matrix.det (fun (i j : Index n) => Polynomial.derivative^[(i : ℕ)]
          (polynomialMatrixGauge A p j)) := by
      rfl
    _ = (P * B).det := by rw [hmat]
    _ = P.det * B.det := Matrix.det_mul P B
    _ = P.det * Polynomial.C A.det := by rw [hdetB]
    _ = polynomialWronskian p * Polynomial.C A.det := by rfl

theorem polynomialWronskian_matrixGauge_eval
    {n : ℕ} (A : Matrix (Index n) (Index n) ℂ)
    (p : Index n → Polynomial ℂ) (z : ℂ) :
    (polynomialWronskian (polynomialMatrixGauge A p)).eval z =
      A.det * (polynomialWronskian p).eval z := by
  rw [polynomialWronskian_matrixGauge]
  simp [Polynomial.eval_mul, mul_comm]

theorem polynomialInitialBasis_wronskian_eval_one
    {n : ℕ} (p : Index n → Polynomial ℂ) {a : ℂ}
    (hW : (polynomialWronskian p).eval a ≠ 0) :
    (polynomialWronskian
      (fun j => polynomialInitialBasis p a j)).eval a = 1 := by
  let M : Matrix (Index n) (Index n) ℂ := polynomialJetMatrix p a
  have hmat :
      (fun (i j : Index n) =>
        iteratedDeriv (i : ℕ) (fun w : ℂ => (p j).eval w) a) = M := by
    funext i j
    exact iteratedDeriv_polynomial_eval (p j) (i : ℕ) a
  have hMdet : M.det = (polynomialWronskian p).eval a := by
    calc
      M.det = Matrix.det (fun (i j : Index n) =>
          iteratedDeriv (i : ℕ) (fun w : ℂ => (p j).eval w) a) := by
            rw [hmat]
      _ = (polynomialWronskian p).eval a :=
        (polynomialWronskian_eval p a).symm
  have hdet : M.det ≠ 0 := by
    rw [hMdet]
    exact hW
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hprod := Matrix.det_nonsing_inv_mul_det M hunit
  have hgate := polynomialWronskian_matrixGauge_eval (A := M⁻¹) p a
  have hgate' :
      (polynomialWronskian
        (fun j => polynomialInitialBasis p a j)).eval a =
        M⁻¹.det * (polynomialWronskian p).eval a := by
    simpa [polynomialInitialBasis, M] using hgate
  rw [← hMdet] at hgate'
  rw [hgate']
  exact hprod

end

end FewInflection
