import ModifiedCartan.NormalizedCoordinates
import ModifiedCartan.ExponentialGauge
import FewInflection.Results
import FewInflection.GaugeTranscendental
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

open scoped Topology BigOperators
open Filter Set Matrix
set_option autoImplicit false
namespace ModifiedCartan

#check Fintype.linearIndependent_iff
#check Fin.sum_univ_eq_sum_range
#check Matrix.isUnit_iff_isUnit_det

/-- Nondegeneracy forces the constant coefficient matrix in a finite
power expansion to be invertible. -/
theorem powerExpansion_matrix_isUnit {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (A : Matrix (Index n) (Index n) ℂ)
    (s : ℂ → ℂ)
    (he : ∀ j z, f.coord j z = s z * ∑ k : Index n, z ^ k.val * A k j) :
    IsUnit A.det := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det A).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  have hkernel : ∀ c : Index n → ℂ, A *ᵥ c = 0 → c = 0 := by
    intro c hc
    have hsum : (∑ j : Index n, c j • f.coord j) = 0 := by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, he]
      have hz : (∑ k : Index n, z ^ k.val * ∑ j : Index n, A k j * c j) = 0 := by
        have hh (k : Index n) : (∑ j : Index n, A k j * c j) = 0 := congrFun hc k
        simp only [hh, mul_zero, Finset.sum_const_zero]
      calc
        _ = s z * ∑ k : Index n, z ^ k.val * ∑ j : Index n, A k j * c j := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [hz, mul_zero]
    funext j
    exact (Fintype.linearIndependent_iff.mp hlin) c hsum j
  intro c d hcd
  have heq : c - d = 0 := hkernel (c - d) (by rw [Matrix.mulVec_sub, hcd, sub_self])
  exact sub_eq_zero.mp heq

/-- Polynomial coordinates of degree at most n give exactly the
rational normal form when the projective curve is nondegenerate. -/
theorem rationalNormalForm_of_polynomial_degree_bound {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (p : Index n → Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ n) (s : ℂ → ℂ)
    (hs : ∀ z, s z ≠ 0) (hsd : Differentiable ℂ s)
    (he : ∀ j z, f.coord j z = s z * (p j).eval z) :
    Nonempty (FewInflection.RationalNormalForm n f) := by
  let A : Matrix (Index n) (Index n) ℂ := fun k j => (p j).coeff k.val
  have hx (j : Index n) (z : ℂ) : f.coord j z =
      s z * ∑ k : Index n, z ^ k.val * A k j := by
    rw [he, Polynomial.eval_eq_sum_range' (n := n + 1) (by have := hp j; omega),
      ← Fin.sum_univ_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  exact ⟨⟨A, powerExpansion_matrix_isUnit f hlin A s hx, s, hs, hsd, hx⟩⟩

/-- Undo translation and the actual inverse-jet change of basis at the
level of polynomial coordinates. This also supports the order-zero proof. -/
theorem gaugedCurve_polynomialRepresentation_of_normalized_polynomials {n : ℕ}
    (f : Curve n) (G : ℂ → ℂ) (hG : Differentiable ℂ G) {b : ℂ}
    (hW : FewInflection.wronskian n (gaugedCoordinates f G) b ≠ 0)
    (p : Index n → Polynomial ℂ)
    (hp : ∀ j z, normalizedCoordinates (gaugedCoordinates f G) b j z = (p j).eval z) :
    f.HasPolynomialRepresentation := by
  let q : Index n → Polynomial ℂ := fun j => ∑ i : Index n,
    Polynomial.C (iteratedDeriv i.val (gaugedCoordinates f G j) b) *
      (p i).comp (Polynomial.X - Polynomial.C b)
  refine ⟨q, fun z => Complex.exp (G z), fun z => Complex.exp_ne_zero _,
    Complex.differentiable_exp.comp hG, ?_⟩
  intro j z
  have hq : (q j).eval z = gaugedCoordinates f G j z := by
    rw [normalizedCoordinates_reconstruct hW j z]
    simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, hp]
  rw [hq]
  simp only [gaugedCoordinates, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, one_mul]

/-- Undo the translation and initial-basis matrix after the normalized
coordinates have been proved to be the divided monomials. -/
theorem gaugedCurve_rationalNormalForm_of_normalized_monomials {n : ℕ}
    (f : Curve n) (hlin : f.linearlyNonDegenerate) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) {b : ℂ}
    (hW : FewInflection.wronskian n (gaugedCoordinates f G) b ≠ 0)
    (hy : ∀ i z, normalizedCoordinates (gaugedCoordinates f G) b i z =
      z ^ i.val / (i.val.factorial : ℂ)) :
    Nonempty (FewInflection.RationalNormalForm n f) := by
  let q : Index n → Polynomial ℂ := fun j => ∑ i : Index n,
    Polynomial.C (iteratedDeriv i.val (gaugedCoordinates f G j) b / (i.val.factorial : ℂ)) *
      (Polynomial.X - Polynomial.C b) ^ i.val
  have hqdeg (j : Index n) : (q j).natDegree ≤ n := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    simpa only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] using
      (Nat.le_of_lt_succ i.isLt)
  have he (j : Index n) (z : ℂ) : f.coord j z = Complex.exp (G z) * (q j).eval z := by
    have hq : (q j).eval z = gaugedCoordinates f G j z := by
      rw [normalizedCoordinates_reconstruct hW j z]
      simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, hy]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hq]
    simp only [gaugedCoordinates, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero, one_mul]
  exact rationalNormalForm_of_polynomial_degree_bound f hlin q hqdeg (fun z => Complex.exp (G z))
    (fun z => Complex.exp_ne_zero _) (Complex.differentiable_exp.comp hG) he

theorem rationalNormalForm_of_matrixGauge {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (h : FewInflection.RationalNormalForm n (f.matrixGauge A hA)) :
    Nonempty (FewInflection.RationalNormalForm n f) := by
  classical
  obtain ⟨s, hs, hsd, he⟩ := h.factor
  let B := h.A * A⁻¹
  have hx (j : Index n) (z : ℂ) : f.coord j z = s z * ∑ k : Index n, z ^ k.val * B k j := by
    rw [FewInflection.matrixGauge_coord_mul_inverse f A hA j z]
    simp only [he, B, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact ⟨⟨B, powerExpansion_matrix_isUnit f hlin B s hx, s, hs, hsd, hx⟩⟩

end ModifiedCartan
#print axioms ModifiedCartan.powerExpansion_matrix_isUnit
#print axioms ModifiedCartan.rationalNormalForm_of_polynomial_degree_bound
#print axioms ModifiedCartan.gaugedCurve_polynomialRepresentation_of_normalized_polynomials
#print axioms ModifiedCartan.gaugedCurve_rationalNormalForm_of_normalized_monomials
#print axioms ModifiedCartan.rationalNormalForm_of_matrixGauge
