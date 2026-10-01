import FewInflection.Definitions

open scoped BigOperators Topology
open Filter Asymptotics

namespace FewInflection

noncomputable section

namespace Curve

/-- Multiplication by a nonzero constant is a reduced homogeneous gauge. -/
def constGauge {n : ℕ} (f : Curve n) (c : ℂ) (hc : c ≠ 0) : Curve n where
  coord := fun j z => c * f.coord j z
  holomorphic := by
    intro j
    exact (f.holomorphic j).const_mul c
  reduced := by
    intro z
    rcases f.reduced z with ⟨j, hj⟩
    exact ⟨j, mul_ne_zero hc hj⟩

/-- Multiplication by a nowhere-zero holomorphic scalar gauge. -/
def scalarGauge {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g) : Curve n where
  coord := fun j z => g z * f.coord j z
  holomorphic := by
    intro j
    exact hgd.mul (f.holomorphic j)
  reduced := by
    intro z
    rcases f.reduced z with ⟨j, hj⟩
    exact ⟨j, mul_ne_zero (hg z) hj⟩

/-! Constant invertible linear changes of homogeneous coordinates. -/
def matrixGauge {n : ℕ} (f : Curve n) (A : Matrix (Index n) (Index n) ℂ)
    (hA : IsUnit A.det) : Curve n where
  coord := fun j z => ∑ k : Index n, f.coord k z * A k j
  holomorphic := by
    intro j
    have hsum : Differentiable ℂ
        (∑ k : Index n, fun z : ℂ => f.coord k z * A k j) := by
      apply Differentiable.sum
      intro k hk
      exact (f.holomorphic k).mul_const _
    convert hsum using 1
    funext z
    simp
  reduced := by
    intro z
    by_contra hzero
    push_neg at hzero
    have hmv : Matrix.vecMul (f.vector z) A = 0 := by
      funext j
      change (∑ k : Index n, f.coord k z * A k j) = 0
      exact hzero j
    have hzvec : f.vector z = 0 := by
      apply (Matrix.vecMul_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det A).2 hA))
      simpa using hmv
    exact (f.vector_ne_zero z) hzvec

theorem matrixGauge_vector {n : ℕ} (f : Curve n)
    (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det) (z : ℂ) :
    (matrixGauge f A hA).vector z = Matrix.vecMul (f.vector z) A := by
  funext j
  simp [matrixGauge, Curve.vector, Matrix.vecMul, dotProduct]

theorem matrixGauge_wronskian {n : ℕ} (f : Curve n)
    (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det) (z : ℂ) :
    wronskian n (matrixGauge f A hA).coord z =
      wronskian n f.coord z * A.det := by
  apply wronskian_matrix_gauge f.coord A z
  intro i j
  have hAcoord : AnalyticOnNhd ℂ (f.coord j) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)
  exact (hAcoord z (Set.mem_univ _)).contDiffAt

theorem matrixGauge_linearlyNonDegenerate {n : ℕ} (f : Curve n)
    (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (hlin : f.linearlyNonDegenerate) :
    (matrixGauge f A hA).linearlyNonDegenerate := by
  unfold Curve.linearlyNonDegenerate at hlin ⊢
  rw [Fintype.linearIndependent_iff] at hlin ⊢
  intro c hc j
  have hcoeff : ∀ k : Index n, ∑ j : Index n, A k j * c j = 0 := by
    intro k
    have hcoefffun :
        (∑ k : Index n, (∑ j : Index n, A k j * c j) • f.coord k) = 0 := by
      funext z
      have hz := congrFun hc z
      simp only [Finset.sum_apply, Pi.zero_apply] at hz ⊢
      simp [matrixGauge, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
        mul_comm, mul_left_comm, mul_assoc] at hz
      rw [Finset.sum_comm] at hz
      simpa [matrixGauge, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
        mul_comm, mul_left_comm, mul_assoc] using hz
    exact hlin (fun k => ∑ j : Index n, A k j * c j) hcoefffun k
  have hmul : Matrix.mulVec A c = 0 := by
    funext k
    change ∑ j : Index n, A k j * c j = 0
    exact hcoeff k
  have hc0 : c = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det A).2 hA))
    simpa using hmul
  exact congrFun hc0 j

/-! Exact characteristic invariance is available for those constant gauges that
    preserve the chosen finite-product norm. -/
theorem characteristic_matrixGauge_of_vector_norm_eq
    {n : ℕ} (f : Curve n) (A : Matrix (Index n) (Index n) ℂ)
    (hA : IsUnit A.det)
    (hnorm : ∀ v : Index n → ℂ, ‖Matrix.vecMul v A‖ = ‖v‖) :
    characteristic (matrixGauge f A hA) = characteristic f := by
  funext r
  unfold characteristic
  rw [show (fun z : ℂ => Real.log ‖(matrixGauge f A hA).vector z‖) =
      (fun z : ℂ => Real.log ‖f.vector z‖) by
        funext z
        rw [matrixGauge_vector f A hA z, hnorm]]
  rw [matrixGauge_vector f A hA 0, hnorm]

theorem constGauge_vector {n : ℕ} (f : Curve n) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (constGauge f c hc).vector z = c • f.vector z := by
  funext j
  rfl

theorem scalarGauge_vector {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g) (z : ℂ) :
    (scalarGauge f g hg hgd).vector z = g z • f.vector z := by
  funext j
  simp [scalarGauge, Curve.vector, smul_eq_mul]

theorem constGauge_wronskian {n : ℕ} (f : Curve n) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    wronskian n (constGauge f c hc).coord z =
      c ^ (n + 1) * wronskian n f.coord z := by
  apply wronskian_const_gauge f.coord c z
  intro i j
  have hA : AnalyticOnNhd ℂ (f.coord j) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)
  exact (hA z (Set.mem_univ z)).contDiffAt

theorem characteristic_constGauge {n : ℕ} (f : Curve n) (c : ℂ) (hc : c ≠ 0) :
    characteristic (constGauge f c hc) = characteristic f := by
  have hvec_cont : Continuous (fun z : ℂ => ‖f.vector z‖) := by
    exact (continuous_pi (fun j => (f.holomorphic j).continuous)).norm
  have hlog_cont : Continuous (fun z : ℂ => Real.log ‖f.vector z‖) := by
    apply hvec_cont.log
    intro z
    exact norm_ne_zero_iff.mpr (f.vector_ne_zero z)
  have hlog_int (r : ℝ) :
      CircleIntegrable (fun z : ℂ => Real.log ‖f.vector z‖) 0 r :=
    hlog_cont.continuousOn.circleIntegrable'
  have hlog_int_g (r : ℝ) :
      CircleIntegrable (fun z : ℂ => Real.log ‖c‖ + Real.log ‖f.vector z‖) 0 r := by
    exact (continuous_const.add hlog_cont).continuousOn.circleIntegrable'
  have hlog_mul (z : ℂ) :
      Real.log ‖(constGauge f c hc).vector z‖ =
        Real.log ‖c‖ + Real.log ‖f.vector z‖ := by
    rw [constGauge_vector, norm_smul,
      Real.log_mul (norm_ne_zero_iff.mpr hc)
        (norm_ne_zero_iff.mpr (f.vector_ne_zero z))]
  funext r
  unfold characteristic
  rw [show (fun z : ℂ => Real.log ‖(constGauge f c hc).vector z‖) =
      (fun z : ℂ => Real.log ‖c‖ + Real.log ‖f.vector z‖) by
        funext z; exact hlog_mul z]
  rw [Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
    (hlog_int r), Real.circleAverage_const]
  rw [hlog_mul 0]
  ring

theorem characteristic_continuous {n : ℕ} (f : Curve n) :
    Continuous (characteristic f) := by
  have hvec_cont : Continuous (fun z : ℂ => ‖f.vector z‖) := by
    exact (continuous_pi (fun j => (f.holomorphic j).continuous)).norm
  have hlog_cont : Continuous (fun z : ℂ => Real.log ‖f.vector z‖) := by
    apply hvec_cont.log
    intro z
    exact norm_ne_zero_iff.mpr (f.vector_ne_zero z)
  unfold characteristic
  exact (Real.Continuous.circleAverage hlog_cont).sub continuous_const

end Curve

end

end FewInflection
