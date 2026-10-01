import FewInflection.Gauge

open scoped BigOperators Topology
open MeasureTheory Metric Set

namespace FewInflection

noncomputable section

def matrixGaugeBound {n : ℕ} (A : Matrix (Index n) (Index n) ℂ) : ℝ :=
  ∑ k : Index n, ∑ j : Index n, (1 + ‖A k j‖)

lemma matrixGaugeBound_pos {n : ℕ} (A : Matrix (Index n) (Index n) ℂ) :
    0 < matrixGaugeBound A := by
  unfold matrixGaugeBound
  positivity

lemma one_le_matrixGaugeBound {n : ℕ}
    (A : Matrix (Index n) (Index n) ℂ) :
    1 ≤ matrixGaugeBound A := by
  let k₀ : Index n := ⟨0, Nat.zero_lt_succ n⟩
  let j₀ : Index n := ⟨0, Nat.zero_lt_succ n⟩
  have hinner : 1 ≤ ∑ j : Index n, (1 + ‖A k₀ j‖) := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Index n => (1 + ‖A k₀ j‖ : ℝ))
      (fun j hj => by positivity) (Finset.mem_univ j₀)
    have hterm : (1 : ℝ) ≤ 1 + ‖A k₀ j₀‖ := by
      linarith [norm_nonneg (A k₀ j₀)]
    exact hterm.trans (by simpa [j₀] using h)
  have houter : (∑ j : Index n, (1 + ‖A k₀ j‖)) ≤
      ∑ k : Index n, ∑ j : Index n, (1 + ‖A k j‖) := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun k : Index n => ∑ j : Index n, (1 + ‖A k j‖))
      (fun k hk => by positivity) (Finset.mem_univ k₀)
  exact le_trans hinner houter

lemma vecMul_norm_le_matrixGaugeBound {n : ℕ}
    (A : Matrix (Index n) (Index n) ℂ) (v : Index n → ℂ) :
    ‖Matrix.vecMul v A‖ ≤ matrixGaugeBound A * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonempty (Matrix.vecMul v A)).2
  intro j
  have hrow : ∀ k : Index n,
      1 + ‖A k j‖ ≤ ∑ j' : Index n, (1 + ‖A k j'‖) := by
    intro k
    simpa using (Finset.single_le_sum (s := Finset.univ)
      (f := fun j' : Index n => (1 + ‖A k j'‖ : ℝ))
      (fun j' hj' => by positivity) (Finset.mem_univ j))
  have hcol : (∑ k : Index n, (1 + ‖A k j‖)) ≤ matrixGaugeBound A := by
    unfold matrixGaugeBound
    exact Finset.sum_le_sum (fun k hk => hrow k)
  change ‖∑ k : Index n, v k * A k j‖ ≤ matrixGaugeBound A * ‖v‖
  calc
    ‖∑ k : Index n, v k * A k j‖ ≤ ∑ k : Index n, ‖v k * A k j‖ := norm_sum_le _ _
    _ = ∑ k : Index n, (‖v k‖ * ‖A k j‖) := by simp
    _ ≤ ∑ k : Index n, (‖v‖ * (1 + ‖A k j‖)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hv : ‖v k‖ ≤ ‖v‖ := norm_le_pi_norm v k
      have ha : ‖A k j‖ ≤ 1 + ‖A k j‖ := by linarith [norm_nonneg (A k j)]
      exact mul_le_mul hv ha (norm_nonneg (A k j)) (norm_nonneg v)
    _ = ‖v‖ * (∑ k : Index n, (1 + ‖A k j‖)) := by rw [Finset.mul_sum]
    _ ≤ ‖v‖ * matrixGaugeBound A := mul_le_mul_of_nonneg_left hcol (norm_nonneg v)
    _ = matrixGaugeBound A * ‖v‖ := by ring

lemma vecMul_norm_le_matrixGaugeBound_inv {n : ℕ}
    (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (v : Index n → ℂ) :
    ‖v‖ ≤ matrixGaugeBound A⁻¹ * ‖Matrix.vecMul v A‖ := by
  have hvec : Matrix.vecMul (Matrix.vecMul v A) A⁻¹ = v := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hA, Matrix.vecMul_one]
  calc
    ‖v‖ = ‖Matrix.vecMul (Matrix.vecMul v A) A⁻¹‖ := by rw [hvec]
    _ ≤ matrixGaugeBound A⁻¹ * ‖Matrix.vecMul v A‖ :=
      vecMul_norm_le_matrixGaugeBound A⁻¹ (Matrix.vecMul v A)

lemma matrixGauge_vector_norm_le {n : ℕ}
    (f : Curve n) (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (z : ℂ) :
    ‖(f.matrixGauge A hA).vector z‖ ≤ matrixGaugeBound A * ‖f.vector z‖ := by
  rw [Curve.matrixGauge_vector]
  exact vecMul_norm_le_matrixGaugeBound A (f.vector z)

lemma matrixGauge_vector_norm_le_inv {n : ℕ}
    (f : Curve n) (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (z : ℂ) :
    ‖f.vector z‖ ≤ matrixGaugeBound A⁻¹ * ‖(f.matrixGauge A hA).vector z‖ := by
  rw [Curve.matrixGauge_vector]
  exact vecMul_norm_le_matrixGaugeBound_inv A hA (f.vector z)

lemma matrixGauge_log_norm_le {n : ℕ}
    (f : Curve n) (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (z : ℂ) :
    Real.log ‖(f.matrixGauge A hA).vector z‖ ≤
      Real.log (matrixGaugeBound A) + Real.log ‖f.vector z‖ := by
  have hB : 0 < matrixGaugeBound A := matrixGaugeBound_pos A
  have hv : 0 < ‖f.vector z‖ := norm_pos_iff.mpr (f.vector_ne_zero z)
  have hg : 0 < ‖(f.matrixGauge A hA).vector z‖ :=
    norm_pos_iff.mpr ((f.matrixGauge A hA).vector_ne_zero z)
  have hmul : 0 < matrixGaugeBound A * ‖f.vector z‖ := mul_pos hB hv
  have hlog := (Real.strictMonoOn_log.le_iff_le hg hmul).2
    (matrixGauge_vector_norm_le f A hA z)
  rw [Real.log_mul (ne_of_gt hB) (ne_of_gt hv)] at hlog
  exact hlog

lemma matrixGauge_log_norm_le_inv {n : ℕ}
    (f : Curve n) (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (z : ℂ) :
    Real.log ‖f.vector z‖ ≤
      Real.log (matrixGaugeBound A⁻¹) +
        Real.log ‖(f.matrixGauge A hA).vector z‖ := by
  have hB : 0 < matrixGaugeBound A⁻¹ := matrixGaugeBound_pos A⁻¹
  have hg : 0 < ‖(f.matrixGauge A hA).vector z‖ :=
    norm_pos_iff.mpr ((f.matrixGauge A hA).vector_ne_zero z)
  have hf : 0 < ‖f.vector z‖ := norm_pos_iff.mpr (f.vector_ne_zero z)
  have hmul : 0 < matrixGaugeBound A⁻¹ *
      ‖(f.matrixGauge A hA).vector z‖ := mul_pos hB hg
  have hlog := (Real.strictMonoOn_log.le_iff_le hf hmul).2
    (matrixGauge_vector_norm_le_inv f A hA z)
  rw [Real.log_mul (ne_of_gt hB) (ne_of_gt hg)] at hlog
  exact hlog

lemma characteristic_matrixGauge_le {n : ℕ}
    (f : Curve n) (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (r : ℝ) :
    characteristic (f.matrixGauge A hA) r ≤ characteristic f r +
      Real.log (matrixGaugeBound A) + Real.log (matrixGaugeBound A⁻¹) := by
  have hvec_cont_f : Continuous (fun z : ℂ => ‖f.vector z‖) := by
    exact (continuous_pi (fun j => (f.holomorphic j).continuous)).norm
  have hlog_cont_f : Continuous (fun z : ℂ => Real.log ‖f.vector z‖) := by
    apply hvec_cont_f.log
    intro z
    exact norm_ne_zero_iff.mpr (f.vector_ne_zero z)
  have hvec_cont_g : Continuous
      (fun z : ℂ => ‖(f.matrixGauge A hA).vector z‖) := by
    exact (continuous_pi (fun j => ((f.matrixGauge A hA).holomorphic j).continuous)).norm
  have hlog_cont_g : Continuous
      (fun z : ℂ => Real.log ‖(f.matrixGauge A hA).vector z‖) := by
    apply hvec_cont_g.log
    intro z
    exact norm_ne_zero_iff.mpr ((f.matrixGauge A hA).vector_ne_zero z)
  have hlog_int_f (s : ℝ) : CircleIntegrable
      (fun z : ℂ => Real.log ‖f.vector z‖) 0 s :=
    hlog_cont_f.continuousOn.circleIntegrable'
  have hlog_int_g (s : ℝ) : CircleIntegrable
      (fun z : ℂ => Real.log ‖(f.matrixGauge A hA).vector z‖) 0 s :=
    hlog_cont_g.continuousOn.circleIntegrable'
  have hsum_int (s : ℝ) : CircleIntegrable
      (fun z : ℂ => Real.log (matrixGaugeBound A) +
        Real.log ‖f.vector z‖) 0 s := by
    exact (continuous_const.add hlog_cont_f).continuousOn.circleIntegrable'
  have hpoint : ∀ z ∈ sphere (0 : ℂ) |r|,
      Real.log ‖(f.matrixGauge A hA).vector z‖ ≤
        Real.log (matrixGaugeBound A) + Real.log ‖f.vector z‖ := by
    intro z hz
    exact matrixGauge_log_norm_le f A hA z
  have havg : Real.circleAverage
      (fun z : ℂ => Real.log ‖(f.matrixGauge A hA).vector z‖) 0 r ≤
      Real.circleAverage
        (fun z : ℂ => Real.log (matrixGaugeBound A) +
          Real.log ‖f.vector z‖) 0 r :=
    Real.circleAverage_mono (hlog_int_g r) (hsum_int r) hpoint
  rw [Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
      (hlog_int_f r), Real.circleAverage_const] at havg
  have hcenter := matrixGauge_log_norm_le_inv f A hA 0
  unfold characteristic at *
  linarith

lemma characteristic_le_matrixGauge {n : ℕ}
    (f : Curve n) (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (r : ℝ) :
    characteristic f r ≤ characteristic (f.matrixGauge A hA) r +
      Real.log (matrixGaugeBound A⁻¹) + Real.log (matrixGaugeBound A) := by
  have hvec_cont_f : Continuous (fun z : ℂ => ‖f.vector z‖) := by
    exact (continuous_pi (fun j => (f.holomorphic j).continuous)).norm
  have hlog_cont_f : Continuous (fun z : ℂ => Real.log ‖f.vector z‖) := by
    apply hvec_cont_f.log
    intro z
    exact norm_ne_zero_iff.mpr (f.vector_ne_zero z)
  have hvec_cont_g : Continuous
      (fun z : ℂ => ‖(f.matrixGauge A hA).vector z‖) := by
    exact (continuous_pi (fun j => ((f.matrixGauge A hA).holomorphic j).continuous)).norm
  have hlog_cont_g : Continuous
      (fun z : ℂ => Real.log ‖(f.matrixGauge A hA).vector z‖) := by
    apply hvec_cont_g.log
    intro z
    exact norm_ne_zero_iff.mpr ((f.matrixGauge A hA).vector_ne_zero z)
  have hlog_int_f (s : ℝ) : CircleIntegrable
      (fun z : ℂ => Real.log ‖f.vector z‖) 0 s :=
    hlog_cont_f.continuousOn.circleIntegrable'
  have hlog_int_g (s : ℝ) : CircleIntegrable
      (fun z : ℂ => Real.log ‖(f.matrixGauge A hA).vector z‖) 0 s :=
    hlog_cont_g.continuousOn.circleIntegrable'
  have hsum_int (s : ℝ) : CircleIntegrable
      (fun z : ℂ => Real.log (matrixGaugeBound A⁻¹) +
        Real.log ‖(f.matrixGauge A hA).vector z‖) 0 s := by
    exact (continuous_const.add hlog_cont_g).continuousOn.circleIntegrable'
  have hpoint : ∀ z ∈ sphere (0 : ℂ) |r|,
      Real.log ‖f.vector z‖ ≤
        Real.log (matrixGaugeBound A⁻¹) +
          Real.log ‖(f.matrixGauge A hA).vector z‖ := by
    intro z hz
    exact matrixGauge_log_norm_le_inv f A hA z
  have havg : Real.circleAverage (fun z : ℂ => Real.log ‖f.vector z‖) 0 r ≤
      Real.circleAverage
        (fun z : ℂ => Real.log (matrixGaugeBound A⁻¹) +
          Real.log ‖(f.matrixGauge A hA).vector z‖) 0 r :=
    Real.circleAverage_mono (hlog_int_f r) (hsum_int r) hpoint
  rw [Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
      (hlog_int_g r), Real.circleAverage_const] at havg
  have hcenter := matrixGauge_log_norm_le f A hA 0
  unfold characteristic at *
  linarith

lemma characteristic_matrixGauge_abs_sub_le {n : ℕ}
    (f : Curve n) (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (r : ℝ) :
    |characteristic (f.matrixGauge A hA) r - characteristic f r| ≤
      Real.log (matrixGaugeBound A) + Real.log (matrixGaugeBound A⁻¹) := by
  have h₁ := characteristic_matrixGauge_le f A hA r
  have h₂ := characteristic_le_matrixGauge f A hA r
  have hB : 1 ≤ matrixGaugeBound A := one_le_matrixGaugeBound A
  have hBi : 1 ≤ matrixGaugeBound A⁻¹ := one_le_matrixGaugeBound A⁻¹
  have hlogB : 0 ≤ Real.log (matrixGaugeBound A) :=
    Real.log_nonneg hB
  have hlogBi : 0 ≤ Real.log (matrixGaugeBound A⁻¹) :=
    Real.log_nonneg hBi
  rw [abs_le]
  constructor <;> linarith

end

end FewInflection
