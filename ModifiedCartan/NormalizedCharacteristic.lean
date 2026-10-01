import ModifiedCartan.NormalizedCoordinates
import ModifiedCartan.ExponentialGauge

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def jetReconstructionBound {n : ℕ} (g : Index n → ℂ → ℂ) (b : ℂ) : ℝ :=
  1 + ∑ j, ∑ i : Index n, ‖iteratedDeriv i.val (g j) b‖

theorem jetReconstructionBound_pos {n : ℕ} (g : Index n → ℂ → ℂ) (b : ℂ) :
    0 < jetReconstructionBound g b := by unfold jetReconstructionBound; positivity

theorem jet_column_sum_le_reconstructionBound {n : ℕ} (g : Index n → ℂ → ℂ)
    (b : ℂ) (j : Index n) :
    (∑ i : Index n, ‖iteratedDeriv i.val (g j) b‖) ≤ jetReconstructionBound g b := by
  have hh : (∑ i : Index n, ‖iteratedDeriv i.val (g j) b‖) ≤
      ∑ k : Index n, ∑ i : Index n, ‖iteratedDeriv i.val (g k) b‖ := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Index n))) =>
      Finset.sum_nonneg (fun (i : Index n) _ => norm_nonneg (iteratedDeriv i.val (g k) b)))
    (Finset.mem_univ j)
  unfold jetReconstructionBound
  linarith

theorem norm_linearCombination_le {n : ℕ} (c v : Index n → ℂ) {M : ℝ}
    (hv : ∀ i, ‖v i‖ ≤ M) :
    ‖∑ i : Index n, c i * v i‖ ≤ (∑ i : Index n, ‖c i‖) * M := by
  calc
    ‖∑ i : Index n, c i * v i‖ ≤ ∑ i : Index n, ‖c i‖ * ‖v i‖ := by
      simpa only [norm_mul] using norm_sum_le (s := Finset.univ)
        (f := fun i : Index n => c i * v i)
    _ ≤ ∑ i : Index n, ‖c i‖ * M :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _))
    _ = _ := (Finset.sum_mul Finset.univ (fun i : Index n => ‖c i‖) M).symm

theorem normalizedCoordinates_component_bound {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) {b : ℂ}
    (hW : FewInflection.wronskian n g b ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    {z : ℂ} (hz : z ∈ closedBall 0 r) (j : Index n) :
    ‖g j z‖ ≤ jetReconstructionBound g b *
      systemMaximum (normalizedCoordinates g b) (r + ‖b‖) := by
  have hy (i : Index n) := (normalizedCoordinates_differentiable hg b i).continuous
  have hzero : normalizedCoordinates g b 0 0 = 1 := by
    simpa using normalizedCoordinates_initialJets hg hW 0 0
  have hM := one_le_systemMaximum hy hzero (by positivity : 0 ≤ r + ‖b‖)
  have hY (i : Index n) : ‖normalizedCoordinates g b i (z - b)‖ ≤
      systemMaximum (normalizedCoordinates g b) (r + ‖b‖) := by
    apply (norm_le_maximumModulus (hy i) (r := r + ‖b‖) ?_).trans
      (maximumModulus_le_systemMaximum _ _ i)
    have hnz : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    rw [mem_closedBall, dist_zero_right]
    exact (norm_sub_le z b).trans (by linarith)
  have hcomb := norm_linearCombination_le
    (fun i : Index n => iteratedDeriv i.val (g j) b)
    (fun i : Index n => normalizedCoordinates g b i (z - b)) hY
  have hbound := mul_le_mul_of_nonneg_right (jet_column_sum_le_reconstructionBound g b j)
    (zero_le_one.trans hM)
  exact (congrArg (fun w : ℂ => ‖w‖) (normalizedCoordinates_reconstruct hW j z)).le.trans
    (hcomb.trans hbound)

theorem normalizedCoordinates_euclidean_bound {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) {b : ℂ}
    (hW : FewInflection.wronskian n g b ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    {z : ℂ} (hz : z ∈ closedBall 0 r) :
    euclideanNorm (fun j => g j z) ≤ (Real.sqrt (n + 1 : ℝ) * jetReconstructionBound g b) *
      systemMaximum (normalizedCoordinates g b) (r + ‖b‖) := by
  have hzero : normalizedCoordinates g b 0 0 = 1 := by
    simpa using normalizedCoordinates_initialJets hg hW 0 0
  have hM := one_le_systemMaximum (fun i => (normalizedCoordinates_differentiable hg b i).continuous)
    hzero (by positivity : 0 ≤ r + ‖b‖)
  have hnorm : ‖fun j => g j z‖ ≤ jetReconstructionBound g b *
      systemMaximum (normalizedCoordinates g b) (r + ‖b‖) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (jetReconstructionBound_pos g b).le
      (zero_le_one.trans hM))).mpr
    exact normalizedCoordinates_component_bound hg hW hr hz
  exact (euclideanNorm_le (fun j => g j z)).trans
    ((mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)).trans_eq (by ring))

/-- The characteristic part of LaTeX `eq:small-order-T`, for the
actual inverse-jet coordinates of any reduced entire curve. -/
theorem normalizedCoordinates_characteristic_bound {n : ℕ} (g : Curve n) {b : ℂ}
    (hW : FewInflection.wronskian n g.coord b ≠ 0) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → characteristic g r ≤
      systemLogMaximum (normalizedCoordinates g.coord b) (r + ‖b‖) + C := by
  let K := Real.sqrt (n + 1 : ℝ) * jetReconstructionBound g.coord b
  have hK : 0 < K := mul_pos (Real.sqrt_pos.mpr (by positivity)) (jetReconstructionBound_pos _ _)
  refine ⟨Real.log K - Real.log (euclideanNorm (g.vector 0)), ?_⟩
  intro r hr
  have hzero : normalizedCoordinates g.coord b 0 0 = 1 := by
    simpa using normalizedCoordinates_initialJets g.holomorphic hW 0 0
  have hM := one_le_systemMaximum
    (fun i => (normalizedCoordinates_differentiable g.holomorphic b i).continuous)
    hzero (by positivity : 0 ≤ r + ‖b‖)
  have havg := Real.circleAverage_mono_on_of_le_circle
    (curve_log_euclideanNorm_continuous g).continuousOn.circleIntegrable'
    (a := Real.log K + systemLogMaximum (normalizedCoordinates g.coord b) (r + ‖b‖))
    (by
      intro z hz
      have hz' : z ∈ closedBall (0 : ℂ) r := by
        rw [abs_of_pos (zero_lt_one.trans_le hr)] at hz
        exact sphere_subset_closedBall hz
      have hh := normalizedCoordinates_euclidean_bound g.holomorphic hW (zero_le_one.trans hr) hz'
      have hl := Real.log_le_log (euclideanNorm_pos (g.vector_ne_zero z)) hh
      rw [Real.log_mul hK.ne' (zero_lt_one.trans_le hM).ne'] at hl
      exact hl)
  unfold characteristic
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.normalizedCoordinates_characteristic_bound
