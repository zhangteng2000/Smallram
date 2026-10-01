import ModifiedCartan.LocalCoefficientSplit
import ModifiedCartan.MeasureLimitTransfer

open scoped Topology Classical BigOperators
open Filter MeasureTheory Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem sublist_card_div_scale_tendsto_zero {M : ℕ → ℕ}
    (S : (ν : ℕ) → Finset (Fin (M ν))) {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => (M ν : ℝ) / s ν) atTop (𝓝 0)) :
    Tendsto (fun ν => ((S ν).card : ℝ) / s ν) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hm
  · filter_upwards [hs.eventually_gt_atTop 0] with ν hν
    positivity
  · filter_upwards [hs.eventually_gt_atTop 0] with ν hν
    apply div_le_div_of_nonneg_right _ hν.le
    exact_mod_cast (show (S ν).card ≤ M ν by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (S ν))

/-- All roots may move arbitrarily. Only their total number divided by
the scale is required to vanish. Auxiliary to LaTeX `eq:gaugesmall`. -/
theorem finite_root_distance_sum_localMeasure_zero {M : ℕ → ℕ}
    (a : (ν : ℕ) → Fin (M ν) → ℂ) {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => (M ν : ℝ) / s ν) atTop (𝓝 0)) :
    LocalMeasureConvergence (ball (0 : ℂ) 6)
      (fun ν z => reciprocalDistanceSum Finset.univ (a ν) z / s ν) (fun _ => (0 : ℝ)) := by
  have hin := inner_root_sum_localMeasure_zero (fun ν => interiorRootIndices (a ν)) a
    (fun ν i hi => (Finset.mem_filter.mp hi).2) hs
    (sublist_card_div_scale_tendsto_zero (fun ν => interiorRootIndices (a ν)) hs hm)
  have hc : LocalMeasureConvergence (ball (0 : ℂ) 6)
      (fun ν (_ : ℂ) => (M ν : ℝ) / s ν) (fun _ => (0 : ℝ)) :=
    uniformlyOn_localMeasureConvergence (hm.tendstoUniformlyOn_const _) (Subset.refl _)
  have hb := hin.add hc
  simp only [add_zero] at hb
  intro K hK hKU
  apply tendstoInMeasure_zero_of_norm_le (hb K hK hKU)
  filter_upwards [hs.eventually_gt_atTop 0] with ν hsν
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  rw [Real.norm_of_nonneg (div_nonneg (reciprocalDistanceSum_nonneg _ _ _) hsν.le),
    ← reciprocalDistanceSum_split (a ν) z, add_div]
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ hsν.le
  have hout := reciprocalDistanceSum_exterior_le (exteriorRootIndices (a ν)) (a ν)
    (fun i hi => (Finset.mem_filter.mp hi).2) (hKU hz)
  have hcard : ((exteriorRootIndices (a ν)).card : ℝ) ≤ M ν := by
    exact_mod_cast (show (exteriorRootIndices (a ν)).card ≤ M ν by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (exteriorRootIndices (a ν)))
  have hM : (0 : ℝ) ≤ M ν := by positivity
  linarith

theorem sum_nonneg_powers_le_power_sum {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) {q : ℕ} (hq : 1 ≤ q) :
    (∑ i ∈ S, x i ^ q) ≤ (∑ i ∈ S, x i) ^ q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  calc
    _ ≤ ∑ i ∈ S, (∑ j ∈ S, x j) ^ k * x i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [pow_succ]
      have hle : x i ≤ ∑ j ∈ S, x j := Finset.single_le_sum hx hi
      gcongr <;> exact hx i hi
    _ = _ := by rw [← Finset.mul_sum, pow_succ]

def finitePoleSum {ι : Type*} (S : Finset ι) (a : ι → ℂ) (q : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ S, (z - a i)⁻¹ ^ q

theorem finitePoleSum_normalized_eq {M : ℕ} (S : Finset (Fin M))
    (a : Fin M → ℂ) (q : ℕ) (s : ℝ) (z : ℂ) :
    finitePoleSum S a q z / (s : ℂ) ^ q =
      ∑ i ∈ S, scaledReciprocalRoot (a i) s z ^ q := by
  simp only [finitePoleSum, Finset.sum_div, scaledReciprocalRoot, div_pow]

theorem norm_finitePoleSum_normalized_le {M : ℕ} (S : Finset (Fin M))
    (a : Fin M → ℂ) {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    ‖finitePoleSum S a q z / (s : ℂ) ^ q‖ ≤
      (reciprocalDistanceSum S a z / s) ^ q := by
  rw [finitePoleSum_normalized_eq]
  calc
    _ ≤ ∑ i ∈ S, ‖scaledReciprocalRoot (a i) s z ^ q‖ := norm_sum_le _ _
    _ = ∑ i ∈ S, ‖scaledReciprocalRoot (a i) s z‖ ^ q := by simp only [norm_pow]
    _ ≤ (∑ i ∈ S, ‖scaledReciprocalRoot (a i) s z‖) ^ q :=
      sum_nonneg_powers_le_power_sum S _ (fun i _ => norm_nonneg _) hq
    _ = _ := by rw [sum_norm_scaledReciprocalRoot S a hs z]

/-- The high-order pole estimates needed for `eq:gaugesmall` follow from
the first-order root sum and a power inequality. This specializes the
paper's fractional-moment argument to its actual o(s) root count. -/
theorem finite_pole_sum_normalized_localMeasure_zero {M : ℕ → ℕ}
    (a : (ν : ℕ) → Fin (M ν) → ℂ) {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => (M ν : ℝ) / s ν) atTop (𝓝 0))
    {q : ℕ} (hq : 1 ≤ q) :
    LocalMeasureConvergence (ball (0 : ℂ) 6)
      (fun ν z => finitePoleSum Finset.univ (a ν) q z / (s ν : ℂ) ^ q) (fun _ => 0) := by
  have hu := finite_root_distance_sum_localMeasure_zero a hs hm
  have hp := hu.continuous_map
    (fun K _ _ ν => by dsimp [reciprocalDistanceSum]; fun_prop)
    (show Continuous (fun x : ℝ => x ^ q) by fun_prop)
  simp only [zero_pow (by omega : q ≠ 0)] at hp
  intro K hK hKU
  apply tendstoInMeasure_zero_of_norm_le (hp K hK hKU)
  filter_upwards [hs.eventually_gt_atTop 0] with ν hsν
  exact Eventually.of_forall (fun z => norm_finitePoleSum_normalized_le Finset.univ (a ν) hq hsν.le z)

end
end ModifiedCartan
#print axioms ModifiedCartan.finite_root_distance_sum_localMeasure_zero
#print axioms ModifiedCartan.finite_pole_sum_normalized_localMeasure_zero
