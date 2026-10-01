import ModifiedCartan.CauchyTruncation
import ModifiedCartan.UniformLocalLp

open scoped Topology ENNReal BigOperators Classical
open Filter MeasureTheory Set Metric
set_option autoImplicit false

namespace ModifiedCartan
noncomputable section

def reciprocalDistanceSum {ι : Type*} (S : Finset ι) (a : ι → ℂ) (z : ℂ) : ℝ :=
  ∑ i ∈ S, ‖z - a i‖⁻¹

def interiorKernelLpBound (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 * Real.pi / (2 - p)) * (15 : ℝ) ^ (2 - p)) ^ p⁻¹)

theorem interiorKernelLpBound_ne_top (p : ℝ) : interiorKernelLpBound p ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem inner_disk_subset_pole_ball {a : ℂ} (ha : ‖a‖ ≤ 8) :
    ball (0 : ℂ) 6 ⊆ ball a 15 := by
  intro z hz
  have hz' : ‖z‖ < 6 := by simpa only [mem_ball, dist_zero_right] using hz
  rw [mem_ball, dist_eq_norm]
  have ht := norm_sub_le z a
  linarith

theorem eLpNorm_reciprocal_distance_inner_disk_le {p : ℝ}
    (hp0 : 0 < p) (hp2 : p < 2) {a : ℂ} (ha : ‖a‖ ≤ 8) :
    eLpNorm (fun z : ℂ => ‖z - a‖⁻¹) (ENNReal.ofReal p)
      (volume.restrict (ball 0 6)) ≤ interiorKernelLpBound p := by
  have hnorm : eLpNorm (fun z : ℂ => ‖z - a‖⁻¹) (ENNReal.ofReal p)
      (volume.restrict (ball 0 6)) =
      eLpNorm (fun z : ℂ => (z - a)⁻¹) (ENNReal.ofReal p)
        (volume.restrict (ball 0 6)) := by
    simpa only [norm_inv] using eLpNorm_norm (fun z : ℂ => (z - a)⁻¹)
  rw [hnorm]
  apply (eLpNorm_mono_measure _
    (Measure.restrict_mono (inner_disk_subset_pole_ball ha) le_rfl)).trans_eq
  have he := eLpNorm_nearCauchyKernel hp0 hp2 (by norm_num : (0 : ℝ) ≤ 15) a
  rw [nearCauchyKernel, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball] at he
  exact he

theorem reciprocalDistanceSum_nonneg {ι : Type*} (S : Finset ι) (a : ι → ℂ) (z : ℂ) :
    0 ≤ reciprocalDistanceSum S a z :=
  Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _))

theorem eLpNorm_reciprocalDistanceSum_le {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) (ha : ∀ i ∈ S, ‖a i‖ ≤ 8) :
    eLpNorm (reciprocalDistanceSum S a) (ENNReal.ofReal p) (volume.restrict (ball 0 6)) ≤
      (S.card : ℝ≥0∞) * interiorKernelLpBound p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have he : reciprocalDistanceSum S a = ∑ i ∈ S, (fun z : ℂ => ‖z - a i‖⁻¹) := by
    funext z
    simp only [reciprocalDistanceSum, Finset.sum_apply]
  rw [he]
  apply (eLpNorm_sum_le (fun i _ => by fun_prop) (ENNReal.one_le_ofReal.mpr hp1)).trans
  calc
    _ ≤ ∑ _i ∈ S, interiorKernelLpBound p := by
      apply Finset.sum_le_sum
      intro i hi
      exact eLpNorm_reciprocal_distance_inner_disk_le hp0 hp2 (ha i hi)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem eLpNorm_scaled_reciprocalDistanceSum_le {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    {p s : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) (hs : 0 ≤ s)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ 8) :
    eLpNorm (fun z => reciprocalDistanceSum S a z / s) (ENNReal.ofReal p)
      (volume.restrict (ball 0 6)) ≤
      ENNReal.ofReal ((S.card : ℝ) / s) * interiorKernelLpBound p := by
  have he : (fun z => reciprocalDistanceSum S a z / s) = s⁻¹ • reciprocalDistanceSum S a := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he, eLpNorm_const_smul, Real.enorm_of_nonneg (inv_nonneg.mpr hs)]
  calc
    _ ≤ ENNReal.ofReal s⁻¹ * ((S.card : ℝ≥0∞) * interiorKernelLpBound p) := by
      gcongr
      exact eLpNorm_reciprocalDistanceSum_le S a hp1 hp2 ha
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (inv_nonneg.mpr hs)]
      congr 2
      ring

theorem reciprocalDistanceSum_exterior_le {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    (ha : ∀ i ∈ S, 8 < ‖a i‖) {z : ℂ} (hz : z ∈ ball 0 6) :
    reciprocalDistanceSum S a z ≤ (S.card : ℝ) / 2 := by
  have hz' : ‖z‖ < 6 := by simpa only [mem_ball, dist_zero_right] using hz
  calc
    _ ≤ ∑ _i ∈ S, (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have ht := norm_sub_norm_le (a i) z
      rw [norm_sub_rev] at ht
      have hd : (2 : ℝ) < ‖z - a i‖ := by linarith [ha i hi]
      have he := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd.le
      simpa only [one_div] using he
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem inner_root_sum_eLpNorm_tendsto_zero {M : ℕ → ℕ}
    (S : (ν : ℕ) → Finset (Fin (M ν))) (a : (ν : ℕ) → Fin (M ν) → ℂ)
    (ha : ∀ ν i, i ∈ S ν → ‖a ν i‖ ≤ 8)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((S ν).card : ℝ) / s ν) atTop (𝓝 0))
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) :
    Tendsto (fun ν => eLpNorm (fun z => reciprocalDistanceSum (S ν) (a ν) z / s ν)
      (ENNReal.ofReal p) (volume.restrict (ball 0 6))) atTop (𝓝 0) := by
  have hm' := ENNReal.tendsto_ofReal hm
  simp only [ENNReal.ofReal_zero] at hm'
  have hlim : Tendsto (fun ν => ENNReal.ofReal (((S ν).card : ℝ) / s ν) *
      interiorKernelLpBound p) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_comm] using ENNReal.Tendsto.const_mul hm'
      (Or.inr (interiorKernelLpBound_ne_top p) :
        (0 : ℝ≥0∞) ≠ 0 ∨ interiorKernelLpBound p ≠ ⊤)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hs.eventually_gt_atTop 0] with ν hν
  exact eLpNorm_scaled_reciprocalDistanceSum_le (S ν) (a ν) hp1 hp2 hν.le (ha ν)

theorem inner_root_sum_localMeasure_zero {M : ℕ → ℕ}
    (S : (ν : ℕ) → Finset (Fin (M ν))) (a : (ν : ℕ) → Fin (M ν) → ℂ)
    (ha : ∀ ν i, i ∈ S ν → ‖a ν i‖ ≤ 8)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((S ν).card : ℝ) / s ν) atTop (𝓝 0)) :
    LocalMeasureConvergence (ball (0 : ℂ) 6)
      (fun ν z => reciprocalDistanceSum (S ν) (a ν) z / s ν) (fun _ => (0 : ℝ)) := by
  have hlp := inner_root_sum_eLpNorm_tendsto_zero S a ha hs hm
    (p := (3 / 2 : ℝ)) (by norm_num) (by norm_num)
  intro K _hK hK
  have hsmall : Tendsto (fun ν => eLpNorm
      (fun z => reciprocalDistanceSum (S ν) (a ν) z / s ν)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict K)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlp (fun _ => bot_le)
    intro ν
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hK le_rfl)
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0)
    (fun ν => by dsimp [reciprocalDistanceSum]; fun_prop) aestronglyMeasurable_const
  convert! hsmall using 1
  funext ν
  congr 1
  funext z
  simp

end
end ModifiedCartan
#print axioms ModifiedCartan.eLpNorm_scaled_reciprocalDistanceSum_le
#print axioms ModifiedCartan.reciprocalDistanceSum_exterior_le
#print axioms ModifiedCartan.inner_root_sum_eLpNorm_tendsto_zero
#print axioms ModifiedCartan.inner_root_sum_localMeasure_zero
