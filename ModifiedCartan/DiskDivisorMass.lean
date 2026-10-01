import ModifiedCartan.DiskBoundaryMean

open scoped Topology
open Filter Set Metric Function MeromorphicOn Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan

theorem closedDiskCounting_parts_eq_abs_sum {ρ : ℝ}
    (D : locallyFinsuppWithin (closedBall (0 : ℂ) |ρ|) ℤ) (h0 : D 0 = 0) :
    closedDiskLogCounting D⁺ + closedDiskLogCounting D⁻ =
      ∑ᶠ z : ℂ, |(D z : ℝ)| * Real.log (ρ * ‖z‖⁻¹) := by
  have hp : Function.HasFiniteSupport (fun z : ℂ => (D⁺ z : ℝ) * Real.log (ρ * ‖z‖⁻¹)) :=
    (D⁺.finiteSupport (isCompact_closedBall ..)).subset (fun z hz => by
      intro he; exact hz (by simp [he]))
  have hn : Function.HasFiniteSupport (fun z : ℂ => (D⁻ z : ℝ) * Real.log (ρ * ‖z‖⁻¹)) :=
    (D⁻.finiteSupport (isCompact_closedBall ..)).subset (fun z hz => by
      intro he; exact hz (by simp [he]))
  have hp0 : D⁺ 0 = 0 := by simp [h0]
  have hn0 : D⁻ 0 = 0 := by simp [h0]
  simp only [closedDiskLogCounting, hp0, hn0, Int.cast_zero, zero_mul, add_zero]
  rw [← finsum_add_distrib hp hn]
  apply finsum_congr
  intro z
  rw [← add_mul]
  congr 1
  have he : (D z)⁺ + (D z)⁻ = |D z| := posPart_add_negPart (D z)
  exact_mod_cast he

/-- Local signed divisor mass is controlled by its actual outer zero and pole counts. -/
theorem closedDisk_divisor_mass_mul_log_le {R ρ : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (D : locallyFinsuppWithin (closedBall (0 : ℂ) |ρ|) ℤ) (h0 : D 0 = 0)
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z‖ ≤ R) :
    (∑ z ∈ S, |(D z : ℝ)|) * Real.log (ρ / R) ≤
      closedDiskLogCounting D⁺ + closedDiskLogCounting D⁻ := by
  classical
  have hρ := hR.trans hRρ
  rw [closedDiskCounting_parts_eq_abs_sum D h0]
  let F : ℂ → ℝ := fun z => |(D z : ℝ)| * Real.log (ρ * ‖z‖⁻¹)
  have hF : Function.HasFiniteSupport F :=
    (D.finiteSupport (isCompact_closedBall ..)).subset (fun z hz => by
      intro he; exact hz (by simp [F, he]))
  have hnonneg (z : ℂ) : 0 ≤ F z := by
    by_cases hd : D z = 0
    · simp [F, hd]
    have hz0 : z ≠ 0 := by intro he; subst z; exact hd h0
    have hzρ : ‖z‖ ≤ ρ := by
      simpa only [mem_closedBall, dist_zero_right, abs_of_pos hρ] using D.supportWithinDomain hd
    apply mul_nonneg (abs_nonneg _)
    apply Real.log_nonneg
    rw [← div_eq_mul_inv]
    exact (one_le_div (norm_pos_iff.mpr hz0)).mpr hzρ
  have hsupp : Function.support F ⊆ (S ∪ hF.toFinset : Finset ℂ) := by
    intro z hz
    exact Finset.mem_union_right S (hF.mem_toFinset.mpr hz)
  rw [finsum_eq_sum_of_support_subset F hsupp, Finset.sum_mul]
  calc
    _ ≤ ∑ z ∈ S, F z := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hz0 : z = 0
      · simp [hz0, h0, F]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Real.log_le_log (div_pos hρ hR)
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left hρ.le (norm_pos_iff.mpr hz0) (hS z hz)
    _ ≤ ∑ z ∈ S ∪ hF.toFinset, F z :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun z _ _ => hnonneg z)

theorem diskCounting_sum_le_characteristic {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : MeromorphicOn f (closedBall 0 |ρ|)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    diskZeroCounting f ρ + diskPoleCounting f ρ ≤
      2 * diskCharacteristic f ρ + Real.posLog (1 / ‖f 0‖) := by
  have hj := diskCounting_jensen hρ.ne' hf
  rw [hfa.meromorphicTrailingCoeffAt_of_ne_zero h0] at hj
  have hmean : Real.circleAverage (fun z => Real.log ‖f z‖) 0 ρ ≤
      ValueDistribution.proximity f ⊤ ρ := by
    rw [ValueDistribution.proximity_top]
    exact Real.circleAverage_mono (hf.mono_set sphere_subset_closedBall).circleIntegrable_log_norm
      (hf.mono_set sphere_subset_closedBall).circleIntegrable_posLog_norm
      (fun _ _ => le_max_right _ _)
  have hp : 0 ≤ ValueDistribution.proximity f ⊤ ρ := by
    rw [ValueDistribution.proximity_top]
    exact Real.circleAverage_nonneg_of_nonneg (fun _ _ => Real.posLog_nonneg)
  have hl : -Real.log ‖f 0‖ ≤ Real.posLog (1 / ‖f 0‖) := by
    rw [one_div, Real.posLog_apply, Real.log_inv]
    exact le_max_right _ _
  unfold diskCharacteristic
  linarith

theorem disk_divisor_mass_bound {f : ℂ → ℂ} {R ρ : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hf : MeromorphicOn f (closedBall 0 |ρ|)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z‖ ≤ R) :
    ∑ z ∈ S, |(divisor f (closedBall 0 |ρ|) z : ℝ)| ≤
      (2 * diskCharacteristic f ρ + Real.posLog (1 / ‖f 0‖)) / Real.log (ρ / R) := by
  have hD0 : divisor f (closedBall 0 |ρ|) 0 = 0 := by
    rw [hf.divisor_apply (by simp), hfa.meromorphicOrderAt_eq, hfa.analyticOrderAt_eq_zero.mpr h0]
    rfl
  apply (le_div_iff₀ (Real.log_pos ((one_lt_div hR).mpr hRρ))).mpr
  exact (closedDisk_divisor_mass_mul_log_le hR hRρ _ hD0 S hS).trans
    (diskCounting_sum_le_characteristic (hR.trans hRρ) hf hfa h0)

end ModifiedCartan
#print axioms ModifiedCartan.closedDisk_divisor_mass_mul_log_le
#print axioms ModifiedCartan.disk_divisor_mass_bound

