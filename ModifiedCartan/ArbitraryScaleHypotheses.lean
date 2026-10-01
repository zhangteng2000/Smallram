import ModifiedCartan.PowerNormalization
import ModifiedCartan.ArbitraryScaleWeight

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- The hypotheses for `prop:representation` at every positive fixed
scale of an arbitrary radius sequence, with one constant independent of R.
This includes LaTeX `eq:regular-scale-bound`. -/
theorem characteristic_arbitrary_scale_hypotheses {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hsmall : SmallRamification f)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hερ : ε < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R →
      Tendsto (fun ν => R * r ν) atTop atTop ∧
      Tendsto (fun ν => arbitraryScaleWeight ρ ε R * characteristic f (r ν)) atTop atTop ∧
      Tendsto (fun ν => Real.log (R * r ν) /
        (arbitraryScaleWeight ρ ε R * characteristic f (r ν))) atTop (𝓝 0) ∧
      (∀ᶠ ν in atTop, characteristic f (256 * (R * r ν)) ≤
        C * (arbitraryScaleWeight ρ ε R * characteristic f (r ν))) ∧
      Tendsto (fun ν => ramification f (256 * (R * r ν)) /
        (arbitraryScaleWeight ρ ε R * characteristic f (r ν))) atTop (𝓝 0) := by
  have hT := fun x hx => characteristic_pos_of_transcendental f htrans (r := x) hx
  obtain ⟨D, r0, hD, hr0, hb⟩ := Paper.lem_power_bounds (characteristic f) hT
    (characteristic_monotoneOn f) (characteristic_unbounded_of_transcendental f htrans)
    hρ hl hu hε hερ
  let C := D * (256 : ℝ) ^ (ρ + ε)
  have hC : 0 < C := mul_pos (zero_lt_one.trans_le hD) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro R hR
  have hM := arbitraryScaleWeight_pos ρ ε hR
  have hS := (characteristic_tendsto_atTop_of_transcendental f htrans).comp hr
  have ht := Filter.Tendsto.const_mul_atTop hR hr
  have hs := Filter.Tendsto.const_mul_atTop hM hS
  have hscale := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 256) ht
  have hlog := (characteristic_log_div_tendsto_zero_of_equal_positive_indices f htrans hρ hl hu).comp hr
  have hlogR : Tendsto (fun ν => Real.log (R * r ν) /
      (arbitraryScaleWeight ρ ε R * characteristic f (r ν))) atTop (𝓝 0) := by
    have he : Tendsto (fun ν =>
        (Real.log R / characteristic f (r ν) + Real.log (r ν) / characteristic f (r ν)) /
          arbitraryScaleWeight ρ ε R) atTop (𝓝 0) := by
      simpa only [Function.comp_def, zero_add, zero_div] using
        ((hS.const_div_atTop (Real.log R)).add hlog).div_const (arbitraryScaleWeight ρ ε R)
    apply he.congr'
    filter_upwards [hr.eventually_gt_atTop 0] with ν hν
    rw [Real.log_mul hR.ne' hν.ne', ← add_div, div_div]
    congr 1
    ring
  have hbound : ∀ᶠ ν in atTop, characteristic f (256 * (R * r ν)) ≤
      C * (arbitraryScaleWeight ρ ε R * characteristic f (r ν)) := by
    filter_upwards [hr.eventually_ge_atTop r0, hscale.eventually_ge_atTop r0] with ν hν hνR
    have hp := hT (r ν) (hr0.trans_le hν)
    have hb' := (hb (256 * R) (r ν) hν (by simpa only [mul_assoc] using hνR)).2
    have hh := (div_le_iff₀ hp).mp hb'
    have hw := arbitraryScaleWeight_mul_le ρ hε.le (by norm_num : (1 : ℝ) ≤ 256) hR
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw (zero_le_one.trans hD)) hp.le
    change characteristic f ((256 * R) * r ν) ≤
      D * arbitraryScaleWeight ρ ε (256 * R) * characteristic f (r ν) at hh
    simpa only [C, mul_assoc] using hh.trans hmul
  have hbig : (fun ν => characteristic f (256 * (R * r ν))) =O[atTop]
      (fun ν => arbitraryScaleWeight ρ ε R * characteristic f (r ν)) := by
    apply IsBigO.of_bound C
    filter_upwards [hbound, hr.eventually_gt_atTop 0] with ν hν hrν
    rw [Real.norm_of_nonneg (hT _ (mul_pos (by norm_num) (mul_pos hR hrν))).le,
      Real.norm_of_nonneg (mul_pos hM (hT _ hrν)).le]
    exact hν
  have hsmall' : (fun ν => ramification f (256 * (R * r ν))) =o[atTop]
      (fun ν => characteristic f (256 * (R * r ν))) := hsmall.comp_tendsto hscale
  exact ⟨ht, hs, hlogR, hbound, (hsmall'.trans_isBigO hbig).tendsto_div_nhds_zero⟩

end ModifiedCartan
#print axioms ModifiedCartan.characteristic_arbitrary_scale_hypotheses
