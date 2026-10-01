import ModifiedCartan.CharacteristicLogLower
import ModifiedCartan.CharacteristicIndices
import ModifiedCartan.PeakLogNormalization

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Exact characteristic peaks and the normalization needed in Step 1 of
LaTeX `prop:indices`. The logarithmic limit uses the specialized Jensen
lower-bound argument recorded in FORMALIZATION_MAP.md. -/
theorem characteristic_peaks_with_normalization {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) {μ : ℝ} (hμ : 0 < μ)
    (hlower : strongLowerIndex (characteristic f) ≤ (μ : EReal))
    (hupper : (μ : EReal) ≤ strongUpperIndex (characteristic f)) :
    ∃ r ε : ℕ → ℝ, (∀ ν, 0 < r ν) ∧ Tendsto r atTop atTop ∧
      (∀ ν, 0 < ε ν) ∧ StrictAnti ε ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun ν => characteristic f (r ν)) atTop atTop ∧
      Tendsto (fun ν => Real.log (r ν) / characteristic f (r ν)) atTop (𝓝 0) ∧
      ∀ ν t, ε ν ≤ t → t ≤ (ε ν)⁻¹ →
        characteristic f (t * r ν) ≤ (1 + ε ν) * t ^ μ * characteristic f (r ν) := by
  have hT := fun x hx => characteristic_pos_of_transcendental f htrans (r := x) hx
  obtain ⟨r, ε, hrpos, hr, hεpos, hεanti, hε, hpeak⟩ :=
    Paper.lem_peaks (characteristic f) hT (characteristic_monotoneOn f)
      (characteristic_unbounded_of_transcendental f htrans) hμ hlower hupper
  obtain ⟨C, hC⟩ := characteristic_log_lower_of_transcendental f htrans
  exact ⟨r, ε, hrpos, hr, hεpos, hεanti, hε,
    (characteristic_tendsto_atTop_of_transcendental f htrans).comp hr,
    peak_log_radius_div_scale_tendsto_zero (characteristic f) hT
      hrpos hr hεpos hε hμ hpeak hC, hpeak⟩

/-- All the actual scale hypotheses for `prop:representation`, at an arbitrary
fixed positive R along the positive-order peaks. The bound in
LaTeX `eq:peak-characteristic-scale` has a constant independent of R. -/
theorem characteristic_peak_scale_hypotheses {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hsmall : SmallRamification f)
    {r ε : ℕ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hrpos : ∀ ν, 0 < r ν) (hr : Tendsto r atTop atTop)
    (hεpos : ∀ ν, 0 < ε ν) (hε : Tendsto ε atTop (𝓝 0))
    (hpeak : ∀ ν t, ε ν ≤ t → t ≤ (ε ν)⁻¹ →
      characteristic f (t * r ν) ≤ (1 + ε ν) * t ^ μ * characteristic f (r ν))
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ν => R * r ν) atTop atTop ∧
      Tendsto (fun ν => R ^ μ * characteristic f (r ν)) atTop atTop ∧
      Tendsto (fun ν => Real.log (R * r ν) / (R ^ μ * characteristic f (r ν))) atTop (𝓝 0) ∧
      (∀ᶠ ν in atTop, characteristic f (256 * (R * r ν)) ≤
        (2 * (256 : ℝ) ^ μ) * (R ^ μ * characteristic f (r ν))) ∧
      Tendsto (fun ν => ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
        (0 : WithTop ℂ) (256 * (R * r ν)) / (R ^ μ * characteristic f (r ν))) atTop (𝓝 0) := by
  have hT := fun x hx => characteristic_pos_of_transcendental f htrans (r := x) hx
  have hS := (characteristic_tendsto_atTop_of_transcendental f htrans).comp hr
  have hRp := Real.rpow_pos_of_pos hR μ
  have ht := Filter.Tendsto.const_mul_atTop hR hr
  have hs := Filter.Tendsto.const_mul_atTop hRp hS
  obtain ⟨C, hC⟩ := characteristic_log_lower_of_transcendental f htrans
  have hlog := peak_log_radius_div_scale_tendsto_zero (characteristic f) hT
    hrpos hr hεpos hε hμ hpeak hC
  have hlogR : Tendsto (fun ν => Real.log (R * r ν) / (R ^ μ * characteristic f (r ν)))
      atTop (𝓝 0) := by
    have he : Tendsto (fun ν =>
        (Real.log R / characteristic f (r ν) + Real.log (r ν) / characteristic f (r ν)) / R ^ μ)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, zero_add, zero_div] using
        ((hS.const_div_atTop (Real.log R)).add hlog).div_const (R ^ μ)
    convert he using 1
    funext ν
    rw [Real.log_mul hR.ne' (hrpos ν).ne', ← add_div, div_div]
    congr 1
    ring
  have hbound : ∀ᶠ ν in atTop, characteristic f (256 * (R * r ν)) ≤
      (2 * (256 : ℝ) ^ μ) * (R ^ μ * characteristic f (r ν)) := by
    filter_upwards [peak_fixed_scale_eventual_bound (characteristic f) hT
      hrpos hεpos hε hpeak (mul_pos (by norm_num : (0 : ℝ) < 256) hR)] with ν hν
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 256) hR.le, mul_assoc] using hν
  have hbig : (fun ν => characteristic f (256 * (R * r ν))) =O[atTop]
      (fun ν => R ^ μ * characteristic f (r ν)) := by
    apply IsBigO.of_bound (2 * (256 : ℝ) ^ μ)
    filter_upwards [hbound] with ν hν
    rw [Real.norm_of_nonneg (hT _ (mul_pos (by norm_num : (0 : ℝ) < 256)
        (mul_pos hR (hrpos ν)))).le,
      Real.norm_of_nonneg (mul_pos hRp (hT _ (hrpos ν))).le]
    exact hν
  have hscale := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 256) ht
  have hsmall' : (fun ν => ramification f (256 * (R * r ν))) =o[atTop]
      (fun ν => characteristic f (256 * (R * r ν))) := hsmall.comp_tendsto hscale
  exact ⟨ht, hs, hlogR, hbound, (hsmall'.trans_isBigO hbig).tendsto_div_nhds_zero⟩

end
end ModifiedCartan
#print axioms ModifiedCartan.characteristic_peaks_with_normalization
#print axioms ModifiedCartan.characteristic_peak_scale_hypotheses
