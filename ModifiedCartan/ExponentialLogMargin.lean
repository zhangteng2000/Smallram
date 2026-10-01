import ModifiedCartan.LogMeasureTransfer

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Exponential approximation preserves a finite logarithmic limit whenever
the error exponent lies strictly below it. The limit may be negative. -/
theorem normalized_log_close_of_margin {x y s : ℕ → ℝ} {A C u : ℝ}
    (hs : Tendsto s atTop atTop) (hx : ∀ᶠ ν in atTop, 0 < x ν)
    (hxlim : Tendsto (fun ν => Real.log (x ν) / s ν) atTop (𝓝 u))
    (hu : -A < u)
    (hclose : ∀ᶠ ν in atTop, |y ν - x ν| ≤ C * Real.exp (-A * s ν)) :
    (∀ᶠ ν in atTop, 0 < y ν) ∧
      Tendsto (fun ν => Real.log (y ν) / s ν) atTop (𝓝 u) := by
  let B := (u - A) / 2
  have hAB : 0 < A + B := by dsimp only [B]; linarith
  have hBu : B < u := by dsimp only [B]; linarith
  have hdec : Tendsto (fun ν => C * Real.exp (-(A + B) * s ν)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (exponential_decay_of_scale hs hAB).const_mul C
  have hcontrol : ∀ᶠ ν in atTop, 0 < y ν ∧
      |Real.log (y ν) / s ν - Real.log (x ν) / s ν| ≤ Real.log 2 / s ν := by
    filter_upwards [hx, hs.eventually_gt_atTop 0, hclose,
      hdec.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hxlim.eventually (lt_mem_nhds hBu)] with ν hxν hsν hcloseν hdecν hlogν
    have hexp : Real.exp (B * s ν) ≤ x ν := by
      rw [← Real.exp_log hxν]
      exact Real.exp_le_exp.mpr ((lt_div_iff₀ hsν).mp hlogν).le
    have hfactor : C * Real.exp (-A * s ν) =
        (C * Real.exp (-(A + B) * s ν)) * Real.exp (B * s ν) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hrelative : |y ν - x ν| ≤ x ν / 2 := by
      calc
        _ ≤ C * Real.exp (-A * s ν) := hcloseν
        _ = _ := hfactor
        _ ≤ (1 / 2) * Real.exp (B * s ν) :=
          mul_le_mul_of_nonneg_right hdecν.le (Real.exp_pos _).le
        _ ≤ x ν / 2 := by nlinarith
    obtain ⟨hy, hlogs⟩ := abs_log_sub_le_log_two_of_close hxν hrelative
    refine ⟨hy, ?_⟩
    rw [← sub_div, abs_div, abs_of_pos hsν]
    exact div_le_div_of_nonneg_right hlogs hsν.le
  refine ⟨hcontrol.mono (fun _ h => h.1), ?_⟩
  have hsmall : Tendsto (fun ν => Real.log 2 / s ν) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp hs).const_mul (Real.log 2)
  have hdiff : Tendsto (fun ν => Real.log (y ν) / s ν - Real.log (x ν) / s ν)
      atTop (𝓝 0) :=
    squeeze_zero_norm' (hcontrol.mono (fun _ h => h.2)) hsmall
  simpa only [sub_add_cancel, zero_add] using hdiff.add hxlim

/-- The preceding transfer in local measure, allowing zeros on null sets
and negative target exponents. -/
theorem localMeasure_log_transfer_of_margin {U : Set ℂ} (hU : IsOpen U)
    {x y : ℕ → ℂ → ℝ} {s : ℕ → ℝ} {u : ℂ → ℝ} {A C : ℝ}
    (hs : Tendsto s atTop atTop)
    (hxpos : ∀ ν, ∀ᵐ z ∂volume.restrict U, 0 < x ν z)
    (hymeas : ∀ K, IsCompact K → K ⊆ U → ∀ ν, AEStronglyMeasurable (y ν) (volume.restrict K))
    (hxlim : LocalMeasureConvergence U (fun ν z => Real.log (x ν z) / s ν) u)
    (hu : ∀ᵐ z ∂volume.restrict U, -A < u z)
    (hclose : ∀ᶠ ν in atTop, ∀ z ∈ U, |y ν z - x ν z| ≤ C * Real.exp (-A * s ν)) :
    LocalMeasureConvergence U (fun ν z => Real.log (y ν z) / s ν) u := by
  intro K hK hKU
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun ν => by
    simpa only [div_eq_mul_inv] using
      ((hymeas K hK hKU ν).aemeasurable.log.aestronglyMeasurable).mul_const (s ν)⁻¹)).mpr
  intro ns hns
  obtain ⟨ms, hms, hm⟩ := (hxlim.comp hns.tendsto_atTop).exists_seq_tendsto_ae hU
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hm.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)),
    hu.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)),
    (ae_all_iff.mpr hxpos).filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)),
    ae_restrict_mem hK.measurableSet] with z hz hzu hpos hzK
  apply (normalized_log_close_of_margin (C := C)
    (hs.comp (hns.tendsto_atTop.comp hms.tendsto_atTop))
    (Eventually.of_forall (fun ν => hpos (ns (ms ν)))) hz hzu ?_).2
  filter_upwards [(hns.tendsto_atTop.comp hms.tendsto_atTop).eventually hclose] with ν hν
  exact hν z (hKU hzK)

end ModifiedCartan
#print axioms ModifiedCartan.normalized_log_close_of_margin
#print axioms ModifiedCartan.localMeasure_log_transfer_of_margin
