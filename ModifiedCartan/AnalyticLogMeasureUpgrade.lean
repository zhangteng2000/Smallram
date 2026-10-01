import ModifiedCartan.NormalizedLogCompactness
import ModifiedCartan.LocalMeasureUniqueness
import ModifiedCartan.UniformLocalLp

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A finite measure limit excludes the collapse alternative for genuine
analytic logarithms. Nontriviality controls their zero sets. -/
theorem normalized_log_not_collapse_of_localMeasure
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hne : U.Nonempty)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ}
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) U) (hn : ∀ ν, ∃ z ∈ U, f ν z ≠ 0)
    (_hs : ∀ ν, 0 < s ν)
    (hlim : LocalMeasureConvergence U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν z‖) u) :
    ¬ LocalUniformlyToBot U (fun ν => normalizedExtendedLog (s ν) (f ν)) := by
  intro hcollapse
  obtain ⟨ns, hns, hnlim⟩ := hlim.exists_seq_tendsto_ae hU
  have hnonzero := ae_all_iff.mpr (fun ν => analytic_ae_ne_zero hU hUc (hf ν) (hn ν))
  obtain ⟨z, hzU, hzlim, hzne⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hU.measure_ne_zero volume hne) (hnlim.and hnonzero)
  have hc := hcollapse {z} isCompact_singleton (singleton_subset_iff.mpr hzU) (u z - 1)
  have hl := hzlim.eventually (lt_mem_nhds (show u z - 1 < u z by linarith))
  obtain ⟨ν, hν, hν'⟩ := ((hns.tendsto_atTop.eventually hc).and hl).exists
  have hh := hν z (mem_singleton z)
  dsimp only [Function.comp_def] at hh hν'
  rw [normalizedExtendedLog_of_ne_zero (s (ns ν)) (hzne (ns ν)), EReal.coe_le_coe_iff] at hh
  exact not_lt_of_ge hh hν'

/-- Analytic logarithms with a uniform exponential upper bound converge
locally in L1 as soon as they converge locally in measure to a finite function.
This uses the proved subharmonic compactness theorem and uniqueness. -/
theorem normalized_log_localL1_of_localMeasure
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hne : U.Nonempty)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {C : ℝ}
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) U) (hn : ∀ ν, ∃ z ∈ U, f ν z ≠ 0)
    (hs : ∀ ν, 0 < s ν)
    (hbound : ∀ ν z, z ∈ U → ‖f ν z‖ ≤ Real.exp (C * s ν))
    (hlim : LocalMeasureConvergence U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν z‖) u) :
    LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν z‖) u := by
  have hsub (ν : ℕ) := normalizedExtendedLog_isSubharmonicOn hU hUc (hf ν) (hn ν) (hs ν)
  have hbdd : ∀ K, IsCompact K → K ⊆ U → ∃ M : ℝ,
      ∀ ν z, z ∈ K → normalizedExtendedLog (s ν) (f ν) z ≤ (M : EReal) := by
    intro K _ hKU
    refine ⟨C, fun ν z hz => ?_⟩
    by_cases hfz : f ν z = 0
    · rw [normalizedExtendedLog_eq_bot (hs ν) hfz]
      exact bot_le
    · rw [normalizedExtendedLog_of_ne_zero (s ν) hfz, EReal.coe_le_coe_iff,
        mul_comm, ← div_eq_mul_inv]
      apply (div_le_iff₀ (hs ν)).mpr
      have hh := Real.log_le_log (norm_pos_iff.mpr hfz) (hbound ν z (hKU hz))
      simpa only [Real.log_exp] using hh
  apply localLpConvergence_of_subseq
  · intro K hK hKU ν
    exact memLp_one_iff_integrable.mpr ((integrableOn_log_norm_on_compact
      (hf ν) hKU hK).const_mul (s ν)⁻¹)
  · intro ns hns
    obtain ⟨ms, hms, hcase⟩ := Paper.lem_subharmonic_compactness hU hUc hne
      (fun ν => hsub (ns ν)) (fun K hK hKU => by
        obtain ⟨M, hM⟩ := hbdd K hK hKU
        exact ⟨M, fun ν z hz => hM (ns ν) z hz⟩)
    have hmeasure := hlim.comp (hns.comp hms.tendsto_atTop)
    rcases hcase with hcollapse | ⟨_, _, _, v, _, hv⟩
    · exact (normalized_log_not_collapse_of_localMeasure hU hUc hne
        (fun ν => hf (ns (ms ν))) (fun ν => hn (ns (ms ν)))
        (fun ν => hs (ns (ms ν))) hmeasure hcollapse).elim
    · refine ⟨ms, hv.normalizedLog_real.congr_ae (fun _ => EventuallyEq.rfl) ?_⟩
      exact (hv.normalizedLog_real.inMeasure one_ne_zero).ae_unique hU hmeasure

end ModifiedCartan
#print axioms ModifiedCartan.normalized_log_not_collapse_of_localMeasure
#print axioms ModifiedCartan.normalized_log_localL1_of_localMeasure
