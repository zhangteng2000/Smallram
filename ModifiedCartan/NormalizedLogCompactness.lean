import ModifiedCartan.AnalyticLogSubharmonic
import ModifiedCartan.SubharmonicCompactness

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The center normalization rules out collapse in the subharmonic
compactness alternative. This is used for the actual coordinates in Step 2
of `prop:indices`. -/
theorem exists_normalized_log_subsequence {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {C : ℝ}
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) (ball 0 4))
    (hf0 : ∀ ν, f ν 0 ≠ 0) (hs : ∀ ν, 0 < s ν)
    (hbound : ∀ ν z, z ∈ ball (0 : ℂ) 4 → ‖f ν z‖ ≤ Real.exp (C * s ν))
    (hcenter : Tendsto (fun ν => Real.log ‖f ν 0‖ / s ν) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ u : ℂ → ℝ,
      LocalLpConvergence 1 (ball (0 : ℂ) 4)
        (fun ν z => (s (ns ν))⁻¹ * Real.log ‖f (ns ν) z‖) u := by
  have h0 : (0 : ℂ) ∈ ball 0 4 := mem_ball_self (by norm_num)
  have hsub (ν : ℕ) : IsSubharmonicOn (ball (0 : ℂ) 4) (normalizedExtendedLog (s ν) (f ν)) :=
    normalizedExtendedLog_isSubharmonicOn isOpen_ball (convex_ball (0 : ℂ) 4).isPreconnected
      (hf ν) ⟨0, h0, hf0 ν⟩ (hs ν)
  have hbdd : ∀ K, IsCompact K → K ⊆ ball (0 : ℂ) 4 → ∃ M : ℝ,
      ∀ ν z, z ∈ K → normalizedExtendedLog (s ν) (f ν) z ≤ (M : EReal) := by
    intro K _ hKU
    refine ⟨C, ?_⟩
    intro ν z hz
    by_cases hfz : f ν z = 0
    · rw [normalizedExtendedLog_eq_bot (hs ν) hfz]
      exact bot_le
    · rw [normalizedExtendedLog_of_ne_zero (s ν) hfz, EReal.coe_le_coe_iff,
        mul_comm, ← div_eq_mul_inv]
      apply (div_le_iff₀ (hs ν)).mpr
      have hl := Real.log_le_log (norm_pos_iff.mpr hfz) (hbound ν z (hKU hz))
      simpa only [Real.log_exp] using hl
  obtain ⟨ns, hns, hcase⟩ := Paper.lem_subharmonic_compactness isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected ⟨0, h0⟩ hsub hbdd
  rcases hcase with hcollapse | ⟨_, _, _, u, _, hu⟩
  · have hc := hcollapse {0} isCompact_singleton (singleton_subset_iff.mpr h0) (-1)
    have hl := (hcenter.comp hns.tendsto_atTop).eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))
    obtain ⟨ν, hν, hν'⟩ := (hc.and hl).exists
    have hle := hν 0 (mem_singleton 0)
    dsimp only [Function.comp_def] at hle hν'
    rw [normalizedExtendedLog_of_ne_zero (s (ns ν)) (hf0 (ns ν)), EReal.coe_le_coe_iff,
      mul_comm, ← div_eq_mul_inv] at hle
    exact (not_lt_of_ge hle hν').elim
  · exact ⟨ns, hns, u, hu.normalizedLog_real⟩

end ModifiedCartan
#print axioms ModifiedCartan.exists_normalized_log_subsequence
