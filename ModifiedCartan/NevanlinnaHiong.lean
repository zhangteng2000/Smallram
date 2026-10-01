import ModifiedCartan.NHHigherRatioControl
import ModifiedCartan.NHControlSize

open scoped Topology ENNReal
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A slightly stronger local form of LaTeX `lem:NH`: meromorphicity in a
neighborhood of the outer closed disk already suffices. -/
theorem nevanlinna_hiong_closed_disk (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (r ρ : ℝ),
      0 < r → r < ρ → MeromorphicOn f (closedBall 0 ρ) →
      AnalyticAt ℂ f 0 → f 0 ≠ 0 →
      ValueDistribution.proximity (fun z => iteratedDeriv k f z / f z) ⊤ r ≤
        C * nhLogarithmicSize f r ρ := by
  obtain ⟨C, hC, hbound⟩ := exists_NH_ratio_control_bound k
  have h6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨C * (1 + Real.log 6), mul_pos hC (by linarith), fun f r ρ hr hrρ hf hfa h0 => ?_⟩
  obtain ⟨h1, hρB, hδB, hrB, hTB, h0B⟩ := nhControl_bounds hr hrρ hf hfa h0
  have hh := hbound f r ρ (nhControl f r ρ) hr hrρ h1 hρB hδB hrB hf hfa h0 hTB h0B
  exact hh.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (one_add_log_nhControl_le f r ρ) hC.le)

/-- LaTeX `lem:NH` (Nevanlinna--Hiong), with the exact manuscript radius and
central-value terms. The extended disk radius includes infinity. AnalyticAt
and a nonzero value express that the meromorphic germ at zero is finite and nonzero. -/
theorem Paper.lem_NH (k : ℕ) (_hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (r ρ : ℝ) (R : ℝ≥0∞),
      0 < r → r < ρ → ENNReal.ofReal ρ < R → MeromorphicOn f (Metric.eball 0 R) →
      AnalyticAt ℂ f 0 → f 0 ≠ 0 →
      ValueDistribution.proximity (fun z => iteratedDeriv k f z / f z) ⊤ r ≤
        C * (1 + Real.posLog (diskCharacteristic f ρ) + Real.posLog (Real.posLog (1 / ‖f 0‖)) +
          Real.posLog ρ + Real.posLog (1 / (ρ - r)) + Real.posLog (1 / r)) := by
  obtain ⟨C, hC, hh⟩ := nevanlinna_hiong_closed_disk k
  refine ⟨C, hC, fun f r ρ R hr hrρ hρR hf hfa h0 => ?_⟩
  apply hh f r ρ hr hrρ _ hfa h0
  apply hf.mono_set
  intro z hz
  have hn : ‖z‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hz
  have he := (ENNReal.ofReal_le_ofReal hn).trans_lt hρR
  simpa only [Metric.mem_eball, edist_dist, dist_zero_right] using he

end ModifiedCartan
#print axioms ModifiedCartan.nevanlinna_hiong_closed_disk
#print axioms ModifiedCartan.Paper.lem_NH
