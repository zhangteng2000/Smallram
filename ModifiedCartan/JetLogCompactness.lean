import ModifiedCartan.PointJetUpper
import ModifiedCartan.LogLimitRepresentatives

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem normalizedExtendedLog_le_iff_norm_le_exp {s : ℝ} (hs : 0 < s)
    (f : ℂ → ℂ) (z : ℂ) (B : ℝ) :
    normalizedExtendedLog s f z ≤ (B : EReal) ↔ ‖f z‖ ≤ Real.exp (B * s) := by
  by_cases hz : f z = 0
  · rw [normalizedExtendedLog_eq_bot hs hz, hz, norm_zero]
    exact iff_of_true bot_le (Real.exp_pos _).le
  · rw [normalizedExtendedLog_of_ne_zero s hz, EReal.coe_le_coe_iff,
      mul_comm, ← div_eq_mul_inv, div_le_iff₀ hs,
      Real.log_le_iff_le_exp (norm_pos_iff.mpr hz)]

theorem analytic_nontrivial_of_scaledJetLength_pos {n : ℕ} {s : ℝ} {f : ℂ → ℂ} {a : ℂ}
    (hs : 1 ≤ s) (ha : a ∈ ball (0 : ℂ) 2)
    (hf : AnalyticOnNhd ℂ f (ball 0 4)) (hj : 0 < scaledJetLength n s f a) :
    ∃ z ∈ ball (0 : ℂ) 4, f z ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hb := scaledJetLength_le_of_sphere_bound (n := n) hs (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 0)
    (hf.differentiableOn.diffContOnCl_ball (closed_unit_disk_subset_D4 ha))
    (fun z hz => by rw [hn z (closed_unit_disk_subset_D4 ha (sphere_subset_closedBall hz)), norm_zero])
  simp only [mul_zero] at hb
  exact (not_lt_of_ge hb hj)

/-- A finite singular exponent prevents collapse of the corresponding
holomorphic component in the compactness dichotomy. -/
theorem not_log_collapse_of_jet_log_limit {n : ℕ} {s : ℕ → ℝ} {f : ℕ → ℂ → ℂ}
    {a : ℂ} {ell : ℝ} (ha : a ∈ ball (0 : ℂ) 2)
    (hs : Tendsto s atTop atTop)
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) (ball 0 4))
    (hj : ∀ᶠ ν in atTop, 0 < scaledJetLength n (s ν) (f ν) a)
    (hlim : Tendsto (fun ν => Real.log (scaledJetLength n (s ν) (f ν) a) / s ν)
      atTop (𝓝 ell)) :
    ¬ LocalUniformlyToBot (ball (0 : ℂ) 4) (fun ν => normalizedExtendedLog (s ν) (f ν)) := by
  intro hc
  have hupper := hc (closedBall a 1) (isCompact_closedBall _ _) (closed_unit_disk_subset_D4 ha) (ell - 2)
  have hK := jetCauchyConstant_pos n (by norm_num : (0 : ℝ) < 1)
  obtain ⟨ν, hν, hsν, hKν, hjν, hlimν⟩ := (hupper.and ((hs.eventually_ge_atTop 1).and
    ((hs.eventually_ge_atTop (Real.log (jetCauchyConstant n 1))).and (hj.and
    (hlim.eventually (lt_mem_nhds (show ell - 1 < ell by linarith))))))).exists
  have hspos : 0 < s ν := zero_lt_one.trans_le hsν
  have hfn : ∀ z ∈ sphere a 1, ‖f ν z‖ ≤ Real.exp ((ell - 2) * s ν) := by
    intro z hz
    exact (normalizedExtendedLog_le_iff_norm_le_exp hspos (f ν) z (ell - 2)).mp
      (hν z (sphere_subset_closedBall hz))
  have hjet := scaledJetLength_le_of_sphere_bound (n := n) hsν (by norm_num : (0 : ℝ) < 1)
    (Real.exp_pos _).le ((hf ν).differentiableOn.diffContOnCl_ball (closed_unit_disk_subset_D4 ha)) hfn
  have hjet' : scaledJetLength n (s ν) (f ν) a ≤ Real.exp ((ell - 1) * s ν) :=
    hjet.trans (by simpa only [show ell - 2 + 1 = ell - 1 by ring] using
      constant_mul_exp_le_exp (a := ell - 2) hK hKν)
  have hh := Real.log_le_log hjν hjet'
  rw [Real.log_exp] at hh
  have he := (div_le_iff₀ hspos).mpr hh
  exact (not_lt_of_ge he hlimν)

end ModifiedCartan
#print axioms ModifiedCartan.not_log_collapse_of_jet_log_limit
