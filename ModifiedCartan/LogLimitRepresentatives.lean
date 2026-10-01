import ModifiedCartan.FiniteLogCompactness

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Retain the actual subharmonic representative of a normalized
holomorphic logarithm limit, including its finite AE representative. -/
theorem normalizedLog_limit_subharmonic_representative {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hne : U.Nonempty)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {v : ℂ → ℝ}
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) U)
    (hnz : ∀ ν, ∃ z ∈ U, f ν z ≠ 0) (hs : ∀ ν, 0 < s ν)
    (hlim : LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν z‖) v) :
    ∃ u : ℂ → EReal, IsSubharmonicOn U u ∧ (∃ z ∈ U, u z ≠ ⊥) ∧
      u =ᵐ[volume.restrict U] (fun z => (v z : EReal)) ∧
      LocalERealLpConvergence 1 U (fun ν => normalizedExtendedLog (s ν) (f ν)) v := by
  have hsub (ν : ℕ) : IsSubharmonicOn U (normalizedExtendedLog (s ν) (f ν)) :=
    normalizedExtendedLog_isSubharmonicOn hU hUc (hf ν) (hnz ν) (hs ν)
  have hfinite (ν : ℕ) : ∀ᵐ z ∂volume.restrict U,
      normalizedExtendedLog (s ν) (f ν) z ≠ ⊥ ∧
      normalizedExtendedLog (s ν) (f ν) z ≠ ⊤ := by
    filter_upwards [analytic_ae_ne_zero hU hUc (hf ν) (hnz ν)] with z hz
    exact (normalizedExtendedLog_finite_iff (hs ν) (f ν) z).mpr hz
  have hreal : LocalLpConvergence 1 U
      (fun ν z => (normalizedExtendedLog (s ν) (f ν) z).toReal) v := by
    simpa only [normalizedExtendedLog_toReal] using hlim
  obtain ⟨u, hu, hune, hrep⟩ :=
    exists_nontrivial_subharmonic_representative_of_localL1_limit hU hne hsub hfinite hreal
  exact ⟨u, hu, hune, hrep, ⟨hfinite, hreal⟩⟩

/-- Simultaneous compactness with the genuine extended subharmonic
limits, as needed for LaTeX `eq:norm-limit`. -/
theorem exists_common_log_limits_with_representatives_eventual {N : ℕ}
    {f : ℕ → Fin N → ℂ → ℂ} {s : ℕ → ℝ} {C : ℝ}
    (hs : Tendsto s atTop atTop)
    (hdata : ∀ᶠ ν in atTop, ∀ j, AnalyticOnNhd ℂ (f ν j) (ball 0 4) ∧
      f ν j 0 ≠ 0 ∧ ∀ z ∈ ball (0 : ℂ) 4, ‖f ν j z‖ ≤ Real.exp (C * s ν))
    (hcenter : ∀ j, Tendsto (fun ν => Real.log ‖f ν j 0‖ / s ν) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ ν, 0 < s (ns ν) ∧ ∀ j, AnalyticOnNhd ℂ (f (ns ν) j) (ball 0 4) ∧
        f (ns ν) j 0 ≠ 0 ∧ ∀ z ∈ ball (0 : ℂ) 4, ‖f (ns ν) j z‖ ≤ Real.exp (C * s (ns ν))) ∧
      ∃ (u : Fin N → ℂ → EReal) (v : Fin N → ℂ → ℝ), ∀ j,
        IsSubharmonicOn (ball (0 : ℂ) 4) (u j) ∧
        (∃ z ∈ ball (0 : ℂ) 4, u j z ≠ ⊥) ∧
        u j =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v j z : EReal)) ∧
        LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
          (fun ν => normalizedExtendedLog (s (ns ν)) (f (ns ν) j)) (v j) := by
  obtain ⟨ns, hns, hd, v, hv⟩ :=
    exists_common_normalized_log_subsequence_eventual hs hdata hcenter
  have hu (j : Fin N) := normalizedLog_limit_subharmonic_representative isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected ⟨0, mem_ball_self (by norm_num)⟩
    (fun ν => ((hd ν).2 j).1)
    (fun ν => ⟨0, mem_ball_self (by norm_num), ((hd ν).2 j).2.1⟩)
    (fun ν => (hd ν).1) (hv j)
  choose u hu using hu
  exact ⟨ns, hns, hd, u, v, hu⟩

end ModifiedCartan
#print axioms ModifiedCartan.normalizedLog_limit_subharmonic_representative
#print axioms ModifiedCartan.exists_common_log_limits_with_representatives_eventual
