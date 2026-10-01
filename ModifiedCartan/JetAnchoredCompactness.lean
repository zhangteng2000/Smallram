import ModifiedCartan.JetLogCompactness

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Holomorphic logarithm compactness with a finite initial-jet exponent
at a fixed point, rather than a nonzero value of the function at that point. -/
theorem exists_jet_anchored_log_subsequence {n : ℕ} {f : ℕ → ℂ → ℂ}
    {s : ℕ → ℝ} {a : ℂ} {C ell : ℝ} (ha : a ∈ ball (0 : ℂ) 2)
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) (ball 0 4))
    (hs1 : ∀ ν, 1 ≤ s ν) (hs : Tendsto s atTop atTop)
    (hj : ∀ ν, 0 < scaledJetLength n (s ν) (f ν) a)
    (hb : ∀ ν z, z ∈ ball (0 : ℂ) 4 → ‖f ν z‖ ≤ Real.exp (C * s ν))
    (hlim : Tendsto (fun ν => Real.log (scaledJetLength n (s ν) (f ν) a) / s ν)
      atTop (𝓝 ell)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ v : ℂ → ℝ,
      LocalLpConvergence 1 (ball (0 : ℂ) 4)
        (fun ν z => (s (ns ν))⁻¹ * Real.log ‖f (ns ν) z‖) v := by
  have hsub (ν : ℕ) := normalizedExtendedLog_isSubharmonicOn isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected (hf ν)
    (analytic_nontrivial_of_scaledJetLength_pos (hs1 ν) ha (hf ν) (hj ν))
    (zero_lt_one.trans_le (hs1 ν))
  have hbdd : ∀ K, IsCompact K → K ⊆ ball (0 : ℂ) 4 → ∃ M : ℝ,
      ∀ ν z, z ∈ K → normalizedExtendedLog (s ν) (f ν) z ≤ (M : EReal) := by
    intro K _ hKU
    exact ⟨C, fun ν z hz => (normalizedExtendedLog_le_iff_norm_le_exp
      (zero_lt_one.trans_le (hs1 ν)) (f ν) z C).mpr (hb ν z (hKU hz))⟩
  obtain ⟨ns, hns, hcase⟩ := Paper.lem_subharmonic_compactness isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected ⟨0, mem_ball_self (by norm_num)⟩ hsub hbdd
  rcases hcase with hc | ⟨_, _, _, v, _, hv⟩
  · exact (not_log_collapse_of_jet_log_limit ha (hs.comp hns.tendsto_atTop)
      (fun ν => hf (ns ν)) (Eventually.of_forall (fun ν => hj (ns ν)))
      (hlim.comp hns.tendsto_atTop) hc).elim
  · exact ⟨ns, hns, v, hv.normalizedLog_real⟩

/-- Simultaneous nontrivial component limits for the pointwise unitary
basis changes, retaining actual functions and finite singular exponents. -/
theorem exists_common_jet_anchored_log_limits {n N : ℕ} {f : ℕ → Fin N → ℂ → ℂ}
    {s : ℕ → ℝ} {a : ℂ} {C : ℝ} {ell : Fin N → ℝ} (ha : a ∈ ball (0 : ℂ) 2)
    (hs : Tendsto s atTop atTop)
    (hd : ∀ᶠ ν in atTop, ∀ j,
      AnalyticOnNhd ℂ (f ν j) (ball 0 4) ∧ 0 < scaledJetLength n (s ν) (f ν j) a ∧
      ∀ z ∈ ball (0 : ℂ) 4, ‖f ν j z‖ ≤ Real.exp (C * s ν))
    (hl : ∀ j, Tendsto (fun ν => Real.log (scaledJetLength n (s ν) (f ν j) a) / s ν)
      atTop (𝓝 (ell j))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ ν, 0 < s (ns ν) ∧ ∀ j, AnalyticOnNhd ℂ (f (ns ν) j) (ball 0 4) ∧
        ∃ z ∈ ball (0 : ℂ) 4, f (ns ν) j z ≠ 0) ∧
      ∃ (u : Fin N → ℂ → EReal) (v : Fin N → ℂ → ℝ), ∀ j,
        IsSubharmonicOn (ball (0 : ℂ) 4) (u j) ∧
        (∃ z ∈ ball (0 : ℂ) 4, u j z ≠ ⊥) ∧
        u j =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v j z : EReal)) ∧
        LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
          (fun ν => normalizedExtendedLog (s (ns ν)) (f (ns ν) j)) (v j) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((hs.eventually_ge_atTop 1).and hd)
  let τ : ℕ → ℕ := fun ν => ν + M
  have hτ : StrictMono τ := fun _ _ h => Nat.add_lt_add_right h M
  have hdata (ν : ℕ) := hM (τ ν) (by dsimp only [τ]; omega)
  let P : Fin N → (ℕ → ℕ) → Prop := fun j ns => ∃ v : ℂ → ℝ,
    LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (s (τ (ns ν)))⁻¹ * Real.log ‖f (τ (ns ν)) j z‖) v
  obtain ⟨ι, hι, hi⟩ := finite_subsequence_extraction N P (by
    intro j ns hns
    exact exists_jet_anchored_log_subsequence ha (fun ν => ((hdata (ns ν)).2 j).1)
      (fun ν => (hdata (ns ν)).1) (hs.comp (hτ.tendsto_atTop.comp hns.tendsto_atTop))
      (fun ν => ((hdata (ns ν)).2 j).2.1) (fun ν => ((hdata (ns ν)).2 j).2.2)
      ((hl j).comp (hτ.tendsto_atTop.comp hns.tendsto_atTop))) (by
    intro j ns ms hP hms
    obtain ⟨v, hv⟩ := hP
    exact ⟨v, hv.comp_tendsto hms.tendsto_atTop⟩)
  choose v hv using hi
  have hf' (ν : ℕ) (j : Fin N) := ((hdata (ι ν)).2 j).1
  have hs' (ν : ℕ) : 0 < s (τ (ι ν)) := zero_lt_one.trans_le (hdata (ι ν)).1
  have hn' (ν : ℕ) (j : Fin N) : ∃ z ∈ ball (0 : ℂ) 4, f (τ (ι ν)) j z ≠ 0 :=
    analytic_nontrivial_of_scaledJetLength_pos (hdata (ι ν)).1 ha (hf' ν j) ((hdata (ι ν)).2 j).2.1
  have hreps (j : Fin N) := normalizedLog_limit_subharmonic_representative isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected ⟨0, mem_ball_self (by norm_num)⟩
    (fun ν => hf' ν j) (fun ν => hn' ν j) hs' (hv j)
  choose u hu using hreps
  exact ⟨τ ∘ ι, hτ.comp hι, fun ν => ⟨hs' ν, fun j => ⟨hf' ν j, hn' ν j⟩⟩, u, v, hu⟩

end ModifiedCartan
#print axioms ModifiedCartan.exists_common_jet_anchored_log_limits
