import ModifiedCartan.JetAnchoredCompactness

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A proved finite exponential jet lower bound excludes uniform logarithmic
collapse. Convergence of the jet exponent is unnecessary. -/
theorem not_log_collapse_of_jet_exp_lower {n : ℕ} {s : ℕ → ℝ} {f : ℕ → ℂ → ℂ}
    {a : ℂ} {B : ℝ} (ha : a ∈ ball (0 : ℂ) 2) (hs : Tendsto s atTop atTop)
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) (ball 0 4))
    (hj : ∀ᶠ ν in atTop, Real.exp (-B * s ν) ≤ scaledJetLength n (s ν) (f ν) a) :
    ¬ LocalUniformlyToBot (ball (0 : ℂ) 4) (fun ν => normalizedExtendedLog (s ν) (f ν)) := by
  intro hc
  have hupper := hc (closedBall a 1) (isCompact_closedBall _ _) (closed_unit_disk_subset_D4 ha) (-B - 2)
  have hK := jetCauchyConstant_pos n (by norm_num : (0 : ℝ) < 1)
  obtain ⟨ν, hν, hsν, hKν, hjν⟩ := (hupper.and ((hs.eventually_ge_atTop 1).and
    ((hs.eventually_ge_atTop (Real.log (jetCauchyConstant n 1))).and hj))).exists
  have hspos : 0 < s ν := zero_lt_one.trans_le hsν
  have hfn : ∀ z ∈ sphere a 1, ‖f ν z‖ ≤ Real.exp ((-B - 2) * s ν) := by
    intro z hz
    exact (normalizedExtendedLog_le_iff_norm_le_exp hspos (f ν) z (-B - 2)).mp
      (hν z (sphere_subset_closedBall hz))
  have hjet := scaledJetLength_le_of_sphere_bound (n := n) hsν (by norm_num : (0 : ℝ) < 1)
    (Real.exp_pos _).le ((hf ν).differentiableOn.diffContOnCl_ball (closed_unit_disk_subset_D4 ha)) hfn
  have hjet' : scaledJetLength n (s ν) (f ν) a ≤ Real.exp ((-B - 1) * s ν) :=
    hjet.trans (by simpa only [show -B - 2 + 1 = -B - 1 by ring] using
      constant_mul_exp_le_exp (a := -B - 2) hK hKν)
  have hh := Real.exp_le_exp.mp (hjν.trans hjet')
  nlinarith

theorem exists_jet_lower_log_subsequence {n : ℕ} {f : ℕ → ℂ → ℂ}
    {s : ℕ → ℝ} {a : ℂ} {C B : ℝ} (ha : a ∈ ball (0 : ℂ) 2)
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) (ball 0 4))
    (hs1 : ∀ ν, 1 ≤ s ν) (hs : Tendsto s atTop atTop)
    (hj : ∀ ν, Real.exp (-B * s ν) ≤ scaledJetLength n (s ν) (f ν) a)
    (hb : ∀ ν z, z ∈ ball (0 : ℂ) 4 → ‖f ν z‖ ≤ Real.exp (C * s ν)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ v : ℂ → ℝ,
      LocalLpConvergence 1 (ball (0 : ℂ) 4)
        (fun ν z => (s (ns ν))⁻¹ * Real.log ‖f (ns ν) z‖) v := by
  have hpos (ν : ℕ) : 0 < scaledJetLength n (s ν) (f ν) a := (Real.exp_pos _).trans_le (hj ν)
  have hsub (ν : ℕ) := normalizedExtendedLog_isSubharmonicOn isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected (hf ν)
    (analytic_nontrivial_of_scaledJetLength_pos (hs1 ν) ha (hf ν) (hpos ν))
    (zero_lt_one.trans_le (hs1 ν))
  have hbdd : ∀ K, IsCompact K → K ⊆ ball (0 : ℂ) 4 → ∃ M : ℝ,
      ∀ ν z, z ∈ K → normalizedExtendedLog (s ν) (f ν) z ≤ (M : EReal) := by
    intro K _ hKU
    exact ⟨C, fun ν z hz => (normalizedExtendedLog_le_iff_norm_le_exp
      (zero_lt_one.trans_le (hs1 ν)) (f ν) z C).mpr (hb ν z (hKU hz))⟩
  obtain ⟨ns, hns, hcase⟩ := Paper.lem_subharmonic_compactness isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected ⟨0, mem_ball_self (by norm_num)⟩ hsub hbdd
  rcases hcase with hc | ⟨_, _, _, v, _, hv⟩
  · exact (not_log_collapse_of_jet_exp_lower ha (hs.comp hns.tendsto_atTop)
      (fun ν => hf (ns ν)) (Eventually.of_forall (fun ν => hj (ns ν))) hc).elim
  · exact ⟨ns, hns, v, hv.normalizedLog_real⟩

/-- Simultaneous component compactness from actual jet bounds. This applies
to a prescribed unitary basis, including a basis selected by a target value. -/
theorem exists_common_jet_lower_log_limits {n N : ℕ} {f : ℕ → Fin N → ℂ → ℂ}
    {s : ℕ → ℝ} {a : ℂ} {C B : ℝ} (ha : a ∈ ball (0 : ℂ) 2)
    (hs : Tendsto s atTop atTop)
    (hd : ∀ᶠ ν in atTop, ∀ j,
      AnalyticOnNhd ℂ (f ν j) (ball 0 4) ∧
        Real.exp (-B * s ν) ≤ scaledJetLength n (s ν) (f ν j) a ∧
          ∀ z ∈ ball (0 : ℂ) 4, ‖f ν j z‖ ≤ Real.exp (C * s ν)) :
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
    exact exists_jet_lower_log_subsequence ha (fun ν => ((hdata (ns ν)).2 j).1)
      (fun ν => (hdata (ns ν)).1) (hs.comp (hτ.tendsto_atTop.comp hns.tendsto_atTop))
      (fun ν => ((hdata (ns ν)).2 j).2.1) (fun ν => ((hdata (ns ν)).2 j).2.2)) (by
    intro j ns ms hP hms
    obtain ⟨v, hv⟩ := hP
    exact ⟨v, hv.comp_tendsto hms.tendsto_atTop⟩)
  choose v hv using hi
  have hf' (ν : ℕ) (j : Fin N) := ((hdata (ι ν)).2 j).1
  have hs' (ν : ℕ) : 0 < s (τ (ι ν)) := zero_lt_one.trans_le (hdata (ι ν)).1
  have hn' (ν : ℕ) (j : Fin N) : ∃ z ∈ ball (0 : ℂ) 4, f (τ (ι ν)) j z ≠ 0 :=
    analytic_nontrivial_of_scaledJetLength_pos (hdata (ι ν)).1 ha (hf' ν j)
      ((Real.exp_pos _).trans_le (((hdata (ι ν)).2 j).2.1))
  have hreps (j : Fin N) := normalizedLog_limit_subharmonic_representative isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected ⟨0, mem_ball_self (by norm_num)⟩
    (fun ν => hf' ν j) (fun ν => hn' ν j) hs' (hv j)
  choose u hu using hreps
  exact ⟨τ ∘ ι, hτ.comp hι, fun ν => ⟨hs' ν, fun j => ⟨hf' ν j, hn' ν j⟩⟩, u, v, hu⟩

end ModifiedCartan
#print axioms ModifiedCartan.not_log_collapse_of_jet_exp_lower
#print axioms ModifiedCartan.exists_common_jet_lower_log_limits
