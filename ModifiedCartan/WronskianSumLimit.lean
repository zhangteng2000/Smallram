import ModifiedCartan.WronskianLogInequality
import FewInflection.FundamentalAnalytic

open scoped Topology ENNReal
open Filter MeasureTheory Set

set_option autoImplicit false

namespace ModifiedCartan

theorem nonneg_of_localMeasure_lower_bound {U : Set ℂ} (hU : IsOpen U)
    {a b c : ℕ → ℂ → ℝ} {u : ℂ → ℝ} {δ : ℕ → ℝ}
    (ha : LocalMeasureConvergence U a u)
    (hb : LocalMeasureConvergence U b (fun _ => 0))
    (hc : LocalMeasureConvergence U c (fun _ => 0))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hle : ∀ n, ∀ᵐ z ∂volume.restrict U, b n z - δ n - c n z ≤ a n z) :
    ∀ᵐ z ∂volume.restrict U, 0 ≤ u z := by
  obtain ⟨ns, hns, haAE⟩ := ha.exists_seq_tendsto_ae hU
  have hb' : LocalMeasureConvergence U (fun n => b (ns n)) (fun _ => 0) :=
    fun K hK hKU => (hb K hK hKU).comp hns.tendsto_atTop
  obtain ⟨ms, hms, hbAE⟩ := hb'.exists_seq_tendsto_ae hU
  have hc' : LocalMeasureConvergence U (fun n => c (ns (ms n))) (fun _ => 0) :=
    fun K hK hKU => ((hc K hK hKU).comp hns.tendsto_atTop).comp hms.tendsto_atTop
  obtain ⟨ks, hks, hcAE⟩ := hc'.exists_seq_tendsto_ae hU
  have hleAE : ∀ᵐ z ∂volume.restrict U, ∀ n, b n z - δ n - c n z ≤ a n z :=
    ae_all_iff.mpr hle
  filter_upwards [haAE, hbAE, hcAE, hleAE] with z haz hbz hcz hlez
  have hal := (haz.comp hms.tendsto_atTop).comp hks.tendsto_atTop
  have hbl := hbz.comp hks.tendsto_atTop
  have hδl := ((hδ.comp hns.tendsto_atTop).comp hms.tendsto_atTop).comp hks.tendsto_atTop
  have hleft := (hbl.sub hδl).sub hcz
  simpa only [sub_zero] using le_of_tendsto_of_tendsto hleft hal
    (Eventually.of_forall (fun n => hlez (ns (ms (ks n)))))

theorem log_sum_nonneg_of_convergence {n : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → FewInflection.Index n → ℂ → ℂ} {s : ℕ → ℝ}
    {v : FewInflection.Index n → ℂ → ℝ}
    (hf : ∀ ν j, AnalyticOnNhd ℂ (f ν j) U)
    (hnz : ∀ ν j, ∃ z ∈ U, f ν j z ≠ 0)
    (hWnz : ∀ ν, ∃ z ∈ U, FewInflection.wronskian n (f ν) z ≠ 0)
    (hpos : ∀ ν, 0 < s ν) (hs : Tendsto s atTop atTop)
    (hv : ∀ j, LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν j z‖) (v j))
    (hW : LocalMeasureConvergence U
      (fun ν z => (s ν)⁻¹ * Real.log ‖FewInflection.wronskian n (f ν) z‖) (fun _ => 0)) :
    ∀ᵐ z ∂volume.restrict U, 0 ≤ ∑ j : FewInflection.Index n, v j z := by
  classical
  have hex : ∀ j, ∃ g : ℂ → ℂ, HasWeakComplexGradient U (v j) g := by
    intro j
    obtain ⟨g, hg, _⟩ := (hv j).log_limit_weak_gradient hU hUc (fun ν => hf ν j)
      (fun ν => hnz ν j) hs
    exact ⟨g, hg⟩
  choose g hg using hex
  have hD := normalizedWronskian_localMeasure hU hUc hv hf hnz hs hg
  have hplus := hD.scaled_logPlus (fun K hK hKU ν =>
    normalizedWronskian_aestronglyMeasurable (hf ν) hK hKU (s ν)) hs
  apply nonneg_of_localMeasure_lower_bound hU (LocalLpConvergence.real_sum_localMeasure hv)
    hW hplus (scaled_log_scale_tendsto_zero hs (∑ i : FewInflection.Index n, (i : ℕ)))
  intro ν
  have hWanalytic : AnalyticOnNhd ℂ (FewInflection.wronskian n (f ν)) U :=
    fun z hz => FewInflection.analyticAt_wronskian (fun j => hf ν j z hz)
  have hfnzAE : ∀ᵐ z ∂volume.restrict U, ∀ j, f ν j z ≠ 0 :=
    ae_all_iff.mpr (fun j => analytic_ae_ne_zero hU hUc (hf ν j) (hnz ν j))
  filter_upwards [hfnzAE, analytic_ae_ne_zero hU hUc hWanalytic (hWnz ν)] with z hz hWz
  exact wronskian_log_sum_lower_bound (hpos ν) hz hWz

namespace Paper

/-- LaTeX labels `lem:sum` and `eq:sum-positive`.
This finite-representative version is stronger: it does not require input
subharmonicity. Nontriviality is derived from the actual extended logarithms
and the stated convergence hypotheses, on a positive tail of the scales. -/
theorem lem_sum {n : ℕ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → FewInflection.Index n → ℂ → ℂ} {s : ℕ → ℝ}
    {v : FewInflection.Index n → ℂ → ℝ}
    (hf : ∀ ν j, DifferentiableOn ℂ (f ν j) U)
    (hs : Tendsto s atTop atTop)
    (hv : ∀ j, LocalERealLpConvergence 1 U
      (fun ν => normalizedExtendedLog (s ν) (f ν j)) (v j))
    (hW : LocalERealMeasureConvergence U
      (fun ν => normalizedExtendedLog (s ν) (FewInflection.wronskian n (f ν))) (fun _ => 0)) :
    ∀ᵐ z ∂volume.restrict U, 0 ≤ ∑ j : FewInflection.Index n, v j z := by
  by_cases hne : U.Nonempty
  · have hWtail := hW.normalizedLog_eventually_nontrivial hU hne hs
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((hs.eventually (eventually_gt_atTop 0)).and hWtail)
    have hpos (ν : ℕ) : 0 < s (ν + N) := (hN _ (Nat.le_add_left N ν)).1
    have hWnz (ν : ℕ) : ∃ z ∈ U, FewInflection.wronskian n (f (ν + N)) z ≠ 0 :=
      (hN _ (Nat.le_add_left N ν)).2
    have hfa (ν : ℕ) (j : FewInflection.Index n) : AnalyticOnNhd ℂ (f (ν + N) j) U :=
      (hf (ν + N) j).analyticOnNhd hU
    have hnz (ν : ℕ) (j : FewInflection.Index n) : ∃ z ∈ U, f (ν + N) j z ≠ 0 :=
      (hv j).normalizedLog_nontrivial hU hne (hpos ν)
    have hWreal := (hW.comp_tendsto (tendsto_add_atTop_nat N)).normalizedLog_real hU hUc
      (fun ν z hz => FewInflection.analyticAt_wronskian (fun j => hfa ν j z hz)) hWnz
    exact log_sum_nonneg_of_convergence hU hUc hfa hnz hWnz hpos
      (hs.comp (tendsto_add_atTop_nat N))
      (fun j => (hv j).normalizedLog_real.comp_tendsto (tendsto_add_atTop_nat N)) hWreal
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hUempty]

end Paper


end ModifiedCartan

