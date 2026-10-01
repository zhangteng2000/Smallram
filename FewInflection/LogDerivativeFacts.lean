import FewInflection.FundamentalAnalytic
import Mathlib.Analysis.Meromorphic.Basic

open scoped BigOperators Topology
open Filter Asymptotics MeromorphicAt MeromorphicOn MeasureTheory Metric Real Set Topology

namespace FewInflection

noncomputable section

/-! The logarithmic derivative of the Wronskian is meromorphic by the basic
    meromorphic derivative/division API. -/
theorem wronskian_logDeriv_meromorphic
    {n : ℕ} (f : Curve n) :
    Meromorphic (logDeriv (fun z : ℂ => wronskian n f.coord z)) := by
  have hA : AnalyticOnNhd ℂ (fun z : ℂ => wronskian n f.coord z) Set.univ := by
    exact Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_wronskian f)
  exact (meromorphicOn_univ.mp hA.meromorphicOn).logDeriv

/-! At a genuine Wronskian zero, the logarithmic derivative has the simple
    pole predicted by the local divisor calculation. -/
theorem wronskian_logDeriv_order_at_zero
    {n : ℕ} (f : Curve n) (z : ℂ)
    (hWz : wronskian n f.coord z = 0)
    (hWnot : ∃ w : ℂ, wronskian n f.coord w ≠ 0) :
    meromorphicOrderAt (logDeriv (fun w : ℂ => wronskian n f.coord w)) z = -1 := by
  have hA : AnalyticOnNhd ℂ (fun w : ℂ => wronskian n f.coord w) Set.univ := by
    exact Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_wronskian f)
  have hAz : AnalyticAt ℂ (fun w : ℂ => wronskian n f.coord w) z :=
    hA z (Set.mem_univ _)
  have hM : MeromorphicAt (fun w : ℂ => wronskian n f.coord w) z := hAz.meromorphicAt
  have hfinite : meromorphicOrderAt (fun w : ℂ => wronskian n f.coord w) z ≠ (⊤ : WithTop ℤ) := by
    obtain ⟨w, hw⟩ := hWnot
    have hAw : AnalyticAt ℂ (fun w : ℂ => wronskian n f.coord w) w :=
      hA w (Set.mem_univ _)
    have ho : analyticOrderAt (fun w : ℂ => wronskian n f.coord w) w = 0 :=
      hAw.analyticOrderAt_eq_zero.mpr hw
    have hfinitew : meromorphicOrderAt (fun w : ℂ => wronskian n f.coord w) w ≠ (⊤ : WithTop ℤ) := by
      rw [hAw.meromorphicOrderAt_eq, ho]
      norm_num
    exact hA.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) hfinitew
  have hne : meromorphicOrderAt (fun w : ℂ => wronskian n f.coord w) z ≠ 0 := by
    intro hz
    have ho : analyticOrderAt (fun w : ℂ => wronskian n f.coord w) z = 0 := by
      rw [hAz.meromorphicOrderAt_eq] at hz
      simpa using hz
    exact (hAz.analyticOrderAt_eq_zero.mp ho) hWz
  exact meromorphicOrderAt_logDeriv_eq_neg_one hM hne hfinite

/-! Away from the discrete Wronskian zero set, the top fundamental
    coefficient is the negative logarithmic derivative. -/
theorem fundamental_last_coefficient_eventuallyEq_neg_wronskian_logDeriv
    {n : ℕ} (f : Curve n)
    (hWnot : ∃ w : ℂ, wronskian n f.coord w ≠ 0) :
    (fun z : ℂ => fundamentalCoefficients n f.coord z ⟨n, Nat.lt_succ_self n⟩) =ᶠ[codiscrete ℂ]
      (fun z : ℂ => -logDeriv (fun w : ℂ => wronskian n f.coord w) z) := by
  have hnon : (fun z : ℂ => wronskian n f.coord z) ⁻¹' ({0}ᶜ : Set ℂ) ∈ codiscrete ℂ := by
    rcases wronskian_zero_or_nonzero_codiscrete f with hzero | hnon
    · obtain ⟨w, hw⟩ := hWnot
      exact False.elim (hw (hzero w))
    · exact hnon
  filter_upwards [hnon] with z hz
  have hz' : wronskian n f.coord z ≠ 0 := hz
  have hcoef := fundamental_last_coefficient_eq_neg_deriv_div
    (g := f.coord) (z := z) (fun j => (f.holomorphic j).analyticAt z) hz'
  rw [hcoef, logDeriv_apply]
  ring

end

end FewInflection
