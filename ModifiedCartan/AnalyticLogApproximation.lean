import ModifiedCartan.ExponentialLogMargin
import ModifiedCartan.AnalyticLogMeasureUpgrade

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Transfer a genuine logarithmic limit through an exponential analytic
approximation. A nonzero anchor for the approximating family is constructed,
then finite-prefix analyticity is handled by a strict subsequence. -/
theorem exists_analytic_log_limit_of_exponential_approximation
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hne : U.Nonempty)
    {X Y : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {A C B : ℝ}
    (hs : Tendsto s atTop atTop) (hspos : ∀ ν, 0 < s ν)
    (hX : LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ * Real.log ‖X ν z‖) u)
    (hXne : ∀ ν, ∀ᵐ z ∂volume.restrict U, X ν z ≠ 0)
    (hu : ∀ᵐ z ∂volume.restrict U, -A < u z)
    (hY : ∀ᶠ ν in atTop, AnalyticOnNhd ℂ (Y ν) U ∧
      ∀ z ∈ U, ‖Y ν z‖ ≤ Real.exp (B * s ν))
    (hclose : ∀ᶠ ν in atTop, ∀ z ∈ U, ‖Y ν z - X ν z‖ ≤ C * Real.exp (-A * s ν)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ ν, AnalyticOnNhd ℂ (Y (ns ν)) U ∧ ∃ z ∈ U, Y (ns ν) z ≠ 0) ∧
      LocalLpConvergence 1 U (fun ν z => (s (ns ν))⁻¹ * Real.log ‖Y (ns ν) z‖) u := by
  obtain ⟨ι, hι, hιlim⟩ := hX.exists_seq_tendsto_ae one_ne_zero hU
  obtain ⟨a, haU, halim, haX, hau⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hU.measure_ne_zero volume hne) (hιlim.and ((ae_all_iff.mpr hXne).and hu))
  have haclose : ∀ᶠ ν in atTop,
      |‖Y (ι ν) a‖ - ‖X (ι ν) a‖| ≤ C * Real.exp (-A * s (ι ν)) := by
    filter_upwards [hι.tendsto_atTop.eventually hclose] with ν hν
    exact (abs_norm_sub_norm_le _ _).trans (hν a haU)
  have hapos := (normalized_log_close_of_margin (hs.comp hι.tendsto_atTop)
    (Eventually.of_forall (fun ν => norm_pos_iff.mpr (haX (ι ν))))
    (by simpa only [Function.comp_def, div_eq_mul_inv, mul_comm] using halim) hau haclose).1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hapos.and (hι.tendsto_atTop.eventually hY))
  let ns : ℕ → ℕ := fun ν => ι (ν + N)
  have hns : StrictMono ns := hι.comp (fun _ _ h => Nat.add_lt_add_right h N)
  have hd (ν : ℕ) := hN (ν + N) (by omega)
  have hy (ν : ℕ) : AnalyticOnNhd ℂ (Y (ns ν)) U := (hd ν).2.1
  have hn (ν : ℕ) : ∃ z ∈ U, Y (ns ν) z ≠ 0 := ⟨a, haU, norm_pos_iff.mp (hd ν).1⟩
  have hmeasure : LocalMeasureConvergence U
      (fun ν z => Real.log ‖Y (ns ν) z‖ / s (ns ν)) u := by
    apply localMeasure_log_transfer_of_margin hU (hs.comp hns.tendsto_atTop)
      (fun ν => (hXne (ns ν)).mono (fun _ hz => norm_pos_iff.mpr hz))
      (fun K hK hKU ν => ((hy ν).continuousOn.norm.mono hKU).aestronglyMeasurable hK.measurableSet)
      (by simpa only [Function.comp_def, div_eq_mul_inv, mul_comm] using
        (hX.comp_strictMono hns).inMeasure one_ne_zero) hu
    filter_upwards [hns.tendsto_atTop.eventually hclose] with ν hν z hz
    exact (abs_norm_sub_norm_le _ _).trans (hν z hz)
  refine ⟨ns, hns, fun ν => ⟨hy ν, hn ν⟩, ?_⟩
  apply normalized_log_localL1_of_localMeasure hU hUc hne hy hn (fun ν => hspos (ns ν))
    (fun ν => (hd ν).2.2)
  simpa only [div_eq_mul_inv, mul_comm] using hmeasure

end ModifiedCartan
#print axioms ModifiedCartan.exists_analytic_log_limit_of_exponential_approximation
