import ModifiedCartan.ScalarPhaseCrosses
import ModifiedCartan.ScalarMovingCrosses
import ModifiedCartan.PositiveRateCompactness

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Construct an eventual positive cross rate on squares around any actual
unit phase peaks. The common disk size comes from proved sector geometry. -/
theorem scalar_phase_peak_moving_crosses
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {a : ℕ → ℂ} (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m (r ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    {ε : ℝ} (hε : 0 < ε)
    (hdisks : ∀ b : ℂ, ‖b‖ = 1 → closedBall b (4 * ε) ⊆ scalarFullSector b ρ) :
    ∃ δ > 0, ∀ᶠ ν in atTop,
      ScalarGoodCross f (r ν) (characteristic f (r ν)) δ (ComplexRect.box (a ν) ε ε hε hε) := by
  have hT := characteristic_tendsto_atTop_of_transcendental f htrans
  apply exists_eventually_positive_rate_of_subsequences
  · filter_upwards [(hT.comp hr).eventually_ge_atTop 0] with ν hν
    intro δ η hη hηδ hgood
    exact hgood.mono_rate hν hηδ
  · intro ns hns
    obtain ⟨a₀, ha₀, ms, hms, hconv⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
      (fun ν => show a (ns ν) ∈ sphere (0 : ℂ) 1 by
        simpa only [mem_sphere, dist_zero_right] using ha (ns ν))
    have ha₀norm : ‖a₀‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using ha₀
    have hr' : Tendsto (fun ν => r (ns (ms ν))) atTop atTop :=
      (hr.comp hns).comp hms.tendsto_atTop
    obtain ⟨ks, hks, hcross⟩ := scalar_phase_peaks_subsequence_crosses f hlin htrans hsmall hρ hl hu hm hr'
      (a := fun (_ : Fin 1) ν => a (ns (ms ν))) (a₀ := fun _ => a₀)
      (fun _ ν => ha (ns (ms ν))) (fun _ => hconv) (fun _ ν => hpeak (ns (ms ν)))
    have hcenter : Tendsto (fun ν => a (ns (ms (ks ν)))) atTop (𝓝 a₀) :=
      hconv.comp hks.tendsto_atTop
    have hscale : Tendsto (fun ν => characteristic f (r (ns (ms (ks ν))))) atTop atTop :=
      (hT.comp hr').comp hks.tendsto_atTop
    obtain ⟨δ, hδ, hgood⟩ := (hcross 0).moving_box hscale hcenter hε (hdisks a₀ ha₀norm)
    exact ⟨ms ∘ ks, hms.tendsto_atTop.comp hks.tendsto_atTop, δ, hδ, hgood⟩

/-- A uniform positive geometric width is constructed for all actual phase
peak sequences of the original curve. No rate or line choices are assumed. -/
theorem scalar_exists_phase_peak_cross_width
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) :
    ∃ ε : ℝ, ∃ hε : 0 < ε,
      (∀ b : ℂ, ‖b‖ = 1 → closedBall b (4 * ε) ⊆ scalarFullSector b ρ ∧
        closedBall ((1 / 2 : ℂ) * b) (4 * ε) ⊆ scalarFullSector b ρ) ∧
      ∀ r : ℕ → ℝ, Tendsto r atTop atTop → ∀ a : ℕ → ℂ,
        (∀ ν, ‖a ν‖ = 1) →
        (∀ ν, scalarPhaseCoefficient f m (r ν) * (a ν) ^ m = (((Real.pi / 2) ^ 2 : ℝ) : ℂ)) →
        ∃ δ > 0, ∀ᶠ ν in atTop,
          ScalarGoodCross f (r ν) (characteristic f (r ν)) δ (ComplexRect.box (a ν) ε ε hε hε) := by
  obtain ⟨ε, hε, hdisks⟩ := scalarFullSector_uniform_peak_disks (lt_of_lt_of_le zero_lt_one hρ)
  refine ⟨ε, hε, hdisks, ?_⟩
  intro r hr a ha hpeak
  exact scalar_phase_peak_moving_crosses f hlin htrans hsmall hρ hl hu hm hr ha hpeak hε
    (fun b hb => (hdisks b hb).1)

end ModifiedCartan
#print axioms ModifiedCartan.scalar_phase_peak_moving_crosses
#print axioms ModifiedCartan.scalar_exists_phase_peak_cross_width