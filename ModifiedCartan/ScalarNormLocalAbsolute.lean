import ModifiedCartan.ScalarNormTwoPhase
import ModifiedCartan.TwoPhaseHomogeneous
import ModifiedCartan.Homogeneity

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Local absolute-harmonic profile of the actual scalar norm limit. Its
coefficient is an actual root of the canonical quadratic at the chart center. -/
theorem ArbitraryRadiusLimitData.scalar_norm_powerChart_local_absolute
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2) :
    ∃ (b : ℂ) (s : ℝ),
      b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) ∧
      0 < s ∧ ball 1 s ⊆ powerChartDomain a ρ ∧
      MapsTo (powerChart a ρ) (ball 1 s) (ball 0 2) ∧
      EqOn (fun w => (d.U (powerChart a ρ w)).toReal) (fun w => |(b * w).re|) (ball 1 s) := by
  have hr : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have ha4 : ‖a‖ < 4 := by linarith
  have haU : a ∈ ball (0 : ℂ) 2 := by simpa only [mem_ball, dist_zero_right] using ha2
  obtain ⟨b, hb, hphase⟩ := d.scalar_norm_powerChart_locallyTwoPhase hρ ha ha4
  have h1 := powerChartDomain_one_mem ha ha4 hr
  obtain ⟨s, hs, hsG, hform⟩ := hphase 1 h1
  have hψ : ContinuousAt (powerChart a ρ) 1 := (powerChart_analytic a ρ 1 h1).continuousAt
  have hnear : ∀ᶠ w in 𝓝 (1 : ℂ), powerChart a ρ w ∈ ball (0 : ℂ) 2 :=
    hψ.eventually (isOpen_ball.mem_nhds (by simpa only [powerChart_one] using haU))
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hnear
  let R := min s δ
  have hR : 0 < R := lt_min hs hδ
  have hRs : ball (1 : ℂ) R ⊆ ball 1 s := ball_subset_ball (min_le_left _ _)
  have hRG : ball (1 : ℂ) R ⊆ powerChartDomain a ρ := hRs.trans hsG
  have hmap : MapsTo (powerChart a ρ) (ball 1 R) (ball 0 2) :=
    fun _ hw => hδU ((ball_subset_ball (min_le_right _ _)) hw)
  have hrad : ∀ t : ℝ, 0 < t → (t : ℂ) ∈ ball (1 : ℂ) R →
      (d.U (powerChart a ρ (t : ℂ))).toReal = t * (d.U (powerChart a ρ 1)).toReal := by
    intro t ht htR
    have htU : ((t ^ ρ⁻¹ : ℝ) : ℂ) * a ∈ ball (0 : ℂ) 2 := by
      simpa only [powerChart_real a ρ ht.le] using hmap htR
    have hh := congrArg EReal.toReal
      (Paper.prop_homogeneity hr d (Real.rpow_pos_of_pos ht ρ⁻¹) haU htU)
    simpa only [powerChart_real a ρ ht.le, powerChart_one, EReal.toReal_mul,
      EReal.toReal_coe, Real.rpow_inv_rpow ht.le hr.ne'] using hh
  have hh := (hform.mono hRs).homogeneous_at_one hR hrad
  have hnon (w : ℂ) (hw : w ∈ ball (1 : ℂ) R) : 0 ≤ (d.U (powerChart a ρ w)).toReal :=
    EReal.toReal_nonneg (d.nonneg _ (powerChart_mapsTo ha hr (hRG hw)))
  refine ⟨b, R, hb, hR, hRG, hmap, ?_⟩
  rcases hh with he | he | he
  · intro w hw
    have hv : (d.U (powerChart a ρ w)).toReal = (b * w).re := he hw
    have hp : 0 ≤ (b * w).re := by rw [← hv]; exact hnon w hw
    exact hv.trans (abs_of_nonneg hp).symm
  · intro w hw
    have hv : (d.U (powerChart a ρ w)).toReal = -(b * w).re := he hw
    have hp : (b * w).re ≤ 0 := by have hh := hnon w hw; rw [hv] at hh; linarith
    exact hv.trans (abs_of_nonpos hp).symm
  · exact he

/-- Pointwise scalar norm profile, obtained from the exact local formula. -/
theorem ArbitraryRadiusLimitData.scalar_norm_value_root
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2) :
    ∃ b : ℂ, b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) ∧
      (d.U a).toReal = |b.re| := by
  obtain ⟨b, s, hb, hs, _, _, he⟩ := d.scalar_norm_powerChart_local_absolute hρ ha ha2
  refine ⟨b, hb, ?_⟩
  simpa only [powerChart_one, mul_one] using he (mem_ball_self hs)

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_powerChart_local_absolute
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_value_root
