import ModifiedCartan.ScalarDyadicTargetRates
import ModifiedCartan.ScalarSharpRadiusTransfer
import ModifiedCartan.ScalarSharpPrescribedWidth
import ModifiedCartan.ScalarPhaseSharpCrosses
import ModifiedCartan.ScalarLevelChartCompact
import ModifiedCartan.ScalarLevelChartDilation
import ModifiedCartan.ScalarDyadicLineTargets

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual local lines approach the previously fixed target with any rate
strictly below the local doubled norm profile. The distant reference scale,
subsequence, and every line are constructed from the original hypotheses.
Auxiliary to LaTeX `thm:A` (b). -/
theorem scalar_sharp_local_target_lines
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    (hstep : Tendsto (fun ν => a (ν + 1) - a ν) atTop (𝓝 0))
    (q : ScalarDyadicPeakTargetData f a ρ)
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    {c : ℕ → ℝ} (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hclim : Tendsto c atTop (𝓝 c₀))
    {a₀ : ℂ} (halim : Tendsto (fun ν => a (n ν)) atTop (𝓝 a₀))
    {κ κ₁ : ℝ} (hκ : 0 < κ) (hκ₁ : κ < κ₁) {z : ℂ}
    (hz : z ∈ scalarLevelChart a₀ ρ ((Real.pi / 2 : ℝ) : ℂ) (κ₁ / 2)) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ ε₀ > 0,
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ y : ℕ → ℝ, ∃ C ≥ 0, ∀ᶠ ν in atTop,
        (y ν ∈ Icc ((((c (ns ν) / (2 : ℝ) ^ K : ℝ) : ℂ) * z).im - ε)
          ((((c (ns ν) / (2 : ℝ) ^ K : ℝ) : ℂ) * z).im + ε)) ∧
        ∀ t ∈ Icc ((((c (ns ν) / (2 : ℝ) ^ K : ℝ) : ℂ) * z).re - ε)
          ((((c (ns ν) / (2 : ℝ) ^ K : ℝ) : ℂ) * z).re + ε),
          ‖scalarCurveSphere f ((((2 : ℝ) ^ (n (ns ν) + K) : ℝ) : ℂ) *
            (⟨t, y ν⟩ : ℂ)) - scalarSphereValue q.target‖ ≤
            C * Real.exp (-κ * characteristic f (c (ns ν) * (2 : ℝ) ^ n (ns ν))) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have ha₀norm : ‖a₀‖ = 1 := tendsto_nhds_unique halim.norm
    (by simpa only [ha] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  have ha₀ : a₀ ≠ 0 := norm_ne_zero_iff.mp (by rw [ha₀norm]; norm_num)
  obtain ⟨ℓ, hℓ, hdisks⟩ := scalar_peak_disks_have_uniform_level_margin hρpos
    (half_pos Real.pi_pos) (fun b hb => (q.sector_disks b hb).1)
  have hη : 0 < min q.lineRate (min q.decayRate (2 * ℓ)) :=
    lt_min q.lineRate_pos (lt_min q.decayRate_pos (by positivity))
  obtain ⟨K, hK, ht, ht1, hδ, hδsmall, hδexact⟩ :=
    exists_dyadic_sharp_rate hρpos hc₀ (hκ.trans hκ₁) hη
  let δ : ℝ := κ₁ * (c₀ / (2 : ℝ) ^ K) ^ ρ
  let Ω := scalarLevelChart a₀ ρ ((Real.pi / 2 : ℝ) : ℂ) (δ / 2)
  have hδline : δ ≤ q.lineRate := hδsmall.le.trans (min_le_left _ _)
  have hδdecay : δ ≤ q.decayRate :=
    hδsmall.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδlevel : δ / 2 ≤ ℓ := by
    have hh : δ < 2 * ℓ := hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hballB : closedBall a₀ (4 * q.width) ⊆ Ω :=
    (hdisks a₀ ha₀norm).trans (scalarLevelChart_antitone a₀ _ ρ hδlevel)
  have hzΩ : ((c₀ / (2 : ℝ) ^ K : ℝ) : ℂ) * z ∈ Ω := by
    have hh := scalarLevelChart_dilation_mem hρpos ht ht1 hz
    have he : (c₀ / (2 : ℝ) ^ K) ^ ρ * (κ₁ / 2) = δ / 2 := by dsimp only [δ]; ring
    rwa [he] at hh
  have hnK : Tendsto (fun ν => n ν + K) atTop atTop := (tendsto_add_atTop_nat K).comp hn
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hR : Tendsto (fun ν => (2 : ℝ) ^ (n ν + K)) atTop atTop := hpow.comp hnK
  have haK : Tendsto (fun ν => a (n ν + K)) atTop (𝓝 a₀) := by
    have hh := ((complex_fixed_shift_sub_tendsto_zero hstep K).comp hn).add halim
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using hh
  obtain ⟨ns, hns, hcross⟩ := scalar_phase_peak_subsequence_sharp_crosses f hlin htrans hsmall
    hρ hl hu hm hR (fun ν => ha (n ν + K)) haK (fun ν => hpeak (n ν + K))
  have hcrossδ := hcross δ hδ
  have hgood := hnK.eventually (q.good_at_rate htrans hδline)
  have hclose := hnK.eventually (q.close_at_rate htrans hδdecay)
  have hΩ := scalarLevelChart_isOpen ha₀ hρpos ((Real.pi / 2 : ℝ) : ℂ) (δ / 2)
  have hconn := scalarLevelChart_isPreconnected a₀ hρpos ((Real.pi / 2 : ℝ) : ℂ) (δ / 2)
  have hzlim : Tendsto (fun ν => ((c (ns ν) / (2 : ℝ) ^ K : ℝ) : ℂ) * z)
      atTop (𝓝 (((c₀ / (2 : ℝ) ^ K : ℝ) : ℂ) * z)) :=
    (((Complex.continuous_ofReal.tendsto _).comp (hclim.div_const ((2 : ℝ) ^ K))).mul_const z).comp
      hns.tendsto_atTop
  obtain ⟨d, hd, hdΩ⟩ :=
    (isCompact_singleton (x := (((c₀ / (2 : ℝ) ^ K : ℝ) : ℂ) * z))).exists_cthickening_subset_open
      hΩ (singleton_subset_iff.mpr hzΩ)
  have htransfer := characteristic_sharp_rate_transfer f htrans hlin hsmall hρpos hl hu
    (hpow.comp hn) hc hc₀ hclim (pow_pos (by norm_num : (0 : ℝ) < 2) K)
    (show κ < δ * (((2 : ℝ) ^ K / c₀) ^ ρ) by rw [hδexact]; exact hκ₁)
  refine ⟨K, hK, ns, hns, d / 4, by positivity, ?_⟩
  intro ε hε hεd
  have hballA : closedBall (((c₀ / (2 : ℝ) ^ K : ℝ) : ℂ) * z) (4 * ε) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith : 4 * ε ≤ d)).trans
      ((closedBall_subset_cthickening_singleton _ d).trans hdΩ)
  obtain ⟨y, C, hC, hlines⟩ := hcrossδ.moving_box_to_fixed_target_of_width hδ
    (hR.comp hns.tendsto_atTop) hΩ hconn (haK.comp hns.tendsto_atTop)
    q.width_pos hballB (by norm_num : (0 : ℝ) ≤ 2)
    (hns.tendsto_atTop.eventually hgood) (hns.tendsto_atTop.eventually hclose) hzlim hε hballA
  refine ⟨y, C, hC, ?_⟩
  filter_upwards [hlines, hns.tendsto_atTop.eventually htransfer] with ν hν htν
  refine ⟨hν.1.1, fun t ht => (hν.2 t ht).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have he : (2 : ℝ) ^ K * (2 : ℝ) ^ n (ns ν) = (2 : ℝ) ^ (n (ns ν) + K) := by
    rw [pow_add, mul_comm]
  dsimp only [Function.comp_def] at htν
  rw [he] at htν
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.scalar_sharp_local_target_lines
