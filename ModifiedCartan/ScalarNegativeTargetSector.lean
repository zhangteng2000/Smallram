import ModifiedCartan.TwoPhaseSmoothPatches
import ModifiedCartan.ScalarSmoothNegativeTarget
import ModifiedCartan.ScalarPrescribedUnitaryLimits
import ModifiedCartan.ScalarNormTwoPhase

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A uniform explicit accuracy threshold for every unit-centered positive
sector, obtained from the actual power-chart norm formula. -/
theorem ArbitraryRadiusLimitData.scalar_positive_sector_norm_lt
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : ‖a‖ = 1)
    (hb : (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic a) :
    ∀ z ∈ scalarPositiveChart a ρ ((Real.pi / 2 : ℝ) : ℂ),
      (d.U z).toReal < (Real.pi / 2) * (2 : ℝ) ^ ρ := by
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  rintro z ⟨w, hw, rfl⟩
  have he := d.scalar_norm_positiveChart_pullback hρ ha0 _ hb hw
  have hnorm : ‖w‖ < (2 : ℝ) ^ ρ := by
    simpa only [mem_ball, dist_zero_right, ha, div_one] using hw.1.2
  have hlt := (Complex.re_le_norm w).trans_lt hnorm
  change (d.U (powerChart a ρ w)).toReal = _ at he
  rw [he]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    using mul_lt_mul_of_pos_left hlt (half_pos Real.pi_pos)

/-- The smooth-point restriction is removed for the actual fixed-target
component. Its local two-phase structure and continuity are derived from
its actual polynomial logarithmic convergence. Auxiliary to LaTeX `thm:A` (b). -/
theorem scalar_target_component_le_neg_norm_on_positive_chart
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
    (d : ArbitraryRadiusLimitData f (fun ν => c ν * (2 : ℝ) ^ n ν) ρ)
    (hA : (Real.pi / 2) * (2 : ℝ) ^ ρ ≤ d.A)
    {u : ℂ → EReal} {v : ℂ → ℝ}
    (hus : IsSubharmonicOn (ball (0 : ℂ) 4) u)
    (hrep : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hlim : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog
        (characteristic f (c (d.subseq ν) * (2 : ℝ) ^ n (d.subseq ν)))
        (fun z => (polynomialMatrixGauge (d.polynomial ν)
          (scalarTargetUnitary q.target : Matrix (Index 1) (Index 1) ℂ) 0).eval z)) v) :
    ∀ z ∈ scalarPositiveChart a₀ ρ ((Real.pi / 2 : ℝ) : ℂ),
      (u z).toReal ≤ -(d.U z).toReal := by
  obtain ⟨ha₀norm, hroot⟩ := d.scalar_comparable_peak_limit
    f hlin htrans hsmall hρ hl hu hm ha hpeak hn hc halim
  have ha₀ : a₀ ≠ 0 := norm_ne_zero_iff.mp (by rw [ha₀norm]; norm_num)
  have hρpos := lt_of_lt_of_le zero_lt_one hρ
  let Ω := scalarPositiveChart a₀ ρ ((Real.pi / 2 : ℝ) : ℂ)
  have hΩ : IsOpen Ω := scalarPositiveChart_isOpen ha₀ hρpos _
  have hΩ4 : Ω ⊆ ball (0 : ℂ) 4 :=
    (scalarPositiveChart_subset ha₀ hρpos).trans (ball_subset_ball (by norm_num))
  have hΩG : Ω ⊆ powerChart a₀ ρ '' powerChartDomain a₀ ρ := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨w, powerChartInnerDomain_subset hρpos.le hw.1, rfl⟩
  have hreg := d.unitary_component_regular (ns := id) strictMono_id
    (fun _ => scalarTargetUnitary q.target) 0 hus hrep hlim
  have hphase := d.unitary_component_locallyTwoPhase_of_root hρ ha₀
    (by rw [ha₀norm]; norm_num : ‖a₀‖ < 4) (ns := id) strictMono_id
    (fun _ => scalarTargetUnitary q.target) 0 hus hrep hlim _ hroot
  have hlog := hlim.normalizedLog_real.congr_ae (fun _ => EventuallyEq.rfl)
    (show v =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (u z).toReal) by
      filter_upwards [hrep] with z hz
      rw [hz, EReal.toReal_coe])
  have hP (ν : ℕ) : polynomialMatrixGauge (d.polynomial ν)
      (scalarTargetUnitary q.target : Matrix (Index 1) (Index 1) ℂ) 0 ≠ 0 := by
    intro hzero
    obtain ⟨z, _, hz⟩ := hlim.normalizedLog_nontrivial isOpen_ball
      (nonempty_ball.mpr (by norm_num : (0 : ℝ) < 4)) (d.scale_pos ν)
    rw [hzero, Polynomial.eval_zero] at hz
    exact hz rfl
  apply hphase.le_of_smooth_physical_balls ha₀ hρ hΩ hΩG
    (hreg.2.continuousOn.mono hΩ4) ((d.norm_limit_continuous.2.mono hΩ4).neg)
  intro z δ hδ hδΩ hsm
  exact scalar_target_component_le_neg_norm_of_smooth f hlin htrans hsmall hρ hl hu
    hm ha hpeak hstep q hn hc hc₀ hclim halim d isOpen_ball (convex_ball z δ).isPreconnected
    (hδΩ.trans hΩ4) hsm hP (hlog.restrict (hδΩ.trans hΩ4)) (mem_ball_self hδ)
    (hδΩ (mem_ball_self hδ))
    ((d.scalar_positive_sector_norm_lt hρ ha₀norm hroot z (hδΩ (mem_ball_self hδ))).le.trans hA)

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_positive_sector_norm_lt
#print axioms ModifiedCartan.scalar_target_component_le_neg_norm_on_positive_chart
