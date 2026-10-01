import ModifiedCartan.ScalarPhaseApproximation

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Approximation by the actual minimizing profiles transfers the physical
slow-change estimate to the selected profiles themselves. -/
theorem scalarPhaseCoefficient_profile_slow_change
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {r c : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) :
    LocalMeasureConvergence (ball (0 : ℂ) 1)
      (fun ν z => scalarQuadraticProfile m (scalarPhaseCoefficient f m (c ν * r ν)) z -
        scalarQuadraticProfile m (scalarPhaseCoefficient f m (r ν)) z) (fun _ => 0) := by
  have hs : Tendsto (fun ν => c ν * r ν) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hr
    filter_upwards [hr.eventually_ge_atTop 0] with ν hν
    nlinarith [(hc ν).1]
  have ha := (scalarPhaseCoefficient_profile_approximates f hlin htrans hsmall hρ hl hu hm hs).inMeasure
    (by norm_num)
  have hb := (scalarPhaseCoefficient_profile_approximates f hlin htrans hsmall hρ hl hu hm hr).inMeasure
    (by norm_num)
  have hslow := scalar_potential_comparable_difference_tendsto_zero f hlin htrans hsmall
    (lt_of_lt_of_le zero_lt_one hρ) hl hu hr hc
  have hsum := (ha.neg_zero.add hslow).add hb
  simp only [zero_add] at hsum
  apply hsum.congr_ae
  exact Eventually.of_forall (fun ν => Eventually.of_forall (fun z => by ring))

/-- The constructed angular coefficient changes slowly between every pair of
comparable radii. No branch of its argument or additional phase regularity is
assumed. Auxiliary to thm:A (b). -/
theorem scalarPhaseCoefficient_slow_change
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {r c : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) :
    Tendsto (fun ν => scalarPhaseCoefficient f m (c ν * r ν) - scalarPhaseCoefficient f m (r ν))
      atTop (𝓝 0) := by
  have hm0 : m ≠ 0 := by intro he; rw [he, Nat.cast_zero, zero_div] at hm; linarith
  have hslow := scalarPhaseCoefficient_profile_slow_change f hlin htrans hsmall hρ hl hu hm hr hc
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨D, hD, σ, hσ, hconv⟩ := scalarPhaseCircle_compact.tendsto_subseq
    (fun ν => mem_scalarPhaseCircle.mpr (scalarPhaseCoefficient_norm f m (r (ns ν))))
  have hDn := mem_scalarPhaseCircle.mp hD
  have hbase : Tendsto (fun ν => scalarPhaseCoefficient f m (r (ns (σ ν)))) atTop (𝓝 D) := by
    simpa only [Function.comp_def] using hconv
  have huni := scalarQuadraticProfile_uniform_of_tendsto m
    (fun ν => scalarPhaseCoefficient_norm f m (r (ns (σ ν)))) hDn hbase
    (isCompact_closedBall (0 : ℂ) 1)
  have hprofile := uniformlyOn_localMeasureConvergence huni ball_subset_closedBall
  have hsum := ((hslow.comp hns).comp hσ.tendsto_atTop).add hprofile
  have hscaled : LocalMeasureConvergence (ball (0 : ℂ) 1)
      (fun ν => scalarQuadraticProfile m (scalarPhaseCoefficient f m (c (ns (σ ν)) * r (ns (σ ν)))))
      (scalarQuadraticProfile m D) := by
    simpa only [sub_add_cancel, zero_add] using hsum
  have hscaledC := scalarQuadraticProfile_parameter_tendsto hm0
    (fun ν => scalarPhaseCoefficient_norm f m (c (ns (σ ν)) * r (ns (σ ν)))) hDn hscaled
  refine ⟨σ, ?_⟩
  simpa only [sub_self] using hscaledC.sub hbase

/-- The minimizing coefficient converges to the exact coefficient of every
actual arbitrary-radius limit. This connects the global choice with the
already constructed sector and polynomial data. -/
theorem ArbitraryRadiusLimitData.scalarPhaseCoefficient_tendsto
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {m : ℕ} (hm : ρ = (m : ℝ) / 2)
    {C : ℂ} (hC : ‖C‖ = (Real.pi / 2) ^ 2)
    (hprofile : EqOn (fun z => 2 * (d.U z).toReal) (scalarQuadraticProfile m C) (ball (0 : ℂ) 2)) :
    Tendsto (fun ν => scalarPhaseCoefficient f m (r (d.subseq ν))) atTop (𝓝 C) := by
  have hm0 : m ≠ 0 := by intro he; rw [he, Nat.cast_zero, zero_div] at hm; linarith
  have hbase := ((d.scalar_spherical_potential_localL1 hlin htrans hsmall
    (lt_of_lt_of_le zero_lt_one hρ) hl hu hr).inMeasure (by norm_num)).mono
    (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 4))
  have herr := (scalarPhaseCoefficient_profile_approximates f hlin htrans hsmall hρ hl hu hm
    (hr.comp d.strictMono.tendsto_atTop)).inMeasure (by norm_num)
  have hsum := herr.neg_zero.add hbase
  simp only [zero_add, Function.comp_def] at hsum
  have hP : LocalMeasureConvergence (ball (0 : ℂ) 1)
      (fun ν => scalarQuadraticProfile m (scalarPhaseCoefficient f m (r (d.subseq ν))))
      (fun z => 2 * (d.U z).toReal) := by
    apply hsum.congr_ae
    exact Eventually.of_forall (fun ν => Eventually.of_forall (fun z => by ring))
  apply scalarQuadraticProfile_parameter_tendsto hm0
    (fun ν => scalarPhaseCoefficient_norm f m (r (d.subseq ν))) hC
  apply hP.congr_limit_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact hprofile (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz)

end ModifiedCartan
#print axioms ModifiedCartan.scalarPhaseCoefficient_profile_slow_change
#print axioms ModifiedCartan.scalarPhaseCoefficient_slow_change
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalarPhaseCoefficient_tendsto
