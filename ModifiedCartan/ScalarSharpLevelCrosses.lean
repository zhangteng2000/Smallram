import ModifiedCartan.ScalarLevelChart
import ModifiedCartan.ScalarFixedRateCrosses
import ModifiedCartan.ScalarSharpCrosses
import ModifiedCartan.ScalarChartDominance

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A strict pointwise margin gives the specified rate on every compact
rectangle. Its positive compact margin is proved, rather than assumed. -/
theorem ArbitraryRadiusLimitData.scalar_component_crosses_at_rate
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop)
    {ns : ℕ → ℕ} (hns : StrictMono ns)
    (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ) (j : Index 1)
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (hΩ : Ω ⊆ ball (0 : ℂ) 2)
    (hP : ∀ ν, polynomialMatrixGauge (d.polynomial (ns ν))
      (V ν : Matrix (Index 1) (Index 1) ℂ) j ≠ 0)
    (hlog : LocalLpConvergence 1 Ω
      (fun ν z => (characteristic f (r (d.subseq (ns ν))))⁻¹ *
        Real.log ‖(polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z‖)
      (fun z => (d.U z).toReal))
    {κ : ℝ} (hκ : 0 < κ) (hκU : ∀ z ∈ Ω, κ < 2 * (d.U z).toReal) :
    HasRectangleCrossesAtRate f (fun ν => r (d.subseq (ns ν)))
      (fun ν => characteristic f (r (d.subseq (ns ν)))) Ω κ := by
  intro R hR
  have hR4 : R.closed ⊆ ball (0 : ℂ) 4 :=
    hR.trans (hΩ.trans (ball_subset_ball (by norm_num)))
  have hcont : ContinuousOn (fun z => 2 * (d.U z).toReal - κ) R.closed :=
    (continuousOn_const.mul (d.norm_limit_continuous.2.mono hR4)).sub continuousOn_const
  obtain ⟨ε, hε, hmargin⟩ := compact_positive_lower_bound R.isCompact_closed
    (R.openSet_nonempty.mono R.openSet_subset_closed) hcont
    (fun z hz => sub_pos.mpr (hκU z (hR hz)))
  apply d.scalar_component_good_cross_sharp hlin htrans hsmall hρ hl hu hr hns V j
    hΩopen hΩconn hΩ (fun z hz => by linarith [hκU z hz]) hP hlog
    R.horizontal_pos R.vertical_pos hR hκ (ℓ := κ / 2 + ε)
  · linarith
  · intro z hz
    have hh := hmargin z hz
    linarith

/-- One constructed component subsequence supplies every strict positive
level region and every corresponding sharp rate. The value 2 is retained. -/
theorem ArbitraryRadiusLimitData.scalar_exists_sharp_level_crosses
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop)
    {a : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2) (b : ℂ)
    (hb : b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2))
    (hbpos : 0 < b.re) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ κ > 0,
      HasRectangleCrossesAtRate f (fun ν => r (d.subseq (ns ν)))
        (fun ν => characteristic f (r (d.subseq (ns ν)))) (scalarLevelChart a ρ b (κ / 2)) κ := by
  obtain ⟨ns, hns, V, j, hP, hlog⟩ := d.scalar_exists_component_on_chart hρ ha ha2 b hb hbpos
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  refine ⟨ns, hns, fun κ hκ => ?_⟩
  have hsub := scalarLevelChart_subset_positive (a := a) (b := b) (ρ := ρ) (half_pos hκ).le
  apply d.scalar_component_crosses_at_rate hlin htrans hsmall hρ hl hu hr hns V j
    (scalarLevelChart_isOpen ha hρpos b (κ / 2))
    (scalarLevelChart_isPreconnected a hρpos b (κ / 2))
    (hsub.trans (scalarPositiveChart_subset ha hρpos)) hP (hlog.restrict hsub) hκ
  intro z hz
  have hh := d.scalarLevelChart_lower hρ ha b hb (half_pos hκ).le z hz
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_component_crosses_at_rate
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_sharp_level_crosses
