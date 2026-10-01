import ModifiedCartan.ComplexRect
import ModifiedCartan.ScalarChartPaths

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Literal exponential speed bounds on constructed crosses for every compact
rectangle in the domain. Existence for actual component limits is proved below. -/
def HasSmallRectangleCrosses (f : Curve 1) (r s : ℕ → ℝ) (Ω : Set ℂ) : Prop :=
  ∀ R : ComplexRect, R.closed ⊆ Ω → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ν in atTop,
    ∃ x ∈ Icc R.left R.right, ∃ y ∈ Icc R.bottom R.top,
      (∀ t ∈ Icc R.left R.right,
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, y⟩ : ℂ)) ≤ Real.exp (-δ * s ν)) ∧
      (∀ t ∈ Icc R.bottom R.top,
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨x, t⟩ : ℂ)) ≤ Real.exp (-δ * s ν))

theorem ArbitraryRadiusLimitData.scalar_component_small_rectangle_crosses
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop)
    {ns : ℕ → ℕ} (hns : StrictMono ns)
    (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ) (j : Index 1)
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (hΩ : Ω ⊆ ball (0 : ℂ) 2) (hpos : ∀ z ∈ Ω, 0 < (d.U z).toReal)
    (hP : ∀ ν, polynomialMatrixGauge (d.polynomial (ns ν))
      (V ν : Matrix (Index 1) (Index 1) ℂ) j ≠ 0)
    (hlog : LocalLpConvergence 1 Ω
      (fun ν z => (characteristic f (r (d.subseq (ns ν))))⁻¹ *
        Real.log ‖(polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z‖)
      (fun z => (d.U z).toReal)) :
    HasSmallRectangleCrosses f (fun ν => r (d.subseq (ns ν)))
      (fun ν => characteristic f (r (d.subseq (ns ν)))) Ω := by
  intro R hR
  have hR4 : R.closed ⊆ ball (0 : ℂ) 4 :=
    hR.trans (hΩ.trans (ball_subset_ball (by norm_num)))
  obtain ⟨δ, hδ, hUδ⟩ := compact_positive_lower_bound R.isCompact_closed
    (R.openSet_nonempty.mono R.openSet_subset_closed) (d.norm_limit_continuous.2.mono hR4)
    (fun z hz => hpos z (hR hz))
  exact ⟨δ / 2, half_pos hδ,
    d.scalar_component_good_cross hlin htrans hsmall hρ hl hu hr hns V j hΩopen hΩconn
      hΩ hpos hP hlog R.horizontal_pos R.vertical_pos hR hδ hUδ⟩

/-- The cross property used in later geometric gluing has an actual positive
chart witness under the original curve hypotheses. Auxiliary to `thm:A` (b). -/
theorem ArbitraryRadiusLimitData.scalar_exists_small_rectangle_crosses
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) :
    ∃ (ns : ℕ → ℕ) (Ω : Set ℂ), StrictMono ns ∧ IsOpen Ω ∧ IsConnected Ω ∧
      Ω ⊆ ball (0 : ℂ) 2 ∧
      HasSmallRectangleCrosses f (fun ν => r (d.subseq (ns ν)))
        (fun ν => characteristic f (r (d.subseq (ns ν)))) Ω := by
  obtain ⟨a, ha, hp⟩ := d.scalar_exists_positive_good_center hρ hr
  obtain ⟨ns, hns, V, j, b, hb, _, hbpos, hP, hlog⟩ :=
    d.scalar_exists_component_on_positive_chart hρ ha hp
  have ha0 : a ≠ 0 := by simpa only [mem_singleton_iff] using (d.good_centers.subset ha).2
  have ha2 : ‖a‖ < 2 := by simpa only [mem_ball, dist_zero_right] using (d.good_centers.subset ha).1
  have hρpos := lt_of_lt_of_le zero_lt_one hρ
  have hΩo := scalarPositiveChart_isOpen ha0 hρpos b
  have hΩc := scalarPositiveChart_isPreconnected a hρpos b
  have hΩ2 : scalarPositiveChart a ρ b ⊆ ball (0 : ℂ) 2 := scalarPositiveChart_subset ha0 hρpos
  exact ⟨ns, scalarPositiveChart a ρ b, hns, hΩo,
    ⟨⟨a, self_mem_scalarPositiveChart ha0 ha2 hρpos hbpos⟩, hΩc⟩, hΩ2,
    d.scalar_component_small_rectangle_crosses hlin htrans hsmall hρ hl hu hr hns V j hΩo hΩc
      hΩ2 (d.scalar_norm_positiveChart_pos hρ ha0 b hb) hP hlog⟩

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_component_small_rectangle_crosses
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_small_rectangle_crosses
