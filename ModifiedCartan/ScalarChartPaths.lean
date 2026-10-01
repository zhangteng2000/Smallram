import ModifiedCartan.ScalarPositiveCenters
import ModifiedCartan.ScalarSectorComponent
import ModifiedCartan.ScalarGoodCross
import ModifiedCartan.ScalarCrossDiameter

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem compact_positive_lower_bound {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty)
    {u : ℂ → ℝ} (hu : ContinuousOn u K) (hpos : ∀ z ∈ K, 0 < u z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, 2 * δ ≤ u z := by
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne hu
  refine ⟨u a / 2, half_pos (hpos a ha), ?_⟩
  intro z hz
  have hh : u a ≤ u z := hmin hz
  linarith

/-- From the actual scalar curve hypotheses, construct a nonempty connected
positive chart and exponentially small physical crosses in every compact
rectangle of that chart. The positive lower bound is constructed by compactness.
Auxiliary to LaTeX `thm:A` (b). -/
theorem ArbitraryRadiusLimitData.scalar_exists_positive_chart_with_small_crosses
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) :
    ∃ (z₀ b₀ : ℂ) (ns : ℕ → ℕ),
      z₀ ∈ d.good_centers.centers ∧ b₀.re = (d.U z₀).toReal ∧ 0 < b₀.re ∧
      b₀ ^ 2 = -(d.coefficient 0 z₀ * (z₀ * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) ∧
      StrictMono ns ∧
      ∀ a b c e : ℝ, a < b → c < e →
        complexClosedRectangle a b c e ⊆ scalarPositiveChart z₀ ρ b₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ν in atTop, ∃ x ∈ Icc a b, ∃ y ∈ Icc c e,
          ∀ z ∈ complexRectangleCross a b c e x y,
          ∀ w ∈ complexRectangleCross a b c e x y,
            ‖scalarCurveSphere f ((r (d.subseq (ns ν)) : ℂ) * z) -
              scalarCurveSphere f ((r (d.subseq (ns ν)) : ℂ) * w)‖ ≤
                Real.exp (-(δ / 2) * characteristic f (r (d.subseq (ns ν)))) *
                  ((b - a) + (e - c)) := by
  obtain ⟨z₀, hz₀, hp⟩ := d.scalar_exists_positive_good_center hρ hr
  obtain ⟨ns, hns, V, j, b₀, hb, hbRe, hbpos, hP, hlog⟩ :=
    d.scalar_exists_component_on_positive_chart hρ hz₀ hp
  have hz0 : z₀ ≠ 0 := by simpa only [mem_singleton_iff] using (d.good_centers.subset hz₀).2
  have hρpos := lt_of_lt_of_le zero_lt_one hρ
  have hΩ2 : scalarPositiveChart z₀ ρ b₀ ⊆ ball (0 : ℂ) 2 := scalarPositiveChart_subset hz0 hρpos
  have hpos := d.scalar_norm_positiveChart_pos hρ hz0 b₀ hb
  refine ⟨z₀, b₀, ns, hz₀, hbRe, hbpos, hb, hns, ?_⟩
  intro a b c e hab hce hK
  have hK4 : complexClosedRectangle a b c e ⊆ ball (0 : ℂ) 4 :=
    hK.trans (hΩ2.trans (ball_subset_ball (by norm_num)))
  have hKne : (complexClosedRectangle a b c e).Nonempty :=
    ⟨(⟨a, c⟩ : ℂ), ⟨⟨le_rfl, hab.le⟩, ⟨le_rfl, hce.le⟩⟩⟩
  obtain ⟨δ, hδ, hUδ⟩ := compact_positive_lower_bound
    (complexClosedRectangle_isCompact a b c e) hKne (d.norm_limit_continuous.2.mono hK4)
    (fun z hz => hpos z (hK hz))
  have hcross := d.scalar_component_good_cross hlin htrans hsmall hρ hl hu hr hns V j
    (scalarPositiveChart_isOpen hz0 hρpos b₀) (scalarPositiveChart_isPreconnected z₀ hρpos b₀)
    hΩ2 hpos hP hlog hab hce hK hδ hUδ
  have hrpos := ((hr.comp d.strictMono.tendsto_atTop).comp hns.tendsto_atTop).eventually_ge_atTop 0
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hcross, hrpos] with ν hν hrν
  obtain ⟨x, hx, y, hy, hH, hV⟩ := hν
  refine ⟨x, hx, y, hy, ?_⟩
  intro z hz w hw
  exact scalar_curve_cross_diameter f hrν (Real.exp_pos _).le hx hy hH hV hz hw

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_positive_chart_with_small_crosses
