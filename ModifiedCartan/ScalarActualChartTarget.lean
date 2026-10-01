import ModifiedCartan.ScalarChartTarget

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual common line target on a positive chart, constructed from the
original curve assumptions and the actual limit data. Auxiliary to thm:A (b).
The conclusion concerns selected lines along one subsequence. -/
theorem ArbitraryRadiusLimitData.scalar_exists_chart_line_target
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop)
    {a : ℂ} (ha : a ∈ d.good_centers.centers) (hpos : 0 < (d.U a).toReal) :
    ∃ (ns : ℕ → ℕ) (b : ℂ) (β : WithTop ℂ), StrictMono ns ∧
      b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) ∧
      b.re = (d.U a).toReal ∧ 0 < b.re ∧
      ∃ q : ScalarHorizontalSelection f (fun ν => r (d.subseq (ns ν)))
        (fun ν => characteristic f (r (d.subseq (ns ν)))) (scalarPositiveChart a ρ b),
        ∀ R : {R : ComplexRect // R.closed ⊆ scalarPositiveChart a ρ b},
          ∀ ε > 0, ∀ᶠ ν in atTop, ∀ t ∈ Icc R.val.left R.val.right,
            ‖scalarCurveSphere f ((r (d.subseq (ns ν)) : ℂ) *
              (⟨t, q.height R ν⟩ : ℂ)) - scalarSphereValue β‖ < ε := by
  obtain ⟨ns₁, hns₁, V, j, b, hb, hbRe, hbpos, hP, hlog⟩ :=
    d.scalar_exists_component_on_positive_chart hρ ha hpos
  have ha0 : a ≠ 0 := by simpa only [mem_singleton_iff] using (d.good_centers.subset ha).2
  have ha2 : ‖a‖ < 2 := by simpa only [mem_ball, dist_zero_right] using (d.good_centers.subset ha).1
  have hρpos := lt_of_lt_of_le zero_lt_one hρ
  have hΩo := scalarPositiveChart_isOpen ha0 hρpos b
  have hΩc : IsConnected (scalarPositiveChart a ρ b) :=
    ⟨⟨a, self_mem_scalarPositiveChart ha0 ha2 hρpos hbpos⟩,
      scalarPositiveChart_isPreconnected a hρpos b⟩
  have hcross := d.scalar_component_small_rectangle_crosses hlin htrans hsmall hρ hl hu hr
    hns₁ V j hΩo hΩc.2 (scalarPositiveChart_subset ha0 hρpos)
    (d.scalar_norm_positiveChart_pos hρ ha0 b hb) hP hlog
  obtain ⟨q⟩ := hcross.exists_horizontal_selection
  have hr₁ := (hr.comp d.strictMono.tendsto_atTop).comp hns₁.tendsto_atTop
  have hs₁ := d.scale_tendsto.comp hns₁.tendsto_atTop
  obtain ⟨β, ns₂, hns₂, ht⟩ := q.exists_common_line_target hcross hr₁ hs₁ hΩo hΩc
  refine ⟨ns₁ ∘ ns₂, b, β, hns₁.comp hns₂, hb, hbRe, hbpos,
    q.reindex ns₂ hns₂.tendsto_atTop, ?_⟩
  exact ht

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_chart_line_target
