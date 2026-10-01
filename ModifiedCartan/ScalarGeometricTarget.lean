import ModifiedCartan.ScalarChartDominance
import ModifiedCartan.ScalarChartTarget
import ModifiedCartan.ScalarPeakChart

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual line targets are available for geometrically chosen charts, with
no good-center premise on their centers. Auxiliary to thm:A (b). -/
theorem ArbitraryRadiusLimitData.scalar_exists_chart_target_of_root
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {a : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2) (b : ℂ)
    (hb : b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2))
    (hbpos : 0 < b.re) :
    ∃ (ns : ℕ → ℕ) (β : WithTop ℂ), StrictMono ns ∧
      ∃ q : ScalarHorizontalSelection f (fun ν => r (d.subseq (ns ν)))
        (fun ν => characteristic f (r (d.subseq (ns ν)))) (scalarPositiveChart a ρ b),
        ∀ R : {R : ComplexRect // R.closed ⊆ scalarPositiveChart a ρ b},
          ∀ ε > 0, ∀ᶠ ν in atTop, ∀ t ∈ Icc R.val.left R.val.right,
            ‖scalarCurveSphere f ((r (d.subseq (ns ν)) : ℂ) *
              (⟨t, q.height R ν⟩ : ℂ)) - scalarSphereValue β‖ < ε := by
  obtain ⟨ns₁, hns₁, V, j, hP, hlog⟩ := d.scalar_exists_component_on_chart hρ ha ha2 b hb hbpos
  have hρpos := lt_of_lt_of_le zero_lt_one hρ
  have hΩo := scalarPositiveChart_isOpen ha hρpos b
  have hΩc : IsConnected (scalarPositiveChart a ρ b) :=
    ⟨⟨a, self_mem_scalarPositiveChart ha ha2 hρpos hbpos⟩,
      scalarPositiveChart_isPreconnected a hρpos b⟩
  have hcross := d.scalar_component_small_rectangle_crosses hlin htrans hsmall hρ hl hu hr
    hns₁ V j hΩo hΩc.2 (scalarPositiveChart_subset ha hρpos)
    (d.scalar_norm_positiveChart_pos hρ ha b hb) hP hlog
  obtain ⟨q⟩ := hcross.exists_horizontal_selection
  have hr₁ := (hr.comp d.strictMono.tendsto_atTop).comp hns₁.tendsto_atTop
  have hs₁ := d.scale_tendsto.comp hns₁.tendsto_atTop
  obtain ⟨β, ns₂, hns₂, ht⟩ := q.exists_common_line_target hcross hr₁ hs₁ hΩo hΩc
  exact ⟨ns₁ ∘ ns₂, β, hns₁.comp hns₂, q.reindex ns₂ hns₂.tendsto_atTop, ht⟩

/-- A full inner right-half power chart with positive real phase, and an
actual common line target on it, are constructed from the original hypotheses. -/
theorem ArbitraryRadiusLimitData.scalar_exists_peak_chart_target
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) :
    ∃ (a : ℂ) (ns : ℕ → ℕ) (β : WithTop ℂ), ‖a‖ = 1 ∧ StrictMono ns ∧
      ∃ q : ScalarHorizontalSelection f (fun ν => r (d.subseq (ns ν)))
        (fun ν => characteristic f (r (d.subseq (ns ν))))
        (powerChart a ρ '' powerChartInnerDomain a ρ),
        ∀ R : {R : ComplexRect // R.closed ⊆ powerChart a ρ '' powerChartInnerDomain a ρ},
          ∀ ε > 0, ∀ᶠ ν in atTop, ∀ t ∈ Icc R.val.left R.val.right,
            ‖scalarCurveSphere f ((r (d.subseq (ns ν)) : ℂ) *
              (⟨t, q.height R ν⟩ : ℂ)) - scalarSphereValue β‖ < ε := by
  obtain ⟨a, ha1, _, hb⟩ := d.scalar_exists_unit_peak_root hρ hr
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha1]; norm_num)
  have ha2 : ‖a‖ < 2 := by rw [ha1]; norm_num
  have hbpos : 0 < (((Real.pi / 2 : ℝ) : ℂ)).re := half_pos Real.pi_pos
  have he : scalarPositiveChart a ρ (((Real.pi / 2 : ℝ) : ℂ)) =
      powerChart a ρ '' powerChartInnerDomain a ρ := by
    unfold scalarPositiveChart
    rw [positivePowerChartDomain_real (half_pos Real.pi_pos)]
  have hh := d.scalar_exists_chart_target_of_root hlin htrans hsmall hρ hl hu hr
    ha0 ha2 (((Real.pi / 2 : ℝ) : ℂ)) hb hbpos
  rw [he] at hh
  obtain ⟨ns, β, hns, q, ht⟩ := hh
  exact ⟨a, ns, β, ha1, hns, q, ht⟩

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_chart_target_of_root
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_peak_chart_target
