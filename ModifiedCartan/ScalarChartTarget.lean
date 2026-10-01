import ModifiedCartan.ScalarHorizontalSelection

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem HasSmallRectangleCrosses.comp {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}
    (h : HasSmallRectangleCrosses f r s Ω) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) :
    HasSmallRectangleCrosses f (r ∘ ns) (s ∘ ns) Ω := by
  intro R hR
  obtain ⟨δ, hδ, hg⟩ := h R hR
  exact ⟨δ, hδ, hns.eventually hg⟩

namespace ScalarHorizontalSelection
variable {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}

noncomputable def reindex (q : ScalarHorizontalSelection f r s Ω) (ns : ℕ → ℕ)
    (hns : Tendsto ns atTop atTop) : ScalarHorizontalSelection f (r ∘ ns) (s ∘ ns) Ω where
  rate := q.rate
  rate_pos := q.rate_pos
  height := fun R => q.height R ∘ ns
  good := fun R => hns.eventually (q.good R)

/-- Compactness at one anchor, combined with the finite rectangle chains,
gives one subsequence and target for all contained rectangles. -/
theorem exists_common_subsequence_target (q : ScalarHorizontalSelection f r s Ω)
    (h : HasSmallRectangleCrosses f r s Ω)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (hΩ : IsOpen Ω) (hc : IsConnected Ω) :
    ∃ (b : WithTop ℂ) (ns : ℕ → ℕ), StrictMono ns ∧
      ∀ R : {R : ComplexRect // R.closed ⊆ Ω},
        Tendsto (fun ν => q.anchor R (ns ν)) atTop (𝓝 (scalarSphereValue b)) := by
  obtain ⟨z, hz⟩ := hc.1
  obtain ⟨a, b, c, d, hab, hcd, _, hRΩ⟩ := exists_closed_rectangle_neighborhood hΩ hz
  let R₀ : {R : ComplexRect // R.closed ⊆ Ω} := ⟨⟨a, b, c, d, hab, hcd⟩, hRΩ⟩
  obtain ⟨v, hv, ns, hns, ht⟩ := scalarSphereImage_isCompact.tendsto_subseq (q.anchor_mem R₀)
  rw [scalarSphereImage_eq_range] at hv
  obtain ⟨β, rfl⟩ := hv
  refine ⟨β, ns, hns, ?_⟩
  intro R
  have hdiff := (q.anchors_tendsto_together h hr hs hΩ hc.2 R R₀).comp hns.tendsto_atTop
  have hvdiff : Tendsto (fun ν => q.anchor R (ns ν) - q.anchor R₀ (ns ν))
      atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hdiff
  have hh := hvdiff.add ht
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hh

/-- Uniform convergence on the selected horizontal line follows from its
anchor limit and the already proved physical diameter estimate. -/
theorem horizontal_line_limit (q : ScalarHorizontalSelection f r s Ω)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (R : {R : ComplexRect // R.closed ⊆ Ω}) {b : WithTop ℂ}
    (hb : Tendsto (q.anchor R) atTop (𝓝 (scalarSphereValue b))) :
    ∀ ε > 0, ∀ᶠ ν in atTop, ∀ t ∈ Icc R.val.left R.val.right,
      ‖scalarCurveSphere f ((r ν : ℂ) * (⟨t, q.height R ν⟩ : ℂ)) - scalarSphereValue b‖ < ε := by
  intro ε hε
  have hd : Tendsto (fun ν => Real.exp (-q.rate R * s ν) * (R.val.right - R.val.left))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using (exp_neg_mul_tendsto_zero hs (q.rate_pos R)).mul_const
      (R.val.right - R.val.left)
  have ha := tendsto_iff_norm_sub_tendsto_zero.mp hb
  have hsum := hd.add ha
  rw [zero_add] at hsum
  have hsmall := hsum.eventually_lt_const hε
  filter_upwards [hsmall, q.good R, hr.eventually_ge_atTop 0] with ν hν hgood hrν
  intro t ht
  have hh : ‖scalarCurveSphere f ((r ν : ℂ) * (⟨t, q.height R ν⟩ : ℂ)) - q.anchor R ν‖ ≤
      Real.exp (-q.rate R * s ν) * (R.val.right - R.val.left) :=
    scalar_curve_horizontal_diameter f hrν (Real.exp_pos _).le hgood.2
      ht ⟨le_rfl, R.val.horizontal_pos.le⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ (q.anchor R ν) _).trans_lt
    ((add_le_add hh le_rfl).trans_lt hν)

/-- A single actual target is the uniform limit on every chosen horizontal
line after one common subsequence. This does not assert full asymptotic values. -/
theorem exists_common_line_target (q : ScalarHorizontalSelection f r s Ω)
    (h : HasSmallRectangleCrosses f r s Ω)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (hΩ : IsOpen Ω) (hc : IsConnected Ω) :
    ∃ (b : WithTop ℂ) (ns : ℕ → ℕ), StrictMono ns ∧
      ∀ R : {R : ComplexRect // R.closed ⊆ Ω}, ∀ ε > 0, ∀ᶠ ν in atTop,
        ∀ t ∈ Icc R.val.left R.val.right,
          ‖scalarCurveSphere f ((r (ns ν) : ℂ) * (⟨t, q.height R (ns ν)⟩ : ℂ)) -
            scalarSphereValue b‖ < ε := by
  obtain ⟨b, ns, hns, ht⟩ := q.exists_common_subsequence_target h hr hs hΩ hc
  refine ⟨b, ns, hns, ?_⟩
  intro R
  exact (q.reindex ns hns.tendsto_atTop).horizontal_line_limit
    (hr.comp hns.tendsto_atTop) (hs.comp hns.tendsto_atTop) R (ht R)

end ScalarHorizontalSelection
end ModifiedCartan
#print axioms ModifiedCartan.ScalarHorizontalSelection.exists_common_subsequence_target
#print axioms ModifiedCartan.ScalarHorizontalSelection.horizontal_line_limit
#print axioms ModifiedCartan.ScalarHorizontalSelection.exists_common_line_target
