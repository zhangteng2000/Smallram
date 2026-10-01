import ModifiedCartan.ScalarFixedRateCrosses

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- An adjacent-rectangle bridge preserves the specified rate exactly. -/
theorem HasRectangleCrossesAtRate.adjacent_horizontal_anchors
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ} {κ : ℝ}
    (h : HasRectangleCrossesAtRate f r s Ω κ) (hr : Tendsto r atTop atTop)
    {R S : ComplexRect} (hR : R.closed ⊆ Ω) (hS : S.closed ⊆ Ω) (hRS : R.Overlaps S)
    {yR yS : ℕ → ℝ}
    (hH₁ : ∀ᶠ ν in atTop, yR ν ∈ Icc R.bottom R.top ∧
      ∀ t ∈ Icc R.left R.right,
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yR ν⟩ : ℂ)) ≤ Real.exp (-κ * s ν))
    (hH₂ : ∀ᶠ ν in atTop, yS ν ∈ Icc S.bottom S.top ∧
      ∀ t ∈ Icc S.left S.right,
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yS ν⟩ : ℂ)) ≤ Real.exp (-κ * s ν)) :
    ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f ((r ν : ℂ) * (⟨R.left, yR ν⟩ : ℂ)) -
        scalarCurveSphere f ((r ν : ℂ) * (⟨S.left, yS ν⟩ : ℂ))‖ ≤ C * Real.exp (-κ * s ν) := by
  let B := R.verticalBridge S hRS
  have hBΩ : B.closed ⊆ Ω := (ComplexRect.verticalBridge_closed_subset hRS).trans (union_subset hR hS)
  let L : ℝ := (R.right - R.left) + (max R.top S.top - min R.bottom S.bottom) +
    (S.right - S.left)
  have hL : 0 ≤ L := by
    have hm : min R.bottom S.bottom < max R.top S.top :=
      (min_le_left _ _).trans_lt (R.vertical_pos.trans_le (le_max_left _ _))
    dsimp only [L]
    linarith [R.horizontal_pos, S.horizontal_pos]
  refine ⟨L, hL, ?_⟩
  filter_upwards [hH₁, hH₂, h B hBΩ, hr.eventually_ge_atTop 0] with ν h₁ h₂ hBν hrν
  obtain ⟨x, hx, y, hy, _, hV⟩ := hBν
  have hxR : x ∈ Icc R.left R.right :=
    ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩
  have hxS : x ∈ Icc S.left S.right :=
    ⟨(le_max_right _ _).trans hx.1, hx.2.trans (min_le_right _ _)⟩
  have hh := scalar_curve_rectangle_bridge_diameter f hrν (Real.exp_pos (-κ * s ν)).le
    hxR hxS h₁.1 h₂.1 h₁.2 h₂.2 hV
    (show R.left ∈ Icc R.left R.right from ⟨le_rfl, R.horizontal_pos.le⟩)
    (show S.left ∈ Icc S.left S.right from ⟨le_rfl, S.horizontal_pos.le⟩)
  simpa only [mul_comm] using hh

/-- Any finite chain in a connected open region retains the same rate;
only the multiplicative path-length constant changes. -/
theorem ScalarHorizontalSelection.anchors_close_at_rate
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ} {κ : ℝ}
    (q : ScalarHorizontalSelection f r s Ω) (hq : ∀ R, q.rate R = κ)
    (h : HasRectangleCrossesAtRate f r s Ω κ) (hr : Tendsto r atTop atTop)
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (R S : {R : ComplexRect // R.closed ⊆ Ω}) :
    ∃ C ≥ 0, ∀ᶠ ν in atTop, ‖q.anchor R ν - q.anchor S ν‖ ≤ C * Real.exp (-κ * s ν) := by
  have hgood (A : {R : ComplexRect // R.closed ⊆ Ω}) : ∀ᶠ ν in atTop,
      q.height A ν ∈ Icc A.val.bottom A.val.top ∧ ∀ t ∈ Icc A.val.left A.val.right,
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, q.height A ν⟩ : ℂ)) ≤
          Real.exp (-κ * s ν) := by simpa only [hq] using q.good A
  have hgen : ∀ {A B : ComplexRect}, Relation.ReflTransGen (ComplexRect.AdjacentIn Ω) A B →
      ∀ (hA : A.closed ⊆ Ω) (hB : B.closed ⊆ Ω),
        ∃ C ≥ 0, ∀ᶠ ν in atTop,
          ‖q.anchor ⟨A, hA⟩ ν - q.anchor ⟨B, hB⟩ ν‖ ≤ C * Real.exp (-κ * s ν) := by
    intro A B hAB
    induction hAB with
    | refl =>
      intro hA hB
      exact ⟨0, le_rfl, Eventually.of_forall (fun ν => by simp only [sub_self, norm_zero, zero_mul, le_refl])⟩
    | @tail B D hAB hBD ih =>
      intro hA hD
      obtain ⟨C₁, hC₁, h₁⟩ := ih hA hBD.1
      obtain ⟨C₂, hC₂, h₂⟩ := h.adjacent_horizontal_anchors hr hBD.1 hD hBD.2.2
        (hgood ⟨B, hBD.1⟩) (hgood ⟨D, hD⟩)
      refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
      filter_upwards [h₁, h₂] with ν h₁ν h₂ν
      calc
        _ ≤ ‖q.anchor ⟨A, hA⟩ ν - q.anchor ⟨B, hBD.1⟩ ν‖ +
            ‖q.anchor ⟨B, hBD.1⟩ ν - q.anchor ⟨D, hD⟩ ν‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C₁ * Real.exp (-κ * s ν) + C₂ * Real.exp (-κ * s ν) := add_le_add h₁ν h₂ν
        _ = _ := by ring
  exact hgen (ComplexRect.reachable_in_open_connected hΩ hc R.property S.property) R.property S.property

end ModifiedCartan
#print axioms ModifiedCartan.HasRectangleCrossesAtRate.adjacent_horizontal_anchors
#print axioms ModifiedCartan.ScalarHorizontalSelection.anchors_close_at_rate
