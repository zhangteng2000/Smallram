import ModifiedCartan.ScalarHorizontalSelection

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The three-segment bridge retains an exponential bound, not merely
convergence to zero. Auxiliary to LaTeX thm:A (b). -/
theorem HasSmallRectangleCrosses.adjacent_horizontal_anchors_exponential
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}
    (h : HasSmallRectangleCrosses f r s Ω)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    {R S : ComplexRect} (hR : R.closed ⊆ Ω) (hS : S.closed ⊆ Ω) (hRS : R.Overlaps S)
    {δR δS : ℝ} (hδR : 0 < δR) (hδS : 0 < δS) {yR yS : ℕ → ℝ}
    (hH₁ : ∀ᶠ ν in atTop, yR ν ∈ Icc R.bottom R.top ∧
      ∀ t ∈ Icc R.left R.right,
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yR ν⟩ : ℂ)) ≤ Real.exp (-δR * s ν))
    (hH₂ : ∀ᶠ ν in atTop, yS ν ∈ Icc S.bottom S.top ∧
      ∀ t ∈ Icc S.left S.right,
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yS ν⟩ : ℂ)) ≤ Real.exp (-δS * s ν)) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f ((r ν : ℂ) * (⟨R.left, yR ν⟩ : ℂ)) -
        scalarCurveSphere f ((r ν : ℂ) * (⟨S.left, yS ν⟩ : ℂ))‖ ≤ C * Real.exp (-δ * s ν) := by
  let B := R.verticalBridge S hRS
  have hBΩ : B.closed ⊆ Ω := (ComplexRect.verticalBridge_closed_subset hRS).trans (union_subset hR hS)
  obtain ⟨δB, hδB, hB⟩ := h B hBΩ
  let δ := min δR (min δS δB)
  let L : ℝ := (R.right - R.left) + (max R.top S.top - min R.bottom S.bottom) +
    (S.right - S.left)
  have hδ : 0 < δ := lt_min hδR (lt_min hδS hδB)
  have hL : 0 ≤ L := by
    have hm : min R.bottom S.bottom < max R.top S.top :=
      (min_le_left _ _).trans_lt (R.vertical_pos.trans_le (le_max_left _ _))
    dsimp only [L]
    linarith [R.horizontal_pos, S.horizontal_pos]
  refine ⟨δ, hδ, L, hL, ?_⟩
  filter_upwards [hH₁, hH₂, hB, hr.eventually_ge_atTop 0, hs.eventually_ge_atTop 0]
    with ν h₁ h₂ hBν hrν hsν
  obtain ⟨x, hx, y, hy, _, hV⟩ := hBν
  have hxR : x ∈ Icc R.left R.right :=
    ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩
  have hxS : x ∈ Icc S.left S.right :=
    ⟨(le_max_right _ _).trans hx.1, hx.2.trans (min_le_right _ _)⟩
  have hmono {η : ℝ} (hη : δ ≤ η) : Real.exp (-η * s ν) ≤ Real.exp (-δ * s ν) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hη) hsν)
  have hRC := hmono (show δ ≤ δR from min_le_left _ _)
  have hSC := hmono (show δ ≤ δS from (min_le_right _ _).trans (min_le_left _ _))
  have hBC := hmono (show δ ≤ δB from (min_le_right _ _).trans (min_le_right _ _))
  have hh := scalar_curve_rectangle_bridge_diameter f hrν (Real.exp_pos (-δ * s ν)).le
    hxR hxS h₁.1 h₂.1 (fun t ht => (h₁.2 t ht).trans hRC)
    (fun t ht => (h₂.2 t ht).trans hSC) (fun t ht => (hV t ht).trans hBC)
    (show R.left ∈ Icc R.left R.right from ⟨le_rfl, R.horizontal_pos.le⟩)
    (show S.left ∈ Icc S.left S.right from ⟨le_rfl, S.horizontal_pos.le⟩)
  simpa only [mul_comm] using hh

/-- Finite rectangle chains preserve a positive exponential rate.
The constants depend on the two rectangles and the finite connecting chain. -/
theorem ScalarHorizontalSelection.anchors_exponentially_close
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}
    (q : ScalarHorizontalSelection f r s Ω)
    (h : HasSmallRectangleCrosses f r s Ω)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (R S : {R : ComplexRect // R.closed ⊆ Ω}) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ‖q.anchor R ν - q.anchor S ν‖ ≤ C * Real.exp (-δ * s ν) := by
  have hgen : ∀ {A B : ComplexRect}, Relation.ReflTransGen (ComplexRect.AdjacentIn Ω) A B →
      ∀ (hA : A.closed ⊆ Ω) (hB : B.closed ⊆ Ω),
        ∃ δ > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop,
          ‖q.anchor ⟨A, hA⟩ ν - q.anchor ⟨B, hB⟩ ν‖ ≤ C * Real.exp (-δ * s ν) := by
    intro A B hAB
    induction hAB with
    | refl =>
      intro hA hB
      exact ⟨1, zero_lt_one, 0, le_rfl,
        Eventually.of_forall (fun ν => by simp only [sub_self, norm_zero, zero_mul, le_refl])⟩
    | @tail B D hAB hBD ih =>
      intro hA hD
      obtain ⟨δ₁, hδ₁, C₁, hC₁, h₁⟩ := ih hA hBD.1
      obtain ⟨δ₂, hδ₂, C₂, hC₂, h₂⟩ :=
        h.adjacent_horizontal_anchors_exponential hr hs hBD.1 hD hBD.2.2
          (q.rate_pos ⟨B, hBD.1⟩) (q.rate_pos ⟨D, hD⟩)
          (q.good ⟨B, hBD.1⟩) (q.good ⟨D, hD⟩)
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
      filter_upwards [h₁, h₂, hs.eventually_ge_atTop 0] with ν h₁ν h₂ν hsν
      have e₁ : Real.exp (-δ₁ * s ν) ≤ Real.exp (-min δ₁ δ₂ * s ν) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hsν)
      have e₂ : Real.exp (-δ₂ * s ν) ≤ Real.exp (-min δ₁ δ₂ * s ν) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) hsν)
      have hb₁ := h₁ν.trans (mul_le_mul_of_nonneg_left e₁ hC₁)
      have hb₂ := h₂ν.trans (mul_le_mul_of_nonneg_left e₂ hC₂)
      calc
        _ ≤ ‖q.anchor ⟨A, hA⟩ ν - q.anchor ⟨B, hBD.1⟩ ν‖ +
            ‖q.anchor ⟨B, hBD.1⟩ ν - q.anchor ⟨D, hD⟩ ν‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C₁ * Real.exp (-min δ₁ δ₂ * s ν) + C₂ * Real.exp (-min δ₁ δ₂ * s ν) :=
          add_le_add hb₁ hb₂
        _ = _ := by ring
  exact hgen (ComplexRect.reachable_in_open_connected hΩ hc R.property S.property) R.property S.property

end ModifiedCartan
#print axioms ModifiedCartan.HasSmallRectangleCrosses.adjacent_horizontal_anchors_exponential
#print axioms ModifiedCartan.ScalarHorizontalSelection.anchors_exponentially_close
