import ModifiedCartan.ScalarAdjacentAnchors
import ModifiedCartan.ScalarSphereValues

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Simultaneous selections of the actual good horizontal lines. -/
structure ScalarHorizontalSelection (f : Curve 1) (r s : ℕ → ℝ) (Ω : Set ℂ) where
  rate : {R : ComplexRect // R.closed ⊆ Ω} → ℝ
  rate_pos : ∀ R, 0 < rate R
  height : {R : ComplexRect // R.closed ⊆ Ω} → ℕ → ℝ
  good : ∀ R, ∀ᶠ ν in atTop, height R ν ∈ Icc R.val.bottom R.val.top ∧
    ∀ t ∈ Icc R.val.left R.val.right,
      r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, height R ν⟩ : ℂ)) ≤
        Real.exp (-rate R * s ν)

theorem HasSmallRectangleCrosses.exists_horizontal_lines
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}
    (h : HasSmallRectangleCrosses f r s Ω)
    (R : ComplexRect) (hR : R.closed ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ y : ℕ → ℝ, ∀ᶠ ν in atTop,
      y ν ∈ Icc R.bottom R.top ∧ ∀ t ∈ Icc R.left R.right,
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤
          Real.exp (-δ * s ν) := by
  classical
  obtain ⟨δ, hδ, hcross⟩ := h R hR
  let good : ℕ → ℝ → Prop := fun ν y =>
    y ∈ Icc R.bottom R.top ∧ ∀ t ∈ Icc R.left R.right,
      r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, y⟩ : ℂ)) ≤
        Real.exp (-δ * s ν)
  have hchoose : ∀ ν, ∃ y, (∃ z, good ν z) → good ν y := by
    intro ν
    by_cases hν : ∃ y, good ν y
    · obtain ⟨y, hy⟩ := hν
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun hh => (hν hh).elim⟩
  choose y hy using hchoose
  refine ⟨δ, hδ, y, ?_⟩
  filter_upwards [hcross] with ν hν
  obtain ⟨x, hx, z, hz, hH, hV⟩ := hν
  exact hy ν ⟨z, hz, hH⟩

theorem HasSmallRectangleCrosses.exists_horizontal_selection
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}
    (h : HasSmallRectangleCrosses f r s Ω) :
    Nonempty (ScalarHorizontalSelection f r s Ω) := by
  classical
  have hex : ∀ R : {R : ComplexRect // R.closed ⊆ Ω},
      ∃ δ : ℝ, 0 < δ ∧ ∃ y : ℕ → ℝ, ∀ᶠ ν in atTop,
        y ν ∈ Icc R.val.bottom R.val.top ∧ ∀ t ∈ Icc R.val.left R.val.right,
          r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤
            Real.exp (-δ * s ν) := fun R => h.exists_horizontal_lines R.val R.property
  choose rate hrate height hgood using hex
  exact ⟨⟨rate, hrate, height, hgood⟩⟩

namespace ScalarHorizontalSelection

variable {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}

noncomputable def anchor (q : ScalarHorizontalSelection f r s Ω)
    (R : {R : ComplexRect // R.closed ⊆ Ω}) (ν : ℕ) : ℂ × ℂ :=
  scalarCurveSphere f ((r ν : ℂ) * (⟨R.val.left, q.height R ν⟩ : ℂ))

theorem anchor_mem (q : ScalarHorizontalSelection f r s Ω)
    (R : {R : ComplexRect // R.closed ⊆ Ω}) (ν : ℕ) :
    q.anchor R ν ∈ scalarSphereImage :=
  scalarSphereProjection_mem _ _

/-- All selected rectangle anchors coalesce along the same sequence. -/
theorem anchors_tendsto_together (q : ScalarHorizontalSelection f r s Ω)
    (h : HasSmallRectangleCrosses f r s Ω)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (R S : {R : ComplexRect // R.closed ⊆ Ω}) :
    Tendsto (fun ν => ‖q.anchor R ν - q.anchor S ν‖) atTop (𝓝 0) := by
  have hgen : ∀ {A B : ComplexRect}, Relation.ReflTransGen (ComplexRect.AdjacentIn Ω) A B →
      ∀ (hA : A.closed ⊆ Ω) (hB : B.closed ⊆ Ω),
        Tendsto (fun ν => ‖q.anchor ⟨A, hA⟩ ν - q.anchor ⟨B, hB⟩ ν‖) atTop (𝓝 0) := by
    intro A B hAB
    induction hAB with
    | refl =>
      intro hA hB
      simpa only [sub_self, norm_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | @tail B C hAB hBC ih =>
      intro hA hC
      have h₁ := ih hA hBC.1
      have h₂ : Tendsto (fun ν => ‖q.anchor ⟨B, hBC.1⟩ ν - q.anchor ⟨C, hC⟩ ν‖)
          atTop (𝓝 0) :=
        h.adjacent_horizontal_anchors hr hs hBC.1 hC hBC.2.2
          (q.rate_pos ⟨B, hBC.1⟩) (q.rate_pos ⟨C, hC⟩)
          (q.good ⟨B, hBC.1⟩) (q.good ⟨C, hC⟩)
      have hsum := h₁.add h₂
      rw [zero_add] at hsum
      apply squeeze_zero' (Eventually.of_forall (fun ν => norm_nonneg _)) _ hsum
      exact Eventually.of_forall (fun ν =>
        norm_sub_le_norm_sub_add_norm_sub (q.anchor ⟨A, hA⟩ ν)
          (q.anchor ⟨B, hBC.1⟩ ν) (q.anchor ⟨C, hC⟩ ν))
  exact hgen (ComplexRect.reachable_in_open_connected hΩ hc R.property S.property) R.property S.property

end ScalarHorizontalSelection
end ModifiedCartan
#print axioms ModifiedCartan.HasSmallRectangleCrosses.exists_horizontal_selection
#print axioms ModifiedCartan.ScalarHorizontalSelection.anchors_tendsto_together
