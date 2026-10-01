import ModifiedCartan.RectangleConnectivity
import ModifiedCartan.RectangleBridge

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A nondegenerate rectangle, used to keep finite path geometry explicit. -/
structure ComplexRect where
  left : ℝ
  right : ℝ
  bottom : ℝ
  top : ℝ
  horizontal_pos : left < right
  vertical_pos : bottom < top

namespace ComplexRect

def closed (R : ComplexRect) : Set ℂ :=
  complexClosedRectangle R.left R.right R.bottom R.top

def openSet (R : ComplexRect) : Set ℂ :=
  complexOpenRectangle R.left R.right R.bottom R.top

theorem isCompact_closed (R : ComplexRect) : IsCompact R.closed :=
  complexClosedRectangle_isCompact _ _ _ _

theorem isOpen_openSet (R : ComplexRect) : IsOpen R.openSet :=
  complexOpenRectangle_isOpen _ _ _ _

theorem openSet_subset_closed (R : ComplexRect) : R.openSet ⊆ R.closed :=
  complexOpenRectangle_subset_closed _ _ _ _

theorem openSet_nonempty (R : ComplexRect) : R.openSet.Nonempty := by
  refine ⟨(⟨(R.left + R.right) / 2, (R.bottom + R.top) / 2⟩ : ℂ), ?_⟩
  exact ⟨⟨by linarith [R.horizontal_pos], by linarith [R.horizontal_pos]⟩,
    ⟨by linarith [R.vertical_pos], by linarith [R.vertical_pos]⟩⟩

def Overlaps (R S : ComplexRect) : Prop := (R.openSet ∩ S.openSet).Nonempty

theorem Overlaps.symm {R S : ComplexRect} (h : R.Overlaps S) : S.Overlaps R := by
  obtain ⟨z, hz, hw⟩ := h
  exact ⟨z, hw, hz⟩

theorem Overlaps.horizontal {R S : ComplexRect} (h : R.Overlaps S) :
    max R.left S.left < min R.right S.right := by
  obtain ⟨z, hz, hw⟩ := h
  have hl : max R.left S.left < z.re := max_lt hz.1.1 hw.1.1
  have hr : z.re < min R.right S.right := lt_min hz.1.2 hw.1.2
  exact hl.trans hr

theorem Overlaps.vertical {R S : ComplexRect} (h : R.Overlaps S) :
    max R.bottom S.bottom < min R.top S.top := by
  obtain ⟨z, hz, hw⟩ := h
  exact (max_lt hz.2.1 hw.2.1).trans (lt_min hz.2.2 hw.2.2)

def verticalBridge (R S : ComplexRect) (h : R.Overlaps S) : ComplexRect where
  left := max R.left S.left
  right := min R.right S.right
  bottom := min R.bottom S.bottom
  top := max R.top S.top
  horizontal_pos := h.horizontal
  vertical_pos := (min_le_left _ _).trans_lt (R.vertical_pos.trans_le (le_max_left _ _))

theorem verticalBridge_closed_subset {R S : ComplexRect} (h : R.Overlaps S) :
    (R.verticalBridge S h).closed ⊆ R.closed ∪ S.closed := by
  have hv := h.vertical
  exact complexRectangle_vertical_bridge_subset
    ((le_max_right _ _).trans (hv.le.trans (min_le_left _ _)))
    ((le_max_left _ _).trans (hv.le.trans (min_le_right _ _)))

def AdjacentIn (Ω : Set ℂ) (R S : ComplexRect) : Prop :=
  R.closed ⊆ Ω ∧ S.closed ⊆ Ω ∧ R.Overlaps S

/-- The finite point-link chain gives a finite chain of overlapping rectangles. -/
theorem reachable_in_open_connected {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    {R S : ComplexRect} (hR : R.closed ⊆ Ω) (hS : S.closed ⊆ Ω) :
    Relation.ReflTransGen (AdjacentIn Ω) R S := by
  obtain ⟨z, hz⟩ := R.openSet_nonempty
  obtain ⟨w, hw⟩ := S.openSet_nonempty
  have hzw := ModifiedCartan.IsPreconnected.rectangle_reachable hc hΩ (hR (R.openSet_subset_closed hz))
    (hS (S.openSet_subset_closed hw))
  have hgen : ∀ {x y : ℂ}, Relation.ReflTransGen (ComplexRectangleLink Ω) x y →
      ∀ {A B : ComplexRect}, A.closed ⊆ Ω → B.closed ⊆ Ω →
        x ∈ A.openSet → y ∈ B.openSet → Relation.ReflTransGen (AdjacentIn Ω) A B := by
    intro x y hxy
    induction hxy with
    | refl =>
      intro A B hA hB hxA hxB
      exact Relation.ReflTransGen.single ⟨hA, hB, ⟨x, hxA, hxB⟩⟩
    | @tail y t hxy hyt ih =>
      intro A B hA hB hxA htB
      obtain ⟨a, b, c, d, hab, hcd, hK, hyK, htK⟩ := hyt
      let K : ComplexRect := ⟨a, b, c, d, hab, hcd⟩
      have hAK : Relation.ReflTransGen (AdjacentIn Ω) A K := ih hA hK hxA hyK
      exact hAK.trans (Relation.ReflTransGen.single ⟨hK, hB, ⟨t, htK, htB⟩⟩)
  exact hgen hzw hR hS hz hw

end ComplexRect
end ModifiedCartan
#print axioms ModifiedCartan.ComplexRect.verticalBridge_closed_subset
#print axioms ModifiedCartan.ComplexRect.reachable_in_open_connected
