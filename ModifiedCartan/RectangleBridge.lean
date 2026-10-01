import ModifiedCartan.ScalarSphericalLine
import ModifiedCartan.ComplexRectangleIntegral

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A vertical strip through the horizontal overlap of two rectangles stays
in their union when the vertical intervals overlap. -/
theorem complexRectangle_vertical_bridge_subset
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ} (hy₁ : c₂ ≤ d₁) (hy₂ : c₁ ≤ d₂) :
    complexClosedRectangle (max a₁ a₂) (min b₁ b₂) (min c₁ c₂) (max d₁ d₂) ⊆
      complexClosedRectangle a₁ b₁ c₁ d₁ ∪ complexClosedRectangle a₂ b₂ c₂ d₂ := by
  intro z hz
  have hx₁ : z.re ∈ Icc a₁ b₁ :=
    ⟨(le_max_left _ _).trans hz.1.1, hz.1.2.trans (min_le_left _ _)⟩
  have hx₂ : z.re ∈ Icc a₂ b₂ :=
    ⟨(le_max_right _ _).trans hz.1.1, hz.1.2.trans (min_le_right _ _)⟩
  have hy : z.im ∈ Icc c₁ d₁ ∪ Icc c₂ d₂ := by
    rw [Icc_union_Icc' hy₁ hy₂]
    exact hz.2
  rcases hy with hy | hy
  · exact Or.inl ⟨hx₁, hy⟩
  · exact Or.inr ⟨hx₂, hy⟩

/-- Three proved line estimates join the selected horizontal lines of
overlapping rectangles through a vertical line in their common strip. -/
theorem scalar_curve_rectangle_bridge_diameter (f : Curve 1)
    {r a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x y₁ y₂ C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hx₁ : x ∈ Icc a₁ b₁) (hx₂ : x ∈ Icc a₂ b₂)
    (hy₁ : y₁ ∈ Icc c₁ d₁) (hy₂ : y₂ ∈ Icc c₂ d₂)
    (hH₁ : ∀ t ∈ Icc a₁ b₁,
      r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨t, y₁⟩ : ℂ)) ≤ C)
    (hH₂ : ∀ t ∈ Icc a₂ b₂,
      r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨t, y₂⟩ : ℂ)) ≤ C)
    (hV : ∀ t ∈ Icc (min c₁ c₂) (max d₁ d₂),
      r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨x, t⟩ : ℂ)) ≤ C)
    {s t : ℝ} (hs : s ∈ Icc a₁ b₁) (ht : t ∈ Icc a₂ b₂) :
    ‖scalarCurveSphere f ((r : ℂ) * (⟨s, y₁⟩ : ℂ)) -
      scalarCurveSphere f ((r : ℂ) * (⟨t, y₂⟩ : ℂ))‖ ≤
        C * ((b₁ - a₁) + (max d₁ d₂ - min c₁ c₂) + (b₂ - a₂)) := by
  let A := scalarCurveSphere f ((r : ℂ) * (⟨s, y₁⟩ : ℂ))
  let B := scalarCurveSphere f ((r : ℂ) * (⟨x, y₁⟩ : ℂ))
  let D := scalarCurveSphere f ((r : ℂ) * (⟨x, y₂⟩ : ℂ))
  let E := scalarCurveSphere f ((r : ℂ) * (⟨t, y₂⟩ : ℂ))
  have hy₁' : y₁ ∈ Icc (min c₁ c₂) (max d₁ d₂) :=
    ⟨(min_le_left _ _).trans hy₁.1, hy₁.2.trans (le_max_left _ _)⟩
  have hy₂' : y₂ ∈ Icc (min c₁ c₂) (max d₁ d₂) :=
    ⟨(min_le_right _ _).trans hy₂.1, hy₂.2.trans (le_max_right _ _)⟩
  calc
    ‖A - E‖ = ‖((A - B) + (B - D)) + (D - E)‖ := by congr 1; abel
    _ ≤ (‖A - B‖ + ‖B - D‖) + ‖D - E‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (C * (b₁ - a₁) + C * (max d₁ d₂ - min c₁ c₂)) + C * (b₂ - a₂) :=
      add_le_add (add_le_add
        (scalar_curve_horizontal_diameter f hr hC hH₁ hs hx₁)
        (scalar_curve_vertical_diameter f hr hC hV hy₁' hy₂'))
        (scalar_curve_horizontal_diameter f hr hC hH₂ hx₂ ht)
    _ = _ := by ring

end ModifiedCartan
#print axioms ModifiedCartan.scalar_curve_rectangle_bridge_diameter
