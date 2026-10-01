import ModifiedCartan.ScalarSphericalLine

open scoped Topology
open Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The two intersecting full line segments of a selected rectangle cross. -/
def complexRectangleCross (a b c d x y : ℝ) : Set ℂ :=
  ((fun t : ℝ => (⟨t, y⟩ : ℂ)) '' Icc a b) ∪
    ((fun t : ℝ => (⟨x, t⟩ : ℂ)) '' Icc c d)

/-- Uniform spherical diameter of an actual physical cross. The estimate
includes pairs of points lying on different segments. -/
theorem scalar_curve_cross_diameter (f : Curve 1) {r a b c d x y C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (hH : ∀ t ∈ Icc a b, r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨t, y⟩ : ℂ)) ≤ C)
    (hV : ∀ t ∈ Icc c d, r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨x, t⟩ : ℂ)) ≤ C)
    {z w : ℂ} (hz : z ∈ complexRectangleCross a b c d x y)
    (hw : w ∈ complexRectangleCross a b c d x y) :
    ‖scalarCurveSphere f ((r : ℂ) * z) - scalarCurveSphere f ((r : ℂ) * w)‖ ≤
      C * ((b - a) + (d - c)) := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hcd : c ≤ d := hy.1.trans hy.2
  have hHV (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc c d) :
      ‖scalarCurveSphere f ((r : ℂ) * (⟨s, y⟩ : ℂ)) -
        scalarCurveSphere f ((r : ℂ) * (⟨x, t⟩ : ℂ))‖ ≤ C * ((b - a) + (d - c)) := by
    let A := scalarCurveSphere f ((r : ℂ) * (⟨s, y⟩ : ℂ))
    let B := scalarCurveSphere f ((r : ℂ) * (⟨x, y⟩ : ℂ))
    let D := scalarCurveSphere f ((r : ℂ) * (⟨x, t⟩ : ℂ))
    calc
      ‖A - D‖ = ‖(A - B) + (B - D)‖ := by congr 1; abel
      _ ≤ ‖A - B‖ + ‖B - D‖ := norm_add_le _ _
      _ ≤ C * (b - a) + C * (d - c) := add_le_add
        (scalar_curve_horizontal_diameter f hr hC hH hs hx)
        (scalar_curve_vertical_diameter f hr hC hV hy ht)
      _ = _ := by ring
  rcases hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact (scalar_curve_horizontal_diameter f hr hC hH hs ht).trans
        (mul_le_mul_of_nonneg_left (by linarith) hC)
    · exact hHV s t hs ht
  · rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [norm_sub_rev]
      exact hHV t s ht hs
    · exact (scalar_curve_vertical_diameter f hr hC hV hs ht).trans
        (mul_le_mul_of_nonneg_left (by linarith) hC)

end ModifiedCartan
#print axioms ModifiedCartan.scalar_curve_cross_diameter
