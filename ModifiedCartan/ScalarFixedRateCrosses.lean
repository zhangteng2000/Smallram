import ModifiedCartan.ScalarMovingCrosses
import ModifiedCartan.ScalarHorizontalSelection

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual rectangle crosses with one specified rate throughout a region.
Keeping the rate is necessary for the exact coefficient in thm:A (b). -/
def HasRectangleCrossesAtRate (f : Curve 1) (r s : ℕ → ℝ) (Ω : Set ℂ) (κ : ℝ) : Prop :=
  ∀ R : ComplexRect, R.closed ⊆ Ω → ∀ᶠ ν in atTop, ScalarGoodCross f (r ν) (s ν) κ R

theorem HasRectangleCrossesAtRate.small {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ} {κ : ℝ}
    (h : HasRectangleCrossesAtRate f r s Ω κ) (hκ : 0 < κ) :
    HasSmallRectangleCrosses f r s Ω := fun R hR => ⟨κ, hκ, h R hR⟩

theorem HasRectangleCrossesAtRate.comp {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ} {κ : ℝ}
    (h : HasRectangleCrossesAtRate f r s Ω κ) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) :
    HasRectangleCrossesAtRate f (r ∘ ns) (s ∘ ns) Ω κ :=
  fun R hR => hns.eventually (h R hR)

theorem HasRectangleCrossesAtRate.exists_horizontal_selection
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ} {κ : ℝ}
    (h : HasRectangleCrossesAtRate f r s Ω κ) (hκ : 0 < κ) :
    ∃ q : ScalarHorizontalSelection f r s Ω, ∀ R, q.rate R = κ := by
  classical
  let good (R : {R : ComplexRect // R.closed ⊆ Ω}) (ν : ℕ) (y : ℝ) : Prop :=
    y ∈ Icc R.val.bottom R.val.top ∧ ∀ t ∈ Icc R.val.left R.val.right,
      r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, y⟩ : ℂ)) ≤ Real.exp (-κ * s ν)
  have hex : ∀ R : {R : ComplexRect // R.closed ⊆ Ω}, ∀ ν : ℕ,
      ∃ y : ℝ, (∃ z, good R ν z) → good R ν y := by
    intro R ν
    by_cases hh : ∃ y, good R ν y
    · obtain ⟨y, hy⟩ := hh
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun hh' => (hh hh').elim⟩
  choose height hheight using hex
  have hgood (R : {R : ComplexRect // R.closed ⊆ Ω}) : ∀ᶠ ν in atTop, good R ν (height R ν) := by
    filter_upwards [h R.val R.property] with ν hν
    obtain ⟨x, hx, y, hy, hH, hV⟩ := hν
    exact hheight R ν ⟨y, hy, hH⟩
  exact ⟨⟨fun _ => κ, fun _ => hκ, height, hgood⟩, fun _ => rfl⟩

end ModifiedCartan
#print axioms ModifiedCartan.HasRectangleCrossesAtRate.exists_horizontal_selection
