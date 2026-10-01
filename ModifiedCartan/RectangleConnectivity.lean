import ModifiedCartan.ComplexRectangleIntegral
import Mathlib.Topology.Connected.Clopen
import Mathlib.Logic.Relation

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

def complexOpenRectangle (a b c d : ℝ) : Set ℂ :=
  Complex.reProdIm (Ioo a b) (Ioo c d)

theorem complexOpenRectangle_isOpen (a b c d : ℝ) : IsOpen (complexOpenRectangle a b c d) := by
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem complexOpenRectangle_subset_closed (a b c d : ℝ) :
    complexOpenRectangle a b c d ⊆ complexClosedRectangle a b c d :=
  fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩

theorem exists_closed_rectangle_neighborhood {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {z : ℂ} (hz : z ∈ Ω) :
    ∃ a b c d : ℝ, a < b ∧ c < d ∧ z ∈ complexOpenRectangle a b c d ∧
      complexClosedRectangle a b c d ⊆ Ω := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ z hz
  let t := ε / 4
  have ht : 0 < t := by dsimp only [t]; positivity
  refine ⟨z.re - t, z.re + t, z.im - t, z.im + t, by linarith, by linarith,
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩
  intro w hw
  have hre : |(w - z).re| ≤ t := by
    rw [Complex.sub_re, abs_le]
    exact ⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩
  have him : |(w - z).im| ≤ t := by
    rw [Complex.sub_im, abs_le]
    exact ⟨by linarith [hw.2.1], by linarith [hw.2.2]⟩
  apply hεΩ
  rw [mem_ball, dist_eq_norm]
  have hnorm := Complex.norm_le_abs_re_add_abs_im (w - z)
  dsimp only [t] at hre him
  linarith

/-- Two points linked through the open interior of one closed rectangle
contained in the domain. This is a finite geometric relation, not a path premise. -/
def ComplexRectangleLink (Ω : Set ℂ) (z w : ℂ) : Prop :=
  ∃ a b c d : ℝ, a < b ∧ c < d ∧ complexClosedRectangle a b c d ⊆ Ω ∧
    z ∈ complexOpenRectangle a b c d ∧ w ∈ complexOpenRectangle a b c d

theorem ComplexRectangleLink.symm {Ω : Set ℂ} {z w : ℂ} (h : ComplexRectangleLink Ω z w) :
    ComplexRectangleLink Ω w z := by
  obtain ⟨a, b, c, d, hab, hcd, hK, hz, hw⟩ := h
  exact ⟨a, b, c, d, hab, hcd, hK, hw, hz⟩

/-- Every pair in an open connected complex domain is joined by a finite
chain of interior rectangle links. Auxiliary to LaTeX `thm:A` (b). -/
theorem IsPreconnected.rectangle_reachable {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (hΩ : IsOpen Ω) {z w : ℂ} (hz : z ∈ Ω) (hw : w ∈ Ω) :
    Relation.ReflTransGen (ComplexRectangleLink Ω) z w := by
  apply hΩc.induction₂' (Relation.ReflTransGen (ComplexRectangleLink Ω)) ?_ ?_ hz hw
  · intro x hx
    obtain ⟨a, b, c, d, hab, hcd, hxR, hK⟩ := exists_closed_rectangle_neighborhood hΩ hx
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ complexOpenRectangle a b c d :=
      (complexOpenRectangle_isOpen a b c d).mem_nhds hxR
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with y hy
    have hxy : ComplexRectangleLink Ω x y := ⟨a, b, c, d, hab, hcd, hK, hxR, hy⟩
    exact ⟨Relation.ReflTransGen.single hxy, Relation.ReflTransGen.single hxy.symm⟩
  · intro x y u hx hy hu hxy hyu
    exact hxy.trans hyu

end ModifiedCartan
#print axioms ModifiedCartan.IsPreconnected.rectangle_reachable
