import ModifiedCartan.SubharmonicLocalConvexity
import ModifiedCartan.LocalToGlobalConvexity

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan.Paper

/-- Manuscript `lem:finite-gradient-convex` (Bergkvist--Rullgard criterion).
The finite weak-gradient hypothesis proves finiteness and convexity of the
original subharmonic representative. The cited criterion is proved in this
repository via actual smoothings, phase cones, affine maxima and the interval
maximum argument. -/
theorem lem_finite_gradient_convex
    {G : Set ℂ} (hG : IsOpen G) (hGc : Convex ℝ G)
    {u : ℂ → EReal} {v : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn G u)
    (hrep : u =ᵐ[volume.restrict G] (fun z => (v z : EReal)))
    (hg : HasWeakComplexGradient G v g)
    (A : Finset ℂ) (hA : ∀ᵐ z ∂volume.restrict G, g z ∈ A) :
    (∀ z ∈ G, u z = ((u z).toReal : EReal)) ∧
      ConvexOn ℝ G (fun z => (u z).toReal) := by
  obtain ⟨hfinite, hlip⟩ := hu.locallyLipschitzOn_of_finite_gradient hG hrep hg A hA
  refine ⟨hfinite, convexOn_of_continuousOn_locally_convex hGc hlip.continuousOn ?_⟩
  intro c hc
  obtain ⟨s, hs, _, hconv⟩ := hu.locally_convex_of_finite_gradient hG hrep hg A hA hc
  exact ⟨s, hs, hconv⟩

end ModifiedCartan.Paper
#print axioms ModifiedCartan.Paper.lem_finite_gradient_convex
