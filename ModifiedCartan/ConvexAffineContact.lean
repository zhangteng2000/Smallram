import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Complex.Basic

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Interior contact with an upper constant forces equality for a convex
function on an open convex domain. Auxiliary to LaTeX `thm:A` (b). -/
theorem convex_eq_zero_of_nonpos_of_zero {G : Set ℂ} (hG : IsOpen G)
    {F : ℂ → ℝ} (hF : ConvexOn ℝ G F) {a : ℂ} (ha : a ∈ G)
    (hzero : F a = 0) (hbound : ∀ z ∈ G, F z ≤ 0) : EqOn F (fun _ => 0) G := by
  obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.mp hG a ha
  have hlocal : ∀ z ∈ ball a ε, 0 ≤ F z := by
    intro z hz
    let w : ℂ := a + (a - z)
    have hw : w ∈ ball a ε := by
      rw [mem_ball, dist_eq_norm]
      have he : w - a = -(z - a) := by dsimp only [w]; ring
      rw [he, norm_neg]
      simpa only [mem_ball, dist_eq_norm] using hz
    have hm : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w = a := by
      simp only [Complex.real_smul, w]
      push_cast
      ring
    have hh := hF.2 (hεG hz) (hεG hw)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    rw [hm, hzero] at hh
    simp only [smul_eq_mul] at hh
    linarith [hbound w (hεG hw)]
  have hmin : IsLocalMinOn F G a := by
    change ∀ᶠ z in 𝓝[G] a, F a ≤ F z
    have hb : ∀ᶠ z in 𝓝 a, z ∈ ball a ε := ball_mem_nhds a hε
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds] with z hz
    rw [hzero]
    exact hlocal z hz
  have hglobal := IsMinOn.of_isLocalMinOn_of_convexOn ha hmin hF
  intro z hz
  have hh : F a ≤ F z := hglobal hz
  rw [hzero] at hh
  exact le_antisymm (hbound z hz) hh

/-- The exact affine-contact comparison needed for the actual power-chart
component. This is proved from convexity, not cited as a maximum principle. -/
theorem convex_eq_affine_of_le_of_eq {G : Set ℂ} (hG : IsOpen G)
    {F : ℂ → ℝ} (hF : ConvexOn ℝ G F) {a b : ℂ} {k : ℝ} (ha : a ∈ G)
    (hpoint : F a = k + (b * a).re)
    (hbound : ∀ z ∈ G, F z ≤ k + (b * z).re) :
    EqOn F (fun z => k + (b * z).re) G := by
  have hA : ConcaveOn ℝ G (fun z => k + (b * z).re) := by
    refine ⟨hF.1, ?_⟩
    intro x hx y hy p q hp hq hpq
    simp only [mul_add, mul_smul_comm, Complex.add_re, Complex.smul_re, smul_eq_mul]
    have hh := congrArg (fun t : ℝ => t * k) hpq
    nlinarith
  have he := convex_eq_zero_of_nonpos_of_zero hG (hF.sub hA) ha
    (by simpa only [Pi.sub_apply, hpoint, sub_self])
    (fun z hz => by simpa only [Pi.sub_apply] using sub_nonpos.mpr (hbound z hz))
  intro z hz
  exact sub_eq_zero.mp (he hz)

end ModifiedCartan
#print axioms ModifiedCartan.convex_eq_affine_of_le_of_eq
