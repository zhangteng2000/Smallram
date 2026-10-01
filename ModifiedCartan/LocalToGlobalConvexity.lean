import ModifiedCartan.LocalMidpointMaximum
import Mathlib.Analysis.Convex.Topology

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Local convexity and continuity imply convexity on a convex domain.
The proof reduces each segment to a proved interval maximum argument. -/
theorem convexOn_of_continuousOn_locally_convex {U : Set ℂ}
    (hU : Convex ℝ U) {u : ℂ → ℝ} (hc : ContinuousOn u U)
    (hlocal : ∀ c ∈ U, ∃ s : ℝ, 0 < s ∧ ConvexOn ℝ (ball c s) u) :
    ConvexOn ℝ U u := by
  refine ⟨hU, ?_⟩
  intro x hx y hy p q hp hq hpq
  let γ : ℝ → ℂ := fun t => (1 - t) • x + t • y
  have hγ : Continuous γ :=
    ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
  have hγU : MapsTo γ (Icc 0 1) U := by
    intro t ht
    exact hU hx hy (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have hfc : ContinuousOn (fun t => u (γ t)) (Icc 0 1) := hc.comp hγ.continuousOn hγU
  have hmid : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧
      t - δ ∈ Icc (0 : ℝ) 1 ∧ t + δ ∈ Icc (0 : ℝ) 1 ∧
      u (γ t) ≤ (u (γ (t - δ)) + u (γ (t + δ))) / 2 := by
    intro t ht
    obtain ⟨s, hs, hsc⟩ := hlocal (γ t) (hγU ⟨ht.1.le, ht.2.le⟩)
    have hn : γ ⁻¹' ball (γ t) s ∩ Ioo 0 1 ∈ 𝓝 t :=
      ((isOpen_ball.preimage hγ).inter isOpen_Ioo).mem_nhds ⟨mem_ball_self hs, ht⟩
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hn
    let δ := ε / 2
    have hδ : 0 < δ := half_pos hε
    have hl : t - δ ∈ ball t ε := by
      rw [mem_ball, Real.dist_eq, show t - δ - t = -δ by ring, abs_neg, abs_of_pos hδ]
      exact half_lt_self hε
    have hr : t + δ ∈ ball t ε := by
      rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ]
      exact half_lt_self hε
    have hl' := hεsub hl
    have hr' := hεsub hr
    refine ⟨δ, hδ, ⟨hl'.2.1.le, hl'.2.2.le⟩, ⟨hr'.2.1.le, hr'.2.2.le⟩, ?_⟩
    have hm := hsc.2 hl'.1 hr'.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hγmid : (1 / 2 : ℝ) • γ (t - δ) + (1 / 2 : ℝ) • γ (t + δ) = γ t := by
      apply Complex.ext <;> simp only [γ, Complex.add_re, Complex.smul_re,
        Complex.add_im, Complex.smul_im, smul_eq_mul] <;> ring
    rw [hγmid] at hm
    simp only [smul_eq_mul] at hm
    linarith
  have hqt : q ∈ Icc (0 : ℝ) 1 := ⟨hq, by linarith⟩
  have hchord := le_chord_of_continuous_local_midpoint hfc hmid hqt
  have hp' : 1 - q = p := by linarith
  simpa only [γ, hp', sub_zero, sub_self, zero_smul, one_smul, add_zero, zero_add, smul_eq_mul] using hchord

end ModifiedCartan
#print axioms ModifiedCartan.convexOn_of_continuousOn_locally_convex
