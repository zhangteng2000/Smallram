import ModifiedCartan.MovingDiskIntegrals
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

open scoped Topology ENNReal NNReal BoundedContinuousFunction
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem exists_uniformly_convergent_subsequence_of_lipschitz
    {K : Set ℂ} (hK : IsCompact K) {F : ℕ → ℂ → ℝ} {L : ℝ≥0}
    (hL : ∀ n, LipschitzWith L (F n)) {B : ℝ}
    (hB : ∀ n x, x ∈ K → ‖F n x‖ ≤ B) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ g : ℂ → ℝ,
      TendstoUniformlyOn (fun n => F (ns n)) g atTop K := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G : ℕ → (K →ᵇ ℝ) := fun n =>
    { toFun := fun x => F n x
      continuous_toFun := (hL n).continuous.comp continuous_subtype_val
      map_bounded' := ⟨2 * B, fun x y => by
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans ((add_le_add (hB n x x.property) (hB n y y.property)).trans
          (by linarith))⟩ }
  have hequi : Equicontinuous ((↑) : range G → K → ℝ) := by
    apply equicontinuous_of_continuity_modulus (fun t : ℝ => (L : ℝ) * t)
      (by simpa only [mul_zero, id_eq] using ((tendsto_id : Tendsto (fun t : ℝ => t)
        (𝓝 0) (𝓝 0)).const_mul (L : ℝ)))
    intro x y g
    obtain ⟨n, hn⟩ := g.property
    have heq : (g : K →ᵇ ℝ) = G n := hn.symm
    change dist ((g : K →ᵇ ℝ) x) ((g : K →ᵇ ℝ) y) ≤ (L : ℝ) * dist x y
    rw [heq]
    exact (hL n).dist_le_mul x y
  have hcompact := BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℝ) B)
    (isCompact_closedBall 0 B) (range G) (fun f x hf => by
      obtain ⟨n, rfl⟩ := hf
      rw [mem_closedBall, dist_zero_right]
      exact hB n x x.property) hequi
  obtain ⟨g, _, ns, hns, hconv⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  let g' : ℂ → ℝ := fun z => if hz : z ∈ K then g ⟨z, hz⟩ else 0
  refine ⟨ns, hns, g', ?_⟩
  have huni := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp huni ε hε] with n hn z hz
  have hnz := hn (⟨z, hz⟩ : K)
  change dist (g ⟨z, hz⟩) (F (ns n) z) < ε at hnz
  simpa only [g', dite_eq_left hz] using hnz


end ModifiedCartan
