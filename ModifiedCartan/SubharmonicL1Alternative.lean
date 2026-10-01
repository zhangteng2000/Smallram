import ModifiedCartan.SubharmonicAnchorSubsequence
import ModifiedCartan.SubharmonicL1Propagation

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- The reduction of `lem:subharmonic-compactness` to the case with uniform
L1 bounds. This is an intermediate reduction, not the compactness theorem. -/
theorem subharmonic_collapse_or_l1_bounded_subsequence {U : Set ℂ} {u : ℕ → ℂ → EReal}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hu : ∀ n, IsSubharmonicOn U (u n))
    (hbdd : ∀ K, IsCompact K → K ⊆ U → ∃ M : ℝ,
      ∀ n z, z ∈ K → u n z ≤ (M : EReal)) :
    LocalUniformlyToBot U u ∨
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        (∀ n, ∃ z ∈ U, u (ns n) z ≠ ⊥) ∧
        (∀ n, ∀ᵐ z ∂volume.restrict U, u (ns n) z ≠ ⊥ ∧ u (ns n) z ≠ ⊤) ∧
        ∀ K, IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧
          ∀ n, IntegrableOn (fun z => (u (ns n) z).toReal) K ∧
            (∫ z in K, ‖(u (ns n) z).toReal‖) ≤ B := by
  by_cases hcollapse : LocalUniformlyToBot U u
  · exact Or.inl hcollapse
  right
  obtain ⟨ns, hns, c, _, r, hr, hrU, B, _, hnz, hB⟩ :=
    subharmonic_exists_subsequence_one_disk_l1_bound hU hu hbdd hcollapse
  refine ⟨ns, hns, hnz, fun n => (hu (ns n)).ae_finite hU hUc (hnz n), ?_⟩
  apply subharmonic_uniform_l1_on_compacts_of_one_open_set hU hUc (fun n => hu (ns n)) hnz
  · intro K hK hKU
    obtain ⟨M, hM⟩ := hbdd K hK hKU
    exact ⟨M, fun n => hM (ns n)⟩
  · refine ⟨ball c r, isOpen_ball, ⟨c, mem_ball_self hr⟩, ?_, B, hB⟩
    exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hrU


end ModifiedCartan

