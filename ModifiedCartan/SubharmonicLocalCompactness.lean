import ModifiedCartan.SubharmonicDiskCompactness
import ModifiedCartan.L1SubsequenceCompactness
import ModifiedCartan.LocalL1Limits

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric TopologicalSpace

set_option autoImplicit false

namespace ModifiedCartan

/-- A common local L1 subsequence on the entire domain; its subharmonic representative is
constructed in the subsequent step of `lem:subharmonic-compactness`. -/
theorem subharmonic_localL1_subsequence
    {U : Set ℂ} (hU : IsOpen U) {u : ℕ → ℂ → EReal}
    (hu : ∀ n, IsSubharmonicOn U (u n))
    (hfinite : ∀ n, ∀ᵐ z ∂volume.restrict U, u n z ≠ ⊥ ∧ u n z ≠ ⊤)
    (hbdd : ∀ K, IsCompact K → K ⊆ U → ∃ B : ℝ, ∀ n,
      IntegrableOn (fun z => (u n z).toReal) K ∧ (∫ z in K, ‖(u n z).toReal‖) ≤ B) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ v : ℂ → ℝ,
      LocalLpConvergence 1 U (fun n z => (u (ns n) z).toReal) v := by
  classical
  have hdisks (x : U) : ∃ R : ℝ, 0 < R ∧ closedBall (x : ℂ) (4 * R) ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x x.property
    refine ⟨ε / 8, by positivity, ?_⟩
    exact (closedBall_subset_ball (by linarith : 4 * (ε / 8) < ε)).trans hεU
  choose R hR hRU using hdisks
  let V : U → Set ℂ := fun x => ball (x : ℂ) (R x)
  have hV : ∀ x, IsOpen (V x) := fun _ => isOpen_ball
  have hcover : U ⊆ ⋃ x : U, V x := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hR _)⟩
  obtain ⟨S, hS, hSU⟩ := isOpen_iUnion_countable V hV
  let : Countable S := hS.to_subtype
  have hcover' : U ⊆ ⋃ i : S, V i := by
    intro z hz
    have hz' : z ∈ ⋃ i ∈ S, V i := by rw [hSU]; exact hcover hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz'
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  let K : S → Set ℂ := fun i => closedBall ((i : U) : ℂ) (R i)
  let f : ℕ → ℂ → ℝ := fun n z => (u n z).toReal
  have hKU : ∀ i, K i ⊆ U := fun i =>
    (closedBall_subset_closedBall (by have := hR i; linarith)).trans (hRU i)
  have hf : ∀ i n, IntegrableOn (f n) (K i) volume := by
    intro i n
    obtain ⟨B, hB⟩ := hbdd (K i) (isCompact_closedBall _ _) (hKU i)
    exact (hB n).1
  have htotal : ∀ i, TotallyBounded (range (fun n =>
      (hf i n).toL1 (μ := volume.restrict (K i)) (f n))) := by
    intro i
    apply totallyBounded_l1_range_of_subsequences (hf i)
    intro k
    obtain ⟨B, hB⟩ := hbdd (closedBall ((i : U) : ℂ) (4 * R i))
      (isCompact_closedBall _ _) (hRU i)
    exact subharmonic_l1_subsequence_on_disk hU (fun n => hu (k n)) (fun n => hfinite (k n))
      (hR i) (hRU i) (fun n => (hB (k n)).1) (fun n => (hB (k n)).2)
  obtain ⟨ns, hns, g, hg⟩ := exists_common_l1_subsequence
    (fun i => volume.restrict (K i)) hf htotal
  have hlocal (i : S) : ∃ v : ℂ → ℝ,
      LocalLpConvergence 1 (V i) (fun n => f (ns n)) v := by
    refine ⟨g i, localL1Convergence_of_eLpNorm_on_set ball_subset_closedBall
      (fun n => hf i (ns n)) (L1.integrable_coeFn (g i)) ?_⟩
    exact tendsto_eLpNorm_of_toL1 (fun n => hf i (ns n)) (hg i)
  obtain ⟨v, hv⟩ := exists_localL1_limit_of_countable_cover (fun i : S => hV i) hcover'
    (fun T hT hTU n => by
      obtain ⟨B, hB⟩ := hbdd T hT hTU
      exact (hB (ns n)).1) hlocal
  exact ⟨ns, hns, v, hv⟩


end ModifiedCartan
