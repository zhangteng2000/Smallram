import ModifiedCartan.UniformLocalLp
import Mathlib.Topology.Sequences

open scoped Topology ENNReal NNReal
open Filter Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- Cauchy extraction suffices for total boundedness; no limit in the original range is required. -/
theorem totallyBounded_of_cauchy_subsequences {X : Type*} [PseudoMetricSpace X] {S : Set X}
    (h : ∀ u : ℕ → X, (∀ n, u n ∈ S) →
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ CauchySeq (u ∘ ns)) : TotallyBounded S := by
  intro V hV
  contrapose! h
  obtain ⟨u, huS, hu⟩ : ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧
      ∀ n m, m < n → u m ∉ UniformSpace.ball (u n) V := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and] using! seq_of_forall_finite_exists h
  refine ⟨u, huS, fun ns hns hc => ?_⟩
  obtain ⟨N, hN⟩ := hc.mem_entourage hV
  exact hu (ns (N + 1)) (ns N) (hns (Nat.lt_add_one N))
    (hN (N + 1) N N.le_succ le_rfl)

theorem totallyBounded_range_of_uniform_approximation {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → X)
    (h : ∀ ε : ℝ, 0 < ε → ∃ g : ℕ → X,
      TotallyBounded (range g) ∧ ∀ n, dist (f n) (g n) ≤ ε) :
    TotallyBounded (range f) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := h (ε / 3) (by positivity)
  obtain ⟨T, hT, hcover⟩ := Metric.totallyBounded_iff.mp hg (ε / 3) (by positivity)
  refine ⟨T, hT, ?_⟩
  rintro _ ⟨n, rfl⟩
  obtain ⟨y, hyT, hgy⟩ := mem_iUnion₂.mp (hcover (mem_range_self n))
  refine mem_iUnion₂.mpr ⟨y, hyT, ?_⟩
  rw [mem_ball] at hgy ⊢
  have := dist_triangle (f n) (g n) y
  linarith [hfg n]


end ModifiedCartan
