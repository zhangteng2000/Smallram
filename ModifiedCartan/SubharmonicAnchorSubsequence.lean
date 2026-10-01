import ModifiedCartan.SubharmonicL1Bounds
import Mathlib.Topology.Sequences

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- Local uniform divergence to negative infinity, tested against every
finite real upper threshold on each compact subset. -/
def LocalUniformlyToBot (U : Set ℂ) (u : ℕ → ℂ → EReal) : Prop :=
  ∀ K, IsCompact K → K ⊆ U → ∀ M : ℝ,
    ∀ᶠ n in atTop, ∀ z ∈ K, u n z ≤ (M : EReal)

theorem exists_lower_anchors_of_not_localUniformlyToBot {U : Set ℂ} {u : ℕ → ℂ → EReal}
    (h : ¬ LocalUniformlyToBot U u) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ ∃ M : ℝ,
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ a : ℕ → ℂ,
        (∀ n, a n ∈ K) ∧ ∀ n, (M : EReal) < u (ns n) (a n) := by
  classical
  simp only [LocalUniformlyToBot, not_forall, exists_prop] at h
  obtain ⟨K, hK, hKU, M, hbad⟩ := h
  have hfreq : ∃ᶠ n in atTop, ∃ z ∈ K, (M : EReal) < u n z := by
    simpa only [not_forall, not_le, exists_prop] using! Filter.not_eventually.mp hbad
  obtain ⟨ns, hns, hnsP⟩ := extraction_of_frequently_atTop hfreq
  choose a ha halower using hnsP
  exact ⟨K, hK, hKU, M, ns, hns, a, ha, halower⟩

/-- The non-collapse branch of `lem:subharmonic-compactness` has a subsequence
with a uniform L1 bound on one disk. The bound and nontriviality are derived
from the original local upper bounds, not supplied as hypotheses. -/
theorem subharmonic_exists_subsequence_one_disk_l1_bound {U : Set ℂ} {u : ℕ → ℂ → EReal}
    (hU : IsOpen U) (hu : ∀ n, IsSubharmonicOn U (u n))
    (hbdd : ∀ K, IsCompact K → K ⊆ U → ∃ M : ℝ,
      ∀ n z, z ∈ K → u n z ≤ (M : EReal))
    (hcollapse : ¬ LocalUniformlyToBot U u) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ c ∈ U, ∃ r : ℝ, 0 < r ∧
      closedBall c (3 * r) ⊆ U ∧ ∃ B : ℝ, 0 ≤ B ∧
        (∀ n, ∃ z ∈ U, u (ns n) z ≠ ⊥) ∧
        ∀ n, IntegrableOn (fun z => (u (ns n) z).toReal) (ball c r) ∧
          (∫ z in ball c r, ‖(u (ns n) z).toReal‖) ≤ B := by
  classical
  obtain ⟨K, hK, hKU, L, ns, hns, a, ha, halower⟩ :=
    exists_lower_anchors_of_not_localUniformlyToBot hcollapse
  obtain ⟨c, hcK, ms, hms, hlim⟩ := hK.tendsto_subseq ha
  have hcU := hKU hcK
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hcU
  let r := ε / 4
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrU : closedBall c (3 * r) ⊆ U :=
    (closedBall_subset_ball (by dsimp only [r]; linarith)).trans hεU
  obtain ⟨M, hM⟩ := hbdd (closedBall c (3 * r)) (isCompact_closedBall c (3 * r)) hrU
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (isOpen_ball.mem_nhds (mem_ball_self hr)))
  let ks : ℕ → ℕ := fun n => ns (ms (n + N))
  have hks : StrictMono ks := hns.comp (hms.comp (by
    intro i j hij
    change i + N < j + N
    omega))
  have haBall (n : ℕ) : a (ms (n + N)) ∈ ball c r := hN (n + N) (Nat.le_add_left N n)
  let B : ℝ := max ((Real.pi * (2 * r) ^ 2) * (2 * max M 0 - L)) 0
  refine ⟨ks, hks, c, hcU, r, hr, hrU, B, le_max_right _ _, ?_, ?_⟩
  · intro n
    refine ⟨a (ms (n + N)), hKU (ha _), ?_⟩
    exact ne_of_gt ((EReal.bot_lt_coe L).trans (halower _))
  · intro n
    have hupper : ∀ z ∈ closedBall c (3 * r), u (ks n) z ≤ ((max M 0 : ℝ) : EReal) :=
      fun z hz => (hM (ks n) z hz).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
    have hlow : (((-(-L) : ℝ)) : EReal) ≤ u (ks n) (a (ms (n + N))) := by
      simpa only [neg_neg] using (halower (ms (n + N))).le
    have hb := (hu (ks n)).l1_bound_of_anchor_in_ball hr hrU (le_max_right M 0)
      hupper (haBall n) hlow
    refine ⟨hb.1, hb.2.trans ?_⟩
    simpa only [B, sub_eq_add_neg] using! le_max_left ((Real.pi * (2 * r) ^ 2) * (2 * max M 0 - L)) 0


end ModifiedCartan

