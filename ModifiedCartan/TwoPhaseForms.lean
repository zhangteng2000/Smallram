import ModifiedCartan.TwoPhaseLocalForm

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Explicit local alternatives for two opposite complex gradient values.
This predicate is only notation for formulas, not an existence assumption. -/
def HasTwoPhaseFormOn (F : ℂ → ℝ) (b c : ℂ) (S : Set ℂ) : Prop :=
  EqOn F (fun z => F c + (b * (z - c)).re) S ∨
  EqOn F (fun z => F c - (b * (z - c)).re) S ∨
  EqOn F (fun z => F c + |(b * (z - c)).re|) S

def LocallyTwoPhaseOn (U : Set ℂ) (F : ℂ → ℝ) (b : ℂ) : Prop :=
  ∀ c ∈ U, ∃ s : ℝ, 0 < s ∧ ball c s ⊆ U ∧ HasTwoPhaseFormOn F b c (ball c s)

theorem HasTwoPhaseFormOn.mono {F : ℂ → ℝ} {b c : ℂ} {S T : Set ℂ}
    (h : HasTwoPhaseFormOn F b c S) (hTS : T ⊆ S) : HasTwoPhaseFormOn F b c T := by
  rcases h with h | h | h
  · exact Or.inl (h.mono hTS)
  · exact Or.inr (Or.inl (h.mono hTS))
  · exact Or.inr (Or.inr (h.mono hTS))

theorem HasTwoPhaseFormOn.congr {F G : ℂ → ℝ} {b c : ℂ} {S : Set ℂ}
    (h : HasTwoPhaseFormOn F b c S) (he : EqOn F G S) (hc : c ∈ S) :
    HasTwoPhaseFormOn G b c S := by
  rcases h with h | h | h
  · left; intro z hz; rw [← he hz, ← he hc]; exact h hz
  · right; left; intro z hz; rw [← he hz, ← he hc]; exact h hz
  · right; right; intro z hz; rw [← he hz, ← he hc]; exact h hz

/-- Either choice of the square root yields the identical class of local forms. -/
theorem HasTwoPhaseFormOn.of_neg_root {F : ℂ → ℝ} {b c : ℂ} {S : Set ℂ}
    (h : HasTwoPhaseFormOn F (-b) c S) : HasTwoPhaseFormOn F b c S := by
  rcases h with h | h | h
  · right; left; intro z hz
    simpa only [neg_mul, Complex.neg_re, sub_eq_add_neg] using h hz
  · left; intro z hz
    simpa only [neg_mul, Complex.neg_re, sub_neg_eq_add] using h hz
  · right; right; intro z hz
    simpa only [neg_mul, Complex.neg_re, abs_neg] using h hz

/-- At equal central values, the maximum retains the same two phases. -/
theorem HasTwoPhaseFormOn.max_of_eq {F G : ℂ → ℝ} {b c : ℂ} {S : Set ℂ}
    (hF : HasTwoPhaseFormOn F b c S) (hG : HasTwoPhaseFormOn G b c S)
    (hc : F c = G c) : HasTwoPhaseFormOn (fun z => max (F z) (G z)) b c S := by
  rcases hF with hF | hF | hF <;> rcases hG with hG | hG | hG
  all_goals first
    | solve
      | left
        intro z hz
        dsimp only
        rw [hF hz, hG hz, ← hc]
        simp only [max_self]
    | solve
      | right; left
        intro z hz
        dsimp only
        rw [hF hz, hG hz, ← hc]
        simp only [max_self]
    | right; right
      intro z hz
      dsimp only
      rw [hF hz, hG hz, ← hc, max_self]
      all_goals by_cases hp : 0 ≤ (b * (z - c)).re
      · simp only [abs_of_nonneg hp, max_def]
        split_ifs <;> linarith
      · simp only [abs_of_neg (lt_of_not_ge hp), max_def]
        split_ifs <;> linarith

/-- Taking a finite coordinate maximum introduces no new gradient phase.
Continuity handles strict central dominance; the equal case is exact algebra. -/
theorem LocallyTwoPhaseOn.max {U : Set ℂ} (hU : IsOpen U) {F G : ℂ → ℝ} {b : ℂ}
    (hF : LocallyTwoPhaseOn U F b) (hG : LocallyTwoPhaseOn U G b)
    (hcF : ContinuousOn F U) (hcG : ContinuousOn G U) :
    LocallyTwoPhaseOn U (fun z => max (F z) (G z)) b := by
  intro c hc
  obtain ⟨s, hs, hsU, hsF⟩ := hF c hc
  obtain ⟨t, ht, htU, htG⟩ := hG c hc
  rcases lt_trichotomy (F c) (G c) with hlt | he | hgt
  · have hn := (hcF.continuousAt (hU.mem_nhds hc)).eventually_lt
      (hcG.continuousAt (hU.mem_nhds hc)) hlt
    obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.mp hn
    refine ⟨min t δ, lt_min ht hδ, (ball_subset_ball (min_le_left _ _)).trans htU, ?_⟩
    apply (htG.mono (ball_subset_ball (min_le_left _ _))).congr
    · intro z hz
      exact (max_eq_right (hδS ((ball_subset_ball (min_le_right _ _)) hz)).le).symm
    · exact mem_ball_self (lt_min ht hδ)
  · refine ⟨min s t, lt_min hs ht, (ball_subset_ball (min_le_left _ _)).trans hsU, ?_⟩
    exact (hsF.mono (ball_subset_ball (min_le_left _ _))).max_of_eq
      (htG.mono (ball_subset_ball (min_le_right _ _))) he
  · have hn := (hcG.continuousAt (hU.mem_nhds hc)).eventually_lt
      (hcF.continuousAt (hU.mem_nhds hc)) hgt
    obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.mp hn
    refine ⟨min s δ, lt_min hs hδ, (ball_subset_ball (min_le_left _ _)).trans hsU, ?_⟩
    apply (hsF.mono (ball_subset_ball (min_le_left _ _))).congr
    · intro z hz
      exact (max_eq_left (hδS ((ball_subset_ball (min_le_right _ _)) hz)).le).symm
    · exact mem_ball_self (lt_min hs hδ)

end ModifiedCartan
#print axioms ModifiedCartan.LocallyTwoPhaseOn.max

