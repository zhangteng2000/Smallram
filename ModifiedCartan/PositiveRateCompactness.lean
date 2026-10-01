import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology
open Filter
set_option autoImplicit false
namespace ModifiedCartan

/-- A downward-closed family of estimates with a positive rate on a refinement
of every escaping sequence has one eventual positive rate. The rate is derived
by a diagonal contradiction, and is not supplied as an extra assumption. -/
theorem exists_eventually_positive_rate_of_subsequences {P : ℝ → ℕ → Prop}
    (hmono : ∀ᶠ n in atTop, ∀ δ ε : ℝ, 0 < ε → ε ≤ δ → P δ n → P ε n)
    (hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, Tendsto ms atTop atTop ∧ ∃ δ > 0,
        ∀ᶠ ν in atTop, P δ (ns (ms ν))) :
    ∃ δ > 0, ∀ᶠ n in atTop, P δ n := by
  classical
  by_contra hn
  have hbad (ν : ℕ) : ∃ n ≥ ν, ¬ P (1 / ((ν : ℝ) + 1)) n := by
    have hrate : 0 < 1 / ((ν : ℝ) + 1) := by positivity
    have hnot : ¬ ∀ᶠ n in atTop, P (1 / ((ν : ℝ) + 1)) n := fun hh => hn ⟨_, hrate, hh⟩
    rw [eventually_atTop] at hnot
    push Not at hnot
    exact hnot ν
  choose ns hns hbad using hbad
  have hnsTop : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  obtain ⟨ms, hms, δ, hδ, hgood⟩ := hsub ns hnsTop
  have hrates : Tendsto (fun ν => 1 / ((ms ν : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hms
  have hh := hgood.and ((hnsTop.comp hms).eventually hmono)
  obtain ⟨ν, ⟨hgoodν, hmonoν⟩, hsmallν⟩ := (hh.and (hrates.eventually_lt_const hδ)).exists
  exact hbad (ms ν) (hmonoν δ _ (by positivity) hsmallν.le hgoodν)

end ModifiedCartan
#print axioms ModifiedCartan.exists_eventually_positive_rate_of_subsequences