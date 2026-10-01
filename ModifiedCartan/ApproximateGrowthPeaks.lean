import ModifiedCartan.TiltedBlockGrowth
import ModifiedCartan.LogGrowthProfile

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Every finite positive order in the closed strong-index interval has
approximate additive peaks in arbitrarily remote fixed windows.
This is the elementary peak-construction step below LaTeX `lem:peaks`. -/
theorem exists_logarithmic_growth_peak (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) (hm : MonotoneOn T (Ioi 0))
    {μ H d : ℝ} (hμ : 0 ≤ μ)
    (hlower : strongLowerIndex T ≤ (μ : EReal))
    (hupper : (μ : EReal) ≤ strongUpperIndex T)
    (hH : 0 < H) (hd : 0 < d) (A : ℝ) :
    ∃ x, A ≤ x ∧ ∀ y, x - H ≤ y → y ≤ x + H →
      logGrowthProfile T y - μ * y ≤ logGrowthProfile T x - μ * x + d := by
  by_contra he
  push Not at he
  let u := logGrowthProfile T
  have hu : Monotone u := monotone_logGrowthProfile T hT hm
  have hgain : ∀ x, A ≤ x → ∃ y, x - H ≤ y ∧ y ≤ x + H ∧
      (u x - μ * x) + d ≤ u y - μ * y := by
    intro x hx
    obtain ⟨y, hy0, hy1, hy⟩ := he x hx
    exact ⟨y, hy0, hy1, hy.le⟩
  have hn := tiltedBlockSup_neighbor_gap hu hμ hH hd hgain
  rcases neighbor_growth_dichotomy hd hn with ⟨N, hN⟩ | hN
  · have hshift : ∀ k, tiltedBlockSup u μ (A + (N : ℝ) * H) H k + d ≤
        tiltedBlockSup u μ (A + (N : ℝ) * H) H (k + 1) := by
      intro k
      rw [tiltedBlockSup_shift, tiltedBlockSup_shift]
      simpa only [Nat.add_assoc] using hN k
    have hi : ((μ + d / H : ℝ) : EReal) ≤ strongLowerIndex T :=
      le_strongLowerIndex_of_log_slope T hT
        (B := A + (N : ℝ) * H + H) (D := 2 * H) (C := 2 * d + 2 * μ * H)
        (fun _ _ hx hy => tiltedBlockSup_growth_slope hu hμ hH hd hshift hx hy)
    have hr : μ + d / H ≤ μ := by exact_mod_cast hi.trans hlower
    linarith [div_pos hd hH]
  · have hi : strongUpperIndex T ≤ ((μ - d / H : ℝ) : EReal) :=
      strongUpperIndex_le_of_log_slope T hT
        (B := A + H) (D := 2 * H) (C := 2 * d + 2 * μ * H)
        (fun _ _ hx hy => tiltedBlockSup_decay_slope hu hμ hH hd hN hx hy)
    have hr : μ ≤ μ - d / H := by exact_mod_cast hupper.trans hi
    linarith [div_pos hd hH]

end
end ModifiedCartan
#print axioms ModifiedCartan.exists_logarithmic_growth_peak
