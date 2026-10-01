import ModifiedCartan.TiltedIntervalSup
import Mathlib.Algebra.Order.Floor.Semiring

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

def tiltedBlockSup (u : ℝ → ℝ) (μ A H : ℝ) (k : ℕ) : ℝ :=
  tiltedIntervalSup u μ (A + (k : ℝ) * H) (A + ((k : ℝ) + 1) * H)

theorem tiltedBlockSup_shift (u : ℝ → ℝ) (μ A H : ℝ) (N k : ℕ) :
    tiltedBlockSup u μ (A + (N : ℝ) * H) H k =
      tiltedBlockSup u μ A H (N + k) := by
  unfold tiltedBlockSup
  congr 1 <;> push_cast <;> ring

theorem tiltedBlockSup_neighbor_gap {u : ℝ → ℝ} (hu : Monotone u)
    {μ A H d : ℝ} (hμ : 0 ≤ μ) (hH : 0 < H) (hd : 0 < d)
    (hgain : ∀ x, A ≤ x → ∃ y, x - H ≤ y ∧ y ≤ x + H ∧
      (u x - μ * x) + d ≤ u y - μ * y) (k : ℕ) :
    tiltedBlockSup u μ A H (k + 1) + d ≤
      max (tiltedBlockSup u μ A H k) (tiltedBlockSup u μ A H (k + 2)) := by
  have hk : 0 ≤ (k : ℝ) * H := mul_nonneg (Nat.cast_nonneg k) hH.le
  have he := tiltedIntervalSup_neighbor_gap hu hμ hH hd
    (a := A + (k : ℝ) * H) (fun x hx => hgain x (by linarith [hx.1]))
  convert he using 1 <;> unfold tiltedBlockSup <;> congr 2 <;> push_cast <;> ring

theorem growth_between_of_successor_gap {a : ℕ → ℝ} {d : ℝ}
    (h : ∀ k, a k + d ≤ a (k + 1)) {i j : ℕ} (hij : i ≤ j) :
    a i + ((j : ℝ) - (i : ℝ)) * d ≤ a j := by
  have he := linear_growth_of_successor_gap h i (j - i)
  simpa only [Nat.add_sub_of_le hij, Nat.cast_sub hij] using he

theorem decay_between_of_successor_gap {a : ℕ → ℝ} {d : ℝ}
    (h : ∀ k, a (k + 1) + d ≤ a k) {i j : ℕ} (hij : i ≤ j) :
    a j + ((j : ℝ) - (i : ℝ)) * d ≤ a i := by
  have he := linear_decay_of_successor_gap h i (j - i)
  simpa only [Nat.add_sub_of_le hij, Nat.cast_sub hij] using he

theorem exists_shifted_grid_interval {A H x : ℝ} (hH : 0 < H) (hx : A + H ≤ x) :
    ∃ i : ℕ, A + ((i : ℝ) + 1) * H ≤ x ∧ x < A + ((i : ℝ) + 2) * H := by
  let q := (x - A - H) / H
  have hq : 0 ≤ q := div_nonneg (by linarith) hH.le
  refine ⟨⌊q⌋₊, ?_, ?_⟩
  · have he := (le_div_iff₀ hH).mp (Nat.floor_le hq)
    linarith
  · have he := (div_lt_iff₀ hH).mp (Nat.lt_floor_add_one q)
    dsimp only [q] at he
    linarith

theorem grid_indices_separated {A H x y : ℝ} {i j : ℕ}
    (hH : 0 < H) (hx : A + ((i : ℝ) + 1) * H ≤ x)
    (hy : y < A + ((j : ℝ) + 2) * H) (hxy : x + 2 * H ≤ y) :
    i + 1 ≤ j := by
  by_contra hc
  have hj : j ≤ i := by omega
  have hj' : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hj
  have hm := mul_le_mul_of_nonneg_right hj' hH.le
  linarith

theorem tiltedBlockSup_growth_slope {u : ℝ → ℝ} (hu : Monotone u)
    {μ A H d : ℝ} (hμ : 0 ≤ μ) (hH : 0 < H) (hd : 0 < d)
    (hg : ∀ k, tiltedBlockSup u μ A H k + d ≤ tiltedBlockSup u μ A H (k + 1))
    {x y : ℝ} (hx : A + H ≤ x) (hxy : x + 2 * H ≤ y) :
    (μ + d / H) * (y - x) - (2 * d + 2 * μ * H) ≤ u y - u x := by
  obtain ⟨i, hi0, hi1⟩ := exists_shifted_grid_interval hH hx
  obtain ⟨j, hj0, hj1⟩ := exists_shifted_grid_interval hH (by linarith : A + H ≤ y)
  have hij := grid_indices_separated hH hi0 hj1 hxy
  have hgap := growth_between_of_successor_gap hg hij
  have hxi : u x - μ * x ≤ tiltedBlockSup u μ A H (i + 1) := by
    apply le_tiltedIntervalSup hu hμ
    constructor
    · simpa only [Nat.cast_add, Nat.cast_one] using hi0
    · convert hi1.le using 1
      push_cast
      ring
  have hyj : tiltedBlockSup u μ A H j ≤ u y - μ * (A + (j : ℝ) * H) := by
    have hb := tiltedIntervalSup_le hu hμ
      (show A + (j : ℝ) * H ≤ A + ((j : ℝ) + 1) * H by linarith)
    exact hb.trans (sub_le_sub_right (hu hj0) _)
  have hmu := mul_le_mul_of_nonneg_left
    (show y - (A + (j : ℝ) * H) ≤ 2 * H by linarith) hμ
  have hdH : d / H * H = d := div_mul_cancel₀ d (ne_of_gt hH)
  have hp : d / H * (y - x) ≤ ((j : ℝ) - (i : ℝ) + 1) * d := by
    calc
      d / H * (y - x) ≤ d / H * (((j : ℝ) - (i : ℝ) + 1) * H) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_pos hd hH).le
      _ = ((j : ℝ) - (i : ℝ) + 1) * d := by
        calc
          _ = ((j : ℝ) - (i : ℝ) + 1) * (d / H * H) := by ring
          _ = _ := by rw [hdH]
  simp only [Nat.cast_add, Nat.cast_one] at hgap
  nlinarith

theorem tiltedBlockSup_decay_slope {u : ℝ → ℝ} (hu : Monotone u)
    {μ A H d : ℝ} (hμ : 0 ≤ μ) (hH : 0 < H) (hd : 0 < d)
    (hg : ∀ k, tiltedBlockSup u μ A H (k + 1) + d ≤ tiltedBlockSup u μ A H k)
    {x y : ℝ} (hx : A + H ≤ x) (hxy : x + 2 * H ≤ y) :
    u y - u x ≤ (μ - d / H) * (y - x) + (2 * d + 2 * μ * H) := by
  obtain ⟨i, hi0, hi1⟩ := exists_shifted_grid_interval hH hx
  obtain ⟨j, hj0, hj1⟩ := exists_shifted_grid_interval hH (by linarith : A + H ≤ y)
  have hij := grid_indices_separated hH hi0 hj1 hxy
  have hgap := decay_between_of_successor_gap hg (show i ≤ j + 1 by omega)
  have hyj : u y - μ * y ≤ tiltedBlockSup u μ A H (j + 1) := by
    apply le_tiltedIntervalSup hu hμ
    constructor
    · simpa only [Nat.cast_add, Nat.cast_one] using hj0
    · convert hj1.le using 1
      push_cast
      ring
  have hxi : tiltedBlockSup u μ A H i ≤ u x - μ * (A + (i : ℝ) * H) := by
    have hb := tiltedIntervalSup_le hu hμ
      (show A + (i : ℝ) * H ≤ A + ((i : ℝ) + 1) * H by linarith)
    exact hb.trans (sub_le_sub_right (hu hi0) _)
  have hmu := mul_le_mul_of_nonneg_left
    (show x - (A + (i : ℝ) * H) ≤ 2 * H by linarith) hμ
  have hdH : d / H * H = d := div_mul_cancel₀ d (ne_of_gt hH)
  have hp : d / H * (y - x) ≤ ((j : ℝ) - (i : ℝ) + 1) * d := by
    calc
      d / H * (y - x) ≤ d / H * (((j : ℝ) - (i : ℝ) + 1) * H) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_pos hd hH).le
      _ = ((j : ℝ) - (i : ℝ) + 1) * d := by
        calc
          _ = ((j : ℝ) - (i : ℝ) + 1) * (d / H * H) := by ring
          _ = _ := by rw [hdH]
  simp only [Nat.cast_add, Nat.cast_one] at hgap
  nlinarith

end
end ModifiedCartan
#print axioms ModifiedCartan.tiltedBlockSup_growth_slope
#print axioms ModifiedCartan.tiltedBlockSup_decay_slope
