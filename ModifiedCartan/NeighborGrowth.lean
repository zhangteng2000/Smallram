import ModifiedCartan.NormComparison

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Lowest-level discrete growth step used in the construction of Polya peaks. -/
theorem neighbor_growth_step {a : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (h : ∀ k, a (k + 1) + d ≤ max (a k) (a (k + 2)))
    {k : ℕ} (hk : a k ≤ a (k + 1)) : a (k + 1) + d ≤ a (k + 2) := by
  rcases le_max_iff.mp (h k) with hleft | hright
  · linarith
  · exact hright

theorem neighbor_growth_dichotomy {a : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (h : ∀ k, a (k + 1) + d ≤ max (a k) (a (k + 2))) :
    (∃ N, ∀ m, a (N + m) + d ≤ a (N + m + 1)) ∨
      (∀ k, a (k + 1) + d ≤ a k) := by
  by_cases he : ∃ k, a k ≤ a (k + 1)
  · obtain ⟨k, hk⟩ := he
    have hf : ∀ m, a (k + m + 1) + d ≤ a (k + m + 2) := by
      intro m
      induction m with
      | zero => simpa only [Nat.add_zero] using neighbor_growth_step hd h hk
      | succ m ih =>
        have hstep := neighbor_growth_step hd h (by linarith : a (k + m + 1) ≤ a (k + m + 2))
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hstep
    refine Or.inl ⟨k + 1, ?_⟩
    intro m
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hf m
  · right
    intro k
    have hdec : a (k + 2) < a (k + 1) := lt_of_not_ge (fun hh => he ⟨k + 1, hh⟩)
    rcases le_max_iff.mp (h k) with hl | hr
    · exact hl
    · linarith

theorem linear_growth_of_successor_gap {a : ℕ → ℝ} {d : ℝ}
    (h : ∀ k, a k + d ≤ a (k + 1)) (i m : ℕ) :
    a i + (m : ℝ) * d ≤ a (i + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs := h (i + m)
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc] at *
    nlinarith

theorem linear_decay_of_successor_gap {a : ℕ → ℝ} {d : ℝ}
    (h : ∀ k, a (k + 1) + d ≤ a k) (i m : ℕ) :
    a (i + m) + (m : ℝ) * d ≤ a i := by
  have hneg : ∀ k, -a k + d ≤ -a (k + 1) := by intro k; linarith [h k]
  have he := linear_growth_of_successor_gap hneg i m
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.neighbor_growth_dichotomy
