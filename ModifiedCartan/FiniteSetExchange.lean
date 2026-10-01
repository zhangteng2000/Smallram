import ModifiedCartan.FiniteRowMinimum

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Replacing some entries by an equal number of strictly smaller entries
strictly decreases the sum. -/
theorem finset_sum_lt_of_equal_card_exchange {A : Type*} [DecidableEq A]
    (s t : Finset A) (f : A → ℕ)
    (hc : s.card = t.card) (hne : s ≠ t)
    (hsep : ∀ a ∈ s \ t, ∀ b ∈ t \ s, f a < f b) :
    ∑ a ∈ s, f a < ∑ a ∈ t, f a := by
  have hs : (s \ t).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hst
    exact hne (Finset.eq_of_subset_of_card_le hst hc.ge))
  let e : ↥(s \ t) ≃ ↥(t \ s) := Finset.equivOfCardEq (Finset.card_sdiff_comm hc)
  have hsum : (∑ a : ↥(s \ t), f a.val) < ∑ a : ↥(s \ t), f (e a).val := by
    apply Finset.sum_lt_sum_of_nonempty
    · obtain ⟨a, ha⟩ := hs
      exact ⟨⟨a, ha⟩, Finset.mem_univ _⟩
    · intro a _
      exact hsep a.val a.property (e a).val (e a).property
  rw [Equiv.sum_comp e (fun a : ↥(t \ s) => f a.val),
    Finset.sum_coe_sort, Finset.sum_coe_sort] at hsum
  have hleft := Finset.sum_sdiff (f := f) (Finset.inter_subset_left (s₁ := s) (s₂ := t))
  have hright := Finset.sum_sdiff (f := f) (Finset.inter_subset_right (s₁ := s) (s₂ := t))
  rw [Finset.sdiff_inter_self_left] at hleft
  have hdiff : t \ (s ∩ t) = t \ s := by ext a; simp
  rw [hdiff] at hright
  omega

end
end ModifiedCartan


