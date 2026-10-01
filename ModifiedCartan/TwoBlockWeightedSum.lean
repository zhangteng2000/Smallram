import ModifiedCartan.SupportedPermutations

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- For two blocks whose weights differ by one, a supported permutation changes
the weighted total by exactly the change in the higher-weight block. -/
theorem two_block_weighted_sum_change {A : Type*} [Fintype A] [DecidableEq A]
    (L R : Finset A) (hdis : Disjoint L R)
    (g : supportedPermutationSubgroup (L ∪ R)) (w f : A → ℤ) (p : ℤ)
    (hL : ∀ a ∈ L, w a = p + 1) (hR : ∀ a ∈ R, w a = p) :
    (∑ a, w a * f (g.val a)) - (∑ a, w a * f a) =
      (∑ a ∈ L, f (g.val a)) - ∑ a ∈ L, f a := by
  let d : A → ℤ := fun a => f (g.val a) - f a
  have hdout : ∀ a ∉ L ∪ R, d a = 0 := by
    intro a ha
    dsimp [d]
    rw [g.property a ha, sub_self]
  have hdall : ∑ a, d a = 0 := by
    dsimp [d]
    rw [Finset.sum_sub_distrib, Equiv.sum_comp g.val f, sub_self]
  have hdLR : (∑ a ∈ L, d a) + (∑ a ∈ R, d a) = 0 := by
    rw [← Finset.sum_union hdis,
      Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hdout a ha)]
    exact hdall
  calc
    _ = ∑ a, w a * d a := by simp only [d, mul_sub, Finset.sum_sub_distrib]
    _ = (∑ a ∈ L, w a * d a) + ∑ a ∈ R, w a * d a := by
      rw [← Finset.sum_union hdis]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      rw [hdout a ha, mul_zero]
    _ = (p + 1) * (∑ a ∈ L, d a) + p * (∑ a ∈ R, d a) := by
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [hL a ha]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [hR a ha]
    _ = (∑ a ∈ L, d a) + p * ((∑ a ∈ L, d a) + ∑ a ∈ R, d a) := by ring
    _ = ∑ a ∈ L, d a := by rw [hdLR, mul_zero, add_zero]
    _ = _ := Finset.sum_sub_distrib _ _

theorem two_block_weighted_sum_lt {A : Type*} [Fintype A] [DecidableEq A]
    (L R : Finset A) (hdis : Disjoint L R)
    (g : supportedPermutationSubgroup (L ∪ R)) (w f : A → ℕ) (p : ℕ)
    (hL : ∀ a ∈ L, w a = p + 1) (hR : ∀ a ∈ R, w a = p)
    (hlt : (∑ a ∈ L, f (g.val a)) < ∑ a ∈ L, f a) :
    (∑ a, w a * f (g.val a)) < ∑ a, w a * f a := by
  have he := two_block_weighted_sum_change L R hdis g
    (fun a => (w a : ℤ)) (fun a => (f a : ℤ)) (p : ℤ)
    (fun a ha => by exact_mod_cast hL a ha) (fun a ha => by exact_mod_cast hR a ha)
  have hlt' : (∑ a ∈ L, (f (g.val a) : ℤ)) < ∑ a ∈ L, (f a : ℤ) := by
    exact_mod_cast hlt
  have htotal : (∑ a, (w a : ℤ) * (f (g.val a) : ℤ)) <
      ∑ a, (w a : ℤ) * (f a : ℤ) := by omega
  exact_mod_cast htotal

end
end ModifiedCartan


