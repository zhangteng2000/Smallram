import ModifiedCartan.SupportedPermutationImages

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [DecidableEq A]

theorem mem_image_permutation_iff (I : Finset A) (u : Equiv.Perm A) (x : A) :
    x ∈ I.image u ↔ u.symm x ∈ I := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    rw [← he, u.symm_apply_apply]
    exact hy
  · intro hx
    exact Finset.mem_image.mpr ⟨u.symm x, hx, u.apply_symm_apply x⟩

theorem finset_image_swap_stable (I : Finset A) (i j : A) (h : i ∈ I ↔ j ∈ I) :
    I.image (Equiv.swap i j) = I := by
  ext x
  rw [mem_image_permutation_iff]
  change Equiv.swap i j x ∈ I ↔ x ∈ I
  by_cases hi : x = i
  · subst x
    rw [Equiv.swap_apply_left]
    exact h.symm
  · by_cases hj : x = j
    · subst x
      rw [Equiv.swap_apply_right]
      exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hi hj]

theorem finset_image_swap_replace (I : Finset A) (i j : A)
    (hi : i ∈ I) (hj : j ∉ I) :
    I.image (Equiv.swap i j) = insert j (I.erase i) := by
  have hij : i ≠ j := fun he => hj (he ▸ hi)
  ext x
  rw [mem_image_permutation_iff]
  change Equiv.swap i j x ∈ I ↔ x ∈ insert j (I.erase i)
  by_cases hxi : x = i
  · subst x
    simp [Equiv.swap_apply_left, hj, hij]
  · by_cases hxj : x = j
    · subst x
      simp [Equiv.swap_apply_right, hi]
    · simp [Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]

theorem finset_image_swap_erase (J : Finset A) (i j : A) (hi : i ∈ J) (hj : j ∈ J) :
    (J.erase j).image (Equiv.swap i j) = J.erase i := by
  by_cases hij : i = j
  · subst j
    simp
  · rw [finset_image_swap_replace _ i j (Finset.mem_erase.mpr ⟨hij, hi⟩)]
    · ext x
      simp only [Finset.mem_insert, Finset.mem_erase]
      by_cases hxj : x = j <;> simp_all [eq_comm]
    · simp

theorem supportedPermutation_image_self (I : Finset A)
    (u : supportedPermutationSubgroup I) : I.image u.val = I := by
  ext x
  rw [mem_image_permutation_iff]
  constructor
  · intro hx
    simpa using supportedPermutation_apply_mem I u hx
  · intro hx
    exact supportedPermutation_apply_mem I u⁻¹ hx

end
end ModifiedCartan


