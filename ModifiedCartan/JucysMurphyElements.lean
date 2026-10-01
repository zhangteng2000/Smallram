import ModifiedCartan.SubsetRepresentationOperators

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [LinearOrder A]

/-- The actual Jucys--Murphy sum for a finite ordered alphabet. -/
def jucysMurphyElement (i : A) : ℂ[Equiv.Perm A] :=
  ∑ j ∈ Finset.univ.filter (fun j => j < i), transpositionElement i j

theorem jucysMurphyElement_eq_sum_ite (i : A) :
    jucysMurphyElement i = ∑ j : A, if j < i then transpositionElement i j else 0 := by
  rw [jucysMurphyElement, Finset.sum_filter]

theorem jucysMurphyElement_max (a : A) (ha : ∀ i : A, i ≤ a) :
    jucysMurphyElement a = permutationStar (Finset.univ.erase a) a := by
  have hs : Finset.univ.filter (fun j : A => j < a) = Finset.univ.erase a := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · exact ne_of_lt
    · intro hj
      exact lt_of_le_of_ne (ha j) hj
  rw [jucysMurphyElement, hs, permutationStar, Finset.sum_coe_sort]

theorem kpSubsetExtension_jucysMurphy_erase (a : A) (ha : ∀ i : A, i ≤ a)
    (i : ↥(Finset.univ.erase a)) :
    kpSubsetExtension (Finset.univ.erase a) (jucysMurphyElement i) = jucysMurphyElement i.val := by
  have he : kpSubsetExtension (Finset.univ.erase a) (jucysMurphyElement i) =
      ∑ j : ↥(Finset.univ.erase a), if j.val < i.val then transpositionElement i.val j.val else 0 := by
    rw [jucysMurphyElement_eq_sum_ite, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j < i
    · rw [ite_eq_left hji]
      change j.val < i.val at hji
      rw [ite_eq_left hji]
      exact kpSubsetExtension_transposition (Finset.univ.erase a) i j
    · rw [ite_eq_right hji, map_zero]
      change ¬j.val < i.val at hji
      rw [ite_eq_right hji]
  rw [he, jucysMurphyElement_eq_sum_ite]
  have hs := Finset.sum_erase_add Finset.univ
    (fun j : A => if j < i.val then transpositionElement i.val j else 0) (Finset.mem_univ a)
  have hna : ¬a < i.val := not_lt_of_ge (ha i.val)
  rw [ite_eq_right hna, add_zero] at hs
  calc
    _ = ∑ j ∈ Finset.univ.erase a,
        if j < i.val then transpositionElement i.val j else 0 :=
      Finset.sum_coe_sort _ (fun j : A => if j < i.val then transpositionElement i.val j else 0)
    _ = _ := hs

end
end ModifiedCartan


