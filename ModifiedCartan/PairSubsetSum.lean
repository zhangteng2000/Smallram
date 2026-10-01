import ModifiedCartan.KPSubsetWeights

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem sum_two_subsets_containing {A V : Type*} [Fintype A] [DecidableEq A]
    [AddCommMonoid V] (i : A) (f : Finset A → V) :
    (∑ I ∈ (Finset.univ : Finset A).powersetCard 2, if i ∈ I then f I else 0) =
      ∑ j ∈ (Finset.univ : Finset A).erase i, f {i, j} := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => ({i, j} : Finset A))
  · intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp [Finset.mem_powersetCard, hji, Ne.symm hji]
  · intro a ha b hb he
    have hmem : a ∈ ({i, b} : Finset A) := he ▸ (by simp)
    rcases Finset.mem_insert.mp hmem with hi | hh
    · exact False.elim ((Finset.mem_erase.mp ha).1 hi)
    · exact Finset.mem_singleton.mp hh
  · intro I hI
    obtain ⟨hc, hi⟩ := Finset.mem_filter.mp hI
    have hcard := (Finset.mem_powersetCard.mp hc).2
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (show (I.erase i).card = 1 by
      rw [Finset.card_erase_of_mem hi, hcard])
    have hji : j ≠ i := by
      have hm : j ∈ I.erase i := hj ▸ Finset.mem_singleton_self j
      exact (Finset.mem_erase.mp hm).1
    refine ⟨j, by simp [hji], ?_⟩
    rw [← hj, Finset.insert_erase hi]
  · intro j hj
    rfl

end
end ModifiedCartan


