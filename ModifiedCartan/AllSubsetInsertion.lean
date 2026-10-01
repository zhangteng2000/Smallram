import ModifiedCartan.SizedSubsetInsertion

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def allSubsetInsertionEquiv :
    (Σ I : Finset A, ↥(Finset.univ \ I)) ≃ (Σ J : Finset A, ↥J) where
  toFun q := ⟨insert q.2.val q.1, ⟨q.2.val, Finset.mem_insert_self _ _⟩⟩
  invFun q := ⟨q.1.erase q.2.val, ⟨q.2.val, by simp⟩⟩
  left_inv q := by
    rcases q with ⟨I, ⟨a, ha⟩⟩
    dsimp
    have hi : (insert a I).erase a = I := Finset.erase_insert (Finset.mem_sdiff.mp ha).2
    apply Sigma.ext hi
    exact (Subtype.heq_iff_coe_eq (by
      intro x
      change x ∈ Finset.univ \ (insert a I).erase a ↔ x ∈ Finset.univ \ I
      rw [hi])).mpr rfl
  right_inv q := by
    rcases q with ⟨J, ⟨a, ha⟩⟩
    dsimp
    have hi : insert a (J.erase a) = J := Finset.insert_erase ha
    apply Sigma.ext hi
    exact (Subtype.heq_iff_coe_eq (by
      intro x
      change x ∈ insert a (J.erase a) ↔ x ∈ J
      rw [hi])).mpr rfl

theorem sum_allSubset_insert {M : Type*} [AddCommMonoid M] (f : Finset A → A → M) :
    (∑ I : Finset A, ∑ a ∈ Finset.univ \ I, f I a) =
      ∑ J : Finset A, ∑ a : J, f (J.erase a.val) a.val := by
  have he := (allSubsetInsertionEquiv (A := A)).symm.sum_comp
    (fun q : Σ I : Finset A, ↥(Finset.univ \ I) => f q.1 q.2.val)
  simp only [Fintype.sum_sigma] at he
  change (∑ J : Finset A, ∑ a : J, f (J.erase a.val) a.val) =
    ∑ I : Finset A, ∑ a : ↥(Finset.univ \ I), f I a.val at he
  simpa only [Finset.sum_coe_sort] using he.symm

theorem sum_subset_insert_with_letter {M : Type*} [AddCommMonoid M]
    (i : A) (f : Finset A → A → M) :
    (∑ j : A, ∑ I : Finset A, if i ∈ I ∧ j ∉ I then f I j else 0) =
      ∑ J : Finset A, if i ∈ J then ∑ j : ↥(J.erase i), f (J.erase j.val) j.val else 0 := by
  rw [Finset.sum_comm]
  have hs : (∑ I : Finset A, ∑ j : A, if i ∈ I ∧ j ∉ I then f I j else 0) =
      ∑ I : Finset A, ∑ j ∈ Finset.univ \ I, if i ∈ I then f I j else 0 := by
    apply Finset.sum_congr rfl
    intro I _
    have hf : Finset.univ \ I = Finset.univ.filter (fun j => j ∉ I) := by ext j; simp
    rw [hf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : i ∈ I <;> by_cases hj : j ∈ I <;> simp [hi, hj]
  rw [hs, sum_allSubset_insert]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hi : i ∈ J
  · rw [ite_eq_left hi]
    simp only [Finset.mem_erase, hi, and_true]
    calc
      _ = ∑ j ∈ J, if i ≠ j then f (J.erase j) j else 0 :=
        Finset.sum_coe_sort J (fun j => if i ≠ j then f (J.erase j) j else 0)
      _ = ∑ j ∈ J.erase i, f (J.erase j) j := by
        rw [← Finset.filter_ne J i, Finset.sum_filter]
      _ = _ := (Finset.sum_coe_sort (J.erase i) (fun j => f (J.erase j) j)).symm
  · simp [Finset.mem_erase, hi]

end
end ModifiedCartan


