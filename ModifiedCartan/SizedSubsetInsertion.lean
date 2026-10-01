import ModifiedCartan.KPOperators

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

abbrev SizedLetterSubset (A : Type*) [Fintype A] (n : ℕ) := {I : Finset A // I.card = n}

variable {A : Type*} [Fintype A] [DecidableEq A]

def sizedSubsetInsertionEquiv (n : ℕ) :
    (Σ I : SizedLetterSubset A n, ↥(Finset.univ \ I.val)) ≃
      (Σ J : SizedLetterSubset A (n + 1), ↥J.val) where
  toFun q := ⟨⟨insert q.2.val q.1.val, by
    rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp q.2.property).2, q.1.property]⟩,
    ⟨q.2.val, Finset.mem_insert_self _ _⟩⟩
  invFun q := ⟨⟨q.1.val.erase q.2.val, by
    rw [Finset.card_erase_of_mem q.2.property, q.1.property]
    omega⟩, ⟨q.2.val, by simp⟩⟩
  left_inv q := by
    rcases q with ⟨⟨I, hI⟩, ⟨a, ha⟩⟩
    dsimp
    have hi : (insert a I).erase a = I := Finset.erase_insert (Finset.mem_sdiff.mp ha).2
    apply Sigma.ext (Subtype.ext hi)
    exact (Subtype.heq_iff_coe_eq (by
      intro x
      change x ∈ Finset.univ \ (insert a I).erase a ↔ x ∈ Finset.univ \ I
      rw [hi])).mpr rfl
  right_inv q := by
    rcases q with ⟨⟨J, hJ⟩, ⟨a, ha⟩⟩
    dsimp
    have hi : insert a (J.erase a) = J := Finset.insert_erase ha
    apply Sigma.ext (Subtype.ext hi)
    exact (Subtype.heq_iff_coe_eq (by
      intro x
      change x ∈ insert a (J.erase a) ↔ x ∈ J
      rw [hi])).mpr rfl

theorem sum_sizedLetterSubset {M : Type*} [AddCommMonoid M] (n : ℕ) (f : Finset A → M) :
    (∑ I ∈ (Finset.univ : Finset A).powersetCard n, f I) =
      ∑ I : SizedLetterSubset A n, f I.val := by
  exact Finset.sum_subtype _ (by intro I; simp [Finset.mem_powersetCard]) f

theorem sum_sizedLetterSubset_congr {M : Type*} [AddCommMonoid M] {n m : ℕ}
    (h : n = m) (f : Finset A → M) :
    (∑ I : SizedLetterSubset A n, f I.val) = ∑ I : SizedLetterSubset A m, f I.val := by
  subst m
  rfl

theorem sum_sizedSubset_insert {M : Type*} [AddCommMonoid M] (n : ℕ) (f : Finset A → A → M) :
    (∑ I : SizedLetterSubset A n, ∑ a ∈ Finset.univ \ I.val, f I.val a) =
      ∑ J : SizedLetterSubset A (n + 1), ∑ a : J.val, f (J.val.erase a.val) a.val := by
  have he := (sizedSubsetInsertionEquiv (A := A) n).symm.sum_comp
    (fun q : Σ I : SizedLetterSubset A n, ↥(Finset.univ \ I.val) => f q.1.val q.2.val)
  simp only [Fintype.sum_sigma] at he
  change (∑ J : SizedLetterSubset A (n + 1), ∑ a : J.val, f (J.val.erase a.val) a.val) =
    ∑ I : SizedLetterSubset A n, ∑ a : ↥(Finset.univ \ I.val), f I.val a.val at he
  simpa only [Finset.sum_coe_sort] using he.symm

theorem complement_erase_eq_complement_insert (I : Finset A) (a : A) :
    (Finset.univ \ I).erase a = Finset.univ \ insert a I := by
  ext b
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert]
  tauto

end
end ModifiedCartan


