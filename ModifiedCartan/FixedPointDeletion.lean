import ModifiedCartan.RemovedPermutations

open scoped Classical

namespace ModifiedCartan
noncomputable section

def fixedPointStabilizerElement {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) (g : Equiv.Perm A) (hg : g a = a) :
    supportedPermutationSubgroup (Finset.univ.erase a) :=
  ⟨g, by
    intro x hx
    have he : x = a := by simpa using hx
    subst x
    exact hg⟩

/-- Restrict an actual permutation fixing a letter to the remaining finite alphabet. -/
def deleteFixedPoint {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) (g : Equiv.Perm A) (hg : g a = a) : Equiv.Perm (↥(Finset.univ.erase a)) :=
  (supportedPermutationEquiv (Finset.univ.erase a)).symm (fixedPointStabilizerElement a g hg)

theorem deleteFixedPoint_apply {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) (g : Equiv.Perm A) (hg : g a = a) (x : ↥(Finset.univ.erase a)) :
    (deleteFixedPoint a g hg x).val = g x.val := by
  have he := supportedPermutationEquiv_apply_coe (Finset.univ.erase a) (deleteFixedPoint a g hg) x
  have hi : supportedPermutationEquiv (Finset.univ.erase a) (deleteFixedPoint a g hg) =
      fixedPointStabilizerElement a g hg :=
    (supportedPermutationEquiv (Finset.univ.erase a)).apply_symm_apply _
  rw [hi] at he
  exact he.symm

def eraseLetterEquiv {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (a : A) : ↥(Finset.univ.erase a) ≃ ↥(Finset.univ.erase (e a)) :=
  e.subtypeEquiv (by intro x; simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
    Equiv.apply_eq_iff_eq])

theorem permCongr_fixes {A B : Type*} (e : A ≃ B) (a : A) (g : Equiv.Perm A) (hg : g a = a) :
    e.permCongr g (e a) = e a := by
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, hg]

theorem deleteFixedPoint_relabel {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (a : A) (g : Equiv.Perm A) (hg : g a = a) :
    (eraseLetterEquiv e a).permCongr (deleteFixedPoint a g hg) =
      deleteFixedPoint (e a) (e.permCongr g) (permCongr_fixes e a g hg) := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (eraseLetterEquiv e a).surjective y
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  rw [deleteFixedPoint_apply]
  change e (deleteFixedPoint a g hg x).val = e (g (e.symm (e x.val)))
  rw [deleteFixedPoint_apply, Equiv.symm_apply_apply]

end
end ModifiedCartan


