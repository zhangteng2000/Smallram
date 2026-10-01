import ModifiedCartan.FixedPointDeletion

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
theorem inverse_fixes_of_fixes (a : A) (g : Equiv.Perm A) (hg : g a = a) : g⁻¹ a = a := by
  calc
    g⁻¹ a = g⁻¹ (g a) := congrArg (fun x => g⁻¹ x) hg.symm
    _ = a := g.symm_apply_apply a

theorem deleteFixedPoint_inv (a : A) (g : Equiv.Perm A) (hg : g a = a) :
    deleteFixedPoint a g⁻¹ (inverse_fixes_of_fixes a g hg) = (deleteFixedPoint a g hg)⁻¹ := by
  apply (supportedPermutationEquiv (Finset.univ.erase a)).injective
  simp only [deleteFixedPoint, MulEquiv.apply_symm_apply, map_inv]
  rfl

def fixedPointPermutationEquiv (a : A) :
    Equiv.Perm (↥(Finset.univ.erase a)) ≃ {g : Equiv.Perm A // g a = a} where
  toFun p := ⟨(supportedPermutationEquiv (Finset.univ.erase a) p).val,
    (supportedPermutationEquiv (Finset.univ.erase a) p).property a (by simp)⟩
  invFun g := deleteFixedPoint a g.val g.property
  left_inv p := (supportedPermutationEquiv (Finset.univ.erase a)).symm_apply_apply p
  right_inv g := by
    apply Subtype.ext
    have he := congrArg (fun p : supportedPermutationSubgroup (Finset.univ.erase a) => p.val)
      ((supportedPermutationEquiv (Finset.univ.erase a)).apply_symm_apply
        (fixedPointStabilizerElement a g.val g.property))
    exact he

theorem sum_dite_eq_sum_subtype {B M : Type*} [Fintype B] [AddCommMonoid M]
    (p : B → Prop) [DecidablePred p] (f : ∀ b, p b → M) :
    (∑ b, if hb : p b then f b hb else 0) = ∑ b : {b // p b}, f b.val b.property := by
  classical
  let F : B → M := fun b => if hb : p b then f b hb else 0
  have he := Finset.sum_subtype (p := p) (F := inferInstance) (Finset.univ.filter p) (by intro b; simp) F
  calc
    _ = ∑ b : B, if p b then F b else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : p b <;> simp [F, hb]
    _ = ∑ b : {b // p b}, F b.val := by
      simpa only [Finset.sum_filter] using he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      exact dif_pos b.property

theorem sum_fixedPointPermutations (a : A) (f : ∀ g : Equiv.Perm A, g a = a → ℂ) :
    (∑ g, if hg : g a = a then f g hg else 0) =
      ∑ p : Equiv.Perm (↥(Finset.univ.erase a)),
        f (fixedPointPermutationEquiv a p).val (fixedPointPermutationEquiv a p).property := by
  rw [sum_dite_eq_sum_subtype]
  exact ((fixedPointPermutationEquiv a).sum_comp (fun g => f g.val g.property)).symm

end
end ModifiedCartan


