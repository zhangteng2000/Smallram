import ModifiedCartan.FixedPointDeletion

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [DecidableEq A]

def eraseInsideEquiv (J : Finset A) (a : J) :
    ↥((Finset.univ : Finset J).erase a) ≃ ↥(J.erase a.val) where
  toFun x := ⟨x.val.val, Finset.mem_erase.mpr ⟨by
    intro he
    exact (Finset.mem_erase.mp x.property).1 (Subtype.ext he), x.val.property⟩⟩
  invFun x := ⟨⟨x.val, (Finset.mem_erase.mp x.property).2⟩, Finset.mem_erase.mpr ⟨by
    intro he
    exact (Finset.mem_erase.mp x.property).1 (congrArg Subtype.val he), Finset.mem_univ _⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem supportedPermutation_nested_erase (J : Finset A) (a : J)
    (p : Equiv.Perm (↥((Finset.univ : Finset J).erase a))) :
    (supportedPermutationEquiv J (supportedPermutationEquiv (Finset.univ.erase a) p).val).val =
      (supportedPermutationEquiv (J.erase a.val) ((eraseInsideEquiv J a).permCongr p)).val := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ J
  · by_cases hxa : x = a.val
    · subst x
      rw [supportedPermutationEquiv_apply_coe J _ a]
      have hfix := (supportedPermutationEquiv (Finset.univ.erase a) p).property a (by simp)
      rw [hfix]
      exact ((supportedPermutationEquiv (J.erase a.val) ((eraseInsideEquiv J a).permCongr p)).property
        a.val (by simp)).symm
    · let k : ↥((Finset.univ : Finset J).erase a) :=
        ⟨⟨x, hx⟩, Finset.mem_erase.mpr ⟨fun he => hxa (congrArg Subtype.val he), Finset.mem_univ _⟩⟩
      calc
        _ = ((supportedPermutationEquiv (Finset.univ.erase a) p).val k.val).val :=
          supportedPermutationEquiv_apply_coe J _ k.val
        _ = (p k).val.val := congrArg Subtype.val
          (supportedPermutationEquiv_apply_coe (Finset.univ.erase a) p k)
        _ = ((eraseInsideEquiv J a) (p k)).val := rfl
        _ = (((eraseInsideEquiv J a).permCongr p) ((eraseInsideEquiv J a) k)).val := by
          rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
        _ = _ := (supportedPermutationEquiv_apply_coe (J.erase a.val)
          ((eraseInsideEquiv J a).permCongr p) ((eraseInsideEquiv J a) k)).symm
  · rw [(supportedPermutationEquiv J (supportedPermutationEquiv (Finset.univ.erase a) p).val).property x hx]
    exact ((supportedPermutationEquiv (J.erase a.val) ((eraseInsideEquiv J a).permCongr p)).property
      x (fun hi => hx (Finset.mem_erase.mp hi).2)).symm

end
end ModifiedCartan


