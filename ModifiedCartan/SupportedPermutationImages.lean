import ModifiedCartan.FixedPointDeletion

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [DecidableEq A]

def permutationImageEquiv (I : Finset A) (u : Equiv.Perm A) : I ≃ ↥(I.image u) where
  toFun a := ⟨u a.val, Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩⟩
  invFun a := ⟨u.symm a.val, by
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp a.property
    rw [← he, u.symm_apply_apply]
    exact hx⟩
  left_inv a := by apply Subtype.ext; exact u.symm_apply_apply a.val
  right_inv a := by apply Subtype.ext; exact u.apply_symm_apply a.val

theorem supportedPermutation_image_conjugate (I : Finset A) (u : Equiv.Perm A) (p : Equiv.Perm I) :
    (supportedPermutationEquiv (I.image u) ((permutationImageEquiv I u).permCongr p)).val =
      u * (supportedPermutationEquiv I p).val * u⁻¹ := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ I.image u
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    change _ = u ((supportedPermutationEquiv I p).val (u.symm (u y)))
    rw [u.symm_apply_apply]
    calc
      _ = (((permutationImageEquiv I u).permCongr p) ((permutationImageEquiv I u) ⟨y, hy⟩)).val :=
        supportedPermutationEquiv_apply_coe (I.image u) _ ((permutationImageEquiv I u) ⟨y, hy⟩)
      _ = u (p ⟨y, hy⟩).val := by
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
        rfl
      _ = _ := by rw [supportedPermutationEquiv_apply_coe I p ⟨y, hy⟩]
  · rw [(supportedPermutationEquiv (I.image u) ((permutationImageEquiv I u).permCongr p)).property x hx]
    have hi : u.symm x ∉ I := fun hi => hx (Finset.mem_image.mpr ⟨u.symm x, hi, u.apply_symm_apply x⟩)
    change x = u ((supportedPermutationEquiv I p).val (u.symm x))
    rw [(supportedPermutationEquiv I p).property _ hi, u.apply_symm_apply]

end
end ModifiedCartan


