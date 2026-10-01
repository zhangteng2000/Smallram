import ModifiedCartan.RemovedPermutations

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem sign_supportedPermutationEquiv {A : Type*} [Fintype A] [DecidableEq A] (S : Finset A)
    (p : Equiv.Perm S) : Equiv.Perm.sign (supportedPermutationEquiv S p).val = Equiv.Perm.sign p := by
  have he : (supportedPermutationEquiv S p).val = Equiv.Perm.ofSubtype p := by
    apply Equiv.ext
    intro a
    by_cases ha : a ∈ S
    · exact (supportedPermutationEquiv_apply_coe S p ⟨a, ha⟩).trans
        (Equiv.Perm.ofSubtype_apply_of_mem p ha).symm
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem p ha]
      exact (supportedPermutationEquiv S p).property a ha
  rw [he]
  exact Equiv.Perm.sign_ofSubtype p

theorem youngRemovalPermutation_sign (μ : YoungDiagram) (b : YoungCorner μ)
    (p : Equiv.Perm (YoungBoxes (removePartitionBox μ b))) :
    youngPermutationSign μ (youngRemovalPermutationEquiv μ b p).val =
      youngPermutationSign (removePartitionBox μ b) p := by
  have he : Equiv.Perm.sign (youngRemovalPermutationEquiv μ b p).val = Equiv.Perm.sign p := by
    calc
      _ = Equiv.Perm.sign ((youngRemovedSetEquiv μ b).permCongrHom p) :=
        sign_supportedPermutationEquiv (Finset.univ.erase b.val) _
      _ = _ := Equiv.Perm.sign_permCongr (youngRemovedSetEquiv μ b) p
  change ((Equiv.Perm.sign (youngRemovalPermutationEquiv μ b p).val : ℤ) : ℂ) =
    ((Equiv.Perm.sign p : ℤ) : ℂ)
  rw [he]

theorem mem_youngLetterStabilizer_iff (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : Equiv.Perm (YoungBoxes μ)) : g ∈ youngLetterStabilizer μ a ↔ g a = a := by
  constructor
  · intro h
    exact h a (by simp)
  · intro h c hc
    have he : c = a := by simpa using hc
    subst c
    exact h

theorem youngColumn_fixes_of_tabloid_row (μ : YoungDiagram) (a : YoungBoxes μ)
    (c : youngColumnSubgroup μ) (hr : youngTabloidRows μ (youngTabloid μ c.val) a = a.val.1) :
    c.val a = a := by
  have hc : (c.val⁻¹ a).val.2 = a.val.2 := (youngColumnSubgroup μ).inv_mem c.property a
  have hi : c.val⁻¹ a = a := Subtype.ext (Prod.ext hr hc)
  calc
    c.val a = c.val (c.val⁻¹ a) := congrArg c.val hi.symm
    _ = a := c.val.apply_symm_apply a

end
end ModifiedCartan


