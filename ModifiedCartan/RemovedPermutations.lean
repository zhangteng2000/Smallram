import ModifiedCartan.RemovedBoxes
import ModifiedCartan.TabloidRowCutoff

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem supportedPermutationEquiv_apply_coe {A : Type*} (S : Finset A)
    (p : Equiv.Perm S) (a : S) : (supportedPermutationEquiv S p).val a.val = (p a).val :=
  Equiv.Perm.ofSubtype_apply_coe p a

def youngRemovedSetEquiv (μ : YoungDiagram) (b : YoungCorner μ) :
    YoungBoxes (removePartitionBox μ b) ≃ ↥(Finset.univ.erase b.val) :=
  (youngRemovedBoxesEquiv μ b).trans (Equiv.subtypeEquivRight (fun a => by simp))

/-- Permutations of the smaller diagram extend by fixing the removed corner. -/
def youngRemovalPermutationEquiv (μ : YoungDiagram) (b : YoungCorner μ) :
    Equiv.Perm (YoungBoxes (removePartitionBox μ b)) ≃* youngLetterStabilizer μ b.val :=
  (youngRemovedSetEquiv μ b).permCongrHom.trans
    (supportedPermutationEquiv (Finset.univ.erase b.val))

theorem youngRemovalPermutation_apply_before (μ : YoungDiagram) (b : YoungCorner μ)
    (p : Equiv.Perm (YoungBoxes (removePartitionBox μ b)))
    (a : YoungBoxes (removePartitionBox μ b)) :
    (youngRemovalPermutationEquiv μ b p).val (youngBoxBeforeRemoval μ b a) =
      youngBoxBeforeRemoval μ b (p a) := by
  have ha : youngBoxBeforeRemoval μ b a ∈ Finset.univ.erase b.val := by
    simp [youngBoxBeforeRemoval_ne μ b a]
  change (supportedPermutationEquiv (Finset.univ.erase b.val)
    ((youngRemovedSetEquiv μ b).permCongrHom p)).val
      (⟨youngBoxBeforeRemoval μ b a, ha⟩ : ↥(Finset.univ.erase b.val)).val = _
  rw [supportedPermutationEquiv_apply_coe]
  change ((youngRemovedSetEquiv μ b)
    (p ((youngRemovedSetEquiv μ b).symm ⟨youngBoxBeforeRemoval μ b a, ha⟩))).val = _
  have he : (⟨youngBoxBeforeRemoval μ b a, ha⟩ : ↥(Finset.univ.erase b.val)) =
      youngRemovedSetEquiv μ b a := rfl
  rw [he, Equiv.symm_apply_apply]
  rfl

theorem youngRemovalPermutation_fiber_iff {I : Type*} (μ : YoungDiagram) (b : YoungCorner μ)
    (p : Equiv.Perm (YoungBoxes (removePartitionBox μ b))) (f : YoungBoxes μ → I) :
    (youngRemovalPermutationEquiv μ b p).val ∈ permutationFiberSubgroup f ↔
      p ∈ permutationFiberSubgroup (fun a => f (youngBoxBeforeRemoval μ b a)) := by
  constructor
  · intro h a
    change f (youngBoxBeforeRemoval μ b (p a)) = f (youngBoxBeforeRemoval μ b a)
    rw [← youngRemovalPermutation_apply_before]
    exact h (youngBoxBeforeRemoval μ b a)
  · intro h a
    change f ((youngRemovalPermutationEquiv μ b p).val a) = f a
    by_cases ha : a = b.val
    · subst a
      rw [youngLetterStabilizer_fixes]
    · have hh := h (youngBoxAfterRemoval μ b a ha)
      change f (youngBoxBeforeRemoval μ b (p (youngBoxAfterRemoval μ b a ha))) =
        f (youngBoxBeforeRemoval μ b (youngBoxAfterRemoval μ b a ha)) at hh
      rw [← youngRemovalPermutation_apply_before, youngBoxBeforeAfterRemoval] at hh
      exact hh

theorem youngRemovalPermutation_row_iff (μ : YoungDiagram) (b : YoungCorner μ)
    (p : Equiv.Perm (YoungBoxes (removePartitionBox μ b))) :
    (youngRemovalPermutationEquiv μ b p).val ∈ youngRowSubgroup μ ↔
      p ∈ youngRowSubgroup (removePartitionBox μ b) :=
  youngRemovalPermutation_fiber_iff μ b p (fun a => a.val.1)

theorem youngRemovalPermutation_column_iff (μ : YoungDiagram) (b : YoungCorner μ)
    (p : Equiv.Perm (YoungBoxes (removePartitionBox μ b))) :
    (youngRemovalPermutationEquiv μ b p).val ∈ youngColumnSubgroup μ ↔
      p ∈ youngColumnSubgroup (removePartitionBox μ b) :=
  youngRemovalPermutation_fiber_iff μ b p (fun a => a.val.2)

end
end ModifiedCartan


