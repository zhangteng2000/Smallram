import ModifiedCartan.SubsetRepresentationOperators
import ModifiedCartan.TotalTranspositionReindex
import ModifiedCartan.YoungTranspositionCorner

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem specht_corner_star_eigenvalue (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (a : A) (b : YoungCorner μ)
    (f : Representation.IntertwiningMap
      (spechtRepresentationOn (removePartitionBox μ b) (card_erase_eq_partition_remove μ h a b))
      (eraseRestrictedSpecht μ h a)) (v : YoungSpechtModule (removePartitionBox μ b)) :
    (spechtRepresentationOn μ h).asAlgebraHom (permutationStar (Finset.univ.erase a) a) (f v) =
      ((b.val.val.2 : ℂ) - (b.val.val.1 : ℂ)) • f v := by
  have hr : totalTranspositionOperator (eraseRestrictedSpecht μ h a) (f v) =
      youngTranspositionScalar (removePartitionBox μ b) • f v := by
    rw [totalTranspositionOperator_natural _ _ f v,
      spechtRepresentationOn_totalTransposition_scalar]
    simp
  have he := congrArg (fun L : Module.End ℂ (YoungSpechtModule μ) => L (f v))
    (totalTranspositionOperator_delete (spechtRepresentationOn μ h) a)
  rw [spechtRepresentationOn_totalTransposition_scalar, LinearMap.smul_apply,
    Module.End.one_apply, LinearMap.add_apply] at he
  change youngTranspositionScalar μ • f v =
    totalTranspositionOperator (eraseRestrictedSpecht μ h a) (f v) +
      (spechtRepresentationOn μ h).asAlgebraHom (permutationStar (Finset.univ.erase a) a) (f v) at he
  rw [hr] at he
  calc
    _ = youngTranspositionScalar μ • f v -
        youngTranspositionScalar (removePartitionBox μ b) • f v := by
      apply (eq_sub_iff_add_eq).mpr
      exact (add_comm _ _).trans he.symm
    _ = (youngTranspositionScalar μ - youngTranspositionScalar (removePartitionBox μ b)) • f v :=
      (sub_smul _ _ _).symm
    _ = _ := by
      rw [youngTranspositionScalar_corner μ b]
      congr 1
      ring

end
end ModifiedCartan


