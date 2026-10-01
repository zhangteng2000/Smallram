import ModifiedCartan.KPCoefficientTranslation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- LaTeX `eq:KP-translation` for the actual group-algebra sums in
`eq:KP-operators`. The finite index set contains every shape of size at most
the alphabet cardinality; all extra summands vanish by the proved support rules. -/
theorem kpBeta_translation (μ : YoungDiagram) (z : A → ℂ) (a t : ℂ) :
    kpBeta μ z (a + t) = ∑ ν : Subpartition (partitionSquare (Fintype.card A)),
      ((standardSkewTableauCount ν.val μ : ℂ) / ((partitionSize ν.val - partitionSize μ).factorial : ℂ) *
        t ^ (partitionSize ν.val - partitionSize μ)) • kpBeta ν.val z a := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  simpa only [kpBetaCoefficientPolynomial_eval, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply, smul_eq_mul] using
      kpBetaCoefficientPolynomial_translation μ z g a t

/-- The translation formula puts every beta value in the algebra generated at zero.
This proves the membership clause of `lem:KP-correspondence` independently of
the still separate commutativity and spectral-correspondence clauses. -/
theorem kpBeta_mem_generated (μ : YoungDiagram) (z : A → ℂ) (a : ℂ) :
    kpBeta μ z a ∈ kpGeneratedAlgebra z := by
  have ht := kpBeta_translation μ z 0 a
  rw [zero_add] at ht
  rw [ht]
  apply Subalgebra.sum_mem
  intro ν _
  exact (kpGeneratedAlgebra z).smul_mem (kpBeta_zero_mem_generated ν.val z) _

namespace Paper

/-- LaTeX equation `eq:KP-translation`, part of `lem:KP-correspondence`.
This theorem does not assert the remaining clauses of that lemma. -/
theorem eq_KP_translation (μ : YoungDiagram) (z : A → ℂ) (a t : ℂ) :
    kpBeta μ z (a + t) = ∑ ν : Subpartition (partitionSquare (Fintype.card A)),
      ((standardSkewTableauCount ν.val μ : ℂ) / ((partitionSize ν.val - partitionSize μ).factorial : ℂ) *
        t ^ (partitionSize ν.val - partitionSize μ)) • kpBeta ν.val z a :=
  kpBeta_translation μ z a t

end Paper
end
end ModifiedCartan


