import ModifiedCartan.SpechtCharacterLabels
import ModifiedCartan.StandardPolytabloidBasis
import ModifiedCartan.SchubertWronskianDegree
import ModifiedCartan.SupportedPermutations
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The actual character sum in LaTeX `eq:KP-operators`, extended by zero
when the subset size does not match the partition size. -/
def kpAlpha (μ : YoungDiagram) (I : Finset A) : ℂ[Equiv.Perm A] :=
  if h : I.card = partitionSize μ then
    ∑ g : Equiv.Perm I, MonoidAlgebra.single (supportedPermutationEquiv I g).val
      (spechtCharacterOn μ ((Fintype.card_coe I).trans h) g)
  else 0

/-- The finite group-algebra polynomial value from LaTeX `eq:KP-operators`. -/
def kpBeta (μ : YoungDiagram) (z : A → ℂ) (a : ℂ) : ℂ[Equiv.Perm A] :=
  ∑ I ∈ (Finset.univ : Finset A).powersetCard (partitionSize μ),
    (∏ l ∈ Finset.univ \ I, (a + z l)) • kpAlpha μ I

/-- The unital algebra generated at center zero, as defined before
LaTeX `lem:KP-correspondence`. Its commutativity is a separate theorem. -/
def kpGeneratedAlgebra (z : A → ℂ) : Subalgebra ℂ ℂ[Equiv.Perm A] :=
  Algebra.adjoin ℂ (Set.range fun μ : YoungDiagram => kpBeta μ z 0)

theorem kpBeta_zero_mem_generated (μ : YoungDiagram) (z : A → ℂ) :
    kpBeta μ z 0 ∈ kpGeneratedAlgebra z :=
  Algebra.subset_adjoin ⟨μ, rfl⟩

omit [Fintype A] in
theorem kpAlpha_of_card_ne (μ : YoungDiagram) (I : Finset A)
    (h : I.card ≠ partitionSize μ) : kpAlpha μ I = 0 := by
  simp only [kpAlpha, dite_eq_right h]

omit [Fintype A] in
theorem kpAlpha_of_card_eq (μ : YoungDiagram) (I : Finset A)
    (h : I.card = partitionSize μ) :
    kpAlpha μ I = ∑ g : Equiv.Perm I,
      MonoidAlgebra.single (supportedPermutationEquiv I g).val
        (spechtCharacterOn μ ((Fintype.card_coe I).trans h) g) := by
  simp only [kpAlpha, dite_eq_left h]

theorem kpBeta_of_size_gt (μ : YoungDiagram) (z : A → ℂ) (a : ℂ)
    (h : Fintype.card A < partitionSize μ) : kpBeta μ z a = 0 := by
  have he : (Finset.univ : Finset A).powersetCard (partitionSize μ) = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using h)
  simp only [kpBeta, he, Finset.sum_empty]

theorem kpAlpha_empty (A : Type*) [Fintype A] [DecidableEq A] :
    kpAlpha (⊥ : YoungDiagram) (∅ : Finset A) = 1 := by
  rw [kpAlpha_of_card_eq _ _ (by simp)]
  have hg (g : Equiv.Perm (↥(∅ : Finset A))) : g = 1 := by
    apply Equiv.ext
    intro x
    exact False.elim (Finset.notMem_empty _ x.property)
  simp_rw [hg, spechtCharacterOn_one, finrank_specht_eq_standardTableauCount,
    standardSkewTableauCount_self]
  simp
  rfl

theorem kpBeta_empty (z : A → ℂ) (a : ℂ) :
    kpBeta (⊥ : YoungDiagram) z a = (∏ l : A, (a + z l)) • (1 : ℂ[Equiv.Perm A]) := by
  simp [kpBeta, kpAlpha_empty]

theorem kpBeta_parameter_shift (μ : YoungDiagram) (z : A → ℂ) (a t : ℂ) :
    kpBeta μ z (a + t) = kpBeta μ (fun l => z l + t) a := by
  unfold kpBeta
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  ring

end
end ModifiedCartan


