import ModifiedCartan.SchubertCoordinates
import ModifiedCartan.SchubertWronskianDegree
import Mathlib.RingTheory.Polynomial.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem PolynomialSchubertFrame.le_degreeLT {n m : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (F : PolynomialSchubertFrame n ω V)
    (hm : n + 1 + ω.rowLen 0 ≤ m) : V ≤ Polynomial.degreeLT ℂ m := by
  have hb : ∀ j, F.polynomials j ∈ Polynomial.degreeLT ℂ m := by
    intro j
    apply Polynomial.mem_degreeLT.mpr
    apply (Polynomial.natDegree_lt_iff_degree_lt (F.polynomials_ne_zero j)).mp
    change (F.basis j).val.natDegree < m
    rw [F.degree_eq]
    have hr := ω.rowLen_anti 0 (n - (j : ℕ)) (Nat.zero_le _)
    have hj := j.isLt
    dsimp [partitionMinorOrders]
    omega
  intro q hq
  have he := congrArg (fun v : V => v.val) (F.basis.sum_repr (⟨q, hq⟩ : V))
  have he' : (∑ j, F.basis.repr (⟨q, hq⟩ : V) j • F.polynomials j) = q := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul, PolynomialSchubertFrame.polynomials] using he
  rw [← he']
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (hb j)

theorem polynomialSchubertCell_finrank {n m : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n m ω) :
    Module.finrank ℂ V = n + 1 := (schubertFrame hV).finrank

theorem polynomialSchubertCell_le_degreeLT {n m : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n m ω) :
    V ≤ Polynomial.degreeLT ℂ m := (schubertFrame hV).le_degreeLT hV.2.1

theorem polynomialSchubertCell_wronskian_degree {n m : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n m ω) :
    (FewInflection.polynomialWronskian (schubertFrame hV).polynomials).natDegree =
      partitionSize ω :=
  polynomialWronskian_natDegree_eq_partitionSize (schubertFrame hV).polynomials hV.1
    (schubertFrame hV).polynomials_ne_zero (schubertFrame hV).degree_eq

theorem normalizedSchubertCoordinate_eq_zero_of_not_le {n m : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n m ω)
    (μ : YoungDiagram) (hμ : ¬ μ ≤ ω) (a : ℂ) : normalizedSchubertCoordinate hV μ a = 0 :=
  normalizedPartitionMinor_eq_zero_of_not_le (schubertFrame hV).polynomials
    (fun j => ((schubertFrame hV).degree_eq j).le) μ hμ a

namespace Paper

/-- LaTeX `lem:plucker-translation`, equation `eq:Plucker-translation`.
The finite sum includes all subpartitions of `ω`; counts outside `μ ≤ ν` are zero.
The coordinates are independent of the basis and use the exact manuscript scalar. -/
theorem lem_plucker_translation {n m : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n m ω)
    (μ : YoungDiagram) (a t : ℂ) :
    normalizedSchubertCoordinate hV μ (a + t) =
      ∑ ν : Subpartition ω,
        (standardSkewTableauCount ν.val μ : ℂ) /
          ((partitionSize ν.val - partitionSize μ).factorial : ℂ) *
        t ^ (partitionSize ν.val - partitionSize μ) * normalizedSchubertCoordinate hV ν.val a :=
  normalizedPartitionMinor_translation μ (schubertFrame hV).polynomials hV.1
    (fun j => ((schubertFrame hV).degree_eq j).le) a t

end Paper
end
end ModifiedCartan


