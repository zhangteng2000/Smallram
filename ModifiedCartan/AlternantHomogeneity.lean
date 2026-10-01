import ModifiedCartan.AlternantCoefficients
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteExponent_degree {m : ℕ} (e : Fin m → ℕ) :
    (finiteExponent e).degree = ∑ i : Fin m, e i := by
  rw [Finsupp.degree_eq_sum]
  rfl

theorem finiteExponent_degree_comp_perm {m : ℕ} (e : Fin m → ℕ)
    (σ : Equiv.Perm (Fin m)) :
    (finiteExponent (e ∘ σ)).degree = (finiteExponent e).degree := by
  rw [finiteExponent_degree, finiteExponent_degree]
  exact Equiv.sum_comp σ e

theorem finiteAlternant_isHomogeneous {m : ℕ} (e : Fin m → ℕ) :
    (finiteAlternant e).IsHomogeneous (finiteExponent e).degree := by
  unfold finiteAlternant
  apply MvPolynomial.IsHomogeneous.sum
  intro σ _
  exact MvPolynomial.isHomogeneous_monomial _ (finiteExponent_degree_comp_perm e σ)

theorem finiteVandermondeAlternant_isHomogeneous (m : ℕ) :
    (finiteVandermondeAlternant m).IsHomogeneous (finiteStaircaseDegree m).degree :=
  finiteAlternant_isHomogeneous _

theorem coloringDegree_degree {A B : Type*} [Fintype A] (f : A → B) :
    (coloringDegree f).degree = Fintype.card A := by
  simp [coloringDegree, map_sum, Finsupp.degree_single]

theorem partitionRowDegree_degree (μ : YoungDiagram) :
    (partitionRowDegree μ).degree = partitionSize μ := by
  rw [partitionRowDegree, coloringDegree_degree]
  exact Fintype.card_coe μ.cells

theorem partitionFiniteDegree_degree {m : ℕ} (μ : YoungDiagram) (hm : μ.colLen 0 ≤ m) :
    (partitionFiniteDegree m μ).degree = partitionSize μ := by
  rw [← Finsupp.degree_mapDomain Fin.val, partitionFiniteDegree_mapDomain μ hm,
    partitionRowDegree_degree]

theorem partitionAlternantExponent_degree {m : ℕ} (μ : YoungDiagram)
    (hm : μ.colLen 0 ≤ m) :
    (partitionFiniteDegree m μ + finiteStaircaseDegree m).degree =
      (finiteStaircaseDegree m).degree + partitionSize μ := by
  rw [map_add, partitionFiniteDegree_degree μ hm, add_comm]

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteVandermondeAlternant_isHomogeneous
#print axioms ModifiedCartan.partitionAlternantExponent_degree
