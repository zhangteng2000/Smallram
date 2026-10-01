import ModifiedCartan.PolynomialBasisReduction
import ModifiedCartan.OrderedPartitionExponents

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

theorem polynomialBasis_exists_min_degree_sum {N : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b₀ : Module.Basis (Fin N) ℂ V) :
    ∃ b : Module.Basis (Fin N) ℂ V, ∀ c : Module.Basis (Fin N) ℂ V,
      (∑ i, (b i).val.natDegree) ≤ ∑ i, (c i).val.natDegree := by
  let P := fun k : ℕ => ∃ b : Module.Basis (Fin N) ℂ V, (∑ i, (b i).val.natDegree) = k
  have hp : ∃ k, P k := ⟨_, b₀, rfl⟩
  obtain ⟨b, hb⟩ := Nat.find_spec hp
  refine ⟨b, ?_⟩
  intro c
  rw [hb]
  exact Nat.find_min' hp ⟨c, rfl⟩

/-- Every finite-dimensional polynomial space admits a basis with distinct
    degrees. This supplies, rather than assumes, the manuscript's adapted basis. -/
theorem polynomialBasis_exists_injective_natDegree {N : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b₀ : Module.Basis (Fin N) ℂ V) :
    ∃ b : Module.Basis (Fin N) ℂ V, Function.Injective (fun i => (b i).val.natDegree) := by
  obtain ⟨b, hb⟩ := polynomialBasis_exists_min_degree_sum b₀
  refine ⟨b, ?_⟩
  intro i j hd
  by_contra hij
  let c := (b i).val.leadingCoeff / (b j).val.leadingCoeff
  obtain ⟨d, hdi, hdk⟩ := basis_exists_elementary_subtraction b i j hij c
  have hn (k : Fin N) : (b k).val ≠ 0 := fun h => b.ne_zero k (Subtype.ext h)
  have hei : (d i).val = (b i).val - c • (b j).val := congrArg Subtype.val hdi
  have hdn : (d i).val ≠ 0 := fun h => d.ne_zero i (Subtype.ext h)
  have hlt : (d i).val.natDegree < (b i).val.natDegree := by
    rw [hei]
    exact polynomial_natDegree_cancel_leading_lt _ _ (hn i) (hn j) hd (hei ▸ hdn)
  have hsum : (∑ k, (d k).val.natDegree) < ∑ k, (b k).val.natDegree := by
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hk : k = i
      · subst k; exact hlt.le
      · rw [hdk k hk]
    · exact ⟨i, Finset.mem_univ i, hlt⟩
  exact (not_lt_of_ge (hb d)) hsum

/-- Increasingly order the degree-adapted basis, as in Step 1 of
    manuscript `lem:universal-minors`. -/
theorem polynomialBasis_exists_strictMono_natDegree {N : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b₀ : Module.Basis (Fin N) ℂ V) :
    ∃ b : Module.Basis (Fin N) ℂ V, StrictMono (fun i => (b i).val.natDegree) := by
  obtain ⟨b, hb⟩ := polynomialBasis_exists_injective_natDegree b₀
  obtain ⟨σ, hσ⟩ := exists_perm_strictAnti (fun i => (b i).val.natDegree) hb
  let θ : Equiv.Perm (Fin N) := Fin.revPerm.trans σ
  refine ⟨b.reindex θ.symm, ?_⟩
  intro i j hij
  simp only [Module.Basis.reindex_apply, Equiv.symm_symm]
  exact hσ (Fin.rev_strictAnti hij)

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialBasis_exists_strictMono_natDegree