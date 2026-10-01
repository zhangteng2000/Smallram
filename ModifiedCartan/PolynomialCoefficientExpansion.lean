import ModifiedCartan.ColumnMinorCramer
import ModifiedCartan.UniversalPolynomialMinors
import Mathlib.Topology.DiscreteSubset

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

/-- Pointwise product expansion at every non-root, with coefficients chosen
    once for the space and independent of the evaluation point. -/
theorem polynomialFundamentalCoefficient_product_expansion {M n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b : Module.Basis (Fin (n + 1)) ℂ V)
    (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) :
    ∃ γ : ℕ → Finset (Fin M) → ℂ,
      (∀ q I, ‖γ q I‖ ≤ (q.factorial : ℝ)) ∧
      ∀ (q : ℕ) (hq0 : 1 ≤ q) (hqn : q ≤ n + 1) (a : ℂ),
        (∏ i, (a - roots i)) ≠ 0 →
        FewInflection.fundamentalCoefficients n (fun j z => (b j).val.eval z) a
          ⟨n + 1 - q, by omega⟩ =
          (-1 : ℂ) ^ q * ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard q,
            γ q I / (∏ i ∈ I, (a - roots i)) := by
  obtain ⟨τ, hτ, hunitary, v, hv, he, hb⟩ := Paper.lem_universal_minors b roots hW
  let γ := fun q I => inner ℂ v
    ((spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha (columnPartition q) I) v)
  refine ⟨γ, ?_, ?_⟩
  · intro q I
    simpa only [γ, partitionSize_columnPartition] using hb (columnPartition q) I
  · intro q hq0 hqn a ha
    let i : Fin (n + 1) := ⟨n + 1 - q, by omega⟩
    have hi : n + 1 - i.val = q := by dsimp [i]; omega
    change FewInflection.fundamentalCoefficients n (fun j z => (b j).val.eval z) a i = _
    rw [fundamentalCoefficients_eq_columnMinor, hi, he b (columnPartition q) a ha,
      partitionSize_columnPartition]

/-- The finitely many roots can be excluded on the codiscrete filter, with
    multiplicities and an empty root list both allowed. -/
theorem eventually_linear_root_product_ne_zero {M : ℕ} (roots : Fin M → ℂ)
    (U : Set ℂ) :
    ∀ᶠ a in Filter.codiscreteWithin U, (∏ i, (a - roots i)) ≠ 0 := by
  have he : (Set.range roots)ᶜ ∈ Filter.codiscreteWithin U :=
    compl_finite_mem_codiscreteWithin (Set.finite_range roots)
  filter_upwards [he] with a ha
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ hi
  exact ha ⟨i, (sub_eq_zero.mp hi).symm⟩

namespace Paper

/-- LaTeX `prop:polynomialcoeff`, equation `eq:productformula`.
    The constants are uniformly bounded by q!, independent of the center
    and all mutual root distances. Equality is asserted at every non-root
    and as meromorphic functions (codiscrete equality), including M=0. -/
theorem prop_polynomialcoeff {M n : ℕ} {V : Submodule ℂ (Polynomial ℂ)}
    (b : Module.Basis (Fin (n + 1)) ℂ V) (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) :
    ∃ γ : ℕ → Finset (Fin M) → ℂ,
      (∀ q I, ‖γ q I‖ ≤ (q.factorial : ℝ)) ∧
      ∀ (q : ℕ) (hq0 : 1 ≤ q) (hqn : q ≤ n + 1),
        (∀ a : ℂ, (∏ i, (a - roots i)) ≠ 0 →
          FewInflection.fundamentalCoefficients n (fun j z => (b j).val.eval z) a
            ⟨n + 1 - q, by omega⟩ =
            (-1 : ℂ) ^ q * ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard q,
              γ q I / (∏ i ∈ I, (a - roots i))) ∧
        (fun a => FewInflection.fundamentalCoefficients n (fun j z => (b j).val.eval z) a
          ⟨n + 1 - q, by omega⟩) =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)]
          (fun a => (-1 : ℂ) ^ q *
            ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard q,
              γ q I / (∏ i ∈ I, (a - roots i))) := by
  obtain ⟨γ, hb, he⟩ := polynomialFundamentalCoefficient_product_expansion b roots hW
  refine ⟨γ, hb, ?_⟩
  intro q hq0 hqn
  refine ⟨he q hq0 hqn, ?_⟩
  filter_upwards [eventually_linear_root_product_ne_zero roots Set.univ] with a ha
  exact he q hq0 hqn a ha

end Paper
end
end ModifiedCartan

#print axioms ModifiedCartan.Paper.prop_polynomialcoeff