import ModifiedCartan.SchubertDimensionStep

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem polynomialSchubertFrame_exists_ge_dimension {n m : ℕ} {τ : YoungDiagram}
    (hτ : PartitionFits n τ) (hn : n ≤ m) {V : Submodule ℂ (Polynomial ℂ)}
    (F : PolynomialSchubertFrame n τ V) :
    ∃ (W : Submodule ℂ (Polynomial ℂ)) (G : PolynomialSchubertFrame m τ W),
      ∀ μ a, normalizedPartitionMinor τ G.polynomials μ a =
        normalizedPartitionMinor τ F.polynomials μ a := by
  induction m, hn using Nat.le_induction with
  | base => exact ⟨V, F, fun _ _ => rfl⟩
  | succ m hm ih =>
    obtain ⟨W, G, hG⟩ := ih
    have ht : PartitionFits m τ := hτ.rowLen_eq_zero (by omega)
    obtain ⟨U, H, hH⟩ := polynomialSchubertFrame_raise_dimension ht G
    exact ⟨U, H, fun μ a => (hH μ a).trans (hG μ a)⟩

theorem polynomialSchubertFrame_exists_le_dimension {n m : ℕ} {τ : YoungDiagram}
    (hτ : PartitionFits m τ) (hn : m ≤ n) {V : Submodule ℂ (Polynomial ℂ)}
    (F : PolynomialSchubertFrame n τ V) :
    ∃ (W : Submodule ℂ (Polynomial ℂ)) (G : PolynomialSchubertFrame m τ W),
      ∀ μ a, normalizedPartitionMinor τ G.polynomials μ a =
        normalizedPartitionMinor τ F.polynomials μ a := by
  induction n, hn using Nat.le_induction generalizing V with
  | base => exact ⟨V, F, fun _ _ => rfl⟩
  | succ n hn ih =>
    have ht : PartitionFits n τ := hτ.rowLen_eq_zero (by omega)
    obtain ⟨W, G, hG⟩ := polynomialSchubertFrame_lower_dimension ht F
    obtain ⟨U, H, hH⟩ := ih G
    exact ⟨U, H, fun μ a => (hH μ a).trans (hG μ a)⟩

/-- All Schubert dimensions accommodating the shape have exactly the same
    normalized coordinate data under the proved primitive/derivative transfer.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomialSchubertFrame_exists_dimension {n m : ℕ} {τ : YoungDiagram}
    (hn : PartitionFits n τ) (hm : PartitionFits m τ)
    {V : Submodule ℂ (Polynomial ℂ)} (F : PolynomialSchubertFrame n τ V) :
    ∃ (W : Submodule ℂ (Polynomial ℂ)) (G : PolynomialSchubertFrame m τ W),
      ∀ μ a, normalizedPartitionMinor τ G.polynomials μ a =
        normalizedPartitionMinor τ F.polynomials μ a := by
  by_cases h : n ≤ m
  · exact polynomialSchubertFrame_exists_ge_dimension hn h F
  · exact polynomialSchubertFrame_exists_le_dimension hm (Nat.le_of_not_ge h) F

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialSchubertFrame_exists_dimension