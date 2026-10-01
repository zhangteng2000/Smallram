import ModifiedCartan.FrobeniusAlternantOrthogonality
import ModifiedCartan.FrobeniusHeightVanishing

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

abbrev FittingSizedYoungDiagram (n m : ℕ) :=
  {μ : SizedYoungDiagram n // μ.val.colLen 0 ≤ m}

theorem frobeniusAlternantCoefficient_zero_of_height {m : ℕ} (μ ν : YoungDiagram)
    (hν : m < ν.colLen 0) : frobeniusAlternantCoefficient m μ ν = 0 := by
  simp [frobeniusAlternantCoefficient, finiteFrobeniusPolynomial_eq_zero_of_height ν hν]

theorem fittingFrobeniusAlternantCoefficient_orthogonality {m n : ℕ}
    (μ ν : FittingSizedYoungDiagram n m) :
    (∑ κ : FittingSizedYoungDiagram n m,
      frobeniusAlternantCoefficient m μ.val.val κ.val.val *
        frobeniusAlternantCoefficient m ν.val.val κ.val.val) = if μ = ν then 1 else 0 := by
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun τ : SizedYoungDiagram n => τ.val.colLen 0 ≤ m)
    (fun τ => frobeniusAlternantCoefficient m μ.val.val τ.val *
      frobeniusAlternantCoefficient m ν.val.val τ.val)
  have hz : (∑ τ : {τ : SizedYoungDiagram n // ¬τ.val.colLen 0 ≤ m},
      frobeniusAlternantCoefficient m μ.val.val τ.val.val *
        frobeniusAlternantCoefficient m ν.val.val τ.val.val) = 0 := by
    apply Finset.sum_eq_zero
    intro τ _
    rw [frobeniusAlternantCoefficient_zero_of_height _ _ (Nat.lt_of_not_ge τ.property), zero_mul]
  rw [hz, add_zero] at hs
  rw [hs]
  simpa only [Subtype.ext_iff] using
    frobeniusAlternantCoefficient_orthogonality μ.val ν.val μ.property ν.property

theorem fittingFrobeniusAlternantCoefficient_identity {m n : ℕ}
    (μ ν : FittingSizedYoungDiagram n m) :
    frobeniusAlternantCoefficient m μ.val.val ν.val.val = if μ = ν then 1 else 0 := by
  refine weighted_triangular_orthogonal_identity
    (fun τ : FittingSizedYoungDiagram n m => partitionRowWeight τ.val.val)
    (fun ρ τ : FittingSizedYoungDiagram n m => frobeniusAlternantCoefficient m ρ.val.val τ.val.val)
      ?_ ?_ ?_ μ ν
  · intro ρ τ hw hne
    exact finiteVandermondeFrobenius_coeff_zero_of_le_ne τ.val.val ρ.val.val ρ.property hw
      (fun he => hne (Subtype.ext (Subtype.ext he)))
  · exact fittingFrobeniusAlternantCoefficient_orthogonality
  · intro ρ
    exact finiteVandermondeFrobenius_diagonal_nat ρ.val.val ρ.property

/-- All finite alphabet coefficients, including the vanishing columns whose
    partitions do not fit. Auxiliary to paper `lem:KP-correspondence`. -/
theorem frobeniusAlternantCoefficient_identity {m n : ℕ}
    (μ ν : SizedYoungDiagram n) (hμ : μ.val.colLen 0 ≤ m) :
    frobeniusAlternantCoefficient m μ.val ν.val = if μ = ν then 1 else 0 := by
  by_cases hν : ν.val.colLen 0 ≤ m
  · simpa only [Subtype.ext_iff] using
      fittingFrobeniusAlternantCoefficient_identity
        (⟨μ, hμ⟩ : FittingSizedYoungDiagram n m) (⟨ν, hν⟩ : FittingSizedYoungDiagram n m)
  · have hne : μ ≠ ν := by rintro rfl; exact hν hμ
    rw [frobeniusAlternantCoefficient_zero_of_height _ _ (Nat.lt_of_not_ge hν), ite_eq_right hne]

end
end ModifiedCartan

#print axioms ModifiedCartan.frobeniusAlternantCoefficient_identity
