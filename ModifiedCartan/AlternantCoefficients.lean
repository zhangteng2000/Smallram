import ModifiedCartan.FiniteAlternants

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteExponent_injective {m : ℕ} :
    Function.Injective (finiteExponent (m := m)) := by
  intro e f h
  funext i
  exact congrArg (fun d : Fin m →₀ ℕ => d i) h

theorem strictAnti_comp_perm_eq {m : ℕ} (e f : Fin m → ℕ)
    (he : StrictAnti e) (hf : StrictAnti f) (σ : Equiv.Perm (Fin m))
    (h : e ∘ σ = f) : σ = 1 ∧ e = f := by
  have hs : StrictMono σ := by
    intro i j hij
    by_contra hn
    have hx : e (σ i) ≤ e (σ j) := he.antitone (le_of_not_gt hn)
    have hi := congrFun h i
    have hj := congrFun h j
    change e (σ i) = f i at hi
    change e (σ j) = f j at hj
    rw [hi, hj] at hx
    exact (not_le_of_gt (hf hij)) hx
  have hσ : σ = 1 := Equiv.ext (fun i => congrFun hs.eq_id i)
  exact ⟨hσ, by simpa [hσ] using h⟩

/-- Ordered exponent coefficients of the literal determinant alternant.
    Auxiliary to paper `lem:KP-correspondence`. -/
theorem finiteAlternant_coeff_strictAnti {m : ℕ} (e f : Fin m → ℕ)
    (he : StrictAnti e) (hf : StrictAnti f) :
    MvPolynomial.coeff (finiteExponent f) (finiteAlternant e) =
      if e = f then 1 else 0 := by
  rw [finiteAlternant, MvPolynomial.coeff_sum, Finset.sum_eq_single 1]
  · simp [MvPolynomial.coeff_monomial, finiteExponent_injective.eq_iff]
  · intro σ _ hσ
    have hn : finiteExponent (e ∘ σ) ≠ finiteExponent f := by
      intro h
      exact hσ (strictAnti_comp_perm_eq e f he hf σ (finiteExponent_injective h)).1
    simp [MvPolynomial.coeff_monomial, hn]
  · simp

def partitionAlternantExponent (m : ℕ) (μ : YoungDiagram) (i : Fin m) : ℕ :=
  μ.rowLen i.val + i.rev.val

theorem partitionAlternantExponent_strictAnti (m : ℕ) (μ : YoungDiagram) :
    StrictAnti (partitionAlternantExponent m μ) := by
  intro i j hij
  have hr := μ.rowLen_anti i.val j.val hij.le
  have hi := i.isLt
  have hj := j.isLt
  simp only [partitionAlternantExponent, Fin.val_rev]
  change i.val < j.val at hij
  omega

theorem finiteExponent_partitionAlternant (m : ℕ) (μ : YoungDiagram) :
    finiteExponent (partitionAlternantExponent m μ) =
      partitionFiniteDegree m μ + finiteStaircaseDegree m := by
  ext i
  rfl

theorem partitionAlternantExponent_injective {m : ℕ} (μ ν : YoungDiagram)
    (hμ : μ.colLen 0 ≤ m) (hν : ν.colLen 0 ≤ m)
    (h : partitionAlternantExponent m μ = partitionAlternantExponent m ν) : μ = ν := by
  apply partitionRowDegree_injective
  rw [← partitionFiniteDegree_mapDomain μ hμ, ← partitionFiniteDegree_mapDomain ν hν]
  congr 1
  ext i
  have hi := congrFun h i
  change μ.rowLen i.val + i.rev.val = ν.rowLen i.val + i.rev.val at hi
  exact Nat.add_right_cancel hi

theorem finiteAlternant_partition_coeff {m : ℕ} (μ ν : YoungDiagram)
    (hμ : μ.colLen 0 ≤ m) (hν : ν.colLen 0 ≤ m) :
    MvPolynomial.coeff (partitionFiniteDegree m ν + finiteStaircaseDegree m)
      (finiteAlternant (partitionAlternantExponent m μ)) = if μ = ν then 1 else 0 := by
  rw [← finiteExponent_partitionAlternant,
    finiteAlternant_coeff_strictAnti _ _ (partitionAlternantExponent_strictAnti m μ)
      (partitionAlternantExponent_strictAnti m ν)]
  have he : partitionAlternantExponent m μ = partitionAlternantExponent m ν ↔ μ = ν :=
    ⟨partitionAlternantExponent_injective μ ν hμ hν, congrArg (partitionAlternantExponent m)⟩
  simp only [he]

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteAlternant_partition_coeff
