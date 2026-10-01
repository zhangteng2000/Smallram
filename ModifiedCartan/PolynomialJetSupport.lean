import ModifiedCartan.PolynomialAlternantMinors
import ModifiedCartan.PolynomialMinorBasisChange

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- A derivative determinant whose total order exceeds the top degree profile
    vanishes whenever the partition coordinates outside that profile vanish.
    Auxiliary to the Schubert-shape step of `lem:KP-correspondence`. -/
theorem polynomialJetDet_zero_of_order_sum_gt {n : ℕ} (τ : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ) (a : ℂ)
    (hp : ∀ μ : YoungDiagram, ¬ μ ≤ τ → (partitionPolynomialMinor μ p).eval a = 0)
    (e : Fin (n + 1) → ℕ)
    (he : (∑ i, partitionMinorOrders n τ i) < ∑ i, e i) :
    Matrix.det (fun i j : Fin (n + 1) => (Polynomial.derivative^[e i] (p j)).eval a) = 0 := by
  by_cases hi : Function.Injective e
  · obtain ⟨σ, hσ⟩ := exists_perm_strictAnti e hi
    obtain ⟨μ, hμ, hμe⟩ := exists_partitionAlternantExponent (e ∘ σ) hσ
    have hf : PartitionFits n μ := (partitionFits_iff_height_le μ).mpr hμ
    let θ : Equiv.Perm (Fin (n + 1)) := Fin.revPerm.trans σ
    have hθ (i : Fin (n + 1)) : e (θ i) = partitionMinorOrders n μ i := by
      have h := congrFun hμe i.rev
      rw [partitionAlternantExponent_rev] at h
      exact h.symm
    have hs : (∑ i, e i) = ∑ i, partitionMinorOrders n μ i := by
      rw [← Equiv.sum_comp θ e]
      exact Finset.sum_congr rfl (fun i _ => hθ i)
    have hn : ¬ μ ≤ τ := by
      intro hl
      have ho := (partition_le_iff_minorOrders_le hf).mp hl
      have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ho i)
      rw [hs] at he
      exact (not_lt_of_ge hh) he
    have hz := hp μ hn
    rw [partitionPolynomialMinor_of_fits hf, polynomialDerivativeMinor_eval] at hz
    have hd := Matrix.det_permute θ (fun i j : Fin (n + 1) =>
      (Polynomial.derivative^[e i] (p j)).eval a)
    have hd' : Matrix.det (fun i j : Fin (n + 1) =>
        (Polynomial.derivative^[partitionMinorOrders n μ i] (p j)).eval a) =
        ((Equiv.Perm.sign θ : ℤ) : ℂ) * Matrix.det (fun i j : Fin (n + 1) =>
          (Polynomial.derivative^[e i] (p j)).eval a) := by
      convert hd using 1
      apply congrArg Matrix.det
      funext i j
      change (Polynomial.derivative^[partitionMinorOrders n μ i] (p j)).eval a =
        (Polynomial.derivative^[e (θ i)] (p j)).eval a
      rw [hθ]
    erw [hz] at hd'
    exact (mul_eq_zero.mp hd'.symm).resolve_left
      (by exact_mod_cast (Equiv.Perm.sign θ).ne_zero)
  · obtain ⟨i, j, hij, hne⟩ : ∃ i j, e i = e j ∧ i ≠ j := by
      simpa only [Function.Injective, not_forall, exists_prop] using hi
    apply Matrix.det_zero_of_row_eq hne
    funext k
    rw [hij]

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialJetDet_zero_of_order_sum_gt