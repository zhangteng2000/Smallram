import ModifiedCartan.PolynomialPrimitives
import ModifiedCartan.MinorDimensionStep
import ModifiedCartan.SchubertFrameReconstruction

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem polynomialSchubertFrame_raise_dimension {n : ℕ} {τ : YoungDiagram}
    (hτ : PartitionFits n τ) {V : Submodule ℂ (Polynomial ℂ)}
    (F : PolynomialSchubertFrame n τ V) :
    ∃ (W : Submodule ℂ (Polynomial ℂ)) (G : PolynomialSchubertFrame (n + 1) τ W),
      ∀ μ a, normalizedPartitionMinor τ G.polynomials μ a =
        normalizedPartitionMinor τ F.polynomials μ a := by
  let p : Fin (n + 2) → Polynomial ℂ := Fin.cons (Polynomial.C (1 : ℂ))
    (fun j => complexPolynomialPrimitive (F.polynomials j))
  have hm (μ : YoungDiagram) : partitionPolynomialMinor μ p =
      partitionPolynomialMinor μ F.polynomials := by
    rw [partitionPolynomialMinor_cons_constant]
    simp only [complexPolynomialPrimitive_derivative, Polynomial.C_1, one_mul]
  have ht : (partitionPolynomialMinor τ p).eval 0 ≠ 0 := by
    rw [hm]
    exact partitionPolynomialMinor_top_eval_ne_zero hτ F.polynomials
      F.polynomials_ne_zero F.degree_eq 0
  have hs : ∀ μ : YoungDiagram, ¬ μ ≤ τ → (partitionPolynomialMinor μ p).eval 0 = 0 := by
    intro μ hμ
    rw [hm, partitionPolynomialMinor_eq_zero_of_not_le μ τ F.polynomials
      (fun j => (F.degree_eq j).le) hμ, Polynomial.eval_zero]
  obtain ⟨W, G, hG⟩ := polynomialSchubertFrame_exists_of_minor_support τ
    (hτ.rowLen_eq_zero (by omega) : PartitionFits (n + 1) τ) p ht hs
  refine ⟨W, G, ?_⟩
  intro μ a
  rw [hG, normalizedPartitionMinor, hm, hm]
  rfl

/-- Differentiation removes the constant basis vector when the target dimension
    still accommodates the partition. Every normalized coordinate is preserved.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomialSchubertFrame_lower_dimension {n : ℕ} {τ : YoungDiagram}
    (hτ : PartitionFits n τ) {V : Submodule ℂ (Polynomial ℂ)}
    (F : PolynomialSchubertFrame (n + 1) τ V) :
    ∃ (W : Submodule ℂ (Polynomial ℂ)) (G : PolynomialSchubertFrame n τ W),
      ∀ μ a, normalizedPartitionMinor τ G.polynomials μ a =
        normalizedPartitionMinor τ F.polynomials μ a := by
  let c := (F.polynomials 0).coeff 0
  have hd : (F.polynomials 0).natDegree = 0 := by
    rw [show (F.polynomials 0).natDegree = partitionMinorOrders (n + 1) τ 0 from F.degree_eq 0,
      partitionMinorOrders_succ_zero]
    exact hτ
  have he0 : F.polynomials 0 = Polynomial.C c := Polynomial.eq_C_of_natDegree_le_zero hd.le
  have hc : c ≠ 0 := by
    intro hz
    rw [hz, Polynomial.C_0] at he0
    exact F.polynomials_ne_zero 0 he0
  let p : Fin (n + 1) → Polynomial ℂ := fun j => F.polynomials j.succ
  let q : Fin (n + 1) → Polynomial ℂ := fun j => (p j).derivative
  have he : F.polynomials = Fin.cons (Polynomial.C c) p := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact he0
    · rfl
  have hm (μ : YoungDiagram) : partitionPolynomialMinor μ F.polynomials =
      Polynomial.C c * partitionPolynomialMinor μ q := by
    rw [he]
    exact partitionPolynomialMinor_cons_constant μ p c
  have ht : (partitionPolynomialMinor τ q).eval 0 ≠ 0 := by
    have h := partitionPolynomialMinor_top_eval_ne_zero
      (hτ.rowLen_eq_zero (by omega) : PartitionFits (n + 1) τ) F.polynomials
      F.polynomials_ne_zero F.degree_eq 0
    rw [hm, Polynomial.eval_mul, Polynomial.eval_C] at h
    exact fun hz => h (by rw [hz, mul_zero])
  have hs : ∀ μ : YoungDiagram, ¬ μ ≤ τ → (partitionPolynomialMinor μ q).eval 0 = 0 := by
    intro μ hμ
    have hh := partitionPolynomialMinor_eq_zero_of_not_le μ τ F.polynomials
      (fun j => (F.degree_eq j).le) hμ
    rw [hm] at hh
    have hh' := congrArg (Polynomial.eval 0) hh
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero] at hh'
    exact (mul_eq_zero.mp hh').resolve_left hc
  obtain ⟨W, G, hG⟩ := polynomialSchubertFrame_exists_of_minor_support τ hτ q ht hs
  refine ⟨W, G, ?_⟩
  intro μ a
  rw [hG, he, normalizedPartitionMinor_cons_constant τ μ p c hc a]

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialSchubertFrame_raise_dimension
#print axioms ModifiedCartan.polynomialSchubertFrame_lower_dimension