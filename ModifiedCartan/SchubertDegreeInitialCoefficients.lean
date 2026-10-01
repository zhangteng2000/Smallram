import ModifiedCartan.SchubertCoordinates
import ModifiedCartan.SizedYoungDiagrams
import ModifiedCartan.PolynomialODEAdjugate
import FewInflection.PolynomialJets

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Every polynomial in an actual Schubert space satisfies the degree bound
    needed in the finite coefficient reconstruction for `lem:KP-correspondence`. -/
theorem PolynomialSchubertFrame.natDegree_le {n : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (F : PolynomialSchubertFrame n τ V) (p : V) :
    p.val.natDegree ≤ n + partitionSize τ := by
  have he : (∑ i, F.basis.repr p i • (F.basis i).val) = p.val := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg (fun u : V => u.val) (F.basis.sum_repr p)
  rw [← he]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_smul_le _ _).trans
  rw [F.degree_eq, partitionMinorOrders]
  exact Nat.add_le_add (by have hi := i.isLt; omega) (partition_rowLen_le_size τ _)

theorem polynomialSchubertCell_natDegree_le {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ) (p : V) :
    p.val.natDegree ≤ n + partitionSize τ :=
  (schubertFrame hV).natDegree_le p

/-- The initial coefficient vector of an identity-jet tuple is explicit. -/
theorem polynomial_identityJets_initialCoefficients {N D : ℕ}
    (p : Fin N → Polynomial ℂ)
    (hp : ∀ i j : Fin N,
      (Polynomial.derivative^[i.val] (p j)).eval 0 = if i = j then 1 else 0)
    (j : Fin N) (r : Fin D) :
    (if r.val < N then (p j).coeff r.val else 0) =
      if r.val = j.val then ((j.val.factorial : ℂ)⁻¹) else 0 := by
  by_cases h : r.val = j.val
  · rw [h, if_pos j.isLt, if_pos rfl,
      FewInflection.polynomial_coeff_eq_jet, FewInflection.iteratedDeriv_polynomial_eval,
      hp, if_pos rfl, one_div]
  · rw [if_neg h]
    by_cases hr : r.val < N
    · rw [if_pos hr, FewInflection.polynomial_coeff_eq_jet,
        FewInflection.iteratedDeriv_polynomial_eval]
      have hne : (⟨r.val, hr⟩ : Fin N) ≠ j := by
        intro he
        exact h (congrArg Fin.val he)
      change (Polynomial.derivative^[(⟨r.val, hr⟩ : Fin N).val] (p j)).eval 0 /
        (r.val.factorial : ℂ) = 0
      rw [hp, if_neg hne, zero_div]
    · rw [if_neg hr]

/-- Adjugate reconstruction of every bounded-degree identity-jet solution.
    Auxiliary to the exact algebra equality in `lem:KP-correspondence`. -/
theorem polynomialODE_identityJets_adjugate_solution {N D : ℕ}
    (c : Fin (N + 1) → Polynomial ℂ) (p : Fin N → Polynomial ℂ)
    (hp : ∀ i j : Fin N,
      (Polynomial.derivative^[i.val] (p j)).eval 0 = if i = j then 1 else 0)
    (hd : ∀ j, (p j).natDegree < D)
    (hsol : ∀ j, (∑ i : Fin (N + 1), c i * Polynomial.derivative^[i.val] (p j)) = 0)
    (j : Fin N) :
    Polynomial.ofFn D ((polynomialODEJetMatrix N D c).adjugate.mulVec
      (fun r : Fin D => if r.val = j.val then ((j.val.factorial : ℂ)⁻¹) else 0)) =
      (polynomialODEJetMatrix N D c).det • p j := by
  have hv : (fun r : Fin D => if r.val < N then (p j).coeff r.val else 0) =
      (fun r : Fin D => if r.val = j.val then ((j.val.factorial : ℂ)⁻¹) else 0) := by
    funext r
    exact polynomial_identityJets_initialCoefficients p hp j r
  rw [← hv]
  exact polynomialODEJetMatrix_ofFn_adjugate_solution c (p j) (hd j) (hsol j)

end
end ModifiedCartan

#print axioms ModifiedCartan.PolynomialSchubertFrame.natDegree_le
#print axioms ModifiedCartan.polynomialODE_identityJets_adjugate_solution
