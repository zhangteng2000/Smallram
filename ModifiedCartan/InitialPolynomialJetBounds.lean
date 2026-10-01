import ModifiedCartan.ReplacedMinorOrders
import ModifiedCartan.PolynomialJetDegreeProfile
import ModifiedCartan.UniversalPolynomialMinors

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Replacing row j in an identity jet matrix realizes the kth derivative
    as a partition minor, up to a sign of norm one. -/
theorem identityJet_exists_minor_norm {n : ℕ} (p : Fin (n + 1) → Polynomial ℂ)
    (a : ℂ) (hp : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (p j)).eval a = if i = j then 1 else 0)
    (j : Fin (n + 1)) (k : ℕ) (hk : n < k) :
    ∃ μ : YoungDiagram, PartitionFits n μ ∧ partitionSize μ = k - j.val ∧
      ‖(partitionPolynomialMinor μ p).eval a‖ = ‖(Polynomial.derivative^[k] (p j)).eval a‖ := by
  obtain ⟨μ, hf, he⟩ := exists_partitionMinorOrders
    (sortedReplacementOrders n j k) (sortedReplacementOrders_strictMono j hk)
  refine ⟨μ, hf, sortedReplacementOrders_partitionSize j hf he, ?_⟩
  let σ := Fin.cycleIcc j (Fin.last n)
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Function.update
    (fun r l : Fin (n + 1) => (Polynomial.derivative^[r.val] (p l)).eval a) j
    (fun l => (Polynomial.derivative^[k] (p l)).eval a)
  have hm : U.submatrix σ id = Matrix.of (fun r l : Fin (n + 1) =>
      (Polynomial.derivative^[partitionMinorOrders n μ r] (p l)).eval a) := by
    funext r l
    change U (σ r) l = (Polynomial.derivative^[partitionMinorOrders n μ r] (p l)).eval a
    rw [congrFun he r, ← sortedReplacementOrders_cycle j r k]
    change U (σ r) l = (Polynomial.derivative^[Function.update
      (fun u : Fin (n + 1) => u.val) j k (σ r)] (p l)).eval a
    by_cases hr : σ r = j
    · simp only [U, hr, Function.update_self]
    · simp only [U, Function.update_of_ne hr]
  have hU : U = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).updateRow j
      (fun l => (Polynomial.derivative^[k] (p l)).eval a) := by
    have hM : (fun r l : Fin (n + 1) =>
        (Polynomial.derivative^[r.val] (p l)).eval a) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
      funext r l
      exact hp r l
    change Function.update _ j _ = _
    rw [hM]
    rfl
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [partitionPolynomialMinor_of_fits hf, polynomialDerivativeMinor_eval,
    ← hm, Matrix.det_permute, norm_mul, hs, one_mul, hU, matrix_det_updateRow_one]

theorem identityJet_polynomialWronskian_eval {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (a : ℂ)
    (hp : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (p j)).eval a = if i = j then 1 else 0) :
    (FewInflection.polynomialWronskian p).eval a = 1 := by
  rw [← polynomialDerivativeMinor_wronskian, polynomialDerivativeMinor_eval]
  have hm : Matrix.of (fun i j : Fin (n + 1) =>
      (Polynomial.derivative^[i.val] (p j)).eval a) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    funext i j
    exact hp i j
  rw [hm, Matrix.det_one]

/-- The high derivatives of a normalized initial basis satisfy the exact
    factorial/elementary-symmetric estimate used in `prop:initial-basis`. -/
theorem initialPolynomialBasis_jet_norm_le {M n : ℕ} {V : Submodule ℂ (Polynomial ℂ)}
    (b : Module.Basis (Fin (n + 1)) ℂ V) (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) (a : ℂ)
    (ha : (∏ i, (a - roots i)) ≠ 0)
    (hb : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval a = if i = j then 1 else 0)
    (j : Fin (n + 1)) (k : ℕ) (hk : n < k) :
    ‖(Polynomial.derivative^[k] (b j).val).eval a‖ ≤ ((k - j.val).factorial : ℝ) *
      FewInflection.elementarySymmetric (fun i => ‖a - roots i‖⁻¹) (k - j.val) := by
  obtain ⟨μ, hf, hs, he⟩ := identityJet_exists_minor_norm (fun j => (b j).val) a hb j k hk
  have h := Paper.eq_minor_es_bound b roots hW μ a ha
  rw [identityJet_polynomialWronskian_eval _ a hb, div_one, hs, he] at h
  exact h

end
end ModifiedCartan

#print axioms ModifiedCartan.initialPolynomialBasis_jet_norm_le