import ModifiedCartan.InitialPolynomialJetBounds

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

theorem elementarySymmetric_nonneg {M : ℕ} (x : Fin M → ℝ)
    (hx : ∀ i, 0 ≤ x i) (s : ℕ) : 0 ≤ FewInflection.elementarySymmetric x s := by
  unfold FewInflection.elementarySymmetric
  exact Finset.sum_nonneg (fun I _ => Finset.prod_nonneg (fun i _ => hx i))

theorem initialPolynomialBasis_taylorCoeff_zero_of_lt {n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b : Module.Basis (Fin (n + 1)) ℂ V) (a : ℂ)
    (hb : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval a = if i = j then 1 else 0)
    (j : Fin (n + 1)) (k : ℕ) (hk : k < j.val) :
    ((b j).val.taylor a).coeff k = 0 := by
  let i : Fin (n + 1) := ⟨k, hk.trans j.isLt⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i] at this; omega
  have he : (Polynomial.derivative^[k] (b j).val).eval a = 0 := by
    simpa only [i, ite_eq_right hij] using hb i j
  rw [FewInflection.polynomial_taylor_coeff_eq_jet, FewInflection.iteratedDeriv_polynomial_eval,
    he, zero_div]

/-- Exact Taylor coefficient majorant for a normalized polynomial initial
    basis, including its prescribed low-order jets. -/
theorem initialPolynomialBasis_taylorCoeff_norm_le {M n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b : Module.Basis (Fin (n + 1)) ℂ V)
    (roots : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) (a : ℂ)
    (ha : (∏ i, (a - roots i)) ≠ 0)
    (hb : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval a = if i = j then 1 else 0)
    (j : Fin (n + 1)) (s : ℕ) :
    ‖((b j).val.taylor a).coeff (j.val + s)‖ ≤
      (1 / (j.val.factorial : ℝ)) *
        FewInflection.elementarySymmetric (fun i => ‖a - roots i‖⁻¹) s := by
  let C := FewInflection.elementarySymmetric (fun i => ‖a - roots i‖⁻¹) s
  have hC : 0 ≤ C := elementarySymmetric_nonneg _ (fun i => inv_nonneg.mpr (norm_nonneg _)) s
  rw [FewInflection.polynomial_taylor_coeff_eq_jet, FewInflection.iteratedDeriv_polynomial_eval,
    norm_div, norm_natCast]
  by_cases hs : s = 0
  · subst s
    simp only [add_zero, hb, ite_true, norm_one, FewInflection.elementarySymmetric_zero, mul_one, le_refl]
  · by_cases hk : j.val + s ≤ n
    · let i : Fin (n + 1) := ⟨j.val + s, by omega⟩
      have hij : i ≠ j := by intro h; have he := congrArg Fin.val h; dsimp [i] at he; omega
      have he : (Polynomial.derivative^[j.val + s] (b j).val).eval a = 0 := by
        simpa only [i, ite_eq_right hij] using hb i j
      rw [he, norm_zero, zero_div]
      exact mul_nonneg (by positivity) hC
    · have he : ‖(Polynomial.derivative^[j.val + s] (b j).val).eval a‖ ≤ (s.factorial : ℝ) * C := by
        simpa only [Nat.add_sub_cancel_left] using
          initialPolynomialBasis_jet_norm_le b roots hW a ha hb j (j.val + s) (by omega)
      have hjf : (0 : ℝ) < (j.val.factorial : ℝ) := by positivity
      have hkf : (0 : ℝ) < ((j.val + s).factorial : ℝ) := by positivity
      have hf : (j.val.factorial : ℝ) * (s.factorial : ℝ) ≤ ((j.val + s).factorial : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (j.val + s))
          (Nat.factorial_mul_factorial_dvd_factorial_add j.val s)
      calc
        _ ≤ C / (j.val.factorial : ℝ) := by
          apply (div_le_div_iff₀ hkf hjf).mpr
          calc
            _ ≤ ((s.factorial : ℝ) * C) * (j.val.factorial : ℝ) :=
              mul_le_mul_of_nonneg_right he hjf.le
            _ = C * ((j.val.factorial : ℝ) * (s.factorial : ℝ)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hf hC
        _ = _ := by dsimp [C]; ring

end
end ModifiedCartan

#print axioms ModifiedCartan.initialPolynomialBasis_taylorCoeff_norm_le