import ModifiedCartan.ZeroSharpRealRoots

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_real_rolle {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) {a b : ℝ} (hab : a < b)
    (ha : f (a : ℂ) = 0) (hb : f (b : ℂ) = 0) :
    ∃ c ∈ Ioo a b, deriv f (c : ℂ) = 0 := by
  obtain ⟨c, hc, hd⟩ := exists_hasDerivAt_eq_zero hab
    ((Complex.continuous_re.comp (hf.continuous.comp Complex.continuous_ofReal)).continuousOn)
    (show (f (a : ℂ)).re = (f (b : ℂ)).re by rw [ha, hb])
    (fun x _ => (hf (x : ℂ)).hasDerivAt.real_of_complex)
  refine ⟨c, hc, Complex.ext hd ?_⟩
  exact entire_deriv_real hf hreal c

theorem exists_interlacing_derivative_roots {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    {x : ℕ → ℝ} (hx : StrictAnti x) (hroot : ∀ j, f (x j : ℂ) = 0) :
    ∃ y : ℕ → ℝ, StrictAnti y ∧
      ∀ j, x (j + 1) < y j ∧ y j < x j ∧ deriv f (y j : ℂ) = 0 := by
  have he (j : ℕ) := entire_real_rolle hf hreal (hx (Nat.lt_succ_self j))
    (hroot (j + 1)) (hroot j)
  choose y hy hz using he
  refine ⟨y, strictAnti_nat_of_succ_lt (fun j => ?_), fun j => ⟨(hy j).1, (hy j).2, hz j⟩⟩
  exact (hy (j + 1)).2.trans (hy j).1

/-- Direct Rolle construction for LaTeX `prop:sharpness-zero`.
The selected roots are actual roots of the entire derivative. -/
theorem zeroSharp_derivative_root_sequence (m : ℕ) :
    ∃ x : ℕ → ℝ, StrictAnti x ∧ ∀ j,
      -Real.exp ((j + m + 1 : ℕ) : ℝ) ≤ x j ∧
      x j ≤ -Real.exp ((j + 1 : ℕ) : ℝ) ∧
      iteratedDeriv m zeroSharpFunction (x j : ℂ) = 0 := by
  induction m with
  | zero =>
    refine ⟨fun j => -Real.exp ((j + 1 : ℕ) : ℝ), ?_, ?_⟩
    · apply strictAnti_nat_of_succ_lt
      intro j
      apply neg_lt_neg (Real.exp_lt_exp.mpr ?_)
      exact_mod_cast Nat.lt_succ_self (j + 1)
    · intro j
      simp only [Nat.add_zero, le_refl, iteratedDeriv_zero, true_and]
      exact zeroSharp_real_root j
  | succ m ih =>
    obtain ⟨x, hx, hroot⟩ := ih
    obtain ⟨y, hy, hyroot⟩ := exists_interlacing_derivative_roots
      (zeroSharpFunction_iteratedDeriv_entire m)
      (zeroSharpFunction_iteratedDeriv_real m) hx (fun j => (hroot j).2.2)
    refine ⟨y, hy, fun j => ⟨?_, ?_, ?_⟩⟩
    · have hb := (hroot (j + 1)).1.trans (hyroot j).1.le
      simpa only [Nat.add_assoc, Nat.add_comm 1 m] using hb
    · exact (hyroot j).2.1.le.trans (hroot j).2.1
    · rw [iteratedDeriv_succ]
      exact (hyroot j).2.2

end ModifiedCartan
#print axioms ModifiedCartan.zeroSharp_derivative_root_sequence
