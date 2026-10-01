import ModifiedCartan.CanonicalGauge

open scoped BigOperators Topology
open Filter Set

namespace ModifiedCartan
noncomputable section

theorem iteratedDeriv_dilate_at (t : ℂ) (m : ℕ) {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (t * z)) :
    iteratedDeriv m (fun w => f (t * w)) z = t ^ m * iteratedDeriv m f (t * z) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    have ht : ContinuousAt (fun w : ℂ => t * w) z := continuousAt_const.mul continuousAt_id
    have he : iteratedDeriv m (fun w => f (t * w)) =ᶠ[𝓝 z]
        (fun w => t ^ m * iteratedDeriv m f (t * w)) := by
      filter_upwards [ht.tendsto.eventually hf.eventually_analyticAt] with w hw
      exact ih hw
    have hd : deriv (fun w => iteratedDeriv m f (t * w)) z =
        deriv (iteratedDeriv m f) (t * z) * t :=
      ((FewInflection.analyticAt_iteratedDeriv hf m).differentiableAt.hasDerivAt.comp z
        (hasDerivAt_const_mul t)).deriv
    rw [iteratedDeriv_succ, he.deriv_eq, deriv_const_mul_field, hd, iteratedDeriv_succ, pow_succ]
    ring

theorem wronskian_dilate_at {n : ℕ} {g : Index n → ℂ → ℂ} {t z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) (t * z)) :
    FewInflection.wronskian n (fun j w => g j (t * w)) z =
      t ^ (∑ i : Index n, (i : ℕ)) * FewInflection.wronskian n g (t * z) := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun i j => iteratedDeriv i (g j) (t * z)
  let D : Matrix (Index n) (Index n) ℂ := Matrix.diagonal (fun i => t ^ (i : ℕ))
  have hM : (fun (i j : Index n) => iteratedDeriv i (fun w => g j (t * w)) z) = D * M := by
    funext i j
    rw [Matrix.diagonal_mul]
    exact iteratedDeriv_dilate_at t i (hg j)
  calc
    FewInflection.wronskian n (fun j w => g j (t * w)) z = (D * M).det := by
      simp only [FewInflection.wronskian, hM]
    _ = D.det * M.det := Matrix.det_mul _ _
    _ = (∏ i : Index n, t ^ (i : ℕ)) * FewInflection.wronskian n g (t * z) := by
      rw [Matrix.det_diagonal]
      rfl
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum]

theorem fundamentalCoefficients_dilate_at {n : ℕ} {g : Index n → ℂ → ℂ} {t z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) (t * z)) (ht : t ≠ 0)
    (hW : FewInflection.wronskian n g (t * z) ≠ 0) :
    FewInflection.fundamentalCoefficients n (fun j w => g j (t * w)) z =
      (fun i : Index n => t ^ (n + 1 - (i : ℕ)) *
        FewInflection.fundamentalCoefficients n g (t * z) i) := by
  have hWd : FewInflection.wronskian n (fun j w => g j (t * w)) z ≠ 0 := by
    rw [wronskian_dilate_at hg]
    exact mul_ne_zero (pow_ne_zero _ ht) hW
  symm
  apply FewInflection.fundamentalCoefficients_unique hWd
  intro j
  rw [iteratedDeriv_dilate_at t (n + 1) (hg j)]
  simp_rw [iteratedDeriv_dilate_at t _ (hg j)]
  have hsum : (∑ i : Index n, (t ^ (n + 1 - (i : ℕ)) *
      FewInflection.fundamentalCoefficients n g (t * z) i) *
      (t ^ (i : ℕ) * iteratedDeriv (i : ℕ) (g j) (t * z))) =
        t ^ (n + 1) * ∑ i : Index n,
          FewInflection.fundamentalCoefficients n g (t * z) i *
            iteratedDeriv (i : ℕ) (g j) (t * z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i : ℕ) ≤ n + 1 := Nat.le_of_lt i.isLt
    calc
      _ = (t ^ (n + 1 - (i : ℕ)) * t ^ (i : ℕ)) *
          (FewInflection.fundamentalCoefficients n g (t * z) i *
            iteratedDeriv (i : ℕ) (g j) (t * z)) := by ring
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel hi]
  rw [hsum]
  linear_combination t ^ (n + 1) * FewInflection.fundamentalCoefficients_spec hW j

/-- Canonical coefficients under any nonzero complex dilation. The manuscript
uses the specialization to positive real dilation factors. -/
theorem canonicalCoefficient_dilate {n : ℕ} {g : Index n → ℂ → ℂ} {t z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) (t * z)) (ht : t ≠ 0) (i : Index n) :
    canonicalCoefficient n (fun j w => g j (t * w)) i z =
      t ^ (n + 1 - (i : ℕ)) * canonicalCoefficient n g i (t * z) := by
  by_cases hW : FewInflection.wronskian n g (t * z) = 0
  · simp [canonicalCoefficient, wronskian_dilate_at hg, hW]
  obtain ⟨η, hη, hη0, hroot⟩ := exists_canonical_gauge_nhds hg hW
  let p : ℕ := ∑ k : Index n, (k : ℕ)
  let c : ℂ := Complex.exp (-Complex.log (t ^ p) / (n + 1 : ℂ))
  have hp : t ^ p ≠ 0 := pow_ne_zero _ ht
  have hc : c ^ (n + 1) = (t ^ p)⁻¹ := by
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    dsimp [c]
    rw [← Complex.exp_nat_mul]
    push_cast
    rw [mul_div_cancel₀ _ hn, Complex.exp_neg, Complex.exp_log hp]
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hta : AnalyticAt ℂ (fun w : ℂ => t * w) z := analyticAt_const.fun_mul analyticAt_id
  have hgd : ∀ j, AnalyticAt ℂ (fun w => g j (t * w)) z := fun j => (hg j).fun_comp hta
  have hηd : AnalyticAt ℂ (fun w => c * η (t * w)) z :=
    analyticAt_const.fun_mul (hη.fun_comp hta)
  have hdroot : ∀ᶠ w in 𝓝 z, (c * η (t * w)) ^ (n + 1) *
      FewInflection.wronskian n (fun j x => g j (t * x)) w = 1 := by
    filter_upwards [hta.continuousAt.tendsto.eventually hroot,
      hta.continuousAt.tendsto.eventually
        (Filter.eventually_all.mpr (fun j => (hg j).eventually_analyticAt))] with w hw hgw
    rw [wronskian_dilate_at hgw]
    change (c * η (t * w)) ^ (n + 1) * (t ^ p * FewInflection.wronskian n g (t * w)) = 1
    calc
      _ = (c ^ (n + 1) * t ^ p) * (η (t * w) ^ (n + 1) *
          FewInflection.wronskian n g (t * w)) := by rw [mul_pow]; ring
      _ = 1 := by rw [hc, inv_mul_cancel₀ hp, hw, mul_one]
  have hgn : ∀ j, AnalyticAt ℂ (fun w => η w * g j w) (t * z) :=
    fun j => hη.fun_mul (hg j)
  have hWn : FewInflection.wronskian n (fun j w => η w * g j w) (t * z) ≠ 0 := by
    rw [FewInflection.wronskian_scalar_mul η g (t * z) hη.contDiffAt
      (fun j => (hg j).contDiffAt)]
    exact mul_ne_zero (pow_ne_zero _ (hη0 (t * z))) hW
  have hWnd : FewInflection.wronskian n (fun j w => η (t * w) * g j (t * w)) z ≠ 0 := by
    rw [wronskian_dilate_at hgn]
    exact mul_ne_zero hp hWn
  rw [canonicalCoefficient_eq_normalized_nhds hgd hηd hdroot,
    canonicalCoefficient_eq_normalized_nhds hg hη hroot]
  simp only [mul_assoc]
  rw [FewInflection.fundamentalCoefficients_const_mul
    (fun j => (hgn j).fun_comp hta) hc0 hWnd]
  exact congrFun (fundamentalCoefficients_dilate_at hgn ht hWn) i

/-- LaTeX label: `eq:scalecoeff`; internal index `i` corresponds to `q=n+1-i`. -/
theorem Paper.eq_scalecoeff {n : ℕ} {g : Index n → ℂ → ℂ} {t : ℝ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) ((t : ℂ) * z)) (ht : 0 < t) (i : Index n) :
    canonicalCoefficient n (fun j w => g j ((t : ℂ) * w)) i z =
      (t : ℂ) ^ (n + 1 - (i : ℕ)) * canonicalCoefficient n g i ((t : ℂ) * z) :=
  canonicalCoefficient_dilate hg (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)) i

end
end ModifiedCartan

