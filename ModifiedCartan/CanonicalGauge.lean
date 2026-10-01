import ModifiedCartan.CanonicalCoefficients

open scoped BigOperators Topology
open Filter Set

namespace ModifiedCartan
noncomputable section

theorem exists_canonical_gauge_nhds {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hW : FewInflection.wronskian n g z ≠ 0) :
    ∃ η : ℂ → ℂ, AnalyticAt ℂ η z ∧ (∀ w, η w ≠ 0) ∧
      (∀ᶠ w in 𝓝 z, η w ^ (n + 1) * FewInflection.wronskian n g w = 1) := by
  have he := (Filter.eventually_all.mpr (fun j => (hg j).eventually_analyticAt)).and
    ((FewInflection.analyticAt_wronskian hg).continuousAt.eventually_ne hW)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp he
  have hz : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  let : ContractibleSpace (Metric.ball z r) :=
    (convex_ball z r).contractibleSpace ⟨z, hz⟩
  have hc : IsSimplyConnected (Metric.ball z r) := SimplyConnectedSpace.ofContractible _
  obtain ⟨η, hη, hη0, hroot, _, _⟩ := FewInflection.exists_canonical_gauge
    hc Metric.isOpen_ball (fun j w hw => (hball w hw).1 j) (fun w hw => (hball w hw).2)
  refine ⟨η, hη z hz, hη0, ?_⟩
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  exact hroot w hw

theorem canonicalCoefficient_eq_normalized_nhds {n : ℕ} {g : Index n → ℂ → ℂ}
    {η : ℂ → ℂ} {z : ℂ} (hg : ∀ j, AnalyticAt ℂ (g j) z)
    (hη : AnalyticAt ℂ η z)
    (hroot : ∀ᶠ w in 𝓝 z, η w ^ (n + 1) * FewInflection.wronskian n g w = 1)
    (i : Index n) : canonicalCoefficient n g i z =
      FewInflection.fundamentalCoefficients n (fun j w => η w * g j w) z i := by
  have he := ((Filter.eventually_all.mpr (fun j => (hg j).eventually_analyticAt)).and
    hη.eventually_analyticAt).and hroot
  obtain ⟨U, hsub, hU, hz⟩ := eventually_nhds_iff.mp he
  apply canonicalCoefficient_eq_normalized hU (fun j w hw => (hsub w hw).1.1 j)
    (fun w hw => (hsub w hw).1.2) _ (fun w hw => (hsub w hw).2) i hz
  intro w hw hzero
  have hh := (hsub w hw).2
  simp [hzero] at hh

/-- The coefficient of `D^n` is zero in the explicit canonical operator.
LaTeX label: `eq:canonical`. -/
theorem canonicalCoefficient_last_eq_zero {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) :
    canonicalCoefficient n g (Fin.last n) z = 0 := by
  by_cases hW : FewInflection.wronskian n g z = 0
  · simp [canonicalCoefficient, hW]
  obtain ⟨η, hη, hη0, hroot⟩ := exists_canonical_gauge_nhds hg hW
  rw [canonicalCoefficient_eq_normalized_nhds hg hη hroot]
  apply FewInflection.fundamental_last_coefficient_eq_zero_of_wronskian_one
    (fun j => hη.mul (hg j))
  filter_upwards [hroot, hη.eventually_analyticAt,
    Filter.eventually_all.mpr (fun j => (hg j).eventually_analyticAt)] with w hw hηw hgw
  change FewInflection.wronskian n (fun j x => η x * g j x) w = 1
  rw [FewInflection.wronskian_scalar_mul η g w hηw.contDiffAt (fun j => (hgw j).contDiffAt)]
  exact hw

theorem canonicalCoefficient_scalar_mul {n : ℕ} {g : Index n → ℂ → ℂ}
    {s : ℂ → ℂ} {z : ℂ} (hg : ∀ j, AnalyticAt ℂ (g j) z)
    (hs : AnalyticAt ℂ s z) (hs0 : s z ≠ 0) (i : Index n) :
    canonicalCoefficient n (fun j w => s w * g j w) i z = canonicalCoefficient n g i z := by
  have hWsg := FewInflection.wronskian_scalar_mul s g z hs.contDiffAt
    (fun j => (hg j).contDiffAt)
  by_cases hW : FewInflection.wronskian n g z = 0
  · simp [canonicalCoefficient, hWsg, hW]
  obtain ⟨η, hη, hη0, hroot⟩ := exists_canonical_gauge_nhds hg hW
  have hquotroot : ∀ᶠ w in 𝓝 z, (η w / s w) ^ (n + 1) *
      FewInflection.wronskian n (fun j x => s x * g j x) w = 1 := by
    filter_upwards [hroot, hs.eventually_analyticAt, hs.continuousAt.eventually_ne hs0,
      Filter.eventually_all.mpr (fun j => (hg j).eventually_analyticAt)] with w hw hsw hs0w hgw
    rw [FewInflection.wronskian_scalar_mul s g w hsw.contDiffAt (fun j => (hgw j).contDiffAt),
      div_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hs0w)]
    exact hw
  rw [canonicalCoefficient_eq_normalized_nhds (fun j => hs.fun_mul (hg j))
    (hη.fun_div hs hs0) hquotroot, canonicalCoefficient_eq_normalized_nhds hg hη hroot]
  apply congrFun (fundamentalCoefficients_congr_nhds _) i
  intro j
  filter_upwards [hs.continuousAt.eventually_ne hs0] with w hw
  rw [← mul_assoc, div_mul_cancel₀ _ hw]

theorem fundamentalCoefficients_matrix {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (A : Matrix (Index n) (Index n) ℂ)
    (hA : A.det ≠ 0) (hW : FewInflection.wronskian n g z ≠ 0) :
    FewInflection.fundamentalCoefficients n (fun j w => ∑ k, g k w * A k j) z =
      FewInflection.fundamentalCoefficients n g z := by
  have hWg : FewInflection.wronskian n (fun j w => ∑ k, g k w * A k j) z ≠ 0 := by
    rw [FewInflection.wronskian_matrix_gauge g A z (fun _ j => (hg j).contDiffAt)]
    exact mul_ne_zero hW hA
  symm
  apply FewInflection.fundamentalCoefficients_unique hWg
  intro j
  have hderiv (m : ℕ) :
      iteratedDeriv m (fun w => ∑ k, g k w * A k j) z =
        ∑ k, iteratedDeriv m (g k) z * A k j := by
    rw [iteratedDeriv_fun_sum]
    · simp only [iteratedDeriv_mul_const_field]
    · intro k _
      simpa [smul_eq_mul] using (hg k).contDiffAt.smul_const (A k j)
  rw [hderiv (n + 1)]
  simp_rw [hderiv]
  have hsum : (∑ k : Index n,
      (iteratedDeriv (n + 1) (g k) z +
        ∑ i, FewInflection.fundamentalCoefficients n g z i *
          iteratedDeriv (i : ℕ) (g k) z) * A k j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [FewInflection.fundamentalCoefficients_spec hW k, zero_mul]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul] at hsum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simpa only [mul_assoc] using hsum

theorem canonicalCoefficient_matrix {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (A : Matrix (Index n) (Index n) ℂ)
    (hA : A.det ≠ 0) (i : Index n) :
    canonicalCoefficient n (fun j w => ∑ k, g k w * A k j) i z =
      canonicalCoefficient n g i z := by
  have hWg := FewInflection.wronskian_matrix_gauge g A z (fun _ j => (hg j).contDiffAt)
  by_cases hW : FewInflection.wronskian n g z = 0
  · simp [canonicalCoefficient, hWg, hW]
  obtain ⟨η, hη, hη0, hroot⟩ := exists_canonical_gauge_nhds hg hW
  let c : ℂ := Complex.exp (-Complex.log A.det / (n + 1 : ℂ))
  have hc : c ^ (n + 1) = A.det⁻¹ := by
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    dsimp [c]
    rw [← Complex.exp_nat_mul]
    push_cast
    rw [mul_div_cancel₀ _ hn, Complex.exp_neg, Complex.exp_log hA]
  have hc0 : c ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (Nat.succ_ne_zero n)] at hc
    exact (inv_ne_zero hA) hc.symm
  have hcroot : ∀ᶠ w in 𝓝 z, (c * η w) ^ (n + 1) *
      FewInflection.wronskian n (fun j x => ∑ k, g k x * A k j) w = 1 := by
    filter_upwards [hroot, Filter.eventually_all.mpr
      (fun j => (hg j).eventually_analyticAt)] with w hw hgw
    rw [FewInflection.wronskian_matrix_gauge g A w (fun _ j => (hgw j).contDiffAt)]
    calc
      (c * η w) ^ (n + 1) * (FewInflection.wronskian n g w * A.det) =
          (c ^ (n + 1) * A.det) * (η w ^ (n + 1) * FewInflection.wronskian n g w) := by
        rw [mul_pow]
        ring
      _ = 1 := by rw [hc, inv_mul_cancel₀ hA, hw, mul_one]
  have hga : ∀ j, AnalyticAt ℂ (fun w => ∑ k, g k w * A k j) z := by
    intro j
    apply Finset.analyticAt_fun_sum
    intro k _
    exact (hg k).fun_mul analyticAt_const
  rw [canonicalCoefficient_eq_normalized_nhds hga (analyticAt_const.fun_mul hη) hcroot,
    canonicalCoefficient_eq_normalized_nhds hg hη hroot]
  have hnorm : FewInflection.wronskian n (fun j w => η w * g j w) z ≠ 0 := by
    rw [FewInflection.wronskian_scalar_mul η g z hη.contDiffAt (fun j => (hg j).contDiffAt)]
    exact mul_ne_zero (pow_ne_zero _ (hη0 z)) hW
  have hscaled : FewInflection.wronskian n (fun j w => c * (η w * g j w)) z ≠ 0 := by
    rw [FewInflection.wronskian_const_gauge _ c z (fun _ j => (hη.fun_mul (hg j)).contDiffAt)]
    exact mul_ne_zero (pow_ne_zero _ hc0) hnorm
  calc
    FewInflection.fundamentalCoefficients n
        (fun j w => c * η w * ∑ k, g k w * A k j) z i =
        FewInflection.fundamentalCoefficients n
          (fun j w => ∑ k, (c * (η w * g k w)) * A k j) z i := by
      apply congrFun (fundamentalCoefficients_congr_nhds _) i
      intro j
      filter_upwards [] with w
      simp only [Finset.mul_sum, mul_assoc]
    _ = FewInflection.fundamentalCoefficients n (fun j w => c * (η w * g j w)) z i :=
      congrFun (fundamentalCoefficients_matrix (fun j => analyticAt_const.fun_mul
        (hη.fun_mul (hg j))) A hA hscaled) i
    _ = FewInflection.fundamentalCoefficients n (fun j w => η w * g j w) z i :=
      congrFun (FewInflection.fundamentalCoefficients_const_mul
        (fun j => hη.fun_mul (hg j)) hc0 hnorm) i

end
end ModifiedCartan

