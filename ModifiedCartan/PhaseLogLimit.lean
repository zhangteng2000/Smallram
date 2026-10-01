import ModifiedCartan.RegularizedLogBounds

open scoped Topology
open Filter Set MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def phaseLogScale (ν : ℕ) : ℝ := ((ν + 1 : ℕ) : ℝ)

theorem one_le_phaseLogScale (ν : ℕ) : 1 ≤ phaseLogScale ν := by
  dsimp only [phaseLogScale]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le ν)

theorem phaseLogScale_pos (ν : ℕ) : 0 < phaseLogScale ν := zero_lt_one.trans_le (one_le_phaseLogScale ν)

theorem phaseLogScale_tendsto : Tendsto phaseLogScale atTop atTop := by
  have hsucc : StrictMono (fun ν : ℕ => ν + 1) := fun _ _ h => Nat.add_lt_add_right h 1
  exact tendsto_natCast_atTop_atTop.comp hsucc.tendsto_atTop

noncomputable def phaseLogApprox (ν : ℕ) (z : ℂ) : ℂ :=
  -(phaseLogScale ν)⁻¹ • Complex.log ((Real.exp (-phaseLogScale ν) : ℂ) - z)

theorem phaseLogApprox_zero (ν : ℕ) : phaseLogApprox ν 0 = 1 := by
  rw [phaseLogApprox, sub_zero, ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  apply Complex.ext <;> simp [inv_mul_cancel₀ (phaseLogScale_pos ν).ne']

theorem neg_mem_slitPlane_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) (hz0 : z ≠ 0) :
    -z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff, Complex.neg_re, Complex.neg_im]
  by_cases hre : z.re < 0
  · exact Or.inl (neg_pos.mpr hre)
  · right
    intro him
    apply hz0
    apply Complex.ext
    · simp only [Complex.zero_re]
      linarith
    · simpa using him

/-- The normalized regularized logarithm converges exactly to the zero-phase
indicator. No discreteness assumption is needed for this limiting step. -/
theorem phaseLogApprox_tendsto {z : ℂ} (hz : z.re ≤ 0) :
    Tendsto (fun ν => phaseLogApprox ν z) atTop (𝓝 (if z = 0 then (1 : ℂ) else 0)) := by
  classical
  by_cases hz0 : z = 0
  · simp only [hz0, phaseLogApprox_zero, if_pos rfl]
    exact tendsto_const_nhds
  · rw [if_neg hz0]
    have hε : Tendsto (fun ν => (Real.exp (-phaseLogScale ν) : ℂ)) atTop (𝓝 0) := by
      exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp phaseLogScale_tendsto)
    have hlog : Tendsto (fun ν => Complex.log ((Real.exp (-phaseLogScale ν) : ℂ) - z))
        atTop (𝓝 (Complex.log (-z))) := by
      apply (continuousAt_clog (neg_mem_slitPlane_of_re_nonpos hz hz0)).tendsto.comp
      simpa only [zero_sub] using hε.sub_const z
    have hi := (tendsto_inv_atTop_zero.comp phaseLogScale_tendsto).neg
    simpa only [neg_zero, zero_smul, phaseLogApprox, Function.comp_def] using! hi.smul hlog

theorem norm_phaseLogApprox_le {z : ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hz : z.re ≤ 0) (hbound : ‖z‖ ≤ C) (ν : ℕ) :
    ‖phaseLogApprox ν z‖ ≤ 1 + Real.log (C + 2) + Real.pi := by
  let t := phaseLogScale ν
  let ε := Real.exp (-t)
  have ht : 0 < t := phaseLogScale_pos ν
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr ht.le)
  have hb := norm_regularized_clog_le hε hz (hbound.trans (by linarith : C ≤ C + 1))
  have hlogpos : 0 ≤ Real.log (ε + (C + 1)) := Real.log_nonneg (by linarith)
  have hlogupper : Real.log (ε + (C + 1)) ≤ Real.log (C + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have habs : |Real.log ε| = t := by
    rw [show Real.log ε = -t from Real.log_exp _, abs_neg, abs_of_pos ht]
  rw [habs, abs_of_nonneg hlogpos] at hb
  have hb' : ‖Complex.log ((ε : ℂ) - z)‖ ≤ t + Real.log (C + 2) + Real.pi := by linarith
  have hi : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_phaseLogScale ν)
  have hB : 0 ≤ Real.log (C + 2) + Real.pi :=
    add_nonneg (Real.log_nonneg (by linarith)) Real.pi_pos.le
  calc
    ‖phaseLogApprox ν z‖ = t⁻¹ * ‖Complex.log ((ε : ℂ) - z)‖ := by
      change ‖-t⁻¹ • Complex.log ((ε : ℂ) - z)‖ = _
      simp only [norm_smul, norm_neg, norm_inv, Real.norm_eq_abs, abs_of_pos ht]
    _ ≤ t⁻¹ * (t + Real.log (C + 2) + Real.pi) := mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr ht.le)
    _ = 1 + t⁻¹ * (Real.log (C + 2) + Real.pi) := by
      rw [mul_add, mul_add, inv_mul_cancel₀ ht.ne']
      ring
    _ ≤ 1 + Real.log (C + 2) + Real.pi := by
      have hh := mul_le_mul_of_nonneg_right hi hB
      linarith

end ModifiedCartan
#print axioms ModifiedCartan.phaseLogApprox_tendsto
#print axioms ModifiedCartan.norm_phaseLogApprox_le
