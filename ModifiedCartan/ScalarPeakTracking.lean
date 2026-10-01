import ModifiedCartan.ScalarRootCorrection
import ModifiedCartan.ScalarPhaseSlowChange

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Coherent peak directions along a sequence of actual phase coefficients.
Each step uses the principal correction near one, instead of resetting a
potentially discontinuous argument branch. -/
noncomputable def scalarPeakTrack (m : ℕ) (C : ℕ → ℂ) : ℕ → ℂ
  | 0 => scalarRootCorrection m (((Real.pi / 2) ^ 2 : ℝ) : ℂ) (C 0)
  | ν + 1 => scalarPeakTrack m C ν * scalarRootCorrection m (C ν) (C (ν + 1))

theorem scalarPeakTrack_norm (m : ℕ) {C : ℕ → ℂ}
    (hC : ∀ ν, ‖C ν‖ = (Real.pi / 2) ^ 2) (ν : ℕ) :
    ‖scalarPeakTrack m C ν‖ = 1 := by
  have hR : 0 < (Real.pi / 2) ^ 2 := sq_pos_of_pos (half_pos Real.pi_pos)
  have hCn (ν : ℕ) : C ν ≠ 0 := norm_ne_zero_iff.mp (by rw [hC ν]; exact hR.ne')
  induction ν with
  | zero =>
      apply scalarRootCorrection_norm m (hCn 0)
      rw [hC 0, Complex.norm_real, Real.norm_of_nonneg hR.le]
  | succ ν ih =>
      rw [scalarPeakTrack, norm_mul, ih,
        scalarRootCorrection_norm m (hCn (ν + 1)) ((hC ν).trans (hC (ν + 1)).symm), one_mul]

theorem scalarPeakTrack_peak {m : ℕ} (hm : m ≠ 0) {C : ℕ → ℂ}
    (hC : ∀ ν, ‖C ν‖ = (Real.pi / 2) ^ 2) (ν : ℕ) :
    C ν * (scalarPeakTrack m C ν) ^ m = (((Real.pi / 2) ^ 2 : ℝ) : ℂ) := by
  have hR : 0 < (Real.pi / 2) ^ 2 := sq_pos_of_pos (half_pos Real.pi_pos)
  have hCn (ν : ℕ) : C ν ≠ 0 := norm_ne_zero_iff.mp (by rw [hC ν]; exact hR.ne')
  induction ν with
  | zero =>
      rw [scalarPeakTrack, scalarRootCorrection_pow hm]
      field_simp [hCn 0]
  | succ ν ih =>
      exact scalarRootCorrection_transports_peak hm (hCn (ν + 1)) ih

theorem scalarPeakTrack_steps_tendsto_zero (m : ℕ) {C : ℕ → ℂ}
    (hC : ∀ ν, ‖C ν‖ = (Real.pi / 2) ^ 2)
    (hstep : Tendsto (fun ν => C (ν + 1) - C ν) atTop (𝓝 0)) :
    Tendsto (fun ν => scalarPeakTrack m C (ν + 1) - scalarPeakTrack m C ν) atTop (𝓝 0) := by
  have hrev : Tendsto (fun ν => C ν - C (ν + 1)) atTop (𝓝 0) := by
    simpa only [neg_sub, neg_zero] using hstep.neg
  have hcorr := scalarRootCorrection_tendsto_one m (sq_pos_of_pos (half_pos Real.pi_pos))
    (fun ν => hC (ν + 1)) hrev
  have he (ν : ℕ) : ‖scalarPeakTrack m C (ν + 1) - scalarPeakTrack m C ν‖ =
      ‖scalarRootCorrection m (C ν) (C (ν + 1)) - 1‖ := by
    have hh : scalarPeakTrack m C (ν + 1) - scalarPeakTrack m C ν =
        scalarPeakTrack m C ν * (scalarRootCorrection m (C ν) (C (ν + 1)) - 1) := by
      rw [scalarPeakTrack]
      ring
    rw [hh, norm_mul, scalarPeakTrack_norm m hC ν, one_mul]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [he, sub_self, norm_zero] using (hcorr.sub_const 1).norm

noncomputable def scalarDyadicPeakCenter (f : Curve 1) (m : ℕ) : ℕ → ℂ :=
  scalarPeakTrack m (fun ν => scalarPhaseCoefficient f m ((2 : ℝ) ^ ν))

theorem scalarDyadicPeakCenter_norm (f : Curve 1) (m ν : ℕ) :
    ‖scalarDyadicPeakCenter f m ν‖ = 1 :=
  scalarPeakTrack_norm m (fun ν => scalarPhaseCoefficient_norm f m _) ν

theorem scalarDyadicPeakCenter_peak (f : Curve 1) {m : ℕ} (hm : m ≠ 0) (ν : ℕ) :
    scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (scalarDyadicPeakCenter f m ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ) :=
  scalarPeakTrack_peak hm (fun ν => scalarPhaseCoefficient_norm f m _) ν

/-- Actual coherently numbered dyadic peak centers move by a vanishing angle.
This follows from the proved phase slow change for the original curve. -/
theorem scalarDyadicPeakCenter_steps_tendsto_zero
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal)) {m : ℕ} (hm : ρ = (m : ℝ) / 2) :
    Tendsto (fun ν => scalarDyadicPeakCenter f m (ν + 1) - scalarDyadicPeakCenter f m ν)
      atTop (𝓝 0) := by
  apply scalarPeakTrack_steps_tendsto_zero m (fun ν => scalarPhaseCoefficient_norm f m _)
  have hh := scalarPhaseCoefficient_slow_change f hlin htrans hsmall hρ hl hu hm
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    (fun _ => show (2 : ℝ) ∈ Icc (1 : ℝ) 2 from ⟨by norm_num, le_rfl⟩)
  simpa only [pow_succ, mul_comm] using hh

end ModifiedCartan
#print axioms ModifiedCartan.scalarPeakTrack_peak
#print axioms ModifiedCartan.scalarPeakTrack_steps_tendsto_zero
#print axioms ModifiedCartan.scalarDyadicPeakCenter_steps_tendsto_zero
