import ModifiedCartan.NHLocalDecomposition
import ModifiedCartan.LocalProximityArithmetic

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Uniform local proximity estimates for every derivative of logDeriv.
The auxiliary control B is later constructed from the exact manuscript data. -/
theorem exists_NH_logDeriv_control_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (r ρ B : ℝ),
      0 < r → r < ρ → 1 ≤ B → ρ ≤ B → (ρ - r)⁻¹ ≤ B → r⁻¹ ≤ B →
      MeromorphicOn f (closedBall 0 ρ) → AnalyticAt ℂ f 0 → f 0 ≠ 0 →
      diskCharacteristic f ρ ≤ B → Real.posLog (1 / ‖f 0‖) ≤ B →
      ValueDistribution.proximity (iteratedDeriv m (logDeriv f)) ⊤ r ≤ C * (1 + Real.log B) := by
  obtain ⟨K, hK, hsing⟩ := integer_poles_derivative_proximity_bound
  let F : ℝ := 144 * (m.factorial : ℝ) * 4 ^ m
  let D : ℝ := 24 * K * (m.factorial : ℝ)
  let P : ℝ := 2 * ((m : ℝ) + 1)
  let a : ℝ := P * (Real.log (1 + D) + 1) + Real.posLog F + Real.log 2
  let b : ℝ := 4 * P + ((m : ℝ) + 4)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hlogD : 0 ≤ Real.log (1 + D) := Real.log_nonneg (by linarith)
  have ha : 0 ≤ a := add_nonneg
    (add_nonneg (mul_nonneg hP.le (by linarith)) Real.posLog_nonneg)
    (Real.log_nonneg (by norm_num))
  have hb : 0 ≤ b := by dsimp [b, P]; positivity
  refine ⟨a + b + 1, by linarith, fun f r ρ B hr hrρ hB hρB hδB hrB hf hfa h0 hTB h0B => ?_⟩
  have hBp := zero_lt_one.trans_le hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  obtain ⟨S, d, A, hA, hmass, hder⟩ := exists_NH_local_decomposition
    hr hrρ hB hρB hδB hf hfa h0 hTB h0B
  let L : ℂ → ℂ := fun z =>
    ∑ w ∈ S, ((d w : ℂ) * (-1 : ℂ) ^ m * (m.factorial : ℂ)) / (z - w) ^ (m + 1)
  have hhalf : r ^ (-(1 / 2 : ℝ)) ≤ 2 * B :=
    (inverse_half_power_le_one_add_inv hr).trans (by linarith)
  have hproduct : K * r ^ (-(1 / 2 : ℝ)) * (m.factorial : ℝ) * ∑ w ∈ S, |(d w : ℝ)| ≤
      D * B ^ 4 := by
    calc
      _ ≤ K * (2 * B) * (m.factorial : ℝ) * (12 * B ^ 3) := by gcongr
      _ = _ := by dsimp [D]; ring
  have hLbound : ValueDistribution.proximity L ⊤ r ≤
      P * (Real.log (1 + D) + 4 * Real.log B + 1) := by
    have hh := hsing S d m r hr
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hP.le
    apply add_le_add _ le_rfl
    exact (Real.log_le_log (by positivity) (add_le_add le_rfl hproduct)).trans
      (by simpa only [Nat.cast_ofNat] using log_one_add_mul_pow_le hD hB 4)
  have hsp : sphere (0 : ℂ) |r| ⊆ closedBall 0 r := by
    rw [abs_of_pos hr]
    exact sphere_subset_closedBall
  have hAm : MeromorphicOn (iteratedDeriv m A) (sphere 0 |r|) :=
    (meromorphic_iteratedDeriv_on hA.meromorphicOn m).mono_set hsp
  have hAbound : ValueDistribution.proximity (iteratedDeriv m A) ⊤ r ≤
      Real.posLog F + ((m : ℝ) + 4) * Real.log B := by
    have hh : ValueDistribution.proximity (iteratedDeriv m A) ⊤ r ≤ Real.posLog (F * B ^ (m + 4)) :=
      local_proximity_le_of_norm_le hAm (by dsimp [F]; positivity)
        (fun z hz => (hder m).2 z (hsp hz))
    exact hh.trans (by simpa only [Nat.cast_add, Nat.cast_ofNat] using
      posLog_mul_pow_le (C := F) hB (m + 4))
  have hLm : MeromorphicOn L (sphere 0 |r|) := by
    simpa only [L, id_eq] using
      (meromorphic_weighted_poles S id (fun w => (d w : ℂ) * (-1 : ℂ) ^ m * (m.factorial : ℂ))
        (m + 1)).meromorphicOn (s := sphere 0 |r|)
  have heq : ValueDistribution.proximity (iteratedDeriv m (logDeriv f)) ⊤ r =
      ValueDistribution.proximity (fun z => L z + iteratedDeriv m A z) ⊤ r :=
    local_proximity_congr hr.ne' (by simpa only [abs_of_pos hr, L] using (hder m).1)
  rw [heq]
  have hmain := (local_proximity_add_le hLm hAm).trans
    (add_le_add (add_le_add hLbound hAbound) le_rfl)
  have he : P * (Real.log (1 + D) + 4 * Real.log B + 1) +
      (Real.posLog F + ((m : ℝ) + 4) * Real.log B) + Real.log 2 = a + b * Real.log B := by
    dsimp [a, b]
    ring
  rw [he] at hmain
  exact hmain.trans (by nlinarith [mul_nonneg ha hlogB])

end ModifiedCartan
#print axioms ModifiedCartan.exists_NH_logDeriv_control_bound


