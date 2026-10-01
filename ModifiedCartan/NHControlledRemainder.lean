import ModifiedCartan.LocalPoissonRemainder

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem poissonJensenRemainder_iteratedDeriv_control_bound {ι : Type*}
    (S : Finset ι) (a c : ι → ℂ) {f : ℂ → ℂ} {r s R B : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hrs : r < s) (hsR : s < R) (hB : 1 ≤ B) (hRB : R ≤ B)
    (hRs : (R - s)⁻¹ ≤ 4 * B) (hsr : (s - r)⁻¹ ≤ 4 * B)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ R) (hf : MeromorphicOn f (sphere 0 |R|))
    (hmass : ∑ i ∈ S, ‖c i‖ ≤ 12 * B ^ 3)
    (hmean : Real.circleAverage (fun ζ => |Real.log ‖f ζ‖|) 0 R ≤ 3 * B)
    (hz : ‖z‖ ≤ r) (m : ℕ) :
    ‖iteratedDeriv m (poissonJensenRemainder S a c f R) z‖ ≤
      144 * (m.factorial : ℝ) * 4 ^ m * B ^ (m + 4) := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hR := (hr.trans_lt hrs).trans hsR
  have hRs0 : 0 ≤ (R - s)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hsR).le
  have hsr0 : 0 ≤ (s - r)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hrs).le
  have hM0 : 0 ≤ ∑ i ∈ S, ‖c i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hL0 : 0 ≤ Real.circleAverage (fun ζ => |Real.log ‖f ζ‖|) 0 R :=
    Real.circleAverage_nonneg_of_nonneg (fun _ _ => abs_nonneg _)
  have hk : 2 * R / (R - s) ^ 2 ≤ 2 * B * (4 * B) ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    gcongr
  have htotal : (R - s)⁻¹ * ∑ i ∈ S, ‖c i‖ +
      (2 * R / (R - s) ^ 2) * Real.circleAverage (fun ζ => |Real.log ‖f ζ‖|) 0 R ≤
        144 * B ^ 4 := by
    calc
      _ ≤ (4 * B) * (12 * B ^ 3) + (2 * B * (4 * B) ^ 2) * (3 * B) :=
        add_le_add (mul_le_mul hRs hmass hM0 (by positivity))
          (mul_le_mul hk hmean hL0 (by positivity))
      _ = _ := by ring
  calc
    _ ≤ (m.factorial : ℝ) * ((R - s)⁻¹ * ∑ i ∈ S, ‖c i‖ +
        (2 * R / (R - s) ^ 2) * Real.circleAverage (fun ζ => |Real.log ‖f ζ‖|) 0 R) /
          (s - r) ^ m := poissonJensenRemainder_iteratedDeriv_bound S a c hr hrs hsR ha hf hz m
    _ = (m.factorial : ℝ) * ((R - s)⁻¹ * ∑ i ∈ S, ‖c i‖ +
        (2 * R / (R - s) ^ 2) * Real.circleAverage (fun ζ => |Real.log ‖f ζ‖|) 0 R) *
          ((s - r)⁻¹) ^ m := by rw [div_eq_mul_inv, ← inv_pow]
    _ ≤ (m.factorial : ℝ) * (144 * B ^ 4) * (4 * B) ^ m := by gcongr
    _ = _ := by rw [mul_pow, pow_add]; ring

end ModifiedCartan
#print axioms ModifiedCartan.poissonJensenRemainder_iteratedDeriv_control_bound
