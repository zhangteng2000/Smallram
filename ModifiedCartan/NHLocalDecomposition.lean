import ModifiedCartan.NHRadiusSelection
import ModifiedCartan.NHControlledRemainder
import ModifiedCartan.LocalPairCharacteristic
import ModifiedCartan.DiskDivisorMass
import ModifiedCartan.MeromorphicDerivativeDecomposition

open scoped Topology
open Filter Set Metric Function MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

/-- All data in the controlled local logarithmic-derivative decomposition
are constructed from the actual meromorphic function and its divisor. -/
theorem exists_NH_local_decomposition {f : ℂ → ℂ} {r ρ B : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hB : 1 ≤ B) (hρB : ρ ≤ B) (hδB : (ρ - r)⁻¹ ≤ B)
    (hf : MeromorphicOn f (closedBall 0 ρ)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hTB : diskCharacteristic f ρ ≤ B) (h0B : Real.posLog (1 / ‖f 0‖) ≤ B) :
    ∃ (S : Finset ℂ) (d : ℂ → ℤ) (A : ℂ → ℂ),
      AnalyticOnNhd ℂ A (closedBall 0 r) ∧
      (∑ a ∈ S, |(d a : ℝ)|) ≤ 12 * B ^ 3 ∧
      ∀ m : ℕ,
        (iteratedDeriv m (logDeriv f) =ᶠ[codiscreteWithin (sphere 0 r)] (fun z =>
          (∑ a ∈ S, ((d a : ℂ) * (-1 : ℂ) ^ m * (m.factorial : ℂ)) / (z - a) ^ (m + 1)) +
            iteratedDeriv m A z)) ∧
        (∀ z ∈ closedBall (0 : ℂ) r, ‖iteratedDeriv m A z‖ ≤
          144 * (m.factorial : ℝ) * 4 ^ m * B ^ (m + 4)) := by
  have hρ := hr.trans hrρ
  have hBp := zero_lt_one.trans_le hB
  obtain ⟨R, s, hrR, hRρ, hrs, hsR, hRB, hRs, hsr, hlogB, hb⟩ :=
    exists_NH_regular_radius hr hrρ hρB hδB hf hfa h0
  have hR := hr.trans hrR
  have hfR : MeromorphicOn f (closedBall 0 R) := hf.mono_set (closedBall_subset_closedBall hRρ.le)
  obtain ⟨S, hS, hSne, hSin⟩ := FewInflection.exists_finset_divisor_support_within_ball hfR hR
  let d : ℂ → ℤ := divisor f (ball 0 R)
  have hfρabs : MeromorphicOn f (closedBall 0 |ρ|) := by simpa only [abs_of_pos hρ] using hf
  have houter := disk_divisor_mass_bound hR hRρ hfρabs hfa h0 S (fun a ha => (hSin a ha).le)
  have hd (a : ℂ) (ha : a ∈ S) : divisor f (closedBall 0 |ρ|) a = d a := by
    have haR : a ∈ ball (0 : ℂ) R := by simpa only [mem_ball, dist_zero_right] using hSin a ha
    have haρ : a ∈ closedBall (0 : ℂ) |ρ| := by
      rw [abs_of_pos hρ]
      exact closedBall_subset_closedBall hRρ.le (ball_subset_closedBall haR)
    dsimp only [d]
    rw [hfρabs.divisor_apply haρ, (hfR.mono_set ball_subset_closedBall).divisor_apply haR]
  have hmass : (∑ a ∈ S, |(d a : ℝ)|) ≤ 12 * B ^ 3 := by
    have he : (∑ a ∈ S, |(divisor f (closedBall 0 |ρ|) a : ℝ)|) = ∑ a ∈ S, |(d a : ℝ)| :=
      Finset.sum_congr rfl (fun a ha => by rw [hd a ha])
    rw [he] at houter
    calc
      _ ≤ (2 * diskCharacteristic f ρ + Real.posLog (1 / ‖f 0‖)) / Real.log (ρ / R) := houter
      _ = (2 * diskCharacteristic f ρ + Real.posLog (1 / ‖f 0‖)) * (Real.log (ρ / R))⁻¹ :=
        div_eq_mul_inv _ _
      _ ≤ (3 * B) * (4 * B ^ 2) :=
        mul_le_mul (by linarith) hlogB
          (inv_nonneg.mpr (Real.log_pos ((one_lt_div hR).mpr hRρ)).le) (by positivity)
      _ = _ := by ring
  have hfRs : MeromorphicOn f (sphere 0 |R|) := by
    rw [abs_of_pos hR]
    exact hfR.mono_set sphere_subset_closedBall
  have hmean : Real.circleAverage (fun ζ => |Real.log ‖f ζ‖|) 0 R ≤ 3 * B := by
    have hh := disk_boundary_abs_log_bound hR
      (by simpa only [abs_of_pos hR] using hfR) hfa h0
    have hm := diskCharacteristic_mono hf hfa h0 hR hRρ.le
    linarith
  let A := poissonJensenRemainder S id (fun a => (d a : ℂ)) f R
  have ha : ∀ a ∈ S, ‖id a‖ ≤ R := fun a ha => (hSin a ha).le
  have hAA : AnalyticOnNhd ℂ A (ball 0 R) := poissonJensenRemainder_analytic S id _ ha hfRs
  have hclosed : closedBall (0 : ℂ) r ⊆ ball 0 R := closedBall_subset_ball hrR
  refine ⟨S, d, A, hAA.mono hclosed, hmass, fun m => ⟨?_, ?_⟩⟩
  · have heq := logDeriv_eq_singular_add_remainder hR hfR hfa h0 hb S hS
    have he := iteratedDeriv_singular_add_analytic_eventuallyEq S (fun a => (d a : ℂ))
      (hfR.mono_set ball_subset_closedBall).logDeriv hAA heq m
    exact he.filter_mono (codiscreteWithin_mono (sphere_subset_closedBall.trans hclosed))
  · intro z hz
    apply poissonJensenRemainder_iteratedDeriv_control_bound S id (fun a => (d a : ℂ))
      hr.le hrs hsR hB hRB hRs hsr ha hfRs _ hmean
      (by simpa only [mem_closedBall, dist_zero_right] using hz) m
    simpa only [Complex.norm_intCast, Real.norm_eq_abs] using hmass

end ModifiedCartan
#print axioms ModifiedCartan.exists_NH_local_decomposition

