import ModifiedCartan.ConvolutionAbsorption
import ModifiedCartan.PolynomialSequence

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem systemMaximum_le_power_of_log_bound {n : ℕ} {y : Index n → ℂ → ℂ}
    (hy : ∀ j, Continuous (y j)) (h0 : y 0 0 = 1) {r a C : ℝ}
    (hr : 0 < r) (ha : 0 < a)
    (hb : a * systemLogMaximum y r ≤ (n : ℝ) * Real.log r + C) :
    systemMaximum y r ≤ Real.exp (C / a) * r ^ ((n : ℝ) / a) := by
  have hlog : systemLogMaximum y r ≤ ((n : ℝ) / a) * Real.log r + C / a := by
    have hh := (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hb)
    convert! hh using 1 <;> ring
  have hpos : 0 < systemMaximum y r :=
    zero_lt_one.trans_le (one_le_systemMaximum hy h0 hr.le)
  calc
    systemMaximum y r = Real.exp (systemLogMaximum y r) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (((n : ℝ) / a) * Real.log r + C / a) := Real.exp_le_exp.mpr hlog
    _ = _ := by rw [Real.exp_add, Real.rpow_def_of_pos hr, mul_comm (Real.log r)]; ring

/-- The precise power exponent obtained by absorption at the envelope
radii, common to every component of the normalized system. -/
theorem system_power_sequence_of_divisor_majorant {n : ℕ} (hn : 1 ≤ n)
    {y : Index n → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    (hjets : ∀ i j : Index n, iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0)
    {α c C : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ho : ∀ j, entireOrder (y j) < (α : EReal)) (hc : 0 ≤ c)
    (hci : c * envelopeConstant α < 1)
    (hN : ∀ t, 0 < t → systemCounting y t ≤ c * systemLogMaximum y (3 * t) + C) :
    ∃ r : ℕ → ℝ, (∀ ν, 0 < r ν) ∧ Tendsto r atTop atTop ∧
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ ν in atTop, ∀ j : Index n,
        maximumModulus (y j) (r ν) ≤ K * (r ν) ^ ((n : ℝ) / (1 - c * envelopeConstant α)) := by
  have h0 : y 0 0 = 1 := by simpa using hjets 0 0
  let j1 : Index n := ⟨1, by omega⟩
  have hderiv : deriv (y j1) 0 = 1 := by
    simpa [j1] using hjets j1 j1
  have hcont := systemLogMaximum_continuousOn (fun j => (hy j).continuous) h0
  have hmono := systemLogMaximum_monotoneOn (fun j => (hy j).continuous) h0
  obtain ⟨_, _, r, hr, ht, _, he⟩ := Paper.lem_envelope
    (hcont.mono Ioi_subset_Ici_self)
    (fun t ht => systemLogMaximum_nonneg (fun j => (hy j).continuous) h0 ht.le)
    (hmono.mono Ioi_subset_Ici_self)
    (systemLogMaximum_eventually_pos_of_deriv_one hy hderiv)
    hα0 hα1 (systemLogMaximum_isLittleO (fun j => (hy j).continuous) h0 ho)
  let a := 1 - c * envelopeConstant α
  have ha : 0 < a := sub_pos.mpr hci
  refine ⟨r, hr, ht, Real.exp (C / a), Real.exp_pos _, ?_⟩
  filter_upwards [ht.eventually (eventually_ge_atTop (1 : ℝ))] with ν hν
  intro j
  have hyorder (k : Index n) : entireOrder (y k) < 1 :=
    (ho k).trans (by exact_mod_cast hα1)
  have hb := system_absorption_at_radius hy hyorder hjets hν hc hN (he ν).1 (he ν).2
  exact (maximumModulus_le_systemMaximum y (r ν) j).trans
    (systemMaximum_le_power_of_log_bound (fun j => (hy j).continuous) h0 (hr ν) ha hb)

end ModifiedCartan
#print axioms ModifiedCartan.system_power_sequence_of_divisor_majorant
