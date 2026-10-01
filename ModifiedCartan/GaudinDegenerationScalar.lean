import ModifiedCartan.KPGaudinCommutation
import Mathlib.Topology.Algebra.Polynomial

open scoped BigOperators Classical Topology

namespace ModifiedCartan
noncomputable section

variable {N : ℕ}

def gaudinDeformedParameters (z : Fin N → ℂ) (t : ℂ) (i : Fin N) : ℂ :=
  z i + (t ^ (i.val + 1))⁻¹

def gaudinDegenerationDenominator (z : Fin N → ℂ) (i j : Fin N) (t : ℂ) : ℂ :=
  (z i - z j) * t ^ (max i.val j.val + 1) +
    t ^ (max i.val j.val - i.val) - t ^ (max i.val j.val - j.val)

def gaudinDegenerationCoefficient (z : Fin N → ℂ) (i j : Fin N) (t : ℂ) : ℂ :=
  if i = j then 0 else t ^ (max i.val j.val - i.val) /
    gaudinDegenerationDenominator z i j t

theorem gaudinDegenerationDenominator_zero (z : Fin N → ℂ) (i j : Fin N) (h : i ≠ j) :
    gaudinDegenerationDenominator z i j 0 = if j < i then 1 else -1 := by
  by_cases hji : j < i
  · have hjiv : j.val < i.val := hji
    have hd : i.val - j.val ≠ 0 := by omega
    simp [gaudinDegenerationDenominator, hji, max_eq_left (Nat.le_of_lt hjiv), hd]
  · have hij : i.val < j.val := by
      have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
      change ¬j.val < i.val at hji
      omega
    have hd : j.val - i.val ≠ 0 := by omega
    simp [gaudinDegenerationDenominator, hji, max_eq_right (Nat.le_of_lt hij), hd]

theorem gaudinDegenerationCoefficient_zero (z : Fin N → ℂ) (i j : Fin N) :
    gaudinDegenerationCoefficient z i j 0 = if j < i then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [gaudinDegenerationCoefficient]
  · rw [gaudinDegenerationCoefficient, if_neg h, gaudinDegenerationDenominator_zero z i j h]
    by_cases hji : j < i
    · have hv : j.val ≤ i.val := Nat.le_of_lt hji
      simp [hji, max_eq_left hv]
    · have hij : i.val < j.val := by
        have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
        change ¬j.val < i.val at hji
        omega
      have hd : j.val - i.val ≠ 0 := by omega
      simp [hji, max_eq_right (Nat.le_of_lt hij), hd]

theorem gaudinDegenerationDenominator_continuous (z : Fin N → ℂ) (i j : Fin N) :
    Continuous (gaudinDegenerationDenominator z i j) := by
  unfold gaudinDegenerationDenominator
  fun_prop

theorem gaudinDegenerationCoefficient_continuousAt_zero (z : Fin N → ℂ) (i j : Fin N) :
    ContinuousAt (gaudinDegenerationCoefficient z i j) 0 := by
  unfold gaudinDegenerationCoefficient
  by_cases h : i = j
  · simp only [ite_eq_left h]
    exact continuousAt_const
  · simp only [ite_eq_right h]
    apply (continuousAt_id.pow _).div (gaudinDegenerationDenominator_continuous z i j).continuousAt
    rw [gaudinDegenerationDenominator_zero z i j h]
    split_ifs <;> norm_num

theorem gaudinDegenerationDenominator_eventually_ne_zero (z : Fin N → ℂ) :
    ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i j : Fin N, i ≠ j → gaudinDegenerationDenominator z i j t ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases h : i = j
  · exact Filter.Eventually.of_forall (fun _ hn => (hn h).elim)
  · have hn : gaudinDegenerationDenominator z i j 0 ≠ 0 := by
      rw [gaudinDegenerationDenominator_zero z i j h]
      split_ifs <;> norm_num
    filter_upwards [(gaudinDegenerationDenominator_continuous z i j).continuousAt.eventually_ne hn]
      with t ht
    exact fun _ => ht

end
end ModifiedCartan


