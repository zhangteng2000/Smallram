import ModifiedCartan.GaudinDegenerationScalar

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {N : ℕ}

theorem gaudin_power_difference (t : ℂ) (ht : t ≠ 0) (i j : Fin N) :
    t ^ (max i.val j.val - i.val) =
      t ^ (max i.val j.val + 1) * (t ^ (i.val + 1))⁻¹ := by
  have hle : i.val + 1 ≤ max i.val j.val + 1 := Nat.succ_le_succ (le_max_left _ _)
  have hd : max i.val j.val + 1 - (i.val + 1) = max i.val j.val - i.val := by omega
  simpa only [hd] using pow_sub₀ t ht hle

theorem gaudinDegenerationDenominator_eq (z : Fin N → ℂ) (i j : Fin N)
    (t : ℂ) (ht : t ≠ 0) :
    gaudinDegenerationDenominator z i j t = t ^ (max i.val j.val + 1) *
      (gaudinDeformedParameters z t i - gaudinDeformedParameters z t j) := by
  unfold gaudinDegenerationDenominator gaudinDeformedParameters
  rw [gaudin_power_difference t ht i j]
  have hj := gaudin_power_difference t ht j i
  rw [max_comm j.val i.val] at hj
  rw [hj]
  ring

theorem gaudinDegenerationCoefficient_eq (z : Fin N → ℂ) (i j : Fin N)
    (t : ℂ) (ht : t ≠ 0) :
    gaudinDegenerationCoefficient z i j t = (t ^ (i.val + 1))⁻¹ *
      (gaudinDeformedParameters z t i - gaudinDeformedParameters z t j)⁻¹ := by
  by_cases h : i = j
  · subst j
    simp [gaudinDegenerationCoefficient]
  · rw [gaudinDegenerationCoefficient, ite_eq_right h,
      gaudinDegenerationDenominator_eq z i j t ht, gaudin_power_difference t ht i j,
      mul_div_mul_left _ _ (pow_ne_zero _ ht), div_eq_mul_inv]

theorem gaudinDeformedParameters_injective (z : Fin N → ℂ) (t : ℂ) (ht : t ≠ 0)
    (hD : ∀ i j : Fin N, i ≠ j → gaudinDegenerationDenominator z i j t ≠ 0) :
    Function.Injective (gaudinDeformedParameters z t) := by
  intro i j hij
  by_contra hn
  apply hD i j hn
  rw [gaudinDegenerationDenominator_eq z i j t ht, hij, sub_self, mul_zero]

end
end ModifiedCartan


