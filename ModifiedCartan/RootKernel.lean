import ModifiedCartan.RootKernelPrimitive

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `eq:kernel-identity`, including actual integrability on the
whole positive axis. -/
theorem root_posLog_kernel_integrable_and_integral {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    IntegrableOn (fun t => Real.posLog (t / a) / (r + t) ^ 2) (Ioi 0) ∧
      r * (∫ t in Ioi 0, Real.posLog (t / a) / (r + t) ^ 2) = Real.log (1 + r / a) := by
  have hzero : ∀ t ∈ Ioc (0 : ℝ) a, Real.posLog (t / a) / (r + t) ^ 2 = 0 := by
    intro t ht
    have hp : Real.posLog (t / a) = 0 := (Real.posLog_eq_zero_iff _).mpr (by
      rw [abs_of_pos (div_pos ht.1 ha)]
      exact (div_le_one ha).mpr ht.2)
    rw [hp, zero_div]
  have heq : ∀ t ∈ Ioi a, Real.posLog (t / a) / (r + t) ^ 2 =
      Real.log (t / a) / (r + t) ^ 2 := by
    intro t ht
    rw [Real.posLog_eq_log (by
      rw [abs_of_pos (div_pos (ha.trans ht) ha)]
      exact (one_le_div ha).mpr ht.le)]
  obtain ⟨hint, hvalue⟩ := root_log_kernel_integrable_and_integral hr ha
  have hhead : IntegrableOn (fun t => Real.posLog (t / a) / (r + t) ^ 2) (Ioc 0 a) :=
    integrableOn_zero.congr_fun (fun t ht => (hzero t ht).symm) measurableSet_Ioc
  have htail : IntegrableOn (fun t => Real.posLog (t / a) / (r + t) ^ 2) (Ioi a) :=
    hint.congr_fun (fun t ht => (heq t ht).symm) measurableSet_Ioi
  have hintall : IntegrableOn (fun t => Real.posLog (t / a) / (r + t) ^ 2) (Ioi 0) := by
    simpa only [Ioc_union_Ioi_eq_Ioi ha.le] using hhead.union htail
  refine ⟨hintall, ?_⟩
  have hheadzero : (∫ t in Ioc (0 : ℝ) a, Real.posLog (t / a) / (r + t) ^ 2) = 0 := by
    calc
      _ = ∫ _t in Ioc (0 : ℝ) a, (0 : ℝ) := setIntegral_congr_fun measurableSet_Ioc hzero
      _ = 0 := integral_zero _ _
  rw [← Ioc_union_Ioi_eq_Ioi ha.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hhead htail,
    hheadzero, zero_add, setIntegral_congr_fun measurableSet_Ioi heq]
  exact hvalue

theorem root_kernel_identity {r : ℝ} (hr : 0 < r) {a : ℂ} (ha : a ≠ 0) :
    IntegrableOn (fun t => Real.posLog (t / ‖a‖) / (r + t) ^ 2) (Ioi 0) ∧
      r * (∫ t in Ioi 0, Real.posLog (t / ‖a‖) / (r + t) ^ 2) = Real.log (1 + r / ‖a‖) :=
  root_posLog_kernel_integrable_and_integral hr (norm_pos_iff.mpr ha)

end ModifiedCartan
#print axioms ModifiedCartan.root_kernel_identity
