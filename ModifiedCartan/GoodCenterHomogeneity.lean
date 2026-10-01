import ModifiedCartan.UnitaryPowerConvexity
import ModifiedCartan.RadialConvexBalance

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Step 3 of `prop:homogeneity`: balance forces equality on every
radial segment for the actual basis chosen at the good center. -/
theorem ArbitraryRadiusLimitData.norm_limit_powerChart_radial_at_good_center
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ∈ d.good_centers.centers)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    d.U (powerChart a ρ (t : ℂ)) = (t : EReal) * d.U a := by
  have hr : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have ha0 : a ≠ 0 := by simpa only [mem_singleton_iff] using (d.good_centers.subset ha).2
  have ha4 : ‖a‖ < 4 := by
    have hh : ‖a‖ < 2 := by simpa only [mem_ball, dist_zero_right] using (d.good_centers.subset ha).1
    linarith
  have haU : a ∈ ball (0 : ℂ) 4 := by simpa only [mem_ball, dist_zero_right] using ha4
  have h0U : (0 : ℂ) ∈ ball (0 : ℂ) 4 := mem_ball_self (by norm_num)
  have htG := powerChartDomain_real_mem ha0 ha4 hr ht ht1
  have htU := powerChart_mapsTo ha0 hr htG
  obtain ⟨ns, hns, V, u, v, hu, hmax, hsum, hsuma⟩ := Paper.lem_basis_at_point d a ha
  have hreg (j : Index n) := d.unitary_component_regular hns V j
    (hu j).1 (hu j).2.2.1 (hu j).2.2.2
  have hs : ∀ z ∈ ball (0 : ℂ) 4, 0 ≤ ∑ j, (u j z).toReal :=
    d.unitary_component_sum_nonneg hns V (fun j => (hu j).1)
      (fun j => (hu j).2.2.1) (fun j => (hu j).2.2.2) hsum
  have huzero : ∀ j, (u j 0).toReal = 0 := by
    apply finite_nonpos_eq_zero_of_sum_nonneg _ _ (hs 0 h0U)
    intro j
    have hh : u j 0 ≤ d.U 0 := by
      rw [hmax h0U]
      exact Finset.le_sup (f := fun k => u k 0) (Finset.mem_univ j)
    rw [(hreg j).1 0 h0U, d.origin_zero] at hh
    exact_mod_cast hh
  have hsumaR : ∑ j, (u j a).toReal = 0 := by
    have he : ((∑ j, (u j a).toReal : ℝ) : EReal) = 0 := by
      rw [ereal_coe_finset_sum]
      calc
        _ = ∑ j, u j a := Finset.sum_congr rfl (fun j _ => ((hreg j).1 a haU).symm)
        _ = 0 := hsuma
    exact_mod_cast he
  have hle (j : Index n) : (u j (powerChart a ρ (t : ℂ))).toReal ≤ t * (u j a).toReal := by
    have hc := (hreg j).2.continuousOn
    have hc0 : ContinuousAt (fun z => (u j z).toReal) (powerChart a ρ 0) := by
      rw [powerChart_zero a hr]
      exact hc.continuousAt (isOpen_ball.mem_nhds h0U)
    have hh := convex_radial_bound_of_zero (powerChartDomain_isOpen a ρ)
      (d.unitary_component_powerChart_convex hρ ha0 ha4 hns V j (hu j).1 (hu j).2.2.1 (hu j).2.2.2)
      (hc.comp (powerChart_analytic a ρ).continuousOn (powerChart_mapsTo ha0 hr))
      (hc0.comp (powerChart_continuousAt_zero a hr))
      (by rw [powerChart_zero a hr, huzero j])
      (fun q hq hq1 => powerChartDomain_real_mem ha0 ha4 hr hq hq1) ht ht1
    simpa only [powerChart_one] using hh
  have heq : ∀ j, (u j (powerChart a ρ (t : ℂ))).toReal = t * (u j a).toReal :=
    finite_balance_forces_equality _ _ hle (hs _ htU) (by rw [← Finset.mul_sum, hsumaR, mul_zero])
  have hreal (z : ℂ) (hz : z ∈ ball (0 : ℂ) 4) :
      d.U z = ((Finset.univ.sup' Finset.univ_nonempty (fun j => (u j z).toReal) : ℝ) : EReal) := by
    rw [hmax hz, ereal_coe_finset_sup']
    exact Finset.sup_congr rfl (fun j _ => (hreg j).1 z hz)
  rw [hreal _ htU, hreal a haU, ← EReal.coe_mul]
  apply congrArg (fun x : ℝ => (x : EReal))
  simp_rw [heq]
  exact (Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty (fun x : ℝ => t * x)
    (fun x y => mul_max_of_nonneg x y ht.le)).symm

theorem ArbitraryRadiusLimitData.norm_limit_dilation_at_good_center
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ∈ d.good_centers.centers)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    d.U ((s : ℂ) * a) = ((s ^ ρ : ℝ) : EReal) * d.U a := by
  have hr : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hh := d.norm_limit_powerChart_radial_at_good_center hρ ha
    (Real.rpow_pos_of_pos hs ρ) (Real.rpow_le_one hs.le hs1 hr.le)
  simpa only [powerChart_real a ρ (Real.rpow_nonneg hs.le ρ), Real.rpow_rpow_inv hs.le hr.ne'] using hh

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.norm_limit_dilation_at_good_center

