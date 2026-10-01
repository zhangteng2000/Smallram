import ModifiedCartan.ScalarCharacteristicBridge
import ModifiedCartan.BoundedGrowthTransfer
import ModifiedCartan.CharacteristicLogLower
import ModifiedCartan.MainTheorem

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

theorem scalarCharacteristic_isEquivalent_lift {f : ℂ → ℂ} (hf : Meromorphic f)
    (F : Curve 1) (htrans : F.Transcendental) (hlin : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (hD : MeromorphicOn.divisor (F.coord 0) univ = (MeromorphicOn.divisor f univ)⁻) :
    scalarCharacteristic f ~[atTop] characteristic F := by
  obtain ⟨C, _, hC⟩ := scalarCharacteristic_abs_sub_curve_le hf F hlin he hD
  apply isEquivalent_of_bounded_difference (C := C)
    (characteristic_tendsto_atTop_of_transcendental F htrans)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact hC r hr.ne'

/-- LaTeX `thm:A`, conclusion (a), for the actual scalar meromorphic function.
The global lift and all its needed hypotheses are constructed, then the proved
n=1 main theorem is transferred through the exact count and bounded-error bridges.
The deficiency assertion (b) is a separate remaining result. -/
theorem Paper.thm_A_growth (f : ℂ → ℂ) (hf : Meromorphic f)
    (htrans : ScalarTranscendental f)
    (hfinite : lowerGrowthOrder (scalarCharacteristic f) < ⊤)
    (hsmall : scalarRamification f =o[atTop] scalarCharacteristic f) :
    ∃ (ρ : ℝ) (m : ℕ) (ℓ : ℝ → ℝ), 2 ≤ m ∧ ρ = (m : ℝ) / 2 ∧
      upperGrowthOrder (scalarCharacteristic f) = (ρ : EReal) ∧
      lowerGrowthOrder (scalarCharacteristic f) = (ρ : EReal) ∧
      FewInflection.SlowlyVarying ℓ ∧
      Tendsto (fun r => scalarCharacteristic f r / (r ^ ρ * ℓ r)) atTop (𝓝 1) := by
  obtain ⟨F, hFt, hFl, he, _, hD⟩ := exists_scalar_curve_lift hf htrans
  have hcomp := scalarCharacteristic_isEquivalent_lift hf F hFt hFl he hD
  have hgrowth := growthOrders_eq_of_isEquivalent hcomp
    (characteristic_tendsto_atTop_of_transcendental F hFt)
  have hFfinite : FiniteLowerOrder F := by
    change lowerGrowthOrder (characteristic F) < ⊤
    rw [← hgrowth.2]
    exact hfinite
  have hFsmall : SmallRamification F := by
    change ramification F =o[atTop] characteristic F
    rw [← scalarRamification_eq_curve hf F hFl he hD]
    exact hsmall.trans_isBigO hcomp.isBigO
  obtain ⟨ρ, ho, hlo, hρ, hslow, hid⟩ :=
    Paper.thm_main_explicit_factor F (by norm_num) hFt hFl hFfinite hFsmall
  obtain ⟨k, q, hq2, hqmax, hρ⟩ := hρ
  have hq : q = 2 := by omega
  subst q
  refine ⟨ρ, k + 2, (fun r => characteristic F r / r ^ ρ), by omega,
    ?_, hgrowth.1.trans ho, hgrowth.2.trans hlo, hslow, ?_⟩
  · rw [hρ]
    push_cast
    ring
  · have hn : ∀ᶠ r in atTop, characteristic F r ≠ 0 :=
      ((characteristic_tendsto_atTop_of_transcendental F hFt).eventually
        (eventually_gt_atTop 0)).mono (fun _ hr => hr.ne')
    have ht : Tendsto (fun r => scalarCharacteristic f r / characteristic F r) atTop (𝓝 1) :=
      (isEquivalent_iff_tendsto_one hn).mp hcomp
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [← hid r hr]

end ModifiedCartan
#print axioms ModifiedCartan.Paper.thm_A_growth
