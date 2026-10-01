import ModifiedCartan.PowerChartGeometry
import ModifiedCartan.ScalarPowerDomain
import Mathlib.Analysis.Complex.OpenMapping

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem powerChart_deriv_ne_zero {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    {w : ℂ} (hw : w ∈ powerChartDomain a ρ) : deriv (powerChart a ρ) w ≠ 0 := by
  rw [powerChart_deriv hw]
  have hi : ((ρ⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hρ.ne')
  have hw0 : w ≠ 0 := by intro he; rw [he] at hw; simpa using hw.1
  exact mul_ne_zero (mul_ne_zero ha hi) (Complex.cpow_ne_zero_iff.mpr (Or.inl hw0))

/-- The proved power chart maps every open subset of its domain to an open
complex set. Its nonzero derivative rules out the constant alternative. -/
theorem powerChart_isOpen_image {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    {S : Set ℂ} (hS : IsOpen S) (hSG : S ⊆ powerChartDomain a ρ) :
    IsOpen (powerChart a ρ '' S) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨w, hw, rfl⟩
  have hn : ¬ ∀ᶠ v in 𝓝 w, powerChart a ρ v = powerChart a ρ w := by
    intro he
    have heq : powerChart a ρ =ᶠ[𝓝 w] (fun _ => powerChart a ρ w) := he
    have hh := heq.deriv_eq
    rw [deriv_const] at hh
    exact powerChart_deriv_ne_zero ha hρ (hSG hw) hh
  have ho := (powerChart_analytic a ρ w (hSG hw)).eventually_constant_or_nhds_le_map_nhds.resolve_left hn
  exact ho (image_mem_map (hS.mem_nhds hw))

/-- The actual positive chart region in the original complex plane. -/
noncomputable def scalarPositiveChart (a : ℂ) (ρ : ℝ) (b : ℂ) : Set ℂ :=
  powerChart a ρ '' positivePowerChartDomain a ρ b

theorem scalarPositiveChart_subset {a b : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    scalarPositiveChart a ρ b ⊆ ball (0 : ℂ) 2 := by
  rintro z ⟨w, hw, rfl⟩
  exact powerChartInnerDomain_mapsTo ha hρ hw.1

theorem scalarPositiveChart_isOpen {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (b : ℂ) :
    IsOpen (scalarPositiveChart a ρ b) :=
  powerChart_isOpen_image ha hρ (positivePowerChartDomain_isOpen a ρ b)
    (fun _ hw => powerChartInnerDomain_subset hρ.le hw.1)

theorem scalarPositiveChart_isPreconnected (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (b : ℂ) :
    IsPreconnected (scalarPositiveChart a ρ b) := by
  exact (positivePowerChartDomain_convex a ρ b).isPreconnected.image (powerChart a ρ)
    ((powerChart_analytic a ρ).continuousOn.mono
      (fun _ hw => powerChartInnerDomain_subset hρ.le hw.1))

theorem self_mem_scalarPositiveChart {a b : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hb : 0 < b.re) : a ∈ scalarPositiveChart a ρ b :=
  ⟨1, positivePowerChartDomain_one_mem ha ha2 hρ hb, powerChart_one a ρ⟩

end ModifiedCartan
#print axioms ModifiedCartan.powerChart_isOpen_image
#print axioms ModifiedCartan.scalarPositiveChart_isOpen
#print axioms ModifiedCartan.scalarPositiveChart_isPreconnected
