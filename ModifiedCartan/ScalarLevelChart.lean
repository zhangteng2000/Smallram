import ModifiedCartan.ScalarSectorComponent

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A strict positive level region in one power chart. -/
noncomputable def levelPowerChartDomain (a : ℂ) (ρ : ℝ) (b : ℂ) (ℓ : ℝ) : Set ℂ :=
  powerChartInnerDomain a ρ ∩ {w | ℓ < (b * w).re}

theorem levelPowerChartDomain_isOpen (a : ℂ) (ρ : ℝ) (b : ℂ) (ℓ : ℝ) :
    IsOpen (levelPowerChartDomain a ρ b ℓ) :=
  (powerChartInnerDomain_isOpen a ρ).inter
    (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul continuous_id)))

theorem levelPowerChartDomain_convex (a : ℂ) (ρ : ℝ) (b : ℂ) (ℓ : ℝ) :
    Convex ℝ (levelPowerChartDomain a ρ b ℓ) := by
  refine (powerChartInnerDomain_convex a ρ).inter ?_
  intro x hx y hy p q hp hq hpq
  change ℓ < (b * (p • x + q • y)).re
  simp only [mul_add, mul_smul_comm, Complex.add_re, Complex.smul_re, smul_eq_mul]
  change ℓ < (b * x).re at hx
  change ℓ < (b * y).re at hy
  have hpqpos : 0 < p ∨ 0 < q := by
    by_contra hn
    push Not at hn
    linarith
  have h₁ : 0 ≤ p * ((b * x).re - ℓ) := mul_nonneg hp (sub_pos.mpr hx).le
  have h₂ : 0 ≤ q * ((b * y).re - ℓ) := mul_nonneg hq (sub_pos.mpr hy).le
  have hℓ : p * ℓ + q * ℓ = ℓ := by rw [← add_mul, hpq, one_mul]
  rcases hpqpos with hp' | hq'
  · have hh := mul_pos hp' (sub_pos.mpr hx)
    nlinarith
  · have hh := mul_pos hq' (sub_pos.mpr hy)
    nlinarith

theorem levelPowerChartDomain_subset_positive {a b : ℂ} {ρ ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    levelPowerChartDomain a ρ b ℓ ⊆ positivePowerChartDomain a ρ b :=
  fun _ hw => ⟨hw.1, hℓ.trans_lt hw.2⟩

noncomputable def scalarLevelChart (a : ℂ) (ρ : ℝ) (b : ℂ) (ℓ : ℝ) : Set ℂ :=
  powerChart a ρ '' levelPowerChartDomain a ρ b ℓ

theorem scalarLevelChart_isOpen {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (b : ℂ) (ℓ : ℝ) :
    IsOpen (scalarLevelChart a ρ b ℓ) :=
  powerChart_isOpen_image ha hρ (levelPowerChartDomain_isOpen a ρ b ℓ)
    (fun _ hw => powerChartInnerDomain_subset hρ.le hw.1)

theorem scalarLevelChart_isPreconnected (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (b : ℂ) (ℓ : ℝ) :
    IsPreconnected (scalarLevelChart a ρ b ℓ) :=
  (levelPowerChartDomain_convex a ρ b ℓ).isPreconnected.image (powerChart a ρ)
    ((powerChart_analytic a ρ).continuousOn.mono
      (fun _ hw => powerChartInnerDomain_subset hρ.le hw.1))

theorem scalarLevelChart_subset_positive {a b : ℂ} {ρ ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    scalarLevelChart a ρ b ℓ ⊆ scalarPositiveChart a ρ b := by
  rintro z ⟨w, hw, rfl⟩
  exact ⟨w, levelPowerChartDomain_subset_positive hℓ hw, rfl⟩

theorem ArbitraryRadiusLimitData.scalarLevelChart_lower
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    (hb : b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2))
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : ∀ z ∈ scalarLevelChart a ρ b ℓ, ℓ < (d.U z).toReal := by
  rintro z ⟨w, hw, rfl⟩
  have he := d.scalar_norm_positiveChart_pullback hρ ha b hb
    (levelPowerChartDomain_subset_positive hℓ hw)
  dsimp only at he
  rw [he]
  exact hw.2

end ModifiedCartan
#print axioms ModifiedCartan.levelPowerChartDomain_convex
#print axioms ModifiedCartan.scalarLevelChart_isPreconnected
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalarLevelChart_lower
