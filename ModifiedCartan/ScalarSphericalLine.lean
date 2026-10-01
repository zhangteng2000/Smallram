import ModifiedCartan.PolynomialVerticalLine

open scoped Topology
open Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Concrete sphere coordinates of the actual curve, including its poles. -/
noncomputable def scalarCurveSphere (f : Curve 1) (z : ℂ) : ℂ × ℂ :=
  scalarSphereProjection (f.coord 0 z) (f.coord 1 z)

theorem scalar_curve_spherical_path_diameter (f : Curve 1) {γ γ' : ℝ → ℂ}
    {a b C : ℝ} (hC : 0 ≤ C)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t)
    (hbound : ∀ t ∈ Icc a b, ‖γ' t‖ * scalarSphericalSpeed f.coord (γ t) ≤ C)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖scalarCurveSphere f (γ x) - scalarCurveSphere f (γ y)‖ ≤ C * (b - a) := by
  have ho {v w : ℝ} (hv : v ∈ Icc a b) (hw : w ∈ Icc a b) (hvw : v ≤ w) :
      ‖scalarCurveSphere f (γ w) - scalarCurveSphere f (γ v)‖ ≤ C * (b - a) := by
    have hi : Icc v w ⊆ Icc a b := fun t ht => ⟨hv.1.trans ht.1, ht.2.trans hw.2⟩
    have hh := scalar_curve_spherical_path_bound f hvw
      (fun t ht => hγ t (hi ht))
      (fun t ht => hbound t (hi ⟨ht.1, ht.2.le⟩))
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hv.1, hw.2]) hC)
  rcases le_total y x with hyx | hxy
  · exact ho hy hx hyx
  · rw [norm_sub_rev]
    exact ho hx hy hxy

/-- Uniform physical spherical diameter along an actual scaled horizontal line. -/
theorem scalar_curve_horizontal_diameter (f : Curve 1) {r a b y C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc a b,
      r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨t, y⟩ : ℂ)) ≤ C)
    {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ Icc a b) (hx₂ : x₂ ∈ Icc a b) :
    ‖scalarCurveSphere f ((r : ℂ) * (⟨x₁, y⟩ : ℂ)) -
      scalarCurveSphere f ((r : ℂ) * (⟨x₂, y⟩ : ℂ))‖ ≤ C * (b - a) := by
  apply scalar_curve_spherical_path_diameter f hC
    (γ' := fun _ => (r : ℂ)) ?_ ?_ hx₁ hx₂
  · intro t _
    simpa only [mul_one] using (hasDerivAt_horizontal_complex t y).const_mul (r : ℂ)
  · intro t ht
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] using hbound t ht

/-- Uniform physical spherical diameter along an actual scaled vertical line. -/
theorem scalar_curve_vertical_diameter (f : Curve 1) {r a b x C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc a b,
      r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨x, t⟩ : ℂ)) ≤ C)
    {y₁ y₂ : ℝ} (hy₁ : y₁ ∈ Icc a b) (hy₂ : y₂ ∈ Icc a b) :
    ‖scalarCurveSphere f ((r : ℂ) * (⟨x, y₁⟩ : ℂ)) -
      scalarCurveSphere f ((r : ℂ) * (⟨x, y₂⟩ : ℂ))‖ ≤ C * (b - a) := by
  apply scalar_curve_spherical_path_diameter f hC
    (γ' := fun _ => (r : ℂ) * Complex.I) ?_ ?_ hy₁ hy₂
  · intro t _
    exact (hasDerivAt_vertical_complex x t).const_mul (r : ℂ)
  · intro t ht
    simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr] using hbound t ht

end ModifiedCartan
#print axioms ModifiedCartan.scalar_curve_spherical_path_diameter
#print axioms ModifiedCartan.scalar_curve_horizontal_diameter
#print axioms ModifiedCartan.scalar_curve_vertical_diameter
