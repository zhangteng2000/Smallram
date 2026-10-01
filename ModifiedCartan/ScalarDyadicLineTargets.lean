import ModifiedCartan.ScalarDyadicTargets

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
namespace ScalarDyadicPeakTargetData

noncomputable def anchor {f : Curve 1} {a : ℕ → ℂ} {ρ : ℝ}
    (q : ScalarDyadicPeakTargetData f a ρ) (ν : ℕ) : ℂ × ℂ :=
  scalarCurveSphere f ((((2 : ℝ) ^ ν : ℝ) : ℂ) * (⟨(a ν).re - q.width, q.height ν⟩ : ℂ))

/-- All points on the constructed dyadic horizontal line approach its fixed
target with an exponential rate, uniformly along the entire segment. -/
theorem horizontal_close {f : Curve 1} {a : ℕ → ℂ} {ρ : ℝ}
    (q : ScalarDyadicPeakTargetData f a ρ) (htrans : f.Transcendental) :
    ∃ η > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ∀ t ∈ Icc ((a ν).re - q.width) ((a ν).re + q.width),
        ‖scalarCurveSphere f ((((2 : ℝ) ^ ν : ℝ) : ℂ) * (⟨t, q.height ν⟩ : ℂ)) -
          scalarSphereValue q.target‖ ≤ C * Real.exp (-η * characteristic f ((2 : ℝ) ^ ν)) := by
  let η := min q.lineRate q.decayRate
  have hη : 0 < η := lt_min q.lineRate_pos q.decayRate_pos
  have hs := (characteristic_tendsto_atTop_of_transcendental f htrans).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  refine ⟨η, hη, 2 * q.width + 2, by linarith [q.width_pos], ?_⟩
  filter_upwards [q.good, q.close, hs.eventually_ge_atTop 0] with ν hgood hclose hsν
  intro t ht
  change 0 ≤ characteristic f ((2 : ℝ) ^ ν) at hsν
  have hrad : 0 ≤ (2 : ℝ) ^ ν := (pow_pos (by norm_num : (0 : ℝ) < 2) ν).le
  have hd := scalar_curve_horizontal_diameter f hrad (Real.exp_pos (-q.lineRate * characteristic f ((2 : ℝ) ^ ν))).le
    hgood.2 ht
    (show (a ν).re - q.width ∈ Icc ((a ν).re - q.width) ((a ν).re + q.width) from
      ⟨le_rfl, by linarith [q.width_pos]⟩)
  have he₁ := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (show η ≤ q.lineRate from min_le_left _ _)) hsν)
  have he₂ := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (show η ≤ q.decayRate from min_le_right _ _)) hsν)
  have hd' : ‖scalarCurveSphere f ((((2 : ℝ) ^ ν : ℝ) : ℂ) * (⟨t, q.height ν⟩ : ℂ)) - q.anchor ν‖ ≤
      2 * q.width * Real.exp (-η * characteristic f ((2 : ℝ) ^ ν)) := by
    have hl : (a ν).re + q.width - ((a ν).re - q.width) = 2 * q.width := by ring
    rw [hl] at hd
    exact hd.trans (by simpa only [mul_comm, Function.comp_def] using mul_le_mul_of_nonneg_right he₁ (by linarith [q.width_pos] : 0 ≤ 2 * q.width))
  calc
    _ ≤ ‖scalarCurveSphere f ((((2 : ℝ) ^ ν : ℝ) : ℂ) * (⟨t, q.height ν⟩ : ℂ)) - q.anchor ν‖ +
        ‖q.anchor ν - scalarSphereValue q.target‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * q.width * Real.exp (-η * characteristic f ((2 : ℝ) ^ ν)) +
        2 * Real.exp (-η * characteristic f ((2 : ℝ) ^ ν)) :=
      add_le_add hd' (hclose.trans (mul_le_mul_of_nonneg_left he₂ (by norm_num)))
    _ = _ := by ring

end ScalarDyadicPeakTargetData
end ModifiedCartan
#print axioms ModifiedCartan.ScalarDyadicPeakTargetData.horizontal_close