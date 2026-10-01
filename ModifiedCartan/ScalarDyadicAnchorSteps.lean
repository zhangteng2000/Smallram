import ModifiedCartan.ScalarMovingLines
import ModifiedCartan.ScalarMovingConnections
import ModifiedCartan.ScalarPeakTracking
import ModifiedCartan.CharacteristicMonotone

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Consecutive dyadic physical anchors have a genuine exponential step bound.
The path at the larger scale joins the old half-radius box to the new unit box
inside one limiting positive sector. Auxiliary to LaTeX thm:A (b). -/
theorem scalar_dyadic_peak_anchor_steps
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    (hstep : Tendsto (fun ν => a (ν + 1) - a ν) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε)
    (hdisks : ∀ b : ℂ, ‖b‖ = 1 → closedBall b (4 * ε) ⊆ scalarFullSector b ρ ∧
      closedBall ((1 / 2 : ℂ) * b) (4 * ε) ⊆ scalarFullSector b ρ)
    {δ : ℝ} (hδ : 0 < δ) {y : ℕ → ℝ}
    (hH : ∀ᶠ ν in atTop, y ν ∈ Icc ((a ν).im - ε) ((a ν).im + ε) ∧
      ∀ t ∈ Icc ((a ν).re - ε) ((a ν).re + ε),
        (2 : ℝ) ^ ν * scalarSphericalSpeed f.coord
          ((((2 : ℝ) ^ ν : ℝ) : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤ Real.exp (-δ * characteristic f ((2 : ℝ) ^ ν))) :
    ∃ η > 0, ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f ((((2 : ℝ) ^ ν : ℝ) : ℂ) * (⟨(a ν).re - ε, y ν⟩ : ℂ)) -
        scalarCurveSphere f ((((2 : ℝ) ^ (ν + 1) : ℝ) : ℂ) * (⟨(a (ν + 1)).re - ε, y (ν + 1)⟩ : ℂ))‖ ≤
          Real.exp (-η * characteristic f ((2 : ℝ) ^ ν)) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hT := characteristic_tendsto_atTop_of_transcendental f htrans
  apply exists_exponential_bound_of_subsequences (hT.comp hpow)
  intro ns hns
  obtain ⟨b, hb, ms, hms, hconv⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
    (fun ν => show a (ns ν) ∈ sphere (0 : ℂ) 1 by
      simpa only [mem_sphere, dist_zero_right] using ha (ns ν))
  have hbnorm : ‖b‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hb
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hbnorm]; norm_num)
  have hb2 : ‖b‖ < 2 := by rw [hbnorm]; norm_num
  have hnsm := hns.comp hms.tendsto_atTop
  have hnext : Tendsto (fun ν => ns (ms ν) + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hnsm
  have hconvNext : Tendsto (fun ν => a (ns (ms ν) + 1)) atTop (𝓝 b) := by
    have hh := (hstep.comp hnsm).add hconv
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using hh
  have hr' := hpow.comp hnext
  obtain ⟨ks, hks, hcross⟩ := scalar_phase_peaks_subsequence_crosses f hlin htrans hsmall hρ hl hu hm hr'
    (a := fun (_ : Fin 1) ν => a (ns (ms ν) + 1)) (a₀ := fun _ => b)
    (fun _ ν => ha (ns (ms ν) + 1)) (fun _ => hconvNext) (fun _ ν => hpeak (ns (ms ν) + 1))
  let τ : ℕ → ℕ := fun ν => ns (ms (ks ν))
  have hτ : Tendsto τ atTop atTop := hnsm.comp hks.tendsto_atTop
  have hτnext : Tendsto (fun ν => τ ν + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hτ
  have haOld : Tendsto (fun ν => (1 / 2 : ℂ) * a (τ ν)) atTop (𝓝 ((1 / 2 : ℂ) * b)) :=
    (hconv.comp hks.tendsto_atTop).const_mul _
  have haNew : Tendsto (fun ν => a (τ ν + 1)) atTop (𝓝 b) := hconvNext.comp hks.tendsto_atTop
  have hscale := hT.comp (hpow.comp hτ)
  have hrad := hpow.comp hτnext
  have hmono (ν : ℕ) : characteristic f ((2 : ℝ) ^ τ ν) ≤ characteristic f ((2 : ℝ) ^ (τ ν + 1)) := by
    apply characteristic_monotoneOn f (pow_pos (by norm_num : (0 : ℝ) < 2) (τ ν))
      (pow_pos (by norm_num : (0 : ℝ) < 2) (τ ν + 1))
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (τ ν)]
  have hc : HasSmallRectangleCrosses f (fun ν => (2 : ℝ) ^ (τ ν + 1))
      (fun ν => characteristic f ((2 : ℝ) ^ τ ν)) (scalarFullSector b ρ) :=
    (hcross 0).mono_scale (Eventually.of_forall hmono)
  have hOld : ∀ᶠ ν in atTop, y (τ ν) / 2 ∈
      Icc (((1 / 2 : ℂ) * a (τ ν)).im - ε / 2) (((1 / 2 : ℂ) * a (τ ν)).im + ε / 2) ∧
      ∀ t ∈ Icc (((1 / 2 : ℂ) * a (τ ν)).re - ε / 2) (((1 / 2 : ℂ) * a (τ ν)).re + ε / 2),
        (2 : ℝ) ^ (τ ν + 1) * scalarSphericalSpeed f.coord
          ((((2 : ℝ) ^ (τ ν + 1) : ℝ) : ℂ) * (⟨t, y (τ ν) / 2⟩ : ℂ)) ≤
            Real.exp (-(δ / 2) * characteristic f ((2 : ℝ) ^ τ ν)) := by
    filter_upwards [hτ.eventually hH, constant_mul_exp_neg_le_half_eventually hscale hδ
      (by norm_num : (0 : ℝ) ≤ 2)] with ν hν habsorb
    have hh := scalar_horizontal_line_double_radius f hν.1 hν.2 habsorb
    simpa only [pow_succ, mul_comm] using hh
  have hNew : ∀ᶠ ν in atTop, y (τ ν + 1) ∈ Icc ((a (τ ν + 1)).im - ε) ((a (τ ν + 1)).im + ε) ∧
      ∀ t ∈ Icc ((a (τ ν + 1)).re - ε) ((a (τ ν + 1)).re + ε),
        (2 : ℝ) ^ (τ ν + 1) * scalarSphericalSpeed f.coord
          ((((2 : ℝ) ^ (τ ν + 1) : ℝ) : ℂ) * (⟨t, y (τ ν + 1)⟩ : ℂ)) ≤
            Real.exp (-δ * characteristic f ((2 : ℝ) ^ τ ν)) := by
    filter_upwards [hτnext.eventually hH] with ν hν
    refine ⟨hν.1, fun t ht => (hν.2 t ht).trans ?_⟩
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hmono ν) (neg_nonpos.mpr hδ.le))
  have hhalfball : closedBall ((1 / 2 : ℂ) * b) (4 * (ε / 2)) ⊆ scalarFullSector b ρ :=
    (closedBall_subset_closedBall (by linarith : 4 * (ε / 2) ≤ 4 * ε)).trans (hdisks b hbnorm).2
  obtain ⟨η, hη, C, hC, hbound⟩ := hc.two_moving_box_anchors_exponential hrad hscale
    (scalarFullSector_isOpen hb0 hρpos) (scalarFullSector_isConnected hb0 hb2 hρpos).isPreconnected
    haOld haNew (half_pos hε) hε hhalfball (hdisks b hbnorm).1 (half_pos hδ) hδ hOld hNew
  refine ⟨ms ∘ ks, hms.tendsto_atTop.comp hks.tendsto_atTop, η, hη, C, hC, ?_⟩
  filter_upwards [hbound] with ν hν
  have he : ((((2 : ℝ) ^ (τ ν + 1) : ℝ) : ℂ) *
      (⟨((1 / 2 : ℂ) * a (τ ν)).re - ε / 2, y (τ ν) / 2⟩ : ℂ)) =
      ((((2 : ℝ) ^ τ ν : ℝ) : ℂ) * (⟨(a (τ ν)).re - ε, y (τ ν)⟩ : ℂ)) := by
    rw [show (2 : ℝ) ^ (τ ν + 1) = 2 * (2 : ℝ) ^ τ ν by rw [pow_succ, mul_comm]]
    exact scalar_doubled_anchor_identity _ _ _ _
  rw [he] at hν
  exact hν

end ModifiedCartan
#print axioms ModifiedCartan.scalar_dyadic_peak_anchor_steps