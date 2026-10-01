import ModifiedCartan.ScalarComparableHorizontalLines
import ModifiedCartan.ScalarDyadicCeilingLines
import ModifiedCartan.ScalarDyadicTargetUniqueness
import ModifiedCartan.ScalarVariableConnections

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- On convergent comparable geometric data, connect the actual new horizontal
anchor to the already constructed fixed dyadic target. -/
theorem scalar_comparable_anchor_target_subsequence
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {c y : ℕ → ℝ} {b : ℕ → ℂ}
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) {c₀ : ℝ} (hcLim : Tendsto c atTop (𝓝 c₀))
    {a₀ : ℂ} (haLim : Tendsto (fun ν => a (n ν)) atTop (𝓝 a₀))
    (hbClose : Tendsto (fun ν => b ν - a (n ν)) atTop (𝓝 0))
    (q : ScalarDyadicPeakTargetData f a ρ)
    (hqRad : ∀ z : ℂ, ‖z‖ = 1 → ∀ t ∈ Icc (1 / 2 : ℝ) 1,
      closedBall ((t : ℂ) * z) (4 * q.width) ⊆ scalarFullSector z ρ)
    {δ : ℝ} (hδ : 0 < δ)
    (hH : ∀ᶠ ν in atTop, y ν ∈ Icc ((b ν).im - q.width) ((b ν).im + q.width) ∧
      ∀ t ∈ Icc ((b ν).re - q.width) ((b ν).re + q.width),
        (c ν * (2 : ℝ) ^ n ν) * scalarSphericalSpeed f.coord
          (((c ν * (2 : ℝ) ^ n ν : ℝ) : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤
            Real.exp (-δ * characteristic f (c ν * (2 : ℝ) ^ n ν))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ η > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f (((c (ns ν) * (2 : ℝ) ^ n (ns ν) : ℝ) : ℂ) *
          (⟨(b (ns ν)).re - q.width, y (ns ν)⟩ : ℂ)) - scalarSphereValue q.target‖ ≤
        C * Real.exp (-η * characteristic f ((2 : ℝ) ^ n (ns ν))) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hm0 : m ≠ 0 := by intro hz; simp only [hz, Nat.cast_zero, zero_div] at hm; linarith
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hbase := hpow.comp hn
  have hbig := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) hbase
  have hc₀ : c₀ ∈ Icc (1 : ℝ) 2 := isClosed_Icc.mem_of_tendsto hcLim (Eventually.of_forall hc)
  have ha₀norm : ‖a₀‖ = 1 := by
    have hh : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 ‖a₀‖) := by simpa only [ha] using haLim.norm
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have ha₀ne : a₀ ≠ 0 := norm_ne_zero_iff.mp (by rw [ha₀norm]; norm_num)
  have hbLim : Tendsto b atTop (𝓝 a₀) := by
    simpa only [sub_add_cancel, zero_add] using hbClose.add haLim
  let bigPeak : ℕ → ℂ := fun ν => scalarComparablePeakCenter f m ((2 : ℝ) ^ n ν) 2 (a (n ν))
  have hBigClose := scalarComparablePeakCenter_difference_tendsto_zero f hlin htrans hsmall hρ hl hu hm
    hbase (fun _ => show (2 : ℝ) ∈ Icc (1 : ℝ) 2 from ⟨by norm_num, le_rfl⟩) (fun ν => ha (n ν))
  have hBigLim : Tendsto bigPeak atTop (𝓝 a₀) := by
    simpa only [sub_add_cancel, zero_add, bigPeak, Function.comp_def] using hBigClose.add haLim
  obtain ⟨ns, hns, hcross⟩ := scalar_phase_peaks_subsequence_crosses f hlin htrans hsmall hρ hl hu hm hbig
    (a := fun (_ : Fin 1) ν => bigPeak ν) (a₀ := fun _ => a₀)
    (fun _ ν => scalarComparablePeakCenter_norm f m _ _ (ha (n ν))) (fun _ => hBigLim)
    (fun _ ν => scalarComparablePeakCenter_peak f hm0 _ _ (hpeak (n ν)))
  have hscale := (characteristic_tendsto_atTop_of_transcendental f htrans).comp (hbase.comp hns.tendsto_atTop)
  have hrad := hbig.comp hns.tendsto_atTop
  have hmono (ν : ℕ) : characteristic f ((2 : ℝ) ^ n (ns ν)) ≤
      characteristic f (2 * (2 : ℝ) ^ n (ns ν)) :=
    (characteristic_comparable_mono f (pow_pos (by norm_num : (0 : ℝ) < 2) _)
      (show (2 : ℝ) ∈ Icc (1 : ℝ) 2 from ⟨by norm_num, le_rfl⟩)).1
  have hh := (hcross 0).mono_scale (Eventually.of_forall hmono)
  have holdSource : ∀ᶠ ν in atTop, q.height (n ν) ∈ Icc ((a (n ν)).im - q.width) ((a (n ν)).im + q.width) ∧
      ∀ t ∈ Icc ((a (n ν)).re - q.width) ((a (n ν)).re + q.width),
        (1 * (2 : ℝ) ^ n ν) * scalarSphericalSpeed f.coord
          (((1 * (2 : ℝ) ^ n ν : ℝ) : ℂ) * (⟨t, q.height (n ν)⟩ : ℂ)) ≤
            Real.exp (-q.lineRate * characteristic f (1 * (2 : ℝ) ^ n ν)) := by
    simpa only [one_mul, Function.comp_def] using hn.eventually q.good
  have hOld := scalar_horizontal_line_at_dyadic_ceiling f htrans hn
    (fun _ => show (1 : ℝ) ∈ Icc (1 : ℝ) 2 from ⟨le_rfl, by norm_num⟩) q.lineRate_pos holdSource
  have hNew := scalar_horizontal_line_at_dyadic_ceiling f htrans hn hc hδ hH
  have hOldCenter : Tendsto (fun ν => (((1 / 2 : ℝ) : ℂ) * a (n (ns ν)))) atTop
      (𝓝 (((1 / 2 : ℝ) : ℂ) * a₀)) := (haLim.comp hns.tendsto_atTop).const_mul _
  have hNewCenter : Tendsto (fun ν => (((c (ns ν) / 2 : ℝ) : ℂ) * b (ns ν))) atTop
      (𝓝 (((c₀ / 2 : ℝ) : ℂ) * a₀)) :=
    ((Complex.continuous_ofReal.tendsto _).comp ((hcLim.comp hns.tendsto_atTop).div_const 2)).mul
      (hbLim.comp hns.tendsto_atTop)
  have hNewWidth := ((hcLim.comp hns.tendsto_atTop).div_const 2).mul_const q.width
  have hwNew : 0 < (c₀ / 2) * q.width := mul_pos (by linarith [hc₀.1]) q.width_pos
  have hOldBall : closedBall (((1 / 2 : ℝ) : ℂ) * a₀) (4 * ((1 / 2 : ℝ) * q.width)) ⊆ scalarFullSector a₀ ρ :=
    (closedBall_subset_closedBall (by linarith [q.width_pos])).trans
      (hqRad a₀ ha₀norm (1 / 2) ⟨le_rfl, by norm_num⟩)
  have hNewBall : closedBall (((c₀ / 2 : ℝ) : ℂ) * a₀) (4 * ((c₀ / 2) * q.width)) ⊆ scalarFullSector a₀ ρ :=
    (closedBall_subset_closedBall (by nlinarith [hc₀.2, q.width_pos])).trans
      (hqRad a₀ ha₀norm (c₀ / 2) ⟨by linarith [hc₀.1], by linarith [hc₀.2]⟩)
  obtain ⟨η, hη, C, hC, hconn⟩ := hh.two_variable_box_anchors_exponential hrad hscale
    (scalarFullSector_isOpen ha₀ne hρpos)
    (scalarFullSector_isConnected ha₀ne (by rw [ha₀norm]; norm_num) hρpos).isPreconnected
    hNewCenter hOldCenter hNewWidth tendsto_const_nhds hwNew (mul_pos (by norm_num) q.width_pos)
    hNewBall hOldBall (half_pos hδ) (half_pos q.lineRate_pos)
    (hns.tendsto_atTop.eventually hNew) (hns.tendsto_atTop.eventually hOld)
  let newAnchor : ℕ → ℂ × ℂ := fun ν => scalarCurveSphere f
    (((c (ns ν) * (2 : ℝ) ^ n (ns ν) : ℝ) : ℂ) * (⟨(b (ns ν)).re - q.width, y (ns ν)⟩ : ℂ))
  have hconnect : ∃ η > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ‖newAnchor ν - q.anchor (n (ns ν))‖ ≤ C * Real.exp (-η * characteristic f ((2 : ℝ) ^ n (ns ν))) := by
    refine ⟨η, hη, C, hC, ?_⟩
    filter_upwards [hconn] with ν hν
    have hcpos : 0 < c (ns ν) := lt_of_lt_of_le zero_lt_one (hc (ns ν)).1
    have hratio : 2 / c (ns ν) ≠ 0 := (div_pos (by norm_num) hcpos).ne'
    have he : (2 / c (ns ν)) * (c (ns ν) * (2 : ℝ) ^ n (ns ν)) = 2 * (2 : ℝ) ^ n (ns ν) := by field_simp
    have hnewEq := scalar_scaled_anchor_identity hratio
      (c (ns ν) * (2 : ℝ) ^ n (ns ν)) q.width (y (ns ν)) (b (ns ν))
    simp only [inv_div, he] at hnewEq
    have holdEq := scalar_scaled_anchor_identity (by norm_num : (2 : ℝ) ≠ 0)
      ((2 : ℝ) ^ n (ns ν)) q.width (q.height (n (ns ν))) (a (n (ns ν)))
    rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num] at holdEq
    dsimp only [Function.comp_def] at hν
    rw [hnewEq, holdEq] at hν
    exact hν
  have htarget : ∃ η > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ‖q.anchor (n (ns ν)) - scalarSphereValue q.target‖ ≤
        C * Real.exp (-η * characteristic f ((2 : ℝ) ^ n (ns ν))) :=
    ⟨q.decayRate, q.decayRate_pos, 2, by norm_num, (hn.comp hns.tendsto_atTop).eventually q.close⟩
  obtain ⟨η', hη', C', hC', hb⟩ := exponential_distance_trans hscale hconnect htarget
  exact ⟨ns, hns, η', hη', C', hC', hb⟩

end ModifiedCartan
#print axioms ModifiedCartan.scalar_comparable_anchor_target_subsequence