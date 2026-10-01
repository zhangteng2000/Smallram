import ModifiedCartan.TwoPhaseForms
import ModifiedCartan.ScalarPositiveChart
import Mathlib.Analysis.Complex.RealDeriv

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Every two-phase model has a nonempty smooth ball inside its original
ball, including the absolute-value alternative. -/
theorem HasTwoPhaseFormOn.exists_smooth_subball
    {F : ℂ → ℝ} {b c : ℂ} {s : ℝ} (hs : 0 < s)
    (h : HasTwoPhaseFormOn F b c (ball c s)) :
    ∃ z : ℂ, ∃ δ > 0, ball z δ ⊆ ball c s ∧ ContDiffOn ℝ 1 F (ball z δ) := by
  have hlin : ContDiff ℝ 1 (fun z : ℂ => (b * (z - c)).re) :=
    Complex.reCLM.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hp : ContDiff ℝ 1 (fun z : ℂ => F c + (b * (z - c)).re) := contDiff_const.add hlin
  have hm : ContDiff ℝ 1 (fun z : ℂ => F c - (b * (z - c)).re) := contDiff_const.sub hlin
  rcases h with h | h | h
  · exact ⟨c, s, hs, Subset.rfl, hp.contDiffOn.congr h⟩
  · exact ⟨c, s, hs, Subset.rfl, hm.contDiffOn.congr h⟩
  · by_cases hb : b = 0
    · refine ⟨c, s, hs, Subset.rfl, hp.contDiffOn.congr ?_⟩
      intro z hz
      simpa only [hb, zero_mul, Complex.zero_re, abs_zero] using h hz
    · have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
      let t : ℝ := s * ‖b‖ / 2
      have ht : 0 < t := by dsimp only [t]; positivity
      let z : ℂ := c + (t : ℂ) / b
      have hz : z ∈ ball c s := by
        rw [mem_ball, dist_eq_norm]
        simp only [z, add_sub_cancel_left, norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le]
        dsimp only [t]
        have he : s * ‖b‖ / 2 / ‖b‖ = s / 2 := by field_simp
        rw [he]; linarith
      have hzpos : 0 < (b * (z - c)).re := by
        have he : b * (z - c) = (t : ℂ) := by dsimp only [z]; field_simp; ring
        rw [he, Complex.ofReal_re]; exact ht
      have hopen : IsOpen {w : ℂ | 0 < (b * (w - c)).re} :=
        isOpen_lt continuous_const (by fun_prop)
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
        ((isOpen_ball.inter hopen).mem_nhds ⟨hz, hzpos⟩)
      refine ⟨z, δ, hδ, fun w hw => (hδsub hw).1, hp.contDiffOn.congr ?_⟩
      intro w hw
      have he := h (hδsub hw).1
      change F w = F c + |(b * (w - c)).re| at he
      rw [he, abs_of_pos (show 0 < (b * (w - c)).re from (hδsub hw).2)]

/-- Smooth patches occur inside every nonempty open subregion of a locally
two-phase function; no differentiability hypothesis is imposed on the limit. -/
theorem LocallyTwoPhaseOn.exists_smooth_subball
    {U O : Set ℂ} {F : ℂ → ℝ} {b : ℂ}
    (h : LocallyTwoPhaseOn U F b) (hO : IsOpen O) (hOU : O ⊆ U) (hne : O.Nonempty) :
    ∃ z : ℂ, ∃ δ > 0, ball z δ ⊆ O ∧ ContDiffOn ℝ 1 F (ball z δ) := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨s, hs, _, hform⟩ := h c (hOU hc)
  obtain ⟨t, ht, htO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hc)
  obtain ⟨z, δ, hδ, hδsub, hsmooth⟩ :=
    (hform.mono (ball_subset_ball (min_le_left s t))).exists_smooth_subball (lt_min hs ht)
  exact ⟨z, δ, hδ, hδsub.trans ((ball_subset_ball (min_le_right s t)).trans htO), hsmooth⟩

/-- Smoothness of the pullback transfers to the physical plane through the
proved analytic inverse of the power chart. -/
theorem contDiffOn_of_powerChart_pullback
    {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 1 ≤ ρ)
    {u : ℂ → ℝ} {S : Set ℂ} (hS : S ⊆ powerChartDomain a ρ)
    (h : ContDiffOn ℝ 1 (fun w => u (powerChart a ρ w)) S) :
    ContDiffOn ℝ 1 u (powerChart a ρ '' S) := by
  have hinv : ContDiffOn ℝ 1 (powerChartInverse a ρ) (powerChart a ρ '' S) :=
    ((powerChartInverse_analytic ha hρ).contDiffOn_of_completeSpace
      (n := 1)).restrict_scalars ℝ |>.mono (image_mono hS)
  have hmap : MapsTo (powerChartInverse a ρ) (powerChart a ρ '' S) S := by
    rintro z ⟨w, hw, rfl⟩
    rwa [powerChart_inverse ha hρ (hS hw)]
  apply (h.comp hinv hmap).congr
  rintro z ⟨w, hw, rfl⟩
  simp only [Function.comp_apply, powerChart_inverse ha hρ (hS hw)]

/-- Every nonempty physical open region in a power chart contains an actual
smooth ball for a limit with the proved local two-phase structure. -/
theorem LocallyTwoPhaseOn.exists_smooth_physical_subball
    {a b : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 1 ≤ ρ) {u : ℂ → ℝ}
    (h : LocallyTwoPhaseOn (powerChartDomain a ρ) (fun w => u (powerChart a ρ w)) b)
    {O : Set ℂ} (hO : IsOpen O) (hOG : O ⊆ powerChart a ρ '' powerChartDomain a ρ)
    (hne : O.Nonempty) :
    ∃ z : ℂ, ∃ δ > 0, ball z δ ⊆ O ∧ ContDiffOn ℝ 1 u (ball z δ) := by
  let W := powerChartDomain a ρ ∩ powerChart a ρ ⁻¹' O
  have hW : IsOpen W := (powerChart_analytic a ρ).continuousOn.isOpen_inter_preimage
    (powerChartDomain_isOpen a ρ) hO
  have hWne : W.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨w, hw, rfl⟩ := hOG hz
    exact ⟨w, hw, hz⟩
  obtain ⟨w, δ, hδ, hδW, hsm⟩ := h.exists_smooth_subball hW inter_subset_left hWne
  have hδG : ball w δ ⊆ powerChartDomain a ρ := hδW.trans inter_subset_left
  have himage : IsOpen (powerChart a ρ '' ball w δ) :=
    powerChart_isOpen_image ha (lt_of_lt_of_le zero_lt_one hρ) isOpen_ball hδG
  have hwim : powerChart a ρ w ∈ powerChart a ρ '' ball w δ :=
    ⟨w, mem_ball_self hδ, rfl⟩
  obtain ⟨ε, hε, hεim⟩ := Metric.mem_nhds_iff.mp (himage.mem_nhds hwim)
  refine ⟨powerChart a ρ w, ε, hε, ?_,
    (contDiffOn_of_powerChart_pullback ha hρ hδG hsm).mono hεim⟩
  intro z hz
  obtain ⟨v, hv, rfl⟩ := hεim hz
  exact (hδW hv).2

/-- A continuous inequality proved at centers of smooth balls extends to the
entire open chart region. Smooth patches are constructed from the local forms. -/
theorem LocallyTwoPhaseOn.le_of_smooth_physical_balls
    {a b : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 1 ≤ ρ) {u g : ℂ → ℝ}
    (h : LocallyTwoPhaseOn (powerChartDomain a ρ) (fun w => u (powerChart a ρ w)) b)
    {O : Set ℂ} (hO : IsOpen O) (hOG : O ⊆ powerChart a ρ '' powerChartDomain a ρ)
    (hu : ContinuousOn u O) (hg : ContinuousOn g O)
    (htest : ∀ z : ℂ, ∀ δ > 0, ball z δ ⊆ O → ContDiffOn ℝ 1 u (ball z δ) → u z ≤ g z) :
    ∀ z ∈ O, u z ≤ g z := by
  intro z hz
  by_contra hbad
  have hlt := (hg.continuousAt (hO.mem_nhds hz)).eventually_lt
    (hu.continuousAt (hO.mem_nhds hz)) (lt_of_not_ge hbad)
  have hnb : ∀ᶠ w in 𝓝 z, w ∈ O ∧ g w < u w :=
    (show ∀ᶠ w in 𝓝 z, w ∈ O from hO.mem_nhds hz).and hlt
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnb
  have hδO : ball z δ ⊆ O := fun w hw => (hδsub hw).1
  obtain ⟨w, ε, hε, hεsub, hsm⟩ := h.exists_smooth_physical_subball ha hρ
    isOpen_ball (hδO.trans hOG) (nonempty_ball.mpr hδ)
  exact (not_lt_of_ge (htest w ε hε (hεsub.trans hδO) hsm))
    (hδsub (hεsub (mem_ball_self hε))).2

end ModifiedCartan
#print axioms ModifiedCartan.HasTwoPhaseFormOn.exists_smooth_subball
#print axioms ModifiedCartan.LocallyTwoPhaseOn.exists_smooth_subball
#print axioms ModifiedCartan.contDiffOn_of_powerChart_pullback
#print axioms ModifiedCartan.LocallyTwoPhaseOn.exists_smooth_physical_subball
#print axioms ModifiedCartan.LocallyTwoPhaseOn.le_of_smooth_physical_balls
