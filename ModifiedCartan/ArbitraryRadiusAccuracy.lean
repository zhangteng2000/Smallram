import ModifiedCartan.ArbitraryRadiusConstruction

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Construct actual arbitrary-radius data with any prescribed Taylor-error
accuracy. This supplies, rather than assumes, the accuracy needed at negative
component exponents in the proof of LaTeX thm:A (b). -/
theorem exists_arbitrary_radius_limits_normalized_with_accuracy {n : ℕ} (f : Curve n) (Amin : ℝ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hf0 : ∀ j, f.coord j 0 ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    ∃ d : ArbitraryRadiusLimitData f r ρ, Amin ≤ d.A := by
  classical
  obtain ⟨ι, hι, b, hb, hbb⟩ := Paper.eq_arbitrary_coefficients f hlin htrans hsmall hρ hl hu hr
  let t : ℕ → ℝ := fun ν => r (ι ν)
  let s : ℕ → ℝ := fun ν => characteristic f (t ν)
  obtain ⟨C, hC, hsc⟩ := characteristic_arbitrary_scale_hypotheses f htrans hsmall
    hρ (ε := ρ / 2) (by positivity) (by linarith) hl hu (hr.comp hι.tendsto_atTop)
  have hsc1 := hsc 1 zero_lt_one
  simp only [arbitraryScaleWeight_one, one_mul] at hsc1
  obtain ⟨ht, hs, hlog, hT, hN⟩ := hsc1
  obtain ⟨A₀, hA₀, hrep⟩ := Paper.lem_replacement n C hC
  let A := max A₀ Amin
  have hA : 0 < A := hA₀.trans_le (le_max_left _ _)
  obtain ⟨L, hL, hrep⟩ := hrep A (le_max_left _ _)
  obtain ⟨H, p, a, η, hp⟩ := hrep f hlin hf0 t s ht hs hlog hT hN
  obtain ⟨ns, hns, hspos, u, v, hcoord, hnorm, hsum, hU, hUV, hUpos⟩ :=
    hp.exists_log_limits hlin hf0 ht hs hN
  have hp1 := hp.comp_tendsto hns.tendsto_atTop
  obtain ⟨ms, hms, E, hEsub, hEfull, hE⟩ := hp1.exists_good_centers
  let τ : ℕ → ℕ := ι ∘ ns ∘ ms
  have hτ : StrictMono τ := hι.comp (hns.comp hms)
  let Hf : ℕ → ℂ → ℂ := fun ν => H (ns (ms ν))
  let pf : ℕ → Index n → Polynomial ℂ := fun ν => p (ns (ms ν))
  let af : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (pf ν)).natDegree → ℂ :=
    fun ν => a (ns (ms ν))
  let ηf : ℕ → ℝ := fun ν => η (ns (ms ν))
  have hpf : PolynomialReplacementData f (fun ν => r (τ ν))
      (fun ν => characteristic f (r (τ ν))) C A L Hf pf af ηf :=
    hp1.comp_tendsto hms.tendsto_atTop
  have hsfpos (ν : ℕ) : 0 < characteristic f (r (τ ν)) := hspos (ms ν)
  have hsf : Tendsto (fun ν => characteristic f (r (τ ν))) atTop atTop :=
    hs.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)
  let U : ℂ → EReal := fun z => Finset.univ.sup (fun j => u j z)
  let V : ℂ → ℝ := fun z => Finset.univ.sup' Finset.univ_nonempty (fun j => v j z)
  have hnormf : LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (characteristic f (r (τ ν)))⁻¹ * Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r (τ ν)) (Hf ν) j z))) V :=
    hnorm.comp_tendsto hms.tendsto_atTop
  have hVpos : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4), 0 ≤ V z := by
    filter_upwards [hUV, ae_restrict_mem measurableSet_ball] with z hz hzD
    have hh := hUpos z hzD
    rw [hz] at hh
    exact_mod_cast hh
  have hpoly := Paper.eq_polynomial_norm hf0 hpf hC hA hL hsfpos hsf hnormf hVpos
  obtain ⟨e, he, hmean⟩ := hpf.normalized_radial_mean
  have horigin := Paper.eq_origin_bound f htrans hρ hl hu (hr.comp hτ.tendsto_atTop)
    hpf.gauge_analytic he hmean hU hUV hUpos hnormf
  refine ⟨{
    subseq := τ
    strictMono := hτ
    scale_pos := hsfpos
    scale_tendsto := hsf
    C := C
    A := A
    L := L
    C_pos := hC
    A_pos := hA
    L_pos := hL
    gauge := Hf
    polynomial := pf
    roots := af
    separatingRadius := ηf
    replacement := hpf
    coefficient := b
    coefficient_analytic := fun i => (hb i).1
    coefficient_limit := fun i => (hb i).2.1.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)
    coefficient_monomial := fun i => (hb i).2.2
    coefficient_bound := hbb
    u := u
    v := v
    coordinate_subharmonic := fun j => (hcoord j).1
    coordinate_nontrivial := fun j => (hcoord j).2.1
    coordinate_representative := fun j => (hcoord j).2.2.1
    coordinate_limit := fun j => (hcoord j).2.2.2.comp_tendsto hms.tendsto_atTop
    coordinate_sum_nonneg := hsum
    U := U
    V := V
    maximum := fun _ => rfl
    real_maximum := fun _ => rfl
    subharmonic := hU
    representative := hUV
    nonneg := hUpos
    norm_limit := hnormf
    polynomial_norm_limit := hpoly
    mean_error := e
    mean_error_zero := he
    radial_mean := hmean
    origin_zero := horigin.1
    origin_bound := horigin.2
    good_centers := {
      centers := E
      subset := hEsub
      full_measure := hEfull
      wronskian_ne_zero := fun z hz => (hE z hz).1
      log_wronskian := fun z hz => (hE z hz).2.1
      root_sum_bound := fun z hz => (hE z hz).2.2 }
  }, le_max_right A₀ Amin⟩

theorem Paper.exists_arbitrary_radius_limits_with_accuracy {n : ℕ} (f : Curve n) (Amin : ℝ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    ∃ (B : Matrix (Index n) (Index n) ℂ) (hB : IsUnit B.det),
      (∀ x, euclideanNorm (fun j => ∑ k, x k * B k j) = euclideanNorm x) ∧
      ∃ d : ArbitraryRadiusLimitData (f.matrixGauge B hB) r ρ, Amin ≤ d.A := by
  obtain ⟨B, hB, hnorm, hB0⟩ :=
    exists_euclidean_matrix_nonzero_coordinates (f.vector 0) (f.vector_ne_zero 0)
  have hT := characteristic_matrixGauge_of_euclidean_isometry f B hB hnorm
  have hN := FewInflection.Curve.matrixGauge_ramification_eq f B hB
  refine ⟨B, hB, hnorm, exists_arbitrary_radius_limits_normalized_with_accuracy
    (f.matrixGauge B hB) Amin
    ((f.matrixGauge_linearlyNonDegenerate_iff B hB).mp hlin)
    ((f.matrixGauge_transcendental_iff B hB).mp htrans) ?_ hB0 hρ ?_ ?_ hr⟩
  · simpa only [SmallRamification, hT, hN] using hsmall
  · simpa only [hT] using hl
  · simpa only [hT] using hu

end ModifiedCartan
#print axioms ModifiedCartan.exists_arbitrary_radius_limits_normalized_with_accuracy
#print axioms ModifiedCartan.Paper.exists_arbitrary_radius_limits_with_accuracy
