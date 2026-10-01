import ModifiedCartan.SubharmonicL1Bounds
import ModifiedCartan.SubharmonicLocalIntegrability

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem exists_ereal_lower_anchor_of_l1_bound {S : Set ℂ} {u : ℂ → EReal} {B : ℝ}
    (hS : MeasurableSet S) (hSpos : volume S ≠ 0) (hSfinite : volume S < ⊤)
    (hfinite : ∀ᵐ z ∂volume.restrict S, u z ≠ ⊥ ∧ u z ≠ ⊤)
    (hint : IntegrableOn (fun z => (u z).toReal) S)
    (hB : (∫ z in S, ‖(u z).toReal‖) ≤ B) :
    ∃ z ∈ S, ((-(B / (volume S).toReal + 1) : ℝ) : EReal) ≤ u z := by
  have harea : 0 < (volume S).toReal := ENNReal.toReal_pos hSpos hSfinite.ne
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hSfinite⟩
  by_contra! hnot
  have hnorm : ∀ᵐ z ∂volume.restrict S,
      B / (volume S).toReal + 1 ≤ ‖(u z).toReal‖ := by
    filter_upwards [hfinite, ae_restrict_mem hS] with z hz hzS
    have hneg := hnot z hzS
    rw [← EReal.coe_toReal hz.2 hz.1, EReal.coe_lt_coe_iff] at hneg
    have habs := neg_le_abs ((u z).toReal)
    rw [Real.norm_eq_abs]
    linarith
  have hle := integral_mono_ae (integrable_const (B / (volume S).toReal + 1)) hint.norm hnorm
  rw [setIntegral_const, smul_eq_mul] at hle
  change (volume S).toReal * (B / (volume S).toReal + 1) ≤ _ at hle
  have heq : (volume S).toReal * (B / (volume S).toReal + 1) = B + (volume S).toReal := by
    field_simp
  rw [heq] at hle
  linarith


theorem subharmonic_uniform_l1_locally_of_one_open_set {U : Set ℂ} {u : ℕ → ℂ → EReal}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hu : ∀ n, IsSubharmonicOn U (u n))
    (hnz : ∀ n, ∃ c ∈ U, u n c ≠ ⊥)
    (hbdd : ∀ K, IsCompact K → K ⊆ U → ∃ M : ℝ,
      ∀ n z, z ∈ K → u n z ≤ (M : EReal))
    (hinit : ∃ V : Set ℂ, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧ ∃ B : ℝ,
      ∀ n, IntegrableOn (fun z => (u n z).toReal) V ∧ (∫ z in V, ‖(u n z).toReal‖) ≤ B) :
    ∀ x ∈ U, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ B : ℝ,
      ∀ n, IntegrableOn (fun z => (u n z).toReal) V ∧ (∫ z in V, ‖(u n z).toReal‖) ≤ B := by
  let G : Set ℂ := {x | ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ B : ℝ,
    ∀ n, IntegrableOn (fun z => (u n z).toReal) V ∧ (∫ z in V, ‖(u n z).toReal‖) ≤ B}
  have hG : IsOpen G := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨V, hV, hxV, hVU, B, hB⟩
    exact mem_of_superset (hV.mem_nhds hxV) (fun y hy => ⟨V, hV, hy, hVU, B, hB⟩)
  have hUGne : (U ∩ G).Nonempty := by
    obtain ⟨V, hV, ⟨x, hx⟩, hVU, B, hB⟩ := hinit
    exact ⟨x, hVU hx, V, hV, hx, hVU, B, hB⟩
  have hclosed : closure G ∩ U ⊆ G := by
    rintro x ⟨hxG, hxU⟩
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
    let r := ε / 4
    have hr : 0 < r := by dsimp only [r]; positivity
    have hrU : closedBall x (3 * r) ⊆ U :=
      (closedBall_subset_ball (by dsimp only [r]; linarith)).trans hεU
    obtain ⟨y, hyx, hyG⟩ := mem_closure_iff.mp hxG (ball x r) isOpen_ball (mem_ball_self hr)
    obtain ⟨V, hV, hyV, hVU, B, hB⟩ := hyG
    let W := ball x r ∩ V
    have hW : IsOpen W := isOpen_ball.inter hV
    have hWpos : volume W ≠ 0 := hW.measure_ne_zero volume ⟨y, hyx, hyV⟩
    have hWsubset : W ⊆ U := inter_subset_right.trans hVU
    have hWfinite : volume W < ⊤ :=
      (measure_mono (inter_subset_left.trans ball_subset_closedBall)).trans_lt
        (isCompact_closedBall x r).measure_lt_top
    let L : ℝ := B / (volume W).toReal + 1
    have hanchors (n : ℕ) : ∃ a ∈ ball x r, ((-L : ℝ) : EReal) ≤ u n a := by
      have hWint : IntegrableOn (fun z => (u n z).toReal) W := (hB n).1.mono_set inter_subset_right
      have hWnorm : (∫ z in W, ‖(u n z).toReal‖) ≤ B := by
        have hmono := setIntegral_mono_set (s := W) (t := V) (hB n).1.norm
          (Eventually.of_forall (fun z => norm_nonneg ((u n z).toReal)))
          (Eventually.of_forall inter_subset_right)
        exact hmono.trans (hB n).2
      have hfinite := ((hu n).ae_finite hU hUc (hnz n)).filter_mono
        (ae_mono (Measure.restrict_mono_set _ hWsubset))
      obtain ⟨a, haW, ha⟩ := exists_ereal_lower_anchor_of_l1_bound hW.measurableSet hWpos hWfinite
        hfinite hWint hWnorm
      exact ⟨a, haW.1, ha⟩
    obtain ⟨M, hM⟩ := hbdd (closedBall x (3 * r)) (isCompact_closedBall x (3 * r)) hrU
    refine ⟨ball x r, isOpen_ball, mem_ball_self hr, ?_,
      (Real.pi * (2 * r) ^ 2) * (2 * max M 0 + L), ?_⟩
    · exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hrU
    · intro n
      obtain ⟨a, ha, halow⟩ := hanchors n
      exact (hu n).l1_bound_of_anchor_in_ball hr hrU (le_max_right M 0)
        (fun z hz => (hM n z hz).trans (EReal.coe_le_coe_iff.mpr (le_max_left M 0))) ha halow
  exact hUc.subset_of_closure_inter_subset hG hUGne hclosed


theorem integral_norm_le_sum_of_finite_cover {ι : Type*} [Fintype ι]
    {K : Set ℂ} {V : ι → Set ℂ} {f : ℂ → ℝ}
    (hcover : K ⊆ ⋃ i, V i) (hfK : IntegrableOn f K) (hfV : ∀ i, IntegrableOn f (V i)) :
    (∫ z in K, ‖f z‖) ≤ ∑ i, ∫ z in V i, ‖f z‖ := by
  have hnn (S : Set ℂ) : 0 ≤ ∫ z in S, ‖f z‖ := integral_nonneg (fun z => norm_nonneg (f z))
  apply (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun i _ => hnn (V i)))).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn (V i)),
    ofReal_integral_norm_eq_lintegral_enorm hfK]
  have heq (i : ι) : ENNReal.ofReal (∫ z in V i, ‖f z‖) = ∫⁻ z in V i, ‖f z‖ₑ :=
    ofReal_integral_norm_eq_lintegral_enorm (hfV i)
  simp_rw [heq]
  calc
    _ ≤ ∫⁻ z in ⋃ i, V i, ‖f z‖ₑ := lintegral_mono_set hcover
    _ ≤ _ := by simpa only [tsum_fintype] using lintegral_iUnion_le V (fun z => ‖f z‖ₑ)

theorem subharmonic_uniform_l1_on_compacts_of_one_open_set {U : Set ℂ} {u : ℕ → ℂ → EReal}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hu : ∀ n, IsSubharmonicOn U (u n))
    (hnz : ∀ n, ∃ c ∈ U, u n c ≠ ⊥)
    (hbdd : ∀ K, IsCompact K → K ⊆ U → ∃ M : ℝ,
      ∀ n z, z ∈ K → u n z ≤ (M : EReal))
    (hinit : ∃ V : Set ℂ, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧ ∃ B : ℝ,
      ∀ n, IntegrableOn (fun z => (u n z).toReal) V ∧ (∫ z in V, ‖(u n z).toReal‖) ≤ B) :
    ∀ K, IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧
      ∀ n, IntegrableOn (fun z => (u n z).toReal) K ∧ (∫ z in K, ‖(u n z).toReal‖) ≤ B := by
  classical
  have hlocal := subharmonic_uniform_l1_locally_of_one_open_set hU hUc hu hnz hbdd hinit
  intro K hK hKU
  choose V hV hxV hVU B hB using (fun x : K => hlocal x (hKU x.2))
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover V hV (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV _⟩)
  have hcover : K ⊆ ⋃ i : S, V i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hS hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  refine ⟨max (∑ i : S, B i) 0, le_max_right _ _, ?_⟩
  intro n
  have hint := (hu n).integrableOn_compact_toReal hU hUc (hnz n) hK hKU
  refine ⟨hint, ?_⟩
  have hsum := integral_norm_le_sum_of_finite_cover hcover hint (fun i : S => (hB i n).1)
  have hsumB : (∑ i : S, ∫ z in V i, ‖(u n z).toReal‖) ≤ ∑ i : S, B i :=
    Finset.sum_le_sum (fun (i : S) _ => (hB i n).2)
  exact hsum.trans (hsumB.trans (le_max_left _ _))


end ModifiedCartan

