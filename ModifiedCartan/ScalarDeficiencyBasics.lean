import ModifiedCartan.ScalarValueCharacteristic

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- The extended-real lower limit commutes with subtraction from a finite
constant. Infinite values of the upper limit are retained. -/
theorem ereal_liminf_const_sub {α : Type*} {l : Filter α} [l.NeBot]
    (c : ℝ) (v : α → ℝ) :
    liminf (fun x => ((c - v x : ℝ) : EReal)) l =
      (c : EReal) - limsup (fun x => (v x : EReal)) l := by
  let C : α → EReal := fun _ => c
  let V : α → EReal := fun x => v x
  have hid : (fun x => ((c - v x : ℝ) : EReal)) = C + (-V) := by
    ext x
    change ((c - v x : ℝ) : EReal) = (c : EReal) + -(v x : EReal)
    rw [EReal.coe_sub]
    rfl
  rw [hid]
  have hc₁ : liminf C l = (c : EReal) := liminf_const _
  have hc₂ : limsup C l = (c : EReal) := limsup_const _
  have hneg : liminf (-V) l = -limsup V l := EReal.liminf_neg
  apply le_antisymm
  · have hh := EReal.liminf_add_le (u := C) (v := -V) (f := l)
      (Or.inl (by rw [hc₂]; exact EReal.coe_ne_bot c))
      (Or.inl (by rw [hc₂]; exact EReal.coe_ne_top c))
    simpa only [hc₂, hneg, sub_eq_add_neg, V] using hh
  · have hh := EReal.le_liminf_add (u := C) (v := -V) (f := l)
    simpa only [hc₁, hneg, sub_eq_add_neg, V] using hh

/-- The deficiency as actually defined in the manuscript is nonnegative. -/
theorem scalarDeficiency_nonneg {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) (a : WithTop ℂ) : 0 ≤ scalarDeficiency f a := by
  apply le_liminf_of_le (by isBoundedDefault)
  filter_upwards [(scalarCharacteristic_tendsto_atTop hf htrans).eventually
    (eventually_gt_atTop 0)] with r hr
  change (0 : EReal) ≤ ((ValueDistribution.proximity f a r / scalarCharacteristic f r : ℝ) : EReal)
  exact EReal.coe_nonneg.mpr (div_nonneg (ValueDistribution.proximity_nonneg (f := f) (a := a) r) hr.le)

/-- Both summands of the normalized value characteristic are bounded above by
its total, at every sufficiently large radius. -/
theorem scalar_proximity_counting_ratio_le_value_ratio {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) (a : WithTop ℂ) : ∀ᶠ r in atTop,
    ValueDistribution.proximity f a r / scalarCharacteristic f r ≤
      ValueDistribution.characteristic f a r / scalarCharacteristic f r ∧
    ValueDistribution.logCounting f a r / scalarCharacteristic f r ≤
      ValueDistribution.characteristic f a r / scalarCharacteristic f r := by
  filter_upwards [(scalarCharacteristic_tendsto_atTop hf htrans).eventually
    (eventually_gt_atTop 0), eventually_ge_atTop (1 : ℝ)] with r hr hr1
  constructor <;> apply div_le_div_of_nonneg_right _ hr.le
  · exact le_add_of_nonneg_right (ValueDistribution.logCounting_nonneg hr1)
  · exact le_add_of_nonneg_left (ValueDistribution.proximity_nonneg r)

/-- Literal upper limiting proximity ratio, before taking the lower limit. -/
theorem scalar_proximity_ratio_limsup_le_one {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) (a : WithTop ℂ) :
    limsup (fun r => ((ValueDistribution.proximity f a r / scalarCharacteristic f r : ℝ) : EReal))
      atTop ≤ 1 := by
  have ht : Tendsto (fun r => ((ValueDistribution.characteristic f a r /
      scalarCharacteristic f r : ℝ) : EReal)) atTop (𝓝 1) := by
    simpa only [EReal.coe_one] using EReal.tendsto_coe.mpr
      (scalarValueCharacteristic_ratio_tendsto_one hf htrans a)
  rw [← ht.limsup_eq]
  refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [scalar_proximity_counting_ratio_le_value_ratio hf htrans a] with r hr
  exact_mod_cast hr.1

/-- First-main-theorem upper bound for the literal scalar deficiency. -/
theorem scalarDeficiency_le_one {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) (a : WithTop ℂ) : scalarDeficiency f a ≤ 1 :=
  (liminf_le_limsup).trans (scalar_proximity_ratio_limsup_le_one hf htrans a)

/-- All counting upper limits are finite and nonnegative; no default conversion
of an infinite EReal to a real is used. -/
theorem scalar_counting_ratio_limsup_mem_Icc {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) (a : WithTop ℂ) :
    limsup (fun r => ((ValueDistribution.logCounting f a r / scalarCharacteristic f r : ℝ) : EReal))
      atTop ∈ Icc (0 : EReal) 1 := by
  constructor
  · apply le_trans (b := liminf (fun r =>
      ((ValueDistribution.logCounting f a r / scalarCharacteristic f r : ℝ) : EReal)) atTop)
    · apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [(scalarCharacteristic_tendsto_atTop hf htrans).eventually
        (eventually_gt_atTop 0), eventually_ge_atTop (1 : ℝ)] with r hr hr1
      exact_mod_cast div_nonneg (ValueDistribution.logCounting_nonneg hr1) hr.le
    · exact liminf_le_limsup
  · have ht : Tendsto (fun r => ((ValueDistribution.characteristic f a r /
        scalarCharacteristic f r : ℝ) : EReal)) atTop (𝓝 1) := by
      simpa only [EReal.coe_one] using EReal.tendsto_coe.mpr
        (scalarValueCharacteristic_ratio_tendsto_one hf htrans a)
    rw [← ht.limsup_eq]
    refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [scalar_proximity_counting_ratio_le_value_ratio hf htrans a] with r hr
    exact_mod_cast hr.2

/-- The first-main-theorem identity for the exact deficiency definition in the
introduction to LaTeX `thm:A`, including the value infinity. -/
theorem scalarDeficiency_eq_one_sub_limsup_counting {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) (a : WithTop ℂ) :
    scalarDeficiency f a = 1 - limsup (fun r =>
      ((ValueDistribution.logCounting f a r / scalarCharacteristic f r : ℝ) : EReal)) atTop := by
  have ht := (scalarValueCharacteristic_ratio_tendsto_one hf htrans a).sub_const 1
  have he : (fun r => ValueDistribution.characteristic f a r / scalarCharacteristic f r - 1) =
      (fun r => ValueDistribution.proximity f a r / scalarCharacteristic f r -
        (1 - ValueDistribution.logCounting f a r / scalarCharacteristic f r)) := by
    ext r
    simp only [ValueDistribution.characteristic, Pi.add_apply, add_div]
    ring
  rw [he] at ht
  have hx := (ereal_extrema_eq_of_sub_tendsto_zero (by simpa only [sub_self] using ht)).2
  change liminf (fun r => ((ValueDistribution.proximity f a r / scalarCharacteristic f r : ℝ) : EReal))
    atTop = _
  rw [hx, ereal_liminf_const_sub]
  rfl

/-- A proved real proximity-ratio limit identifies the literal deficiency. -/
theorem scalarDeficiency_eq_of_proximity_ratio_tendsto {f : ℂ → ℂ} {a : WithTop ℂ} {d : ℝ}
    (h : Tendsto (fun r => ValueDistribution.proximity f a r / scalarCharacteristic f r)
      atTop (𝓝 d)) : scalarDeficiency f a = (d : EReal) :=
  (EReal.tendsto_coe.mpr h).liminf_eq

/-- A proved counting-ratio limit gives the deficiency by the first main theorem. -/
theorem scalarDeficiency_eq_of_counting_ratio_tendsto {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) {a : WithTop ℂ} {d : ℝ}
    (h : Tendsto (fun r => ValueDistribution.logCounting f a r / scalarCharacteristic f r)
      atTop (𝓝 d)) : scalarDeficiency f a = ((1 - d : ℝ) : EReal) := by
  rw [scalarDeficiency_eq_one_sub_limsup_counting hf htrans a,
    (EReal.tendsto_coe.mpr h).limsup_eq, EReal.coe_sub, EReal.coe_one]

/-- The deficiency is a finite real number, with the canonical EReal value
preserved exactly by conversion. -/
theorem scalarDeficiency_coe_toReal {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) (a : WithTop ℂ) :
    ((scalarDeficiency f a).toReal : EReal) = scalarDeficiency f a := by
  apply EReal.coe_toReal
  · exact ne_of_lt ((scalarDeficiency_le_one hf htrans a).trans_lt (EReal.coe_lt_top 1))
  · exact ne_of_gt ((EReal.bot_lt_coe 0).trans_le (scalarDeficiency_nonneg hf htrans a))

/-- Changing only the exceptional point values of a meromorphic representative
cannot change its deficiency. -/
theorem scalarDeficiency_congr_codiscrete {f g : ℂ → ℂ}
    (he : f =ᶠ[codiscrete ℂ] g) (a : WithTop ℂ) :
    scalarDeficiency f a = scalarDeficiency g a := by
  apply liminf_congr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [ValueDistribution.proximity_congr_codiscrete he hr.ne']
  change ((ValueDistribution.proximity g a r / ValueDistribution.characteristic f ⊤ r : ℝ) : EReal) = _
  rw [ValueDistribution.characteristic_congr_codiscrete he hr.ne']

end ModifiedCartan
#print axioms ModifiedCartan.scalarDeficiency_le_one
#print axioms ModifiedCartan.scalarDeficiency_eq_one_sub_limsup_counting



