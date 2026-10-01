import FewInflection.Results
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Elementary convergence-in-measure consequences

The rescaling argument in the paper repeatedly turns a uniform norm bound
whose scalar majorant tends to zero into convergence in measure.  This file
records that implication with the measure and filter parameters explicit.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace FewInflection

theorem tendstoInMeasure_of_norm_sub_le_of_tendsto_zero
    {α ι E : Type*} [MeasurableSpace α] [SeminormedAddCommGroup E]
    {μ : Measure α} {f : ι → α → E} {g : α → E} {c : ι → ℝ} {l : Filter ι}
    (hc : Tendsto c l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ x, ‖f i x - g x‖ ≤ c i) :
    TendstoInMeasure μ f l g := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hcε : ∀ᶠ i in l, c i < ε :=
    (tendsto_order.1 hc).2 ε hε
  have heq : (fun i => μ {x | ε ≤ ‖f i x - g x‖}) =ᶠ[l]
      (fun _ => 0) := by
    filter_upwards [hcε, hbound] with i hiε hi
    have hzero : {x | ε ≤ ‖f i x - g x‖} = (∅ : Set α) := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro hx
      exact (not_le_of_gt (lt_of_le_of_lt (hi x) hiε)) hx
    rw [hzero, measure_empty]
  exact tendsto_const_nhds.congr' heq.symm

theorem tendstoInMeasure_of_norm_le_of_tendsto_zero
    {α ι E : Type*} [MeasurableSpace α] [SeminormedAddCommGroup E]
    {μ : Measure α} {f : ι → α → E} {c : ι → ℝ} {l : Filter ι}
    (hc : Tendsto c l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ x, ‖f i x‖ ≤ c i) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hcε : ∀ᶠ i in l, c i < ε :=
    (tendsto_order.1 hc).2 ε hε
  have heq : (fun i => μ {x | ε ≤ ‖f i x - (0 : E)‖}) =ᶠ[l]
      (fun _ => 0) := by
    filter_upwards [hcε, hbound] with i hiε hi
    have hzero : {x | ε ≤ ‖f i x - (0 : E)‖} = (∅ : Set α) := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, sub_zero]
      intro hx
      exact (not_le_of_gt (lt_of_le_of_lt (hi x) hiε)) hx
    rw [hzero, measure_empty]
  exact tendsto_const_nhds.congr' heq.symm

/- A product with a uniformly bounded factor preserves convergence to zero in
 measure.  The proof uses only the defining superlevel-set characterization,
 so it does not identify convergence in measure with pointwise convergence. -/
theorem tendstoInMeasure_mul_of_norm_le_const_of_tendsto_zero
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : ι → α → ℂ} {l : Filter ι} {C : ℝ}
    (ha : TendstoInMeasure μ a l (fun _ => 0))
    (hb : ∀ᶠ i in l, ∀ x, ‖b i x‖ ≤ C) :
    TendstoInMeasure μ (fun i x => a i x * b i x) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let B : ℝ := max C 1
  have hB : 0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hupper : Tendsto (fun i => μ {x | ε / B ≤ ‖a i x‖}) l (𝓝 0) := by
    have h := (tendstoInMeasure_iff_norm.mp ha) (ε / B) (div_pos hε hB)
    simpa using h
  have hbound : ∀ᶠ i in l, ∀ x, ‖b i x‖ ≤ B := by
    filter_upwards [hb] with i hi x
    exact (hi x).trans (le_max_left _ _)
  have hle : ∀ᶠ i in l,
      μ {x | ε ≤ ‖a i x * b i x‖} ≤
        μ {x | ε / B ≤ ‖a i x‖} := by
    filter_upwards [hbound] with i hi
    apply measure_mono
    intro x hx
    change ε ≤ ‖a i x * b i x‖ at hx
    change ε / B ≤ ‖a i x‖
    by_contra hnot
    have hlt : ‖a i x‖ < ε / B := lt_of_not_ge hnot
    have hmul_le : ‖a i x‖ * ‖b i x‖ ≤ ‖a i x‖ * B :=
      mul_le_mul_of_nonneg_left (hi x) (norm_nonneg _)
    have hmul_lt : ‖a i x‖ * B < (ε / B) * B :=
      mul_lt_mul_of_pos_right hlt hB
    have hprod : ‖a i x * b i x‖ < ε := by
      rw [norm_mul]
      have heq : (ε / B) * B = ε := by
        field_simp [ne_of_gt hB]
      exact hmul_le.trans_lt (hmul_lt.trans_eq heq)
    exact (not_lt_of_ge hx) hprod
  have hzero : ∀ᶠ i in l, 0 ≤ μ {x | ε ≤ ‖a i x * b i x‖} :=
    Filter.Eventually.of_forall (fun _ => bot_le)
  have hprod : Tendsto (fun i => μ {x | ε ≤ ‖a i x * b i x‖}) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper hzero hle
  simpa using hprod

/- A denominator bounded away from zero can be inverted in the preceding
 product estimate.  This is the measure-theoretic quotient step used for
 normalized logarithmic derivatives. -/
theorem tendstoInMeasure_div_of_norm_ge_const_of_tendsto_zero
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : ι → α → ℂ} {l : Filter ι} {c : ℝ}
    (ha : TendstoInMeasure μ a l (fun _ => 0))
    (hc : 0 < c)
    (hb : ∀ᶠ i in l, ∀ x, c ≤ ‖b i x‖) :
    TendstoInMeasure μ (fun i x => a i x / b i x) l (fun _ => 0) := by
  have hinv : ∀ᶠ i in l, ∀ x, ‖(b i x)⁻¹‖ ≤ c⁻¹ := by
    filter_upwards [hb] with i hi x
    have hpos : 0 < ‖b i x‖ := lt_of_lt_of_le hc (hi x)
    rw [norm_inv]
    exact (inv_le_inv₀ hpos hc).2 (hi x)
  simpa [div_eq_mul_inv] using
    (tendstoInMeasure_mul_of_norm_le_const_of_tendsto_zero
      (μ := μ) (a := a) (b := fun i x => (b i x)⁻¹) (C := c⁻¹) ha hinv)

/- Addition is also stable under convergence in measure.  The proof keeps the
superlevel-set union estimate explicit instead of replacing measure
convergence by pointwise convergence. -/
theorem tendstoInMeasure_add_of_tendsto_zero
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : ι → α → ℂ} {l : Filter ι}
    (ha : TendstoInMeasure μ a l (fun _ => 0))
    (hb : TendstoInMeasure μ b l (fun _ => 0)) :
    TendstoInMeasure μ (fun i x => a i x + b i x) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hA : Tendsto (fun i => μ {x | ε / 2 ≤ ‖a i x‖}) l (𝓝 0) := by
    simpa using (tendstoInMeasure_iff_norm.mp ha) (ε / 2) (half_pos hε)
  have hB : Tendsto (fun i => μ {x | ε / 2 ≤ ‖b i x‖}) l (𝓝 0) := by
    simpa using (tendstoInMeasure_iff_norm.mp hb) (ε / 2) (half_pos hε)
  have hle : ∀ᶠ i in l,
      μ {x | ε ≤ ‖a i x + b i x‖} ≤
        μ {x | ε / 2 ≤ ‖a i x‖} + μ {x | ε / 2 ≤ ‖b i x‖} := by
    filter_upwards [] with i
    apply (measure_mono ?_).trans
    exact measure_union_le _ _
    intro x hx
    by_contra hnot
    have hna : ‖a i x‖ < ε / 2 := by
      by_contra hna
      apply hnot
      exact Or.inl (le_of_not_gt hna)
    have hnb : ‖b i x‖ < ε / 2 := by
      by_contra hnb
      apply hnot
      exact Or.inr (le_of_not_gt hnb)
    have hsum : ‖a i x + b i x‖ < ε := by
      calc
        ‖a i x + b i x‖ ≤ ‖a i x‖ + ‖b i x‖ := norm_add_le _ _
        _ < ε / 2 + ε / 2 := add_lt_add hna hnb
        _ = ε := by ring
    exact (not_lt_of_ge hx) hsum
  have hsum : Tendsto
      (fun i => μ {x | ε / 2 ≤ ‖a i x‖} + μ {x | ε / 2 ≤ ‖b i x‖}) l (𝓝 0) := by
    simpa using hA.add hB
  have hnonneg : ∀ᶠ i in l, 0 ≤ μ {x | ε ≤ ‖a i x + b i x‖} :=
    Filter.Eventually.of_forall (fun _ => bot_le)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum (by simpa only [sub_zero] using hnonneg)
      (by simpa only [sub_zero] using hle)

theorem tendstoInMeasure_finset_sum_of_tendsto_zero
    {α ι κ : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} (s : Finset κ) {f : κ → ι → α → ℂ}
    (h : ∀ j ∈ s, TendstoInMeasure μ (fun i x => f j i x) l (fun _ => 0)) :
    TendstoInMeasure μ (fun i x => ∑ j ∈ s, f j i x) l (fun _ => 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [tendstoInMeasure_iff_norm]
      intro ε hε
      simpa [not_le_of_gt hε] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ENNReal)) l (𝓝 0))
  | @insert a s ha ih =>
      have ha' : TendstoInMeasure μ (fun i x => f a i x) l (fun _ => 0) :=
        h a (by simp)
      have hs' : TendstoInMeasure μ (fun i x => ∑ j ∈ s, f j i x) l (fun _ => 0) := by
        apply ih
        intro j hj
        exact h j (by simp [hj])
      simpa [Finset.sum_insert, ha, add_comm] using
        (tendstoInMeasure_add_of_tendsto_zero (μ := μ) ha' hs')

/- Locally uniform convergence on a measurable set implies convergence in
 measure for the restricted measure.  The restriction is explicit, so no
 finiteness assumption on the ambient measure is needed. -/
theorem tendstoInMeasure_restrict_of_tendstoUniformlyOn
    {α ι E : Type*} [MeasurableSpace α] [SeminormedAddCommGroup E]
    {μ : Measure α} {K : Set α} (hK : MeasurableSet K)
    {f : ι → α → E} {g : α → E} {l : Filter ι}
    (h : TendstoUniformlyOn f g l K) :
    TendstoInMeasure (μ.restrict K) f l g := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hU := Metric.tendstoUniformlyOn_iff.mp h (ε / 2) (half_pos hε)
  have heq : (fun i => (μ.restrict K) {x | ε ≤ ‖f i x - g x‖}) =ᶠ[l]
      (fun _ => 0) := by
    filter_upwards [hU] with i hi
    have hae : ∀ᵐ x ∂μ.restrict K,
        x ∉ {x | ε ≤ ‖f i x - g x‖} := by
      filter_upwards [ae_restrict_mem hK] with x hxK
      have hnorm : ‖f i x - g x‖ < ε := by
        calc
          ‖f i x - g x‖ = dist (f i x) (g x) := (dist_eq_norm _ _).symm
          _ = dist (g x) (f i x) := dist_comm _ _
          _ < ε / 2 := hi x hxK
          _ < ε := half_lt_self hε
      exact not_le_of_gt hnorm
    have hz := ae_iff.mp hae
    have hz' : (μ.restrict K) {x | ε ≤ ‖f i x - g x‖} = 0 := by
      simpa using hz
    simp [hz']
  exact tendsto_const_nhds.congr' heq.symm

/- A uniform scalar majorant also gives convergence in the extended `L¹`
 seminorm whenever the underlying measure is finite. -/
theorem tendsto_eLpNorm'_one_of_norm_sub_le_of_tendsto_zero
    {α ι E : Type*} [MeasurableSpace α] [SeminormedAddCommGroup E]
    {μ : Measure α} {f : ι → α → E} {g : α → E} {c : ι → ℝ} {l : Filter ι}
    (hc : Tendsto c l (𝓝 0))
    (hc_nonneg : ∀ᶠ i in l, 0 ≤ c i)
    (hbound : ∀ᶠ i in l, ∀ x, ‖f i x - g x‖ ≤ c i)
    (hμ : μ Set.univ ≠ (⊤ : ENNReal)) :
    Tendsto (fun i => eLpNorm' (fun x => f i x - g x) 1 μ) l (𝓝 0) := by
  have hcoe : Tendsto (fun i => ENNReal.ofReal (c i)) l (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hc
  have hprod : Tendsto (fun i => ENNReal.ofReal (c i) * μ Set.univ) l (𝓝 0) := by
    have hm := ENNReal.Tendsto.mul hcoe (a := (0 : ENNReal))
      (b := μ Set.univ) (by exact Or.inr hμ) tendsto_const_nhds (by simp)
    simpa using hm
  have hle : ∀ᶠ i in l,
      eLpNorm' (fun x => f i x - g x) 1 μ ≤
        ENNReal.ofReal (c i) * μ Set.univ := by
    filter_upwards [hc_nonneg, hbound] with i hci hi
    rw [eLpNorm'_eq_lintegral_enorm]
    simp only [one_div, inv_one, ENNReal.rpow_one]
    apply le_trans (lintegral_mono (fun x => ?_))
      (by rw [lintegral_const])
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hi x)
  have hnonneg : ∀ᶠ i in l,
      0 ≤ eLpNorm' (fun x => f i x - g x) 1 μ :=
    Filter.Eventually.of_forall (fun i => bot_le)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hprod hnonneg hle

theorem exists_strictMono_subsequence_tendsto_ae
    {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
    {μ : Measure α} {f : ℕ → α → E} {g : α → E}
    (hfg : TendstoInMeasure μ f atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
  exact hfg.exists_seq_tendsto_ae

/- A single subsequence can be chosen for two convergence-in-measure
 sequences.  This is the finite diagonal step used when several normalized
 coordinates must be compared almost everywhere on the same set. -/
theorem exists_strictMono_subsequence_tendsto_ae_pair
    {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
    {μ : Measure α} {f₁ f₂ : ℕ → α → E} {g₁ g₂ : α → E}
    (h₁ : TendstoInMeasure μ f₁ atTop g₁)
    (h₂ : TendstoInMeasure μ f₂ atTop g₂) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ᵐ x ∂μ, Tendsto (fun i => f₁ (ns i) x) atTop (𝓝 (g₁ x))) ∧
      (∀ᵐ x ∂μ, Tendsto (fun i => f₂ (ns i) x) atTop (𝓝 (g₂ x))) := by
  obtain ⟨n₁, hn₁, ha₁⟩ := exists_strictMono_subsequence_tendsto_ae h₁
  have h₂' := h₂.comp hn₁.tendsto_atTop
  obtain ⟨n₂, hn₂, ha₂⟩ := exists_strictMono_subsequence_tendsto_ae h₂'
  let ns : ℕ → ℕ := fun i => n₁ (n₂ i)
  have hns : StrictMono ns := hn₁.comp hn₂
  refine ⟨ns, hns, ?_, ha₂⟩
  filter_upwards [ha₁] with x hx
  have ht := hx.comp hn₂.tendsto_atTop
  simpa [ns, Function.comp_def] using ht

/- The same diagonal argument for a finite family of coordinates. -/
theorem exists_strictMono_subsequence_tendsto_ae_fin
    {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
    {μ : Measure α} {m : ℕ} {f : ℕ → Fin m → α → E} {g : Fin m → α → E}
    (h : ∀ j : Fin m,
      TendstoInMeasure μ (fun n x => f n j x) atTop (g j)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, ∀ j : Fin m,
        Tendsto (fun i => f (ns i) j x) atTop (𝓝 (g j x)) := by
  induction m with
  | zero =>
      refine ⟨id, strictMono_id, ?_⟩
      filter_upwards [] with x
      intro j
      exact Fin.elim0 j
  | succ m ih =>
      let ft : ℕ → Fin m → α → E := fun n j x => f n j.succ x
      let gt : Fin m → α → E := fun j => g j.succ
      have ht : ∀ j : Fin m,
          TendstoInMeasure μ (fun n x => ft n j x) atTop (gt j) := by
        intro j
        simpa [ft, gt] using h j.succ
      obtain ⟨n₁, hn₁, ha₁⟩ := ih ht
      have h0 : TendstoInMeasure μ (fun n x => f n 0 x) atTop (g 0) := h 0
      have h0' := h0.comp hn₁.tendsto_atTop
      obtain ⟨n₂, hn₂, ha₂⟩ := exists_strictMono_subsequence_tendsto_ae h0'
      let ns : ℕ → ℕ := fun i => n₁ (n₂ i)
      refine ⟨ns, hn₁.comp hn₂, ?_⟩
      filter_upwards [ha₁, ha₂] with x hxTail hxZero
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa [ns, Function.comp_def] using hxZero
      · have htail := (hxTail j).comp hn₂.tendsto_atTop
        simpa [ft, gt, ns, Function.comp_def] using htail

/- Determinants preserve an already synchronized almost-everywhere matrix
 limit.  This is the finite algebraic step behind Wronskian limits. -/
theorem ae_tendsto_matrix_det_of_ae_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {m : ℕ}
    {Mν : ℕ → α → Matrix (Fin m) (Fin m) ℂ}
    {M : α → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ᵐ x ∂μ,
      Tendsto (fun ν => Mν ν x) atTop (𝓝 (M x))) :
    ∀ᵐ x ∂μ,
      Tendsto (fun ν => (Mν ν x).det) atTop (𝓝 ((M x).det)) := by
  have hdet : Continuous (fun A : Matrix (Fin m) (Fin m) ℂ => A.det) :=
    Continuous.matrix_det continuous_id
  filter_upwards [h] with x hx
  exact hdet.continuousAt.tendsto.comp hx

/- The preceding matrix lemma specializes to Wronskians when every entry of
 the finite derivative jet converges almost everywhere.  The finite index
 intersection is made explicit through `ae_all_iff`; no pointwise upgrade of
 convergence in measure is used here. -/
theorem ae_tendsto_wronskian_of_ae_tendsto_iteratedDeriv
    {n : ℕ} {F : ℕ → Index n → ℂ → ℂ} {G : Index n → ℂ → ℂ}
    {μ : Measure ℂ}
    (h : ∀ i j : Index n,
      ∀ᵐ z ∂μ,
        Tendsto (fun ν => iteratedDeriv (i : ℕ) (F ν j) z) atTop
          (𝓝 (iteratedDeriv (i : ℕ) (G j) z))) :
    ∀ᵐ z ∂μ,
      Tendsto (fun ν => wronskian n (F ν) z) atTop
        (𝓝 (wronskian n G z)) := by
  let Mν : ℕ → ℂ → Matrix (Index n) (Index n) ℂ := fun ν z i j =>
    iteratedDeriv (i : ℕ) (F ν j) z
  let M : ℂ → Matrix (Index n) (Index n) ℂ := fun z i j =>
    iteratedDeriv (i : ℕ) (G j) z
  have hcommon : ∀ᵐ z ∂μ, ∀ i j : Index n,
      Tendsto (fun ν => iteratedDeriv (i : ℕ) (F ν j) z) atTop
        (𝓝 (iteratedDeriv (i : ℕ) (G j) z)) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => h i j
  have hentries : ∀ᵐ z ∂μ,
      Tendsto (fun ν => Mν ν z) atTop (𝓝 (M z)) := by
    filter_upwards [hcommon] with z hz
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    exact hz i j
  have hdet := ae_tendsto_matrix_det_of_ae_tendsto hentries
  filter_upwards [hdet] with z hz
  simpa [Mν, M, wronskian] using hz

end FewInflection
