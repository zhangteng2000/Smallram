import ModifiedCartan.AnnularRatioLimit

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Monotonicity in the spatial variable upgrades weighted integral limits to pointwise limits. -/
theorem tendsto_of_monotone_weighted_integrals
    {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {B : ℝ}
    (hF : ∀ᶠ ν in atTop, ContinuousOn (F ν) (Ioo 0 B))
    (hmono : ∀ᶠ ν in atTop, MonotoneOn (F ν) (Ioo 0 B))
    (hg : ContinuousOn g (Ioo 0 B))
    (hi : ∀ a b : ℝ, 0 < a → a < b → b < B →
      Tendsto (fun ν => ∫ t in a..b, t * F ν t) atTop
        (𝓝 (∫ t in a..b, t * g t))) :
    ∀ t : ℝ, 0 < t → t < B → Tendsto (fun ν => F ν t) atTop (𝓝 (g t)) := by
  intro t ht htB
  have hgc : ContinuousAt g t := hg.continuousAt (isOpen_Ioo.mem_nhds ⟨ht, htB⟩)
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have hn : ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 B ∧ l < g s :=
      (show ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 B from isOpen_Ioo.mem_nhds ⟨ht, htB⟩).and (hgc (Ioi_mem_nhds hl))
    obtain ⟨a₀, b₀, ht₀, hab₀⟩ := hn.exists_Ioo_subset
    let a := (a₀ + t) / 2
    have ha₀ : a₀ < a := by dsimp [a]; linarith [ht₀.1]
    have hat : a < t := by dsimp [a]; linarith [ht₀.1]
    have hnear : ∀ s ∈ Icc a t, s ∈ Ioo 0 B ∧ l < g s := by
      intro s hs
      exact hab₀ ⟨ha₀.trans_le hs.1, hs.2.trans_lt ht₀.2⟩
    have ha : 0 < a := (hnear a ⟨le_rfl, hat.le⟩).1.1
    have hsub : Icc a t ⊆ Ioo 0 B := fun s hs => (hnear s hs).1
    have hmass : 0 < ∫ s in a..t, s :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (continuous_id.intervalIntegrable _ _)
        (fun s hs => ha.trans hs.1) hat
    have hstrict : (∫ s in a..t, s) * l < ∫ s in a..t, s * g s := by
      have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hat
        (show ContinuousOn (fun s : ℝ => s * l) (Icc a t) from (continuous_id.mul_const l).continuousOn)
        (continuousOn_id.mul (hg.mono hsub))
        (fun s hs => mul_le_mul_of_nonneg_left (hnear s ⟨hs.1.le, hs.2⟩).2.le (ha.le.trans hs.1.le))
        ⟨t, ⟨hat.le, le_rfl⟩, mul_lt_mul_of_pos_left hl ht⟩
      simpa only [intervalIntegral.integral_mul_const] using! h
    have he := (tendsto_order.mp (hi a t ha hat htB)).1 _ hstrict
    filter_upwards [hF, hmono, he] with ν hc hm heν
    have hbound : (∫ s in a..t, s * F ν s) ≤ (∫ s in a..t, s) * F ν t := by
      have h := intervalIntegral.integral_mono_on (μ := volume) hat.le
        ((continuousOn_id.mul (hc.mono hsub)).intervalIntegrable_of_Icc hat.le)
        ((show Continuous (fun s : ℝ => s * F ν t) from continuous_id.mul_const _).intervalIntegrable _ _)
        (fun s hs => mul_le_mul_of_nonneg_left (hm (hsub hs) ⟨ht, htB⟩ hs.2) (ha.le.trans hs.1))
      simpa only [intervalIntegral.integral_mul_const] using! h
    nlinarith [heν.trans_le hbound]
  · intro u hu
    have hn : ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 B ∧ g s < u :=
      (show ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 B from isOpen_Ioo.mem_nhds ⟨ht, htB⟩).and (hgc (Iio_mem_nhds hu))
    obtain ⟨a₀, b₀, ht₀, hab₀⟩ := hn.exists_Ioo_subset
    let b := (t + b₀) / 2
    have htb : t < b := by dsimp [b]; linarith [ht₀.2]
    have hb₀ : b < b₀ := by dsimp [b]; linarith [ht₀.2]
    have hnear : ∀ s ∈ Icc t b, s ∈ Ioo 0 B ∧ g s < u := by
      intro s hs
      exact hab₀ ⟨ht₀.1.trans_le hs.1, hs.2.trans_lt hb₀⟩
    have hb : b < B := (hnear b ⟨htb.le, le_rfl⟩).1.2
    have hsub : Icc t b ⊆ Ioo 0 B := fun s hs => (hnear s hs).1
    have hmass : 0 < ∫ s in t..b, s :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (continuous_id.intervalIntegrable _ _)
        (fun s hs => ht.trans hs.1) htb
    have hstrict : (∫ s in t..b, s * g s) < (∫ s in t..b, s) * u := by
      have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt htb
        (continuousOn_id.mul (hg.mono hsub))
        (show ContinuousOn (fun s : ℝ => s * u) (Icc t b) from (continuous_id.mul_const u).continuousOn)
        (fun s hs => mul_le_mul_of_nonneg_left (hnear s ⟨hs.1.le, hs.2⟩).2.le (ht.le.trans hs.1.le))
        ⟨t, ⟨le_rfl, htb.le⟩, mul_lt_mul_of_pos_left hu ht⟩
      simpa only [intervalIntegral.integral_mul_const] using! h
    have he := (tendsto_order.mp (hi t b ht htb hb)).2 _ hstrict
    filter_upwards [hF, hmono, he] with ν hc hm heν
    have hbound : (∫ s in t..b, s) * F ν t ≤ ∫ s in t..b, s * F ν s := by
      have h := intervalIntegral.integral_mono_on (μ := volume) htb.le
        ((show Continuous (fun s : ℝ => s * F ν t) from continuous_id.mul_const _).intervalIntegrable _ _)
        ((continuousOn_id.mul (hc.mono hsub)).intervalIntegrable_of_Icc htb.le)
        (fun s hs => mul_le_mul_of_nonneg_left (hm ⟨ht, htB⟩ (hsub hs) hs.1) (ht.le.trans hs.1))
      simpa only [intervalIntegral.integral_mul_const] using! h
    nlinarith [hbound.trans_lt heν]

end ModifiedCartan
#print axioms ModifiedCartan.tendsto_of_monotone_weighted_integrals


