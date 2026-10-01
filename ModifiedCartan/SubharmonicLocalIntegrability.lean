import ModifiedCartan.SubharmonicBasic

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric TopologicalSpace

set_option autoImplicit false

namespace ModifiedCartan

/-- Connectedness propagates the disks on which finiteness and integrability
are obtained directly from one finite center. -/
theorem IsSubharmonicOn.exists_finite_center_disk {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hne : ∃ c ∈ U, u c ≠ ⊥) :
    ∀ x ∈ U, ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ closedBall c r ⊆ U ∧ u c ≠ ⊥ ∧ x ∈ ball c r := by
  let G : Set ℂ := {x | ∃ c : ℂ, ∃ r : ℝ,
    0 < r ∧ closedBall c r ⊆ U ∧ u c ≠ ⊥ ∧ x ∈ ball c r}
  have hG : IsOpen G := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨c, r, hr, hrU, hc, hxr⟩
    exact mem_of_superset (isOpen_ball.mem_nhds hxr)
      (fun y hy => ⟨c, r, hr, hrU, hc, hy⟩)
  have hUGne : (U ∩ G).Nonempty := by
    obtain ⟨c, hcU, hc⟩ := hne
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hcU
    refine ⟨c, hcU, c, ε / 2, half_pos hε, ?_, hc, mem_ball_self (half_pos hε)⟩
    exact (closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hclosed : closure G ∩ U ⊆ G := by
    rintro x ⟨hxG, hxU⟩
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
    obtain ⟨y, hyx, hyG⟩ := mem_closure_iff.mp hxG (ball x (ε / 4)) isOpen_ball
      (mem_ball_self (by positivity))
    obtain ⟨c, r, hr, hrU, hc, hyr⟩ := hyG
    let V := ball x (ε / 4) ∩ ball c r
    have hV : IsOpen V := isOpen_ball.inter isOpen_ball
    have hVpos : volume V ≠ 0 := hV.measure_ne_zero volume ⟨y, hyx, hyr⟩
    have hfinite : ∀ᵐ z ∂volume.restrict V, u z ≠ ⊥ :=
      ((hu.ae_finite_on_ball hr hrU hc).mono (fun _ hz => hz.1)).filter_mono
        (ae_mono (Measure.restrict_mono_set _ inter_subset_right))
    obtain ⟨z, hzV, hzu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hVpos hfinite
    have hzx : dist z x < ε / 4 := hzV.1
    refine ⟨z, ε / 2, half_pos hε, ?_, hzu, ?_⟩
    · exact (closedBall_subset_ball' (by linarith : ε / 2 + dist z x < ε)).trans hεU
    · change dist x z < ε / 2
      rw [dist_comm]
      linarith
  exact hUc.subset_of_closure_inter_subset hG hUGne hclosed

theorem ae_on_set_of_open_neighborhoods {U : Set ℂ} {P : ℂ → Prop}
    (h : ∀ x ∈ U, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ ∀ᵐ z ∂volume.restrict V, P z) :
    ∀ᵐ z ∂volume.restrict U, P z := by
  classical
  choose V hV hxV hP using (fun x : U => h x x.2)
  have hcover : U ⊆ ⋃ x : U, V x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV _⟩
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable V hV
  letI : Countable T := hT.to_subtype
  have hcover' : U ⊆ ⋃ i : T, V i := by
    intro z hz
    have hz' : z ∈ ⋃ i ∈ T, V i := by rw [hTU]; exact hcover hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz'
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  have hall : ∀ᵐ z ∂volume.restrict (⋃ i : T, V i), P z :=
    (ae_restrict_iUnion_iff (fun i : T => V i) P).mpr (fun i => hP i)
  exact hall.filter_mono (ae_mono (Measure.restrict_mono_set _ hcover'))

theorem IsSubharmonicOn.ae_finite {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hne : ∃ c ∈ U, u c ≠ ⊥) :
    ∀ᵐ z ∂volume.restrict U, u z ≠ ⊥ ∧ u z ≠ ⊤ := by
  apply ae_on_set_of_open_neighborhoods
  intro x hx
  obtain ⟨c, r, hr, hrU, hc, hxr⟩ := hu.exists_finite_center_disk hU hUc hne x hx
  exact ⟨ball c r, isOpen_ball, hxr, hu.ae_finite_on_ball hr hrU hc⟩

theorem IsSubharmonicOn.locallyIntegrableOn_toReal {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hne : ∃ c ∈ U, u c ≠ ⊥) : LocallyIntegrableOn (fun z => (u z).toReal) U := by
  intro x hx
  obtain ⟨c, r, hr, hrU, hc, hxr⟩ := hu.exists_finite_center_disk hU hUc hne x hx
  exact ⟨ball c r, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hxr),
    hu.integrableOn_toReal_ball hr hrU hc⟩

theorem IsSubharmonicOn.integrableOn_compact_toReal {U K : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hne : ∃ c ∈ U, u c ≠ ⊥) (hK : IsCompact K) (hKU : K ⊆ U) :
    IntegrableOn (fun z => (u z).toReal) K :=
  (hu.locallyIntegrableOn_toReal hU hUc hne).integrableOn_compact_subset hKU hK


end ModifiedCartan

