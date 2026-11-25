import QuantumNLS.Ext025GP04FlowR30m

/-! Common real Picard neighborhoods, uniqueness, and reversed-time differentials. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Topology Filter ODE
open scoped NNReal
namespace QuantumNLS.Ext025GP04LocalR30m

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A positive state margin and common bounds give a positive two-sided time
with the Picard displacement bound and contraction constant at most 1/2. -/
theorem common_time {f : ℝ → E → E} {c η : ℝ} {p : E} {R r L K : ℝ≥0}
    (hη : 0 < η) (hmargin : r < R)
    (hL : ∀ t ∈ Icc (c - η) (c + η), LipschitzOnWith K (f t) (closedBall p R))
    (hc : ∀ x ∈ closedBall p R, ContinuousOn (fun t => f t x) (Icc (c - η) (c + η)))
    (hb : ∀ t ∈ Icc (c - η) (c + η), ∀ x ∈ closedBall p R, ‖f t x‖ ≤ L) :
    ∃ T > (0 : ℝ), T ≤ η ∧ 2 * (K : ℝ) * T ≤ 1 ∧
      ∃ s : Icc (c - T) (c + T), (s : ℝ) = c ∧ IsPicardLindelof f s p R r L K := by
  let T := min η (min (((R : ℝ) - r) / ((L : ℝ) + 1)) (1 / (2 * ((K : ℝ) + 1))))
  have hm : (r : ℝ) < R := NNReal.coe_lt_coe.mpr hmargin
  have hT : 0 < T := lt_min hη (lt_min (by positivity) (by positivity))
  have hTη : T ≤ η := min_le_left _ _
  have hLT : (L : ℝ) * T ≤ (R : ℝ) - r := by
    have hbound : T ≤ ((R : ℝ) - r) / ((L : ℝ) + 1) :=
      (min_le_right η _).trans (min_le_left _ _)
    have h := (le_div_iff₀ (show 0 < (L : ℝ) + 1 by positivity)).mp hbound
    nlinarith
  have hKT : 2 * (K : ℝ) * T ≤ 1 := by
    have hbound : T ≤ 1 / (2 * ((K : ℝ) + 1)) :=
      (min_le_right η _).trans (min_le_right _ _)
    have h := (le_div_iff₀ (show 0 < 2 * ((K : ℝ) + 1) by positivity)).mp hbound
    nlinarith
  let s : Icc (c - T) (c + T) := ⟨c, by constructor <;> linarith⟩
  have hsub : Icc (c - T) (c + T) ⊆ Icc (c - η) (c + η) :=
    Icc_subset_Icc (by linarith) (by linarith)
  refine ⟨T, hT, hTη, hKT, s, rfl, ?_⟩
  refine ⟨fun t ht => hL t (hsub ht), fun x hx => (hc x hx).mono hsub,
    fun t ht => hb t (hsub ht), ?_⟩
  have hmax : max (c + T - c) (c - (c - T)) = T := by
    rw [show c + T - c = T by ring, show c - (c - T) = T by ring, max_self]
  change (L : ℝ) * max (c + T - c) (c - (c - T)) ≤ (R : ℝ) - r
  rw [hmax]
  exact hLT

variable {f : ℝ → E → E} {a b : ℝ} {s : Icc a b} {p : E} {R r L K : ℝ≥0}

/-- Uniqueness on the entire chosen closed time interval for continuous
solutions of the integral equation in the Picard ball. -/
theorem unique_integral (hf : IsPicardLindelof f s p R r L K)
    (hshort : 2 * (K : ℝ) * max (b - s) (s - a) ≤ 1)
    {v w : ℝ → E} {x : E} (hv : Continuous v) (hw : Continuous w)
    (hvm : MapsTo v (Icc a b) (closedBall p R)) (hwm : MapsTo w (Icc a b) (closedBall p R))
    (hvq : ∀ t ∈ Icc a b, v t = picard f s x v t)
    (hwq : ∀ t ∈ Icc a b, w t = picard f s x w t) : EqOn v w (Icc a b) := by
  have hv0 : v s = x := by simpa using hvq s s.2
  have hw0 : w s = x := by simpa using hwq s s.2
  intro t ht
  have hb := Ext025GP04FlowR30m.separated hf hshort hv hw hvm hwm hv0 hw0 hvq hwq t ht
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hb) (norm_nonneg _)))

/-- A forward map and a map starting at the target time have inverse
differentials wherever their initial neighborhoods overlap along a solution. -/
theorem inverse_differential {t : Icc a b} {r' L' K' : ℝ≥0}
    (hs : IsPicardLindelof f s p R r L K) (ht : IsPicardLindelof f t p R r' L' K')
    (hshorts : 2 * (K : ℝ) * max (b - s) (s - a) ≤ 1)
    (hshortt : 2 * (K' : ℝ) * max (b - t) (t - a) ≤ 1)
    {φ ψ : ℝ → E → E}
    (hφ : ∀ x ∈ ball p r, Continuous (fun z => φ z x) ∧
      MapsTo (fun z => φ z x) (Icc a b) (closedBall p R) ∧
      ∀ z ∈ Icc a b, φ z x = picard f s x (fun q => φ q x) z)
    (hψ : ∀ y ∈ ball p r', Continuous (fun z => ψ z y) ∧
      MapsTo (fun z => ψ z y) (Icc a b) (closedBall p R) ∧
      ∀ z ∈ Icc a b, ψ z y = picard f t y (fun q => ψ q y) z)
    {x : E} {D D' : E →L[ℝ] E}
    (hx : x ∈ ball p r) (hy : φ t x ∈ ball p r')
    (hD : HasFDerivAt (φ t) D x) (hD' : HasFDerivAt (ψ s) D' (φ t x)) :
    ψ s (φ t x) = x ∧ D'.comp D = ContinuousLinearMap.id ℝ E ∧
      D.comp D' = ContinuousLinearMap.id ℝ E := by
  have rebase {v : ℝ → E} {c d : Icc a b} {x' : E}
      (hfc : ContinuousOn (fun z => f z (v z)) (Icc a b))
      (hq : ∀ z ∈ Icc a b, v z = picard f c x' v z)
      (z : ℝ) (hz : z ∈ Icc a b) : v z = picard f d (v d) v z := by
    have hint (u w : Icc a b) : IntervalIntegrable (fun z => f z (v z))
        MeasureTheory.volume u w :=
      (hfc.mono (uIcc_subset_Icc u.2 w.2)).intervalIntegrable
    have hi := intervalIntegral.integral_add_adjacent_intervals (hint c d) (hint d ⟨z,hz⟩)
    rw [hq z hz, hq d d.2, picard_apply, picard_apply, picard_apply]
    rw [← hi]
    abel
  have rev (u : E) (hu : u ∈ ball p r) (hv : φ t u ∈ ball p r') :
      ψ s (φ t u) = u := by
    obtain ⟨huc, hum, huq⟩ := hφ u hu
    obtain ⟨hvc, hvm, hvq⟩ := hψ (φ t u) hv
    have he := unique_integral ht hshortt hvc huc hvm hum hvq
      (rebase (d := t) (ODE.continuousOn_comp hs.continuousOn_uncurry huc.continuousOn hum) huq) s.2
    exact he.trans (by simpa using huq s s.2)
  have fwd (v : E) (hv : v ∈ ball p r') (hu : ψ s v ∈ ball p r) :
      φ t (ψ s v) = v := by
    obtain ⟨huc, hum, huq⟩ := hφ (ψ s v) hu
    obtain ⟨hvc, hvm, hvq⟩ := hψ v hv
    have he := unique_integral hs hshorts huc hvc hum hvm huq
      (rebase (d := s) (ODE.continuousOn_comp ht.continuousOn_uncurry hvc.continuousOn hvm) hvq) t.2
    exact he.trans (by simpa using hvq t t.2)
  have hrev := rev x hx hy
  have hleft : (ψ s ∘ φ t) =ᶠ[𝓝 x] id := by
    filter_upwards [isOpen_ball.mem_nhds hx,
      hD.continuousAt.eventually (isOpen_ball.mem_nhds hy)] with u hu hv
    exact rev u hu hv
  have hright : (φ t ∘ ψ s) =ᶠ[𝓝 (φ t x)] id := by
    filter_upwards [isOpen_ball.mem_nhds hy, hD'.continuousAt.eventually
      (isOpen_ball.mem_nhds (show ψ s (φ t x) ∈ ball p r by rwa [hrev]))] with v hv hu
    exact fwd v hv hu
  have hD₁ : HasFDerivAt id (D'.comp D) x := (hD'.comp x hD).congr_of_eventuallyEq hleft.symm
  have hD₂ : HasFDerivAt (φ t) D (ψ s (φ t x)) := by rwa [hrev]
  have hD₃ : HasFDerivAt id (D.comp D') (φ t x) :=
    (hD₂.comp _ hD').congr_of_eventuallyEq hright.symm
  exact ⟨hrev, hD₁.unique (hasFDerivAt_id x), hD₃.unique (hasFDerivAt_id _)⟩

/-- The graph of a finite real trajectory segment admits a finite subcover
by its open local flow neighborhoods. -/
theorem finite_trajectory_cover {ι : Type*} {a b : ℝ} {v : ℝ → E}
    (hv : ContinuousOn v (Icc a b)) (U : ι → Set (ℝ × E))
    (ho : ∀ i, IsOpen (U i))
    (hcover : ∀ t ∈ Icc a b, ∃ i, (t,v t) ∈ U i) :
    ∃ F : Finset ι, ∀ t ∈ Icc a b, ∃ i ∈ F, (t,v t) ∈ U i := by
  let g : ℝ → ℝ × E := fun t => (t, v t)
  have hc : IsCompact (g '' Icc a b) := isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hv)
  obtain ⟨F,hF⟩ := hc.elim_finite_subcover U ho (by
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨i,hi⟩ := hcover t ht
    exact mem_iUnion.mpr ⟨i,hi⟩)
  refine ⟨F, fun t ht => ?_⟩
  have htF : (t,v t) ∈ ⋃ i ∈ F, U i := hF ⟨t,ht,rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp htF
  obtain ⟨hif, htu⟩ := mem_iUnion.mp hi
  exact ⟨i, hif, htu⟩

/-- A bounded field on a compact trajectory gives a strong endpoint limit.
The endpoint belongs to the compact set and can serve as new Picard data. -/
theorem compact_endpoint {a b : ℝ} (hab : a < b) {v : ℝ → E} {S : Set E} {M : ℝ≥0}
    (hS : IsCompact S) (hm : MapsTo v (Ico a b) S)
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt v (f t (v t)) (Ico a b) t)
    (hb : ∀ t ∈ Ico a b, ‖f t (v t)‖ ≤ M) :
    ∃ x ∈ S, Tendsto v (𝓝[Ico a b] b) (𝓝 x) := by
  have hl : LipschitzOnWith M v (Ico a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    exact (convex_Ico a b).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun t ht => (hd t ht).hasFDerivWithinAt)
      (fun t ht => by simpa only [ContinuousLinearMap.norm_toSpanSingleton] using hb t ht) hy hx
  have hcl : b ∈ closure (Ico a b) := by
    rw [closure_Ico hab.ne]
    exact ⟨hab.le, le_rfl⟩
  have : (𝓝[Ico a b] b).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hC : Cauchy (Filter.map v (𝓝[Ico a b] b)) :=
    (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le hl.uniformContinuousOn inf_le_right
  obtain ⟨x,hx⟩ := cauchy_map_iff_exists_tendsto.mp hC
  exact ⟨x, hS.isClosed.mem_of_tendsto hx (eventually_mem_nhdsWithin.mono hm), hx⟩

/-- Restart the local integral equation from the strong endpoint limit, using
the field bounds in the selected neighborhood of the limiting point. -/
theorem compact_restart {a b : ℝ} (hab : a < b) {v : ℝ → E} {S : Set E}
    {M R L K : ℝ≥0}
    (hS : IsCompact S) (hm : MapsTo v (Ico a b) S)
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt v (f t (v t)) (Ico a b) t)
    (hb : ∀ t ∈ Ico a b, ‖f t (v t)‖ ≤ M)
    (hR : 0 < R) {η : ℝ} (hη : 0 < η)
    (hLip : ∀ x ∈ S, ∀ t ∈ Icc (b - η) (b + η),
      LipschitzOnWith K (f t) (closedBall x R))
    (hc : ∀ x ∈ S, ∀ y ∈ closedBall x R,
      ContinuousOn (fun t => f t y) (Icc (b - η) (b + η)))
    (hL : ∀ x ∈ S, ∀ t ∈ Icc (b - η) (b + η), ∀ y ∈ closedBall x R, ‖f t y‖ ≤ L) :
    ∃ x ∈ S, Tendsto v (𝓝[Ico a b] b) (𝓝 x) ∧
      ∃ T > (0 : ℝ), ∃ w : ℝ → E, Continuous w ∧ w b = x ∧
        (∀ t ∈ Icc (b - T) (b + T), w t = picard f b x w t ∧
          HasDerivWithinAt w (f t (w t)) (Icc (b - T) (b + T)) t) := by
  obtain ⟨x, hx, hlim⟩ := compact_endpoint hab hS hm hd hb
  obtain ⟨T, hT, _, _, s, hs, hp⟩ := common_time (r := 0) hη hR (hLip x hx) (hc x hx) (hL x hx)
  obtain ⟨w, hw, hw0, _, hwq, hwd⟩ := Ext025A2.gp04_differential_existence hp
    (show x ∈ closedBall x (0 : ℝ) by simp)
  refine ⟨x,hx,hlim,T,hT,w,hw,?_,fun t ht => ⟨?_,hwd t ht⟩⟩
  · rwa [hs] at hw0
  · simpa only [hs] using hwq t ht

end QuantumNLS.Ext025GP04LocalR30m

#print axioms QuantumNLS.Ext025GP04LocalR30m.common_time
#print axioms QuantumNLS.Ext025GP04LocalR30m.unique_integral
#print axioms QuantumNLS.Ext025GP04LocalR30m.inverse_differential
#print axioms QuantumNLS.Ext025GP04LocalR30m.finite_trajectory_cover
#print axioms QuantumNLS.Ext025GP04LocalR30m.compact_endpoint
#print axioms QuantumNLS.Ext025GP04LocalR30m.compact_restart
