import Mathlib

/- G1-083 Sup1 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1083Sup1.lean.
   Pure real-analysis oscillation lemma for  g'' = D(g)/4,  4 g'^2 = N(g),  g in [lo,hi],  N > 0 inside,  N(lo)=N(hi)=0,
   D(lo), D(hi) != 0:  every state (x, c) with 4 c^2 = N(x), x in [lo,hi] is attained by (g t, g' t) for some t.
   No ODE uniqueness is used: first-zero + monotone-limit + mean-value arguments. -/
set_option autoImplicit false

open Set Filter Topology

namespace NlsGge.Atomic.G1083Sup1
noncomputable section

structure OscSetup (g v N D : ℝ → ℝ) (lo hi : ℝ) : Prop where
  lt : lo < hi
  hg : ∀ t, HasDerivAt g (v t) t
  hv : ∀ t, HasDerivAt v (D (g t) / 4) t
  hrng : ∀ t, lo ≤ g t ∧ g t ≤ hi
  hen : ∀ t, 4 * v t ^ 2 = N (g t)
  hpos : ∀ x, lo < x → x < hi → 0 < N x
  hlo0 : N lo = 0
  hhi0 : N hi = 0
  hNc : Continuous N
  hDc : Continuous D
  hDlo : D lo ≠ 0
  hDhi : D hi ≠ 0

theorem OscSetup.neg {g v N D : ℝ → ℝ} {lo hi : ℝ} (h : OscSetup g v N D lo hi) :
    OscSetup (fun t => -g t) (fun t => -v t) (fun x => N (-x)) (fun x => -D (-x)) (-hi) (-lo) where
  lt := by linarith [h.lt]
  hg := fun t => (h.hg t).neg
  hv := fun t => by
    have := (h.hv t).neg
    convert this using 1
    simp only [neg_neg]; ring
  hrng := fun t => by have := h.hrng t; constructor <;> linarith [this.1, this.2]
  hen := fun t => by simp only [neg_neg, neg_sq]; exact h.hen t
  hpos := fun x h1 h2 => h.hpos (-x) (by linarith) (by linarith)
  hlo0 := by simpa using h.hhi0
  hhi0 := by simpa using h.hlo0
  hNc := h.hNc.comp continuous_neg
  hDc := (h.hDc.comp continuous_neg).neg
  hDlo := by simpa using h.hDhi
  hDhi := by simpa using h.hDlo

variable {g v N D : ℝ → ℝ} {lo hi : ℝ}

theorem OscSetup.cont_g (h : OscSetup g v N D lo hi) : Continuous g :=
  continuous_iff_continuousAt.mpr fun t => (h.hg t).continuousAt

theorem OscSetup.cont_v (h : OscSetup g v N D lo hi) : Continuous v :=
  continuous_iff_continuousAt.mpr fun t => (h.hv t).continuousAt

theorem OscSetup.v_ne_zero_of_mem (h : OscSetup g v N D lo hi) {t : ℝ}
    (h1 : lo < g t) (h2 : g t < hi) : v t ≠ 0 := by
  intro h0
  have := h.hen t
  rw [h0] at this
  have := h.hpos _ h1 h2
  nlinarith

/-- the zero of `v` after a time where `v < 0` exists -/
theorem OscSetup.zero_exists (h : OscSetup g v N D lo hi) {t0 : ℝ} (ht0 : v t0 < 0) :
    ∃ τ, t0 < τ ∧ v τ = 0 := by
  by_contra hno
  push Not at hno
  have hneg : ∀ t, t0 ≤ t → v t < 0 := by
    intro t ht
    rcases ht.eq_or_lt with rfl | ht'
    · exact ht0
    · by_contra hge
      push Not at hge
      have hpos' : 0 < v t := lt_of_le_of_ne hge (hno t ht').symm
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht h.cont_v.continuousOn
        (show (0 : ℝ) ∈ Icc (v t0) (v t) from ⟨ht0.le, hpos'.le⟩)
      rcases hs.1.eq_or_lt with rfl | hs'
      · linarith
      · exact hno s hs' hs0
  have hanti : StrictAntiOn g (Ici t0) :=
    strictAntiOn_of_deriv_neg (convex_Ici t0) h.cont_g.continuousOn (fun x hx => by
      rw [interior_Ici] at hx
      rw [(h.hg x).deriv]; exact hneg x (le_of_lt hx))
  -- limit of g
  set L : ℝ := sInf (g '' Ici t0) with hL
  have hbdd : BddBelow (g '' Ici t0) := ⟨lo, by rintro _ ⟨s, _, rfl⟩; exact (h.hrng s).1⟩
  have hne : (g '' Ici t0).Nonempty := ⟨g t0, t0, self_mem_Ici, rfl⟩
  have hLle : ∀ t, t0 ≤ t → L ≤ g t := fun t ht => csInf_le hbdd ⟨t, ht, rfl⟩
  have hlolL : lo ≤ L := le_csInf hne (by rintro _ ⟨s, _, rfl⟩; exact (h.hrng s).1)
  have hLlt : L < hi := by
    have h1 : g (t0 + 1) < g t0 := hanti self_mem_Ici (by simp [Set.mem_Ici]) (by linarith)
    have := hLle (t0 + 1) (by linarith)
    linarith [(h.hrng t0).2]
  have hlim : Tendsto g atTop (𝓝 L) := by
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [eventually_ge_atTop t0] with t ht
      exact lt_of_lt_of_le ha (hLle t ht)
    · obtain ⟨_, ⟨s, hs, rfl⟩, hsa⟩ := exists_lt_of_csInf_lt hne ha
      filter_upwards [eventually_ge_atTop s] with t ht
      exact lt_of_le_of_lt (hanti.antitoneOn hs (le_trans hs ht |> fun h => show t ∈ Ici t0 from h) ht) hsa
  have hv2 : Tendsto (fun t => v t ^ 2) atTop (𝓝 (N L / 4)) := by
    have : Tendsto (fun t => N (g t) / 4) atTop (𝓝 (N L / 4)) :=
      ((h.hNc.tendsto L).comp hlim).div_const 4
    refine this.congr (fun t => ?_)
    have := h.hen t; linarith
  have hNL : N L = 0 := by
    by_contra hNL
    have hNLpos : 0 < N L := by
      have : 0 ≤ N L / 4 := ge_of_tendsto hv2 (Eventually.of_forall fun t => sq_nonneg _)
      exact lt_of_le_of_ne (by linarith) (Ne.symm hNL)
    set c : ℝ := Real.sqrt (N L / 8) with hc
    have hcpos : 0 < c := Real.sqrt_pos.mpr (by linarith)
    have hc2 : c ^ 2 = N L / 8 := Real.sq_sqrt (by linarith)
    have hev : ∀ᶠ t in atTop, c ^ 2 < v t ^ 2 :=
      (tendsto_order.1 hv2).1 (c ^ 2) (by linarith)
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop t0))
    have hvc : ∀ t, T ≤ t → v t < -c := by
      intro t ht
      obtain ⟨h1, h2⟩ := hT t ht
      have := hneg t h2
      nlinarith
    have hT0 : t0 ≤ T := (hT T le_rfl).2
    have hmono : AntitoneOn (fun t => g t + c * t) (Ici T) :=
      antitoneOn_of_deriv_nonpos (convex_Ici T)
        ((h.cont_g.add (continuous_const.mul continuous_id)).continuousOn)
        (fun x _ => ((h.hg x).add ((hasDerivAt_id x).const_mul c)).differentiableAt.differentiableWithinAt)
        (fun x hx => by
          rw [interior_Ici] at hx
          have hd : HasDerivAt (fun t => g t + c * t) (v x + c) x := by
            exact ((h.hg x).add ((hasDerivAt_id x).const_mul c)).congr_deriv (by simp)
          rw [hd.deriv]
          have := hvc x (le_of_lt hx); linarith)
    set t := T + (g T - L) / c + 1 with htdef
    have hgTL : 0 ≤ g T - L := by linarith [hLle T hT0]
    have htT : T ≤ t := by
      have : 0 ≤ (g T - L) / c := div_nonneg hgTL hcpos.le
      linarith
    have h1 := hmono (Set.mem_Ici.2 le_rfl) (show t ∈ Ici T from htT) htT
    have h2 := hLle t (le_trans hT0 htT)
    have h3 : c * ((g T - L) / c) = g T - L := by field_simp
    simp only at h1
    nlinarith
  have hLlo : L = lo := by
    by_contra hne'
    have := h.hpos L (lt_of_le_of_ne hlolL (Ne.symm hne')) hLlt
    linarith
  have hgl : Tendsto g atTop (𝓝 lo) := hLlo ▸ hlim
  have hvt0 : Tendsto v atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => v t ^ 2) atTop (𝓝 0) := by rw [hNL] at hv2; simpa using hv2
    have h2 : Tendsto (fun t => Real.sqrt (v t ^ 2)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at this; exact this
    refine (tendsto_zero_iff_abs_tendsto_zero _).2 ?_
    show Tendsto (fun t => |v t|) atTop (𝓝 0)
    simpa [Real.sqrt_sq_eq_abs] using h2
  set m : ℝ := |D lo| / 4 with hm
  have hmpos : 0 < m := by have := abs_pos.2 h.hDlo; positivity
  have hDt : Tendsto (fun t => D (g t) / 4) atTop (𝓝 (D lo / 4)) :=
    ((h.hDc.tendsto lo).comp hgl).div_const 4
  have ev1 : ∀ᶠ t in atTop, m / 2 < |D (g t) / 4| := by
    have h1 := hDt.abs
    have hm' : |D lo / 4| = m := by rw [abs_div]; norm_num [hm]
    rw [hm'] at h1
    exact (tendsto_order.1 h1).1 (m / 2) (by linarith)
  have ev2 : ∀ᶠ t in atTop, |v t| < m / 4 := by
    have := Metric.tendsto_nhds.1 hvt0 (m / 4) (by positivity)
    filter_upwards [this] with t ht
    simpa [Real.dist_eq] using ht
  obtain ⟨T, hT⟩ := eventually_atTop.1 (ev1.and ev2)
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope v (fun x => D (g x) / 4)
    (show T < T + 1 by linarith) h.cont_v.continuousOn (fun x _ => h.hv x)
  have hξT : T ≤ ξ := le_of_lt hξ.1
  have e1 := (hT ξ hξT).1
  have e2 := (hT T le_rfl).2
  have e3 := (hT (T + 1) (by linarith)).2
  have : D (g ξ) / 4 = v (T + 1) - v T := by rw [hξe]; field_simp; ring
  rw [this] at e1
  have := abs_sub (v (T + 1)) (v T)
  linarith

theorem OscSetup.down (h : OscSetup g v N D lo hi) {t0 : ℝ} (ht0 : v t0 < 0) :
    ∃ τ, t0 < τ ∧ g τ = lo ∧ v τ = 0 ∧ ∀ t, t0 ≤ t → t < τ → v t < 0 := by
  obtain ⟨z, hz, hz0⟩ := h.zero_exists ht0
  set Z : Set ℝ := {τ | t0 ≤ τ ∧ v τ = 0} with hZ
  have hZc : IsClosed Z := isClosed_Ici.inter (isClosed_eq h.cont_v continuous_const)
  have hZne : Z.Nonempty := ⟨z, hz.le, hz0⟩
  have hZb : BddBelow Z := ⟨t0, fun x hx => hx.1⟩
  have hτ : sInf Z ∈ Z := hZc.csInf_mem hZne hZb
  set τ := sInf Z with hτdef
  have ht0τ : t0 < τ := by
    refine lt_of_le_of_ne hτ.1 (fun e => ?_)
    have := hτ.2; rw [← e] at this; linarith
  have hneg : ∀ t, t0 ≤ t → t < τ → v t < 0 := by
    intro t ht1 ht2
    by_contra hge
    push Not at hge
    have hne : v t ≠ 0 := fun e => by
      have : τ ≤ t := csInf_le hZb ⟨ht1, e⟩
      linarith
    have hpos' : 0 < v t := lt_of_le_of_ne hge (Ne.symm hne)
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht1 h.cont_v.continuousOn
      (show (0 : ℝ) ∈ Icc (v t0) (v t) from ⟨ht0.le, hpos'.le⟩)
    have : τ ≤ s := csInf_le hZb ⟨hs.1, hs0⟩
    linarith [hs.2]
  have hanti : StrictAntiOn g (Icc t0 τ) :=
    strictAntiOn_of_deriv_neg (convex_Icc t0 τ) h.cont_g.continuousOn (fun x hx => by
      rw [interior_Icc] at hx
      rw [(h.hg x).deriv]; exact hneg x hx.1.le hx.2)
  have hlt : g τ < g t0 := hanti (Set.mem_Icc.2 ⟨le_rfl, ht0τ.le⟩) (Set.mem_Icc.2 ⟨ht0τ.le, le_rfl⟩) ht0τ
  have hNτ : N (g τ) = 0 := by have := h.hen τ; rw [hτ.2] at this; linarith
  have hglo : g τ = lo := by
    by_contra hne
    have h1 : lo < g τ := lt_of_le_of_ne (h.hrng τ).1 (Ne.symm hne)
    have h2 : g τ < hi := lt_of_lt_of_le hlt (h.hrng t0).2
    have := h.hpos _ h1 h2
    linarith
  exact ⟨τ, ht0τ, hglo, hτ.2, hneg⟩

theorem OscSetup.up (h : OscSetup g v N D lo hi) {t0 : ℝ} (ht0 : 0 < v t0) :
    ∃ τ, t0 < τ ∧ g τ = hi ∧ v τ = 0 ∧ ∀ t, t0 ≤ t → t < τ → 0 < v t := by
  obtain ⟨τ, h1, h2, h3, h4⟩ := h.neg.down (t0 := t0) (by simpa using ht0)
  refine ⟨τ, h1, ?_, ?_, fun t a b => ?_⟩
  · simpa using h2
  · simpa using h3
  · have := h4 t a b; simpa using this

theorem OscSetup.after_lo (h : OscSetup g v N D lo hi) {τ : ℝ} (hg : g τ = lo) (hv : v τ = 0) :
    ∀ᶠ t in 𝓝[>] τ, 0 < v t := by
  have hd : HasDerivAt v (D lo / 4) τ := by simpa [hg] using h.hv τ
  have hne : D lo / 4 ≠ 0 := div_ne_zero h.hDlo (by norm_num)
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exfalso
    have hev : ∀ᶠ t in 𝓝[<] τ, slope v τ t < 0 :=
      (tendsto_order.1 (hs.mono_left (nhdsWithin_mono τ (fun t ht => ne_of_lt ht)))).2 0 hneg
    obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hev
    have hvpos : ∀ t ∈ Ioo l τ, 0 < v t := by
      intro t ht
      have := hsub ht
      simp only [Set.mem_ofPred_eq, slope_def_field, hv, sub_zero] at this
      have h1 : t - τ < 0 := by linarith [ht.2]
      by_contra hle
      push Not at hle
      have := div_nonneg_of_nonpos hle h1.le
      linarith
    set l' := (l + τ) / 2 with hl'
    have hl'1 : l < l' := by have := Set.mem_Iio.1 hl; linarith
    have hl'2 : l' < τ := by have := Set.mem_Iio.1 hl; linarith
    have hmono : StrictMonoOn g (Icc l' τ) :=
      strictMonoOn_of_deriv_pos (convex_Icc l' τ) h.cont_g.continuousOn (fun x hx => by
        rw [interior_Icc] at hx
        rw [(h.hg x).deriv]; exact hvpos x ⟨by linarith [hx.1], hx.2⟩)
    have := hmono (Set.mem_Icc.2 ⟨le_rfl, hl'2.le⟩) (Set.mem_Icc.2 ⟨hl'2.le, le_rfl⟩) hl'2
    have := (h.hrng l').1
    linarith
  · have hev : ∀ᶠ t in 𝓝[>] τ, 0 < slope v τ t :=
      (tendsto_order.1 (hs.mono_left (nhdsWithin_mono τ (fun t ht => ne_of_gt ht)))).1 0 hpos
    filter_upwards [hev, self_mem_nhdsWithin] with t ht ht'
    simp only [slope_def_field, hv, sub_zero] at ht
    have h1 : 0 < t - τ := by simpa using ht'
    by_contra hle
    push Not at hle
    have := div_nonpos_of_nonpos_of_nonneg hle h1.le
    linarith

theorem OscSetup.after_hi (h : OscSetup g v N D lo hi) {τ : ℝ} (hg : g τ = hi) (hv : v τ = 0) :
    ∀ᶠ t in 𝓝[>] τ, v t < 0 := by
  have := h.neg.after_lo (τ := τ) (by simpa using hg) (by simpa using hv)
  filter_upwards [this] with t ht
  simpa using ht

theorem OscSetup.lo_to_hi (h : OscSetup g v N D lo hi) {l : ℝ} (hg : g l = lo) (hv : v l = 0) :
    ∃ h0, g h0 = hi ∧ v h0 = 0 := by
  obtain ⟨t2, ht2⟩ := (h.after_lo hg hv).and self_mem_nhdsWithin |>.exists
  obtain ⟨τ, -, h2, h3, -⟩ := h.up ht2.1
  exact ⟨τ, h2, h3⟩

theorem OscSetup.hi_to_lo (h : OscSetup g v N D lo hi) {l : ℝ} (hg : g l = hi) (hv : v l = 0) :
    ∃ h0, g h0 = lo ∧ v h0 = 0 := by
  obtain ⟨t2, ht2⟩ := (h.after_hi hg hv).and self_mem_nhdsWithin |>.exists
  obtain ⟨τ, -, h2, h3, -⟩ := h.down ht2.1
  exact ⟨τ, h2, h3⟩

theorem OscSetup.eq_endpoint_of_v_zero (h : OscSetup g v N D lo hi) {t : ℝ} (hv : v t = 0) :
    g t = lo ∨ g t = hi := by
  by_contra hno
  push Not at hno
  exact h.v_ne_zero_of_mem (lt_of_le_of_ne (h.hrng t).1 (Ne.symm hno.1))
    (lt_of_le_of_ne (h.hrng t).2 hno.2) hv

theorem OscSetup.exists_lo (h : OscSetup g v N D lo hi) : ∃ l, g l = lo ∧ v l = 0 := by
  rcases lt_trichotomy (v 0) 0 with h1 | h1 | h1
  · obtain ⟨τ, -, h2, h3, -⟩ := h.down h1
    exact ⟨τ, h2, h3⟩
  · rcases h.eq_endpoint_of_v_zero h1 with h2 | h2
    · exact ⟨0, h2, h1⟩
    · exact h.hi_to_lo h2 h1
  · obtain ⟨τ, -, h2, h3, -⟩ := h.up h1
    exact h.hi_to_lo h2 h3

theorem OscSetup.cover_pos (h : OscSetup g v N D lo hi) (x c : ℝ) (hc0 : 0 < c)
    (hx1 : lo ≤ x) (hx2 : x ≤ hi) (hc : 4 * c ^ 2 = N x) : ∃ t, g t = x ∧ v t = c := by
  have hxlo : lo < x := by
    refine lt_of_le_of_ne hx1 (fun e => ?_)
    rw [← e, h.hlo0] at hc; nlinarith
  have hxhi : x < hi := by
    refine lt_of_le_of_ne hx2 (fun e => ?_)
    rw [e, h.hhi0] at hc; nlinarith
  obtain ⟨l, hl1, hl2⟩ := h.exists_lo
  have hgc : ContinuousAt g l := h.cont_g.continuousAt
  have hev : ∀ᶠ t in 𝓝[>] l, g t < x :=
    (hgc.eventually (gt_mem_nhds (show g l < x by rw [hl1]; exact hxlo))).filter_mono nhdsWithin_le_nhds
  obtain ⟨t2, ⟨ht2a, ht2b⟩, -⟩ := (((h.after_lo hl1 hl2).and hev).and self_mem_nhdsWithin).exists
  obtain ⟨τ, hτ1, hτ2, -, hτ4⟩ := h.up ht2a
  obtain ⟨s, hs, hsx⟩ := intermediate_value_Icc hτ1.le h.cont_g.continuousOn
    (show x ∈ Icc (g t2) (g τ) from ⟨ht2b.le, by rw [hτ2]; exact hx2⟩)
  have hsτ : s < τ := by
    refine lt_of_le_of_ne hs.2 (fun e => ?_)
    rw [e, hτ2] at hsx; linarith
  have hvs : 0 < v s := hτ4 s hs.1 hsτ
  have h1 := h.hen s
  rw [hsx, ← hc] at h1
  refine ⟨s, hsx, ?_⟩
  have : (v s - c) * (v s + c) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with e | e
  · linarith
  · linarith

theorem OscSetup.cover (h : OscSetup g v N D lo hi) (x c : ℝ)
    (hx1 : lo ≤ x) (hx2 : x ≤ hi) (hc : 4 * c ^ 2 = N x) : ∃ t, g t = x ∧ v t = c := by
  rcases lt_trichotomy c 0 with h1 | h1 | h1
  · obtain ⟨t, ht1, ht2⟩ := h.neg.cover_pos (-x) (-c) (by linarith) (by linarith) (by linarith)
      (by simpa using hc)
    exact ⟨t, by linarith, by linarith⟩
  · subst h1
    have hN : N x = 0 := by linarith
    have hxe : x = lo ∨ x = hi := by
      by_contra hno
      push Not at hno
      have := h.hpos x (lt_of_le_of_ne hx1 (Ne.symm hno.1)) (lt_of_le_of_ne hx2 hno.2)
      linarith
    rcases hxe with rfl | rfl
    · obtain ⟨l, hl1, hl2⟩ := h.exists_lo
      exact ⟨l, hl1, hl2⟩
    · obtain ⟨l, hl1, hl2⟩ := h.exists_lo
      obtain ⟨t, ht1, ht2⟩ := h.lo_to_hi hl1 hl2
      exact ⟨t, ht1, ht2⟩
  · exact h.cover_pos x c h1 hx1 hx2 hc

end
end NlsGge.Atomic.G1083Sup1
