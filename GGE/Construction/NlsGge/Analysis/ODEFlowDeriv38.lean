import Mathlib

/-!
# Differentiable dependence of ODE flows on initial data (38)

Generic finite-dimensional analysis: if a flow `φ` of a `C¹` vector field is uniformly Lipschitz
in the initial point, then it is differentiable in the initial point, with derivative the solution
of the variational equation.
-/

open Set Metric Filter Topology
open scoped NNReal

namespace NlsGge.ODEFlowDeriv38

section Linear

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Local existence for a linear time-dependent ODE on a short interval. -/
lemma local_lin38 (A : ℝ → G →L[ℝ] G) {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁) (m : ℝ≥0)
    (hA : ∀ t ∈ Icc s₀ s₁, ‖A t‖ ≤ m) (hc : ContinuousOn A (Icc s₀ s₁))
    (hτ : 2 * (m : ℝ) * (s₁ - s₀) ≤ 1) (M₀ : G) :
    ∃ E : ℝ → G, E s₀ = M₀ ∧
      ∀ t ∈ Icc s₀ s₁, HasDerivWithinAt E (A t (E t)) (Icc s₀ s₁) t := by
  let t₀ : Icc s₀ s₁ := ⟨s₀, le_rfl, hs⟩
  have hPL : IsPicardLindelof (fun t (x : G) => A t x) t₀ M₀ (‖M₀‖₊ + 1) 0
      (m * (‖M₀‖₊ + (‖M₀‖₊ + 1))) m := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact (A t).le_opNorm _ |>.trans (by gcongr; exact hA t ht)
    · intro x _
      exact hc.clm_apply continuousOn_const
    · intro t ht x hx
      have hx' : ‖x‖ ≤ ‖M₀‖ + (‖M₀‖ + 1) := by
        have h1 := mem_closedBall_iff_norm.mp hx
        have h2 : ‖x‖ ≤ ‖x - M₀‖ + ‖M₀‖ := by simpa [add_comm] using norm_le_insert' x M₀
        push_cast at h1
        linarith
      calc ‖A t x‖ ≤ ‖A t‖ * ‖x‖ := (A t).le_opNorm x
        _ ≤ m * (‖M₀‖ + (‖M₀‖ + 1)) := by gcongr; exact hA t ht
        _ = _ := by push_cast; simp
    · have h0 : max (s₁ - (t₀ : ℝ)) ((t₀ : ℝ) - s₀) = s₁ - s₀ := by
        simp [t₀, hs]
      rw [h0]
      simp only [NNReal.coe_zero, tsub_zero]
      have : ((m * (‖M₀‖₊ + (‖M₀‖₊ + 1)) : ℝ≥0) : ℝ) * (s₁ - s₀)
          ≤ ((‖M₀‖₊ + 1 : ℝ≥0) : ℝ) := by
        push_cast
        have h1 : (m:ℝ) * (s₁ - s₀) ≤ 1 / 2 := by linarith
        have h2 : 0 ≤ ‖M₀‖ := norm_nonneg _
        nlinarith [mul_nonneg h2 (mul_nonneg m.coe_nonneg (sub_nonneg.2 hs))]
      exact this
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hα⟩

omit [CompleteSpace G] in
/-- Gluing two solutions on adjacent intervals. -/
lemma glue_lin38 (A : ℝ → G →L[ℝ] G) {s₀ s₁ s₂ : ℝ} (h01 : s₀ ≤ s₁) (h12 : s₁ ≤ s₂)
    {E₁ E₂ : ℝ → G} (hE : E₁ s₁ = E₂ s₁)
    (h₁ : ∀ t ∈ Icc s₀ s₁, HasDerivWithinAt E₁ (A t (E₁ t)) (Icc s₀ s₁) t)
    (h₂ : ∀ t ∈ Icc s₁ s₂, HasDerivWithinAt E₂ (A t (E₂ t)) (Icc s₁ s₂) t) :
    ∀ t ∈ Icc s₀ s₂, HasDerivWithinAt (fun t => if t ≤ s₁ then E₁ t else E₂ t)
      (A t ((fun t => if t ≤ s₁ then E₁ t else E₂ t) t)) (Icc s₀ s₂) t := by
  set D : ℝ → G := fun t => if t ≤ s₁ then E₁ t else E₂ t with hD
  have hD1 : ∀ t ∈ Icc s₀ s₁, D t = E₁ t := fun t ht => by simp [hD, ht.2]
  have hD2 : ∀ t ∈ Icc s₁ s₂, D t = E₂ t := fun t ht => by
    by_cases h : t ≤ s₁
    · have : t = s₁ := le_antisymm h ht.1
      subst this; simp [hD, hE]
    · simp [hD, h]
  have k1 : ∀ t ∈ Icc s₀ s₁, HasDerivWithinAt D (A t (D t)) (Icc s₀ s₁) t := fun t ht => by
    rw [hD1 t ht]; exact (h₁ t ht).congr_of_mem (fun y hy => hD1 y hy) ht
  have k2 : ∀ t ∈ Icc s₁ s₂, HasDerivWithinAt D (A t (D t)) (Icc s₁ s₂) t := fun t ht => by
    rw [hD2 t ht]; exact (h₂ t ht).congr_of_mem (fun y hy => hD2 y hy) ht
  intro t ht
  rcases lt_trichotomy t s₁ with h | h | h
  · refine (k1 t ⟨ht.1, h.le⟩).mono_of_mem_nhdsWithin ?_
    filter_upwards [inter_mem_nhdsWithin (Icc s₀ s₂) (Iio_mem_nhds h)] with y hy
    exact ⟨hy.1.1, hy.2.le⟩
  · subst h
    have := (k1 t ⟨ht.1, le_rfl⟩).union (k2 t ⟨le_rfl, ht.2⟩)
    rwa [Icc_union_Icc_eq_Icc h01 h12] at this
  · refine (k2 t ⟨h.le, ht.2⟩).mono_of_mem_nhdsWithin ?_
    filter_upwards [inter_mem_nhdsWithin (Icc s₀ s₂) (Ioi_mem_nhds h)] with y hy
    exact ⟨hy.2.le, hy.1.2⟩

/-- Global existence for a linear time-dependent ODE with continuous coefficients, by chaining
short-time local solutions. -/
lemma exists_lin38 (A : ℝ → G →L[ℝ] G) {s₀ T : ℝ} (m : ℝ≥0)
    (hA : ∀ t ∈ Icc s₀ T, ‖A t‖ ≤ m) (hc : ContinuousOn A (Icc s₀ T)) (M₀ : G) :
    ∃ D : ℝ → G, D s₀ = M₀ ∧ ∀ t ∈ Icc s₀ T, HasDerivWithinAt D (A t (D t)) (Icc s₀ T) t := by
  set τ : ℝ := 1 / (2 * m + 1) with hτ
  have hτpos : 0 < τ := by positivity
  have key : ∀ n : ℕ, ∀ (a b : ℝ), s₀ ≤ a → a ≤ b → b ≤ T → b ≤ a + n * τ → ∀ M : G,
      ∃ D : ℝ → G, D a = M ∧ ∀ t ∈ Icc a b, HasDerivWithinAt D (A t (D t)) (Icc a b) t := by
    intro n
    induction n with
    | zero =>
      intro a b _ hab _ hb M
      have : b = a := le_antisymm (by simpa using hb) hab
      subst this
      refine ⟨fun _ => M, rfl, fun t ht => ?_⟩
      have : t = b := by simpa using ht
      subst this
      rw [Icc_self]
      refine HasFDerivWithinAt.of_not_accPt ?_
      rw [accPt_iff_clusterPt, inf_principal]
      simp [ClusterPt]
    | succ n ih =>
      intro a b ha hab hbT hb M
      set c := min b (a + τ) with hc'
      have hac : a ≤ c := le_min hab (by linarith)
      have hcb : c ≤ b := min_le_left _ _
      have hsub : Icc a c ⊆ Icc s₀ T := fun t ht => ⟨ha.trans ht.1, ht.2.trans (hcb.trans hbT)⟩
      have hlen : 2 * (m : ℝ) * (c - a) ≤ 1 := by
        have h1 : c - a ≤ τ := by have := min_le_right b (a + τ); linarith
        have h2 : 2 * (m : ℝ) * τ ≤ 1 := by
          rw [hτ, mul_one_div, div_le_one (by positivity)]; linarith
        nlinarith [m.coe_nonneg]
      obtain ⟨E₁, hE₁0, hE₁⟩ := local_lin38 A hac m (fun t ht => hA t (hsub ht))
        (hc.mono hsub) hlen M
      have hb' : b ≤ c + n * τ := by
        rcases min_cases b (a + τ) with ⟨h, _⟩ | ⟨h, _⟩
        · rw [hc', h]; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hτpos.le]
        · rw [hc', h]; push_cast at hb; linarith
      obtain ⟨E₂, hE₂0, hE₂⟩ := ih c b (ha.trans hac) hcb hbT hb' (E₁ c)
      refine ⟨fun t => if t ≤ c then E₁ t else E₂ t, ?_, glue_lin38 A hac hcb hE₂0.symm hE₁ hE₂⟩
      simp [hac, hE₁0]
  by_cases hT : s₀ ≤ T
  · obtain ⟨n, hn⟩ := exists_nat_ge ((T - s₀) / τ)
    exact key n s₀ T le_rfl hT le_rfl (by rw [div_le_iff₀ hτpos] at hn; linarith) M₀
  · refine ⟨fun _ => M₀, rfl, fun t ht => absurd (ht.1.trans ht.2) hT⟩

end Linear

section Nonlinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Elementary bound on the Grönwall function with zero initial datum. -/
lemma gronwallBound_zero_le38 {K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (_hx : 0 ≤ x) :
    gronwallBound 0 K ε x ≤ ε * x * Real.exp (K * x) := by
  rcases hK.eq_or_lt with h | h
  · subst h; simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 h.ne']
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have := Real.add_one_le_exp (-(K * x))
      rw [Real.exp_neg] at this
      have hp := Real.exp_pos (K * x)
      have := mul_le_mul_of_nonneg_right this hp.le
      rw [add_mul, inv_mul_cancel₀ hp.ne'] at this
      nlinarith
    show 0 * Real.exp (K * x) + ε / K * (Real.exp (K * x) - 1) ≤ _
    calc 0 * Real.exp (K * x) + ε / K * (Real.exp (K * x) - 1)
        = ε / K * (Real.exp (K * x) - 1) := by ring
      _ ≤ ε / K * (K * x * Real.exp (K * x)) := by gcongr
      _ = ε * x * Real.exp (K * x) := by field_simp

/-- Grönwall for a remainder vanishing at time `0`, with right-derivative on `[0,T]`. -/
lemma gronwall_rem38 {r r' : ℝ → E} {T M ε : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (h0 : r 0 = 0) (hr : ∀ t ∈ Icc 0 T, HasDerivWithinAt r (r' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, ‖r' t‖ ≤ M * ‖r t‖ + ε) :
    ∀ t ∈ Icc 0 T, ‖r t‖ ≤ ε * T * Real.exp (M * T) := by
  have hcont : ContinuousOn r (Icc 0 T) := fun t ht => (hr t ht).continuousWithinAt
  have hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt r (r' t) (Ici t) t := fun t ht =>
    (hr t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (by
      have : Icc 0 T ∈ 𝓝[Ici t] t := by
        have h2 : Iio T ∈ 𝓝 t := Iio_mem_nhds ht.2
        filter_upwards [inter_mem_nhdsWithin (Ici t) h2] with y hy
        exact ⟨ht.1.trans hy.1, hy.2.le⟩
      exact this)
  intro t ht
  have := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) hcont hder (by simp [h0])
    (fun t ht => hb t ⟨ht.1, ht.2.le⟩) t ht
  refine this.trans ?_
  rw [sub_zero] at *
  calc _ ≤ ε * t * Real.exp (M * t) := gronwallBound_zero_le38 hM hε ht.1
    _ ≤ ε * T * Real.exp (M * T) := by
      have := ht.2; have := ht.1; gcongr

/-- Second-order Taylor-type estimate from a uniform bound on the oscillation of the derivative on
a ball. -/
lemma taylor38 {X : E → E} {X' : E → E →L[ℝ] E} {a : E} {ρ ε : ℝ}
    (hX : ∀ z ∈ ball a ρ, HasFDerivAt X (X' z) z)
    (hε : ∀ z ∈ ball a ρ, ‖X' z - X' a‖ ≤ ε) {b : E} (hb : b ∈ ball a ρ) :
    ‖X b - X a - X' a (b - a)‖ ≤ ε * ‖b - a‖ := by
  have hg : ∀ z ∈ ball a ρ, HasFDerivWithinAt (fun z => X z - X' a z) (X' z - X' a) (ball a ρ) z :=
    fun z hz => ((hX z hz).sub (X' a).hasFDerivAt).hasFDerivWithinAt
  have := (convex_ball a ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hε
    (mem_ball_self (by simpa using hb |> fun h => (dist_nonneg.trans_lt h))) hb
  have e : (X b - X' a b) - (X a - X' a a) = X b - X a - X' a (b - a) := by
    rw [map_sub]; abel
  simpa only [e] using this

/-- Uniform continuity of the derivative on a neighbourhood of a compact set. -/
lemma unif38 [ProperSpace E] {X' : E → E →L[ℝ] E} {U K : Set E} (hU : IsOpen U)
    (hX' : ContinuousOn X' U) (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ a ∈ K, ball a ρ ⊆ U ∧ ∀ z ∈ ball a ρ, ‖X' z - X' a‖ ≤ ε := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening δ K) := hK.cthickening
  have huc := hK'.uniformContinuousOn_of_continuous (hX'.mono hsub)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨ρ₀, hρ₀, h⟩ := huc ε hε
  refine ⟨min ρ₀ δ, lt_min hρ₀ hδ, fun a ha => ?_⟩
  have hmem : ∀ z ∈ ball a (min ρ₀ δ), z ∈ cthickening δ K := fun z hz =>
    mem_cthickening_of_dist_le z a δ K ha
      (by have := mem_ball.1 hz; have := min_le_right ρ₀ δ; linarith)
  refine ⟨fun z hz => hsub (hmem z hz), fun z hz => ?_⟩
  have := h z (hmem z hz) a (self_subset_cthickening _ ha)
    (by have := mem_ball.1 hz; have := min_le_left ρ₀ δ; linarith)
  rw [dist_eq_norm] at this
  exact this.le

/-- **Differentiability of the flow in the initial point.**  Any solution `D` of the variational
equation is the Fréchet derivative of `φ t` at `x₀`. -/
theorem hasFDerivAt_flow_of_variational38 [FiniteDimensional ℝ E]
    {X : E → E} {X' : E → E →L[ℝ] E} {U V : Set E} {φ : ℝ → E → E} {T : ℝ} {x₀ : E}
    (hU : IsOpen U) (hX : ∀ z ∈ U, HasFDerivAt X (X' z) z) (hX' : ContinuousOn X' U)
    (hV : V ∈ 𝓝 x₀) (hT : 0 ≤ T)
    (hφ0 : ∀ x ∈ V, φ 0 x = x)
    (hφd : ∀ x ∈ V, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => φ s x) (X (φ t x)) (Icc 0 T) t)
    (hφU : ∀ x ∈ V, ∀ t ∈ Icc 0 T, φ t x ∈ U)
    (hLip : ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ y ∈ V, ‖φ t y - φ t x₀‖ ≤ C * ‖y - x₀‖)
    {D : ℝ → E →L[ℝ] E} (hD0 : D 0 = 1)
    (hD : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt D ((X' (φ t x₀)).comp (D t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, HasFDerivAt (φ t) (D t) x₀ := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  have hx₀ : x₀ ∈ V := mem_of_mem_nhds hV
  obtain ⟨C, hC⟩ := hLip
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hC1 : ∀ t ∈ Icc 0 T, ∀ y ∈ V, ‖φ t y - φ t x₀‖ ≤ C' * ‖y - x₀‖ := fun t ht y hy =>
    (hC t ht y hy).trans (by gcongr; exact le_max_left _ _)
  have hcont : ContinuousOn (fun t => φ t x₀) (Icc 0 T) := fun t ht =>
    (hφd x₀ hx₀ t ht).continuousWithinAt
  set K : Set E := (fun t => φ t x₀) '' Icc 0 T with hK
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn hcont
  have hKU : K ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩; exact hφU x₀ hx₀ t ht
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn (hX'.mono hKU)
  set M : ℝ := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hAM : ∀ t ∈ Icc 0 T, ‖X' (φ t x₀)‖ ≤ M := fun t ht =>
    (hM₀ _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  intro t₁ ht₁
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set P : ℝ := (C' + 1) * (T + 1) * Real.exp (M * T) with hP
  have hPpos : 0 < P := by positivity
  set ε : ℝ := c / P with hε
  have hεpos : 0 < ε := div_pos hc hPpos
  obtain ⟨ρ, hρ, hρK⟩ := unif38 hU hX' hKc hKU hεpos
  have hVh : (fun h => x₀ + h) ⁻¹' V ∈ 𝓝 (0 : E) := by
    apply (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
    simpa using hV
  filter_upwards [ball_mem_nhds (0 : E) (div_pos hρ (by positivity : 0 < C' + 1)), hVh]
    with h hh hhV
  have hhn : ‖h‖ < ρ / (C' + 1) := by simpa using hh
  have hy : x₀ + h ∈ V := hhV
  -- pointwise estimates
  have hb : ∀ t ∈ Icc 0 T, φ t (x₀ + h) ∈ ball (φ t x₀) ρ := fun t ht => by
    rw [mem_ball, dist_eq_norm]
    have h1 := hC1 t ht (x₀ + h) hy
    simp only [add_sub_cancel_left] at h1
    have h2 : C' * ‖h‖ < ρ := by
      have := (lt_div_iff₀ (by positivity : 0 < C' + 1)).1 hhn
      nlinarith [norm_nonneg h]
    linarith
  have htay : ∀ t ∈ Icc 0 T, ‖X (φ t (x₀ + h)) - X (φ t x₀) - X' (φ t x₀) (φ t (x₀ + h) - φ t x₀)‖
      ≤ ε * (C' * ‖h‖) := fun t ht => by
    obtain ⟨hsub, hosc⟩ := hρK (φ t x₀) ⟨t, ht, rfl⟩
    refine (taylor38 (fun z hz => hX z (hsub hz)) hosc (hb t ht)).trans ?_
    have h1 := hC1 t ht (x₀ + h) hy
    simp only [add_sub_cancel_left] at h1
    gcongr
  set r : ℝ → E := fun t => φ t (x₀ + h) - φ t x₀ - D t h with hr
  set r' : ℝ → E := fun t => X (φ t (x₀ + h)) - X (φ t x₀) - (X' (φ t x₀)) (D t h) with hr'
  have hrd : ∀ t ∈ Icc 0 T, HasDerivWithinAt r (r' t) (Icc 0 T) t := fun t ht => by
    have h1 := ((hφd (x₀ + h) hy t ht).sub (hφd x₀ hx₀ t ht)).sub
      ((hD t ht).clm_apply (hasDerivWithinAt_const t (Icc 0 T) h))
    refine h1.congr_deriv ?_
    simp [hr']
  have hrb : ∀ t ∈ Icc 0 T, ‖r' t‖ ≤ M * ‖r t‖ + ε * (C' * ‖h‖) := fun t ht => by
    have e : r' t = (X (φ t (x₀ + h)) - X (φ t x₀) - X' (φ t x₀) (φ t (x₀ + h) - φ t x₀))
        + X' (φ t x₀) (r t) := by
      simp only [hr', hr, map_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_comm (M * ‖r t‖) _ ▸ add_le_add (htay t ht) ?_)
    exact ((X' (φ t x₀)).le_opNorm _).trans (by gcongr; exact hAM t ht)
  have hr0 : r 0 = 0 := by
    simp [hr, hφ0 _ hy, hφ0 _ hx₀, hD0]
  have hg := gronwall_rem38 hT hM0 (by positivity) hr0 hrd hrb t₁ ht₁
  have hfin : ‖r t₁‖ ≤ c * ‖h‖ := by
    refine hg.trans ?_
    have hT1 : T ≤ T + 1 := by linarith
    calc ε * (C' * ‖h‖) * T * Real.exp (M * T)
        = (ε * (C' * T * Real.exp (M * T))) * ‖h‖ := by ring
      _ ≤ (ε * P) * ‖h‖ := by
        gcongr
        rw [hP]
        have : 0 ≤ Real.exp (M * T) := (Real.exp_pos _).le
        nlinarith [mul_nonneg hC'0 hT, mul_nonneg (mul_nonneg hC'0 hT) this,
          mul_nonneg hT this, mul_nonneg hC'0 this]
      _ = c * ‖h‖ := by rw [hε]; field_simp
  simpa [hr] using hfin

/-- **Existence of the variational flow and differentiability at a point.** -/
theorem exists_flow_fderiv38 [FiniteDimensional ℝ E]
    {X : E → E} {X' : E → E →L[ℝ] E} {U V : Set E} {φ : ℝ → E → E} {T : ℝ} {x₀ : E}
    (hU : IsOpen U) (hX : ∀ z ∈ U, HasFDerivAt X (X' z) z) (hX' : ContinuousOn X' U)
    (hV : V ∈ 𝓝 x₀) (hT : 0 ≤ T)
    (hφ0 : ∀ x ∈ V, φ 0 x = x)
    (hφd : ∀ x ∈ V, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => φ s x) (X (φ t x)) (Icc 0 T) t)
    (hφU : ∀ x ∈ V, ∀ t ∈ Icc 0 T, φ t x ∈ U)
    (hLip : ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ y ∈ V, ‖φ t y - φ t x₀‖ ≤ C * ‖y - x₀‖) :
    ∃ D : ℝ → E →L[ℝ] E, D 0 = 1 ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt D ((X' (φ t x₀)).comp (D t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, HasFDerivAt (φ t) (D t) x₀ := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  have hx₀ : x₀ ∈ V := mem_of_mem_nhds hV
  have hcont : ContinuousOn (fun t => φ t x₀) (Icc 0 T) := fun t ht =>
    (hφd x₀ hx₀ t ht).continuousWithinAt
  have hKc : IsCompact ((fun t => φ t x₀) '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hcont
  have hKU : ((fun t => φ t x₀) '' Icc 0 T) ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩; exact hφU x₀ hx₀ t ht
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn (hX'.mono hKU)
  let A : ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := fun t =>
    ContinuousLinearMap.compL ℝ E E E (X' (φ t x₀))
  have hAn : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ ((max M₀ 0).toNNReal : ℝ) := fun t ht => by
    refine (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun M =>
      ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hM₀ _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  have hAc : ContinuousOn A (Icc 0 T) :=
    (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn
      (hX'.comp hcont (fun t ht => hKU ⟨t, ht, rfl⟩))
  obtain ⟨D, hD0, hD⟩ := exists_lin38 A (max M₀ 0).toNNReal hAn hAc 1
  exact ⟨D, hD0, hD, hasFDerivAt_flow_of_variational38 hU hX hX' hV hT hφ0 hφd hφU hLip hD0 hD⟩

/-- Version on an open set `V` with a uniform Lipschitz bound. -/
theorem flow_hasFDerivAt_on38 [FiniteDimensional ℝ E]
    {X : E → E} {X' : E → E →L[ℝ] E} {U V : Set E} {φ : ℝ → E → E} {T : ℝ}
    (hU : IsOpen U) (hX : ∀ z ∈ U, HasFDerivAt X (X' z) z) (hX' : ContinuousOn X' U)
    (hVo : IsOpen V) (hT : 0 ≤ T)
    (hφ0 : ∀ x ∈ V, φ 0 x = x)
    (hφd : ∀ x ∈ V, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => φ s x) (X (φ t x)) (Icc 0 T) t)
    (hφU : ∀ x ∈ V, ∀ t ∈ Icc 0 T, φ t x ∈ U)
    (hLip : ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ x ∈ V, ∀ y ∈ V, ‖φ t y - φ t x‖ ≤ C * ‖y - x‖) :
    ∀ x ∈ V, ∃ D : ℝ → E →L[ℝ] E, D 0 = 1 ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt D ((X' (φ t x)).comp (D t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, HasFDerivAt (φ t) (D t) x := fun x hx =>
  exists_flow_fderiv38 hU hX hX' (hVo.mem_nhds hx) hT hφ0 hφd hφU
    (by obtain ⟨C, hC⟩ := hLip; exact ⟨C, fun t ht y hy => hC t ht x hx y hy⟩)

end Nonlinear

end NlsGge.ODEFlowDeriv38
