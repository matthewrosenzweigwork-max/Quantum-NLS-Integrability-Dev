import Mathlib

                                                                                                         
                                                                                                 
                                                                                                           
                                                                                                                   
                                                                                                                     
                                                                                                            
                                                                                                                      
                                                                                                                    
                                                       
                                                                                                                          

set_option autoImplicit false
open Set Filter Topology Metric Complex

namespace NlsGge.ThirdConsultation.M016ChartAux

theorem quad_dichotomy (v D ε : ℂ) (h : v ^ 2 - D * v + ε = 0) (hD : ‖D - 1‖ ≤ 1 / 4) :
    ‖v - 1‖ ≤ 2 * ‖ε‖ + ‖D - 1‖ ∨ ‖v‖ ≤ 4 * ‖ε‖ := by
  have hfac : v * (v - D) = -ε := by linear_combination h
  have hprod : ‖v‖ * ‖v - D‖ = ‖ε‖ := by rw [← norm_mul, hfac, norm_neg]
  by_cases hv : 1 / 2 ≤ ‖v‖
  · left
    have h1 : ‖v - D‖ ≤ 2 * ‖ε‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hv (norm_nonneg (v - D))]
    calc ‖v - 1‖ = ‖(v - D) + (D - 1)‖ := by ring_nf
      _ ≤ ‖v - D‖ + ‖D - 1‖ := norm_add_le _ _
      _ ≤ 2 * ‖ε‖ + ‖D - 1‖ := by linarith
  · right
    push_neg at hv
    have hD1 : ‖(1 : ℂ)‖ - ‖D‖ ≤ ‖1 - D‖ := norm_sub_norm_le 1 D
    rw [norm_one, norm_sub_rev] at hD1
    have hvD : ‖D‖ - ‖v‖ ≤ ‖D - v‖ := norm_sub_norm_le D v
    rw [norm_sub_rev] at hvD
    have hge : 1 / 4 ≤ ‖v - D‖ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hge (norm_nonneg v)]

theorem norm_int_mul_two_pi_I (k : ℤ) (hk : k ≠ 0) : 2 * Real.pi ≤ ‖(k : ℂ) * (2 * Real.pi * I)‖ := by
  rw [norm_mul, norm_intCast, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two,
    Real.norm_of_nonneg Real.pi_pos.le, mul_one]
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  nlinarith [Real.pi_pos]

theorem preconnected_propagate {X : Type*} [TopologicalSpace X] (S : Set X) (hS : IsPreconnected S)
    (p : X → Prop) (hloc : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, (p y ↔ p x)) (x₀ : X) (hx₀ : x₀ ∈ S) (hp : p x₀) :
    ∀ x ∈ S, p x := by
  intro x hx
  let f : S → Prop := fun y => p y.1
  have hf : IsLocallyConstant f := (IsLocallyConstant.iff_eventually_eq f).2 fun y => by
    filter_upwards [(continuous_subtype_val.tendsto y).eventually (hloc y.1 y.2)] with z hz
    exact propext hz
  have : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have heq : f ⟨x, hx⟩ = f ⟨x₀, hx₀⟩ :=
    hf.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
  have h0 : f ⟨x₀, hx₀⟩ := hp
  rw [← heq] at h0
  exact h0

theorem ray_gauge_tendsto (K : ℝ) :
    Tendsto (fun t : ℝ => 3 * Real.exp (-(2 * t)) + K / (2 * t) + (K / t) ^ 2) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop two_pos)
  have h1 : Tendsto (fun t : ℝ => K / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun t : ℝ => K / (2 * t)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop two_pos)
  have h := ((he.const_mul 3).add h2).add (h1.pow 2)
  have h0 : (3 : ℝ) * 0 + 0 + 0 ^ 2 = 0 := by norm_num
  rw [h0] at h
  exact h

theorem ray_tendsto_locally_constant {X : Type*} [TopologicalSpace X] (q : X → ℝ → ℂ)
    (ψ₀ : X) (W : Set X) (hW : W ∈ 𝓝 ψ₀) (T₀ : ℝ) (g : ℝ → ℝ)
    (hg : Tendsto g atTop (𝓝 0))
    (hdich : ∀ ψ ∈ W, ∀ t : ℝ, T₀ ≤ t → ‖exp (q ψ t) - 1‖ ≤ g t ∨ ‖exp (q ψ t)‖ < 1 / 2)
    (hcont : ∀ ψ ∈ W, ContinuousOn (q ψ) (Ici T₀))
    (hcontψ : ∀ t : ℝ, T₀ ≤ t → ContinuousAt (fun ψ => q ψ t) ψ₀) :
    ∀ᶠ ψ in 𝓝 ψ₀, (Tendsto (q ψ) atTop (𝓝 0) ↔ Tendsto (q ψ₀) atTop (𝓝 0)) := by
  have h1slit : (1 : ℂ) ∈ slitPlane := by simp [slitPlane]
  obtain ⟨δ₀, hδ₀, hlog⟩ : ∃ δ₀ > 0, ∀ w : ℂ, ‖w - 1‖ < δ₀ → ‖log w‖ < 1 / 4 := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 (continuousAt_clog h1slit) (1 / 4) (by norm_num)
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have := hδ' (by rwa [dist_eq_norm])
    rwa [dist_eq_norm, log_one, sub_zero] at this
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hg.eventually (gt_mem_nhds hδ₀))
  set T := max T₀ T₁ with hT
  set U : Set ℂ := ball 0 (1 / 4) with hUdef
  set V : Set ℂ := (⋃ k : ℤ, ⋃ (_ : k ≠ 0), ball ((k : ℂ) * (2 * Real.pi * I)) (1 / 4)) ∪
    {w | ‖exp w‖ < 1 / 2} with hVdef
  have hUo : IsOpen U := isOpen_ball
  have hVo : IsOpen V := (isOpen_iUnion fun k => isOpen_iUnion fun _ => isOpen_ball).union
    (isOpen_lt (continuous_norm.comp continuous_exp) continuous_const)
  have hnormU : ∀ w ∈ U, ‖w‖ < 1 / 4 := fun w hw => by simpa [hUdef] using hw
  have hexpU : ∀ w ∈ U, 3 / 4 ≤ ‖exp w‖ := by
    intro w hw
    rw [norm_exp]
    have hw' := hnormU w hw
    have h1 : |w.re| ≤ ‖w‖ := abs_re_le_norm w
    have h2 := Real.add_one_le_exp w.re
    linarith [neg_abs_le w.re]
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro w hwU hwV
    rcases hwV with hk | hs
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hk
      obtain ⟨hk0, hk⟩ := mem_iUnion.1 hk
      rw [mem_ball, dist_eq_norm] at hk
      have hw' := hnormU w hwU
      have htri : ‖(k : ℂ) * (2 * Real.pi * I)‖ ≤ ‖w‖ + ‖w - (k : ℂ) * (2 * Real.pi * I)‖ := by
        calc ‖(k : ℂ) * (2 * Real.pi * I)‖ = ‖w - (w - (k : ℂ) * (2 * Real.pi * I))‖ := by ring_nf
          _ ≤ ‖w‖ + ‖w - (k : ℂ) * (2 * Real.pi * I)‖ := norm_sub_le _ _
      have h2 := norm_int_mul_two_pi_I k hk0
      linarith [Real.pi_gt_three]
    · have hs' : ‖exp w‖ < 1 / 2 := hs
      linarith [hexpU w hwU]
  have hmem : ∀ ψ ∈ W, ∀ t : ℝ, T ≤ t → q ψ t ∈ U ∪ V := by
    intro ψ hψ t ht
    have ht0 : T₀ ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : T₁ ≤ t := le_trans (le_max_right _ _) ht
    rcases hdich ψ hψ t ht0 with hb | hs
    · have hlt : ‖exp (q ψ t) - 1‖ < δ₀ := lt_of_le_of_lt hb (hT₁ t ht1)
      have hl := hlog _ hlt
      obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 (exp_log (exp_ne_zero (q ψ t))).symm
      by_cases hn0 : n = 0
      · left
        rw [hn, hn0, Int.cast_zero, zero_mul, add_zero, hUdef, mem_ball, dist_zero_right]
        exact hl
      · right; left
        refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨hn0, ?_⟩⟩
        rw [mem_ball, dist_eq_norm, hn, add_sub_cancel_right]
        exact hl
    · right; right; exact hs
  have hchar : ∀ ψ ∈ W, (Tendsto (q ψ) atTop (𝓝 0) ↔ q ψ T ∈ U) := by
    intro ψ hψ
    have himg : IsPreconnected (q ψ '' Ici T) :=
      isPreconnected_Ici.image _ ((hcont ψ hψ).mono (Ici_subset_Ici.2 (le_max_left _ _)))
    have hsub : q ψ '' Ici T ⊆ U ∪ V := by
      rintro _ ⟨t, ht, rfl⟩
      exact hmem ψ hψ t ht
    constructor
    · intro htend
      by_contra hTU
      have hTV : q ψ T ∈ V := (hmem ψ hψ T le_rfl).resolve_left hTU
      have hsubV : q ψ '' Ici T ⊆ V :=
        himg.subset_right_of_subset_union hUo hVo hdisj hsub ⟨q ψ T, ⟨T, self_mem_Ici, rfl⟩, hTV⟩
      obtain ⟨t, ht⟩ := ((htend.eventually (hUo.mem_nhds (mem_ball_self (by norm_num)))).and
        (eventually_ge_atTop T)).exists
      exact Set.disjoint_left.1 hdisj ht.1 (hsubV ⟨t, ht.2, rfl⟩)
    · intro hTU
      have hsubU : q ψ '' Ici T ⊆ U :=
        himg.subset_left_of_subset_union hUo hVo hdisj hsub ⟨q ψ T, ⟨T, self_mem_Ici, rfl⟩, hTU⟩
      have hbig : ∀ t : ℝ, T ≤ t → ‖exp (q ψ t) - 1‖ ≤ g t := by
        intro t ht
        have hU' := hsubU ⟨t, ht, rfl⟩
        rcases hdich ψ hψ t (le_trans (le_max_left _ _) ht) with hb | hs
        · exact hb
        · linarith [hexpU _ hU']
      have hexp : Tendsto (fun t => exp (q ψ t)) atTop (𝓝 1) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _)
          ((eventually_ge_atTop T).mono hbig) hg
      have hlog' : Tendsto (fun t => log (exp (q ψ t))) atTop (𝓝 0) := by
        have := (continuousAt_clog h1slit).tendsto.comp hexp
        rwa [log_one] at this
      refine hlog'.congr' ((eventually_ge_atTop T).mono fun t ht => ?_)
      have hU' : ‖q ψ t‖ < 1 / 4 := hnormU _ (hsubU ⟨t, ht, rfl⟩)
      have him : |(q ψ t).im| ≤ ‖q ψ t‖ := abs_im_le_norm _
      exact log_exp (by linarith [neg_abs_le (q ψ t).im, Real.pi_gt_three])
        (by linarith [le_abs_self (q ψ t).im, Real.pi_gt_three])
  have hψ₀W : ψ₀ ∈ W := mem_of_mem_nhds hW
  have hT0 : T₀ ≤ T := le_max_left _ _
  rcases hmem ψ₀ hψ₀W T le_rfl with hU0 | hV0
  · filter_upwards [hW, (hcontψ T hT0).eventually_mem (hUo.mem_nhds hU0)] with ψ hψ hψU
    rw [hchar ψ hψ, hchar ψ₀ hψ₀W]
    exact ⟨fun _ => hU0, fun _ => hψU⟩
  · filter_upwards [hW, (hcontψ T hT0).eventually_mem (hVo.mem_nhds hV0)] with ψ hψ hψV
    rw [hchar ψ hψ, hchar ψ₀ hψ₀W]
    exact ⟨fun h => absurd hψV (Set.disjoint_left.1 hdisj h),
      fun h => absurd hV0 (Set.disjoint_left.1 hdisj h)⟩

theorem norm_exp_neg_sq (t : ℝ) : ‖((Real.exp (-t) : ℝ) : ℂ) ^ 2‖ = Real.exp (-(2 * t)) := by
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add]
  congr 1
  ring

/-- The quadratic relation for `v = e^{F(it) − t}` from `2 cosh F = Δ`. -/
theorem ray_quadratic (F Δ : ℂ) (t : ℝ) (hF : 2 * Complex.cosh F = Δ) :
    Complex.exp (F - t) ^ 2 - (((Real.exp (-t) : ℝ) : ℂ) * Δ) * Complex.exp (F - t) +
      ((Real.exp (-t) : ℝ) : ℂ) ^ 2 = 0 := by
  have he : ((Real.exp (-t) : ℝ) : ℂ) = Complex.exp (-(t : ℂ)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  have hv : Complex.exp (F - t) = Complex.exp F * ((Real.exp (-t) : ℝ) : ℂ) := by
    rw [he, ← Complex.exp_add, sub_eq_add_neg]
  have hab : Complex.exp F * Complex.exp (-F) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [← hF, Complex.two_cosh, hv]
  linear_combination (-(((Real.exp (-t) : ℝ) : ℂ) ^ 2)) * hab

end NlsGge.ThirdConsultation.M016ChartAux
