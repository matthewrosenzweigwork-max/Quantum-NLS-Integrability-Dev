import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic

/-! # F08 (v2 `C:thm:bare`), file a: Phi-free probability tools

* `condExp_indep_mix38`: if `X`, `Y` are independent under a probability measure `P` and
  `Φ(X, Y)` is integrable, then `E[Φ(X,Y) | σ(X)] = (a ↦ ∫ Φ(a, y) d(law Y))` almost surely.
  (This is "independence and (C:eq:correction) give `E[V_m(U) | A_N] = V_m(P_N U) + C_{m,N}(P_N U)`"
  of v2, l.826-828.)
* `unifIntegrable_of_dominated38`, `tendsto_L1_of_dominated38`: a nonnegative sequence dominated
  eventually by a constant multiple of conditional expectations of one integrable function is
  uniformly integrable, and converges in `L¹` if it converges a.e. to an integrable limit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

section CondExp

variable {Ω A B : Type*} [mΩ : MeasurableSpace Ω] [mA : MeasurableSpace A] [mB : MeasurableSpace B]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Conditional expectation of a function of two independent variables, given the first. -/
theorem condExp_indep_mix38 {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y P) (Φ : A → B → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (hint : Integrable (fun ω => Φ (X ω) (Y ω)) P) :
    (fun ω => ∫ y, Φ (X ω) y ∂(P.map Y)) =ᵐ[P]
      P[fun ω => Φ (X ω) (Y ω) | MeasurableSpace.comap X mA] := by
  have hXY : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  have hmap : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hind
  have : IsProbabilityMeasure (P.map X) := (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (P.map Y) := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have hΦint : Integrable (Function.uncurry Φ) ((P.map X).prod (P.map Y)) := by
    rw [← hmap]
    exact (integrable_map_measure hΦ.aestronglyMeasurable hXY.aemeasurable).2 hint
  have hhint : Integrable (fun a => ∫ y, Φ a y ∂(P.map Y)) (P.map X) :=
    hΦint.integral_prod_left
  have hhmeas : StronglyMeasurable (fun a => ∫ y, Φ a y ∂(P.map Y)) :=
    hΦ.stronglyMeasurable.integral_prod_right'
  have hgint : Integrable (fun ω => ∫ y, Φ (X ω) y ∂(P.map Y)) P :=
    (integrable_map_measure hhint.aestronglyMeasurable hX.aemeasurable).1 hhint
  have hle : MeasurableSpace.comap X mA ≤ mΩ := hX.comap_le
  refine ae_eq_condExp_of_forall_setIntegral_eq hle hint (fun s _ _ => hgint.integrableOn)
    (fun s hs _ => ?_) ?_
  · obtain ⟨S, hS, rfl⟩ := hs
    have h1 : ∫ ω in X ⁻¹' S, (∫ y, Φ (X ω) y ∂(P.map Y)) ∂P =
        ∫ a in S, (∫ y, Φ a y ∂(P.map Y)) ∂(P.map X) := by
      rw [← setIntegral_map hS hhmeas.aestronglyMeasurable hX.aemeasurable]
    have h2 : ∫ ω in X ⁻¹' S, Φ (X ω) (Y ω) ∂P =
        ∫ p in S ×ˢ (Set.univ : Set B), Function.uncurry Φ p ∂((P.map X).prod (P.map Y)) := by
      rw [← hmap, setIntegral_map (hS.prod MeasurableSet.univ) hΦ.aestronglyMeasurable
        hXY.aemeasurable]
      have hset : (fun ω => (X ω, Y ω)) ⁻¹' (S ×ˢ (Set.univ : Set B)) = X ⁻¹' S := by
        ext ω; simp
      rw [hset]
      rfl
    rw [h1, h2]
    have h3 : ∫ p in S ×ˢ (Set.univ : Set B), Function.uncurry Φ p ∂((P.map X).prod (P.map Y)) =
        ∫ p, (S ×ˢ (Set.univ : Set B)).indicator (Function.uncurry Φ) p
          ∂((P.map X).prod (P.map Y)) := by
      rw [integral_indicator (hS.prod MeasurableSet.univ)]
    rw [h3]
    have h4 : (S ×ˢ (Set.univ : Set B)).indicator (Function.uncurry Φ) =
        fun p => S.indicator (fun a => Φ a p.2) p.1 := by
      funext p
      by_cases hp : p.1 ∈ S
      · simp [Set.indicator, hp, Function.uncurry]
      · simp [Set.indicator, hp]
    have hint2 : Integrable (fun p : A × B => S.indicator (fun a => Φ a p.2) p.1)
        ((P.map X).prod (P.map Y)) := by
      rw [← h4]
      exact hΦint.indicator (hS.prod MeasurableSet.univ)
    rw [h4, integral_prod _ hint2, ← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    by_cases ha : a ∈ S
    · simp [Set.indicator, ha]
    · simp [Set.indicator, ha]
  · have hm : @Measurable Ω ℝ (MeasurableSpace.comap X mA) _
        (fun ω => ∫ y, Φ (X ω) y ∂(P.map Y)) :=
      hhmeas.measurable.comp (comap_measurable X)
    exact hm.stronglyMeasurable.aestronglyMeasurable

end CondExp

section Domination

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A sequence of integrable functions, eventually dominated by a constant multiple of a uniformly
integrable sequence, is uniformly integrable (the finitely many small indices are integrable). -/
theorem unifIntegrable_dominated38 {W H : ℕ → Ω → ℝ} (hH : UnifIntegrable H 1 P) (c : ℝ) (hc : 0 ≤ c)
    (N₀ : ℕ) (hW : ∀ N, MemLp (W N) 1 P)
    (hdom : ∀ N, N₀ ≤ N → ∀ᵐ ω ∂P, ‖W N ω‖ ≤ c * ‖H N ω‖) :
    UnifIntegrable W 1 P := by
  rw [unifIntegrable_iff] at hH ⊢
  intro ε hε
  -- finitely many small indices
  have hfin : UnifIntegrable (fun i : Fin N₀ => W i) 1 P :=
    unifIntegrable_finite le_rfl ENNReal.one_ne_top (fun i => hW i)
  rw [unifIntegrable_iff] at hfin
  obtain ⟨δ₁, hδ₁, h₁⟩ := hfin ε hε
  set K : ℝ≥0∞ := ENNReal.ofReal |c| + 1 with hK
  have hKtop : K ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
  have hK0 : K ≠ 0 := by simp [hK]
  have hε' : 0 < ε / K := ENNReal.div_pos hε.ne' hKtop
  obtain ⟨δ₂, hδ₂, h₂⟩ := hH (ε / K) hε'
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun N s hs => ?_⟩
  by_cases hN : N < N₀
  · exact h₁ ⟨N, hN⟩ s (hs.trans (min_le_left _ _))
  · push Not at hN
    have h3 : eLpNorm (W N) 1 (P.restrict s) ≤ eLpNorm (fun ω => c * H N ω) 1 (P.restrict s) := by
      refine eLpNorm_mono_ae (f := W N) (g := fun ω => c * H N ω) (hW N).aestronglyMeasurable.restrict (ae_restrict_of_ae ?_)
      filter_upwards [hdom N hN] with ω hω
      rw [Real.norm_eq_abs] at hω ⊢
      simpa [abs_mul, abs_of_nonneg hc] using hω
    have h4 : eLpNorm (fun ω => c * H N ω) 1 (P.restrict s) =
        ‖c‖ₑ * eLpNorm (H N) 1 (P.restrict s) := by
      have := eLpNorm_const_smul (μ := P.restrict s) (p := 1) c (H N)
      exact this
    have h5 : ‖c‖ₑ ≤ K := by
      rw [hK, Real.enorm_eq_ofReal_abs]
      exact le_self_add
    calc eLpNorm (W N) 1 (P.restrict s) ≤ ‖c‖ₑ * eLpNorm (H N) 1 (P.restrict s) := h3.trans h4.le
      _ ≤ K * (ε / K) := mul_le_mul' h5 (h₂ N s (hs.trans (min_le_right _ _)))
      _ = ε := ENNReal.mul_div_cancel hK0 hKtop

end Domination

section L1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integral_abs_sub_tendsto_zero38 {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ N, Integrable (f N) P) (hg : Integrable g P)
    (h : Tendsto (fun N => eLpNorm (f N - g) 1 P) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ ω, |f N ω - g ω| ∂P) atTop (𝓝 0) := by
  have hint : ∀ N, Integrable (fun ω => f N ω - g ω) P := fun N => (hf N).sub hg
  have e : ∀ N, ∫ ω, |f N ω - g ω| ∂P = (eLpNorm (f N - g) 1 P).toReal := by
    intro N
    have h1 : eLpNorm (f N - g) 1 P = ∫⁻ ω, ‖f N ω - g ω‖ₑ ∂P := by
      exact eLpNorm_one_eq_lintegral_enorm (hint N).aestronglyMeasurable
    rw [h1, ← ofReal_integral_norm_eq_lintegral_enorm (hint N), ENNReal.toReal_ofReal
      (integral_nonneg fun ω => norm_nonneg _)]
    simp only [Real.norm_eq_abs]
  simp_rw [e]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def] using this

/-- Uniform integrability of a closed martingale `E[G | 𝒜 N]`, domination, and a.e. convergence
give `L¹` convergence (Vitali). -/
theorem tendsto_L1_martingale_dominated38 (𝒜 : ℕ → MeasurableSpace Ω) (h𝒜 : ∀ N, 𝒜 N ≤ mΩ)
    (G : Ω → ℝ) (hG : Integrable G P) {W : ℕ → Ω → ℝ} {Winf : Ω → ℝ} (c : ℝ) (hc : 0 ≤ c)
    (N₀ : ℕ) (hW : ∀ N, Integrable (W N) P) (hWinf : Integrable Winf P)
    (hdom : ∀ N, N₀ ≤ N → ∀ᵐ ω ∂P, ‖W N ω‖ ≤ c * ‖P[G | 𝒜 N] ω‖)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun N => W N ω) atTop (𝓝 (Winf ω))) :
    UnifIntegrable W 1 P ∧ Tendsto (fun N => ∫ ω, |W N ω - Winf ω| ∂P) atTop (𝓝 0) := by
  have hUI : UniformIntegrable (fun N => P[G | 𝒜 N]) 1 P := hG.uniformIntegrable_condExp h𝒜
  have hWUI : UnifIntegrable W 1 P :=
    unifIntegrable_dominated38 hUI.unifIntegrable c hc N₀
      (fun N => memLp_one_iff_integrable.2 (hW N)) hdom
  refine ⟨hWUI, integral_abs_sub_tendsto_zero38 hW hWinf ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun N => (hW N).aestronglyMeasurable) (memLp_one_iff_integrable.2 hWinf) hWUI hconv

end L1

section Tests

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- If the weights `W N → Wi` in `L¹` and the tests `Gs N` are uniformly bounded, a.e. convergent,
then `E[Gs N · W N] → E[G · Wi]`.  (v2: "the same argument applied to `F(P_N U)` times the
weights gives convergence of the normalized expectations".) -/
theorem tendsto_integral_mul_L1_38 {W : ℕ → Ω → ℝ} {Wi : Ω → ℝ}
    (hW : ∀ N, Integrable (W N) P) (hWi : Integrable Wi P)
    (hL1 : Tendsto (fun N => ∫ ω, |W N ω - Wi ω| ∂P) atTop (𝓝 0))
    {Gs : ℕ → Ω → ℝ} {G : Ω → ℝ} {C : ℝ} (hGm : ∀ N, AEStronglyMeasurable (Gs N) P)
    (hGb : ∀ N, ∀ᵐ ω ∂P, ‖Gs N ω‖ ≤ C)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun N => Gs N ω) atTop (𝓝 (G ω))) :
    Tendsto (fun N => ∫ ω, Gs N ω * W N ω ∂P) atTop (𝓝 (∫ ω, G ω * Wi ω ∂P)) := by
  have hC : 0 ≤ C := by
    have := hGb 0
    obtain ⟨ω, hω⟩ := this.exists
    exact (norm_nonneg _).trans hω
  have hWd : ∀ N, Integrable (fun ω => W N ω - Wi ω) P := fun N => (hW N).sub hWi
  have hI1 : ∀ N, Integrable (fun ω => Gs N ω * (W N ω - Wi ω)) P := fun N => by
    refine Integrable.mono' ((hWd N).norm.const_mul C) ((hGm N).mul (hWd N).aestronglyMeasurable) ?_
    filter_upwards [hGb N] with ω hω
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
  have hI2 : ∀ N, Integrable (fun ω => Gs N ω * Wi ω) P := fun N => by
    refine Integrable.mono' (hWi.norm.const_mul C) ((hGm N).mul hWi.aestronglyMeasurable) ?_
    filter_upwards [hGb N] with ω hω
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
  -- the second piece: `∫ Gs N * Wi → ∫ G * Wi` (dominated convergence)
  have h2 : Tendsto (fun N => ∫ ω, Gs N ω * Wi ω ∂P) atTop (𝓝 (∫ ω, G ω * Wi ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => C * ‖Wi ω‖)
      (fun N => (hGm N).mul hWi.aestronglyMeasurable) (hWi.norm.const_mul C) (fun N => ?_) ?_
    · filter_upwards [hGb N] with ω hω
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
    · filter_upwards [hconv] with ω hω
      exact hω.mul_const _
  -- the first piece: `|∫ Gs N * (W N - Wi)| ≤ C ∫ |W N - Wi|`
  have h1 : Tendsto (fun N => ∫ ω, Gs N ω * (W N ω - Wi ω) ∂P) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (by simpa using hL1.const_mul C)
    calc ‖∫ ω, Gs N ω * (W N ω - Wi ω) ∂P‖ ≤ ∫ ω, ‖Gs N ω * (W N ω - Wi ω)‖ ∂P :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ ω, C * |W N ω - Wi ω| ∂P := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
            ((hWd N).abs.const_mul C) ?_
          filter_upwards [hGb N] with ω hω
          rw [norm_mul, Real.norm_eq_abs (W N ω - Wi ω)]
          exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
      _ = C * ∫ ω, |W N ω - Wi ω| ∂P := integral_const_mul _ _
  have := h1.add h2
  simp only [zero_add] at this
  refine this.congr fun N => ?_
  rw [← integral_add (hI1 N) (hI2 N)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only []
  ring

end Tests

end NlsGge.Birkhoff

end
