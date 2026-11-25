import NlsGge.Spectral.SobolevToL2Map38
import NlsGge.Spectral.TraceFormulaHk38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38

/-! # Q3: uniform tails of the top moment along `H^k`-convergent sequences

Conditional on the R3c hypothesis `NonlinRiccatiSmoothBound38 k`. The full moments
`(2/π)∫(1+(2t)^{2k}) v = ‖u‖² + chargeSobolev38 (k+1) k y` converge (R4 and continuity of the charge);
on compacts the heights converge (E03-cont); hence the tails are uniformly small. -/

/-- The weighted height `(1 + (2t)^{2k}) v_u(t)`. -/
def momentDensity38 (k : ℕ) (u : PhysicalL2) (t : ℝ) : ℝ :=
  (1 + (2*t)^(2*k)) * actualGapHeightE02_38 u t

theorem momentDensity38_nonneg (k : ℕ) (u : PhysicalL2) (t : ℝ) : 0 ≤ momentDensity38 k u t := by
  unfold momentDensity38
  have h1 : 0 ≤ (2*t)^(2*k) := by rw [pow_mul]; positivity
  exact mul_nonneg (by linarith) (actualGapHeightE02_38_nonneg u t)

theorem continuous_momentDensity38 (k : ℕ) (u : PhysicalL2) : Continuous (momentDensity38 k u) := by
  unfold momentDensity38
  exact (continuous_const.add (by fun_prop)).mul (continuous_actualGapHeightE02_38 u)

/-- Full moment of the `H^k` field, from the L² trace formula and the top trace formula. -/
theorem fullMoment38 (k : ℕ) (hk : 1 ≤ k) (hR3c : NonlinRiccatiSmoothBound38 k)
    (y : SobolevHilbert (k : ℝ)) :
    Integrable (momentDensity38 k (sobolevToL2_38 k y)) ∧
    (2/Real.pi) * ∫ t, momentDensity38 k (sobolevToL2_38 k y) t =
      ‖sobolevToL2_38 k y‖ ^ 2 + chargeSobolev38 (k + 1) k y := by
  have hpi := Real.pi_pos
  set u := sobolevToL2_38 k y with hu
  have hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n := fun n => (sobolevToL2_38_fourier k y n).symm
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) :=
    hk_summable38 k u y hy hk u (fun _ => le_rfl)
  obtain ⟨h0I, h0E⟩ := actualGapHeight_integral_eq_normSq_E02_38 u hu1
  obtain ⟨hkI, hkE⟩ := actualTraceFormula_Hk38 k hk hR3c u y hy
  have hfun : momentDensity38 k u =
      fun t => actualGapHeightE02_38 u t + (2*t)^(2*k) * actualGapHeightE02_38 u t := by
    funext t; unfold momentDensity38; ring
  have hI : Integrable (momentDensity38 k u) := by rw [hfun]; exact h0I.add hkI
  refine ⟨hI, ?_⟩
  rw [hfun, integral_add h0I hkI, mul_add, h0E, hkE]

/-- Heights converge uniformly on compacts along `L²`-convergent sequences. -/
theorem heights_uniform_eventually38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hu : Tendsto u atTop (𝓝 u₀)) (L : ℝ) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ j in atTop, ∀ x ∈ Icc (-L) L,
      |actualGapHeightE02_38 (u j) x - actualGapHeightE02_38 u₀ x| < ε' := by
  obtain ⟨τ, hτ, hclose⟩ := gapHeight_uniform_close_E02_38 u₀ (-L) L ε' hε'
  have hd := (Metric.tendsto_nhds.mp hu) τ hτ
  filter_upwards [hd] with j hj
  exact hclose (u j) (by rw [← dist_eq_norm]; exact hj.le)

/-- On a compact interval the weighted integrals converge. -/
theorem Icc_moment_tendsto38 (k : ℕ) (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hu : Tendsto u atTop (𝓝 u₀)) (L : ℝ) :
    Tendsto (fun j => ∫ t in Icc (-L) L, momentDensity38 k (u j) t) atTop
      (𝓝 (∫ t in Icc (-L) L, momentDensity38 k u₀ t)) := by
  have hev := heights_uniform_eventually38 u u₀ hu L one_pos
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => (1 + (2*t)^(2*k)) * (actualGapHeightE02_38 u₀ t + 1)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun j => (continuous_momentDensity38 k (u j)).aestronglyMeasurable
  · filter_upwards [hev] with j hj
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun x hx => ?_)
    have h1 : 0 ≤ (2*x)^(2*k) := by rw [pow_mul]; positivity
    have h2 := hj x hx
    have h3 := actualGapHeightE02_38_nonneg (u j) x
    rw [Real.norm_eq_abs, abs_of_nonneg (momentDensity38_nonneg k (u j) x)]
    unfold momentDensity38
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have := (abs_lt.mp h2).2
    linarith
  · have hc : Continuous (fun t : ℝ => (1 + (2*t)^(2*k)) * (actualGapHeightE02_38 u₀ t + 1)) :=
      (continuous_const.add (by fun_prop)).mul ((continuous_actualGapHeightE02_38 u₀).add continuous_const)
    exact hc.continuousOn.integrableOn_Icc
  · refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun x hx => ?_)
    unfold momentDensity38
    refine Tendsto.const_mul _ ?_
    rw [Metric.tendsto_nhds]
    intro ε' hε'
    filter_upwards [heights_uniform_eventually38 u u₀ hu L hε'] with j hj
    rw [Real.dist_eq]
    exact hj x hx

/-- **Q3.** Uniform tails of the top moment along `H^k`-convergent sequences. -/
theorem moment_tight38 (k : ℕ) (hk : 1 ≤ k) (hR3c : NonlinRiccatiSmoothBound38 k)
    (y : ℕ → SobolevHilbert (k : ℝ)) (yLim : SobolevHilbert (k : ℝ)) (hy : Tendsto y atTop (𝓝 yLim)) :
    ∀ ε > 0, ∃ L : ℝ, 0 ≤ L ∧ ∃ j₀ : ℕ, ∀ j ≥ j₀,
      ∫ t in (Set.Icc (-L) L)ᶜ, (1 + (2*t)^(2*k)) * actualGapHeightE02_38 (sobolevToL2_38 k (y j)) t ≤ ε := by
  intro ε hε
  have hpi := Real.pi_pos
  set u : ℕ → PhysicalL2 := fun j => sobolevToL2_38 k (y j) with hu
  set u₀ : PhysicalL2 := sobolevToL2_38 k yLim with hu₀
  have huT : Tendsto u atTop (𝓝 u₀) := ((sobolevToL2_38 k).continuous.tendsto yLim).comp hy
  -- full moments
  have hF : Continuous (fun z : SobolevHilbert (k : ℝ) =>
      ‖sobolevToL2_38 k z‖ ^ 2 + chargeSobolev38 (k + 1) k z) :=
    (((sobolevToL2_38 k).continuous.norm).pow 2).add (continuous_chargeSobolev38 (k + 1) k (by omega))
  have hfull : Tendsto (fun j => ∫ t, momentDensity38 k (u j) t) atTop (𝓝 (∫ t, momentDensity38 k u₀ t)) := by
    have hc : ∀ z : SobolevHilbert (k : ℝ), ∫ t, momentDensity38 k (sobolevToL2_38 k z) t =
        (Real.pi / 2) * (‖sobolevToL2_38 k z‖ ^ 2 + chargeSobolev38 (k + 1) k z) := by
      intro z
      have := (fullMoment38 k hk hR3c z).2
      field_simp at this ⊢
      linarith
    have h1 := (hF.tendsto yLim).comp hy
    have h2 := h1.const_mul (Real.pi / 2)
    simp only [hu, hu₀, hc]
    exact h2
  -- tails of the limit
  have hILim := (fullMoment38 k hk hR3c yLim).1
  have hmono : Monotone (fun n : ℕ => Icc (-(n : ℝ)) n) := by
    intro a b hab x hx
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hunion : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
    ext x
    simp only [mem_iUnion, mem_Icc, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hlim := tendsto_setIntegral_of_monotone (μ := volume) (f := momentDensity38 k u₀)
    (fun n => measurableSet_Icc) hmono hILim.integrableOn
  rw [hunion, setIntegral_univ] at hlim
  obtain ⟨N, hN⟩ := ((Metric.tendsto_nhds.mp hlim) (ε / 2) (by linarith)).exists
  refine ⟨(N : ℝ), Nat.cast_nonneg N, ?_⟩
  have htail : ∀ (v : PhysicalL2), Integrable (momentDensity38 k v) → ∀ L : ℝ,
      ∫ t in (Icc (-L) L)ᶜ, momentDensity38 k v t =
        (∫ t, momentDensity38 k v t) - ∫ t in Icc (-L) L, momentDensity38 k v t := by
    intro v hv L
    have := integral_add_compl (μ := volume) (measurableSet_Icc (a := -L) (b := L)) hv
    linarith
  have hconv : Tendsto (fun j => (∫ t, momentDensity38 k (u j) t) -
      ∫ t in Icc (-(N : ℝ)) N, momentDensity38 k (u j) t) atTop
      (𝓝 ((∫ t, momentDensity38 k u₀ t) - ∫ t in Icc (-(N : ℝ)) N, momentDensity38 k u₀ t)) :=
    hfull.sub (Icc_moment_tendsto38 k u u₀ huT (N : ℝ))
  have hlt : (∫ t, momentDensity38 k u₀ t) - ∫ t in Icc (-(N : ℝ)) N, momentDensity38 k u₀ t < ε := by
    have := hN
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1, this.2]
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (hconv.eventually (gt_mem_nhds hlt))
  refine ⟨j₀, fun j hj => ?_⟩
  have hIj := (fullMoment38 k hk hR3c (y j)).1
  have := htail (u j) hIj N
  have h2 := hj₀ j hj
  show ∫ t in (Icc (-(N : ℝ)) N)ᶜ, momentDensity38 k (u j) t ≤ ε
  rw [this]
  exact h2.le

end NlsGge.SpectralFoundations
