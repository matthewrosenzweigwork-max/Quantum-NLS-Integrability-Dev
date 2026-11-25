import QuantumNLS.R52CFCount
import QuantumNLS.R52CFDev

/-!
# R-52CF5DA1 stage 11b: the strong scalar limit of each fixed intensive count, near a rough center

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101), second printed clause "On the same profile class
each fixed intensive count has a strong scalar limit `I_n(u)`, uniformly", proof paragraph "Taking `p = 4` and using
the bounded cutoff operators extends the intensive reconstruction bound to `v^{⊗N}`, uniformly with error `C_* N^{-2}`.
Lemma `lem:audit-scalar-period` identifies the scalar leading contour exactly with `I_n(v)`. Lipschitz continuity of
the fixed cutoff functions and the second-moment transfer estimates then give `‖(C^{(0)}_{N,n} - I_n(v)) v^{⊗N}‖ ...
≤ C_* N^{-1/2}` ... This proves the local uniform count concentration."

**`scalar_local`**: for every unit rough center `u` and label `n` there is a neighborhood `U ∋ u` such that for every
`ε > 0` there is `N₀` with `‖(M_{N,n}/N - I_n(v)) v^{⊗N}‖ ≤ ε` for all `N ≥ N₀` and all unit `v ∈ U`
(`M_{N,n}/N` = the accepted PROP-010 normalized count `B`, `I_n` = the indexed action `mass`).
Ingredients: the accepted PROP-010 extensions and leading identification at `u` (rectangle height `1`), stage 10a
(`count_near`), stage 11a (`C0_dev`), and the PROP-010 eigenvalue bound for `C^{(1)}`.
No hypothesis is added; all inherited modules are read-only.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open Set Filter Topology Complex MeasureTheory
open scoped InnerProductSpace BigOperators

namespace QuantumNLS.R52CFScalar

open QuantumNLS.Prop010ContourBindingR11
open PhysicalTensor (L2T)
open RootMassInvolutionR8 (mass)
open LabelExactPeriod (rectIntegral)

variable (L : ℝ) [Fact (0 < L)] {κ : ℝ}

/-- The three error terms tend to zero. -/
theorem error_tendsto (D K0 C K1 : ℝ) :
    Tendsto (fun N : ℕ => D * ((N : ℝ)⁻¹) ^ 2 + K0 * Real.sqrt (C / N) + (N : ℝ)⁻¹ * K1) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using h1.const_mul C
  have h3 : Tendsto (fun N : ℕ => Real.sqrt (C / N)) atTop (𝓝 0) := by
    have h4 := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at h4
    exact h4
  have := ((h1.pow 2).const_mul D).add (h3.const_mul K0) |>.add (h1.mul_const K1)
  simpa using this

theorem norm_C1_le (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (g : Extension (ℂ × (ℂ × ℂ))) {a b h : ℝ}
    (hab : a ≤ b) (hh : 0 ≤ h) :
    ‖C1 L hκ hN g a b h‖ ≤ (2 * Real.pi)⁻¹ * (2 * (b - a) + 4 * h) * g.bound := by
  apply BoundedBetheTransfer.diagonal_norm_le (basis L hκ hN) _ (fun i => ((c1 L hκ hN g a b h i : ℝ) : ℂ))
    (C1_basis L hκ hN g hab hh)
  · have := g.bound_nonneg
    have : 0 ≤ b - a := by linarith
    positivity
  · intro i
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact c1_bound L hκ hN g hab hh i

/-- **Local uniform strong scalar limit of the intensive count.** -/
theorem scalar_local (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (n : ℤ) :
    ∃ U ∈ 𝓝 u, ∀ ε > 0, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N → ∀ v ∈ U, ‖v‖ = 1 →
      ‖(B L hκ hN n - ((mass hκ n v : ℝ) : ℂ) •
        (1 : BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N))
        (HighMomentsOps.wvec N v)‖ ≤ ε := by
  obtain ⟨F, H, hF, hFc, hH, hHc, r, hr, hf, hg, -, ⟨U1, hU1o, hU1, hlead, -, -⟩, -⟩ :=
    Prop010SingleContourR17.condensate_reconstruction hκ u hu n (h := 1) one_pos
  let f := Extension.ofSmooth F hF hFc
  let g := Extension.ofSmooth H hH hHc
  obtain ⟨D, hD, N₀, U0, hU0, hcount⟩ := R52CFCount.count_near L hκ u hu n one_pos hr f g hf hg
  refine ⟨U0 ∩ U1, inter_mem hU0 (hU1o.mem_nhds hU1), ?_⟩
  intro ε hε
  set a := RootScalarPeriodR8.cut hκ u (n-1) with ha
  set b := RootScalarPeriodR8.cut hκ u n with hb
  have hab : a ≤ b :=
    ((DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).phase.separator_strictMono (by omega)).le
  let K0 := |(2 * Real.pi * κ)⁻¹| * ((2 * (b - a) + 4 * 1) * f.constant)
  let K1 := (2 * Real.pi)⁻¹ * (2 * (b - a) + 4 * 1) * g.bound
  let Cu := HighMomentsTransfer.Cunif L κ 1 1
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((error_tendsto D K0 Cu K1).eventually (ge_mem_nhds hε))
  refine ⟨max N₀ N₁, ?_⟩
  intro N hN hNN v hv hv1
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hNN
  have hN1 : N₁ ≤ N := le_trans (le_max_right _ _) hNN
  set ψ := HighMomentsOps.wvec N v
  have hψ : ‖ψ‖ = 1 := HighMomentsFinal.norm_wvec v hv1 N
  have hI : -(2 * Real.pi * κ)⁻¹ *
      (rectIntegral (fun z => f.value (z, NormalizedTransfer.productSymbol L κ v z)) a b 1).re = mass hκ n v :=
    hlead v hv.2
  have hdec : B L hκ hN n - ((mass hκ n v : ℝ) : ℂ) • 1 =
      (B L hκ hN n - C L hκ hN f g a b 1) +
        (C0 L hκ hN f a b 1 - ((mass hκ n v : ℝ) : ℂ) • 1) + ((N : ℂ)⁻¹) • C1 L hκ hN g a b 1 := by
    simp only [Prop010ContourBindingR11.C]
    abel
  have e1 := hcount N hN hN0 v hv.1 hv1
  have e2 := R52CFDev.C0_dev L hκ hN f hab zero_le_one v hv1
  rw [hI] at e2
  have e3 : ‖((N : ℂ)⁻¹ • C1 L hκ hN g a b 1) ψ‖ ≤ (N : ℝ)⁻¹ * K1 := by
    rw [ContinuousLinearMap.smul_apply, norm_smul, norm_inv, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖C1 L hκ hN g a b 1 ψ‖ ≤ ‖C1 L hκ hN g a b 1‖ * ‖ψ‖ := (C1 L hκ hN g a b 1).le_opNorm ψ
      _ ≤ K1 * 1 := by rw [hψ]; exact mul_le_mul_of_nonneg_right (norm_C1_le L hκ hN g hab zero_le_one) zero_le_one
      _ = K1 := mul_one _
  have e2' : ‖(C0 L hκ hN f a b 1 - ((mass hκ n v : ℝ) : ℂ) • 1) ψ‖ ≤ K0 * Real.sqrt (Cu / N) := by
    refine e2.trans (le_of_eq ?_)
    simp only [K0, Cu]
    ring
  calc ‖(B L hκ hN n - ((mass hκ n v : ℝ) : ℂ) • 1) ψ‖
      ≤ ‖(B L hκ hN n - C L hκ hN f g a b 1) ψ‖ + ‖(C0 L hκ hN f a b 1 - ((mass hκ n v : ℝ) : ℂ) • 1) ψ‖ +
          ‖((N : ℂ)⁻¹ • C1 L hκ hN g a b 1) ψ‖ := by
        rw [hdec, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ D * ((N : ℝ)⁻¹) ^ 2 + K0 * Real.sqrt (Cu / N) + (N : ℝ)⁻¹ * K1 :=
        add_le_add (add_le_add e1 e2') e3
    _ ≤ ε := hN₁ N hN1

end QuantumNLS.R52CFScalar

#print axioms QuantumNLS.R52CFScalar.scalar_local
