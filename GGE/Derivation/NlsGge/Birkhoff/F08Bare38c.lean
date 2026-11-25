import NlsGge.Birkhoff.F08Bare38b

/-! # F08 (v2 `C:thm:bare`), file c: domination of the bare weights (F08.03)

`e^{-V_m(P_N U)} ≤ e^δ E[e^{-V_m(U) + δ M(U)^m} | A_N]` almost surely, for `N` large
(v2 l.829-845, `C:eq:domination`).  Conditional on `B`, `O` only through `F07_expMass38`
(integrability of the terminal variable).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory ProbabilityTheory Filter Topology NlsGge.Measure NlsGge.Pilot
  NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38 NlsGge.SpectralFoundations
open scoped ENNReal

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {m : ℕ} {β : ℕ → ℝ}
  (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

/-- The terminal variable `F = exp(-V_m(U) + δ M(U)^m)` on the Gaussian sequence space. -/
def termG38 (m : ℕ) (β : ℕ → ℝ) (δ : ℝ) (ω : ℤ → ℂ) : ℝ :=
  Real.exp (-(vSobolev38 m β (gaussianRealization38 m ω)) +
    δ * (chargeSobolev38 m 0 (gaussianRealization38 m ω)) ^ m)

include O hm hβ in
theorem integrable_termG38 {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < β (m - 1)) :
    Integrable (termG38 m β δ) (gammaM38 m β) := by
  obtain ⟨hint, -⟩ := F07_expMass38 B O hm hβ hδ0 hδ
  rw [gammaFM38_eq_realization m β] at hint
  exact (integrable_map_measure hint.aestronglyMeasurable
    measurable_gaussianRealization38.aemeasurable).1 hint

include O hm hβ in
/-- **F08.03** (v2 `C:eq:domination`). -/
theorem F08_domination38 {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < β (m - 1)) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N, N₀ ≤ N → ∀ᵐ ω ∂(gammaM38 m β),
      Real.exp (-(vSobolev38 m β (PN38 m N ω))) ≤
        Real.exp δ * (gammaM38 m β)[termG38 m β δ | NlsGge.Ramer.windowSigma N] ω := by
  have hb := fun i (hi : i ≤ m) => (hβ i hi).le
  obtain ⟨A, Bc, hA, hBc, hcon⟩ := contractions_massBound38 hm hb (hβ 0 (Nat.zero_le _))
    (hβ m le_rfl)
  refine ⟨max 1 ⌈Bc / δ⌉₊, le_max_left _ _, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNδ : Bc ≤ δ * N := by
    have h1 : ⌈Bc / δ⌉₊ ≤ N := le_trans (le_max_right _ _) hN
    have h2 : Bc / δ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    rw [div_le_iff₀ hδ0] at h2
    linarith
  set γ := gammaM38 m β with hγ
  have hsle : NlsGge.Ramer.windowSigma N ≤ MeasurableSpace.pi := NlsGge.Ramer.windowSigma_le_pi N
  set Vg : (ℤ → ℂ) → ℝ := fun ω => vSobolev38 m β (gaussianRealization38 m ω) with hVg
  set Mg : (ℤ → ℂ) → ℝ := fun ω => (chargeSobolev38 m 0 (gaussianRealization38 m ω)) ^ m with hMg
  set Xf : (ℤ → ℂ) → ℝ := fun ω => -Vg ω + δ * Mg ω with hXf
  have hVint : Integrable Vg γ := integrable_Vgr38 hm hβ
  have hMint : Integrable Mg γ := integrable_mass_pow38 hm hβ
  have hXint : Integrable Xf γ := hVint.neg.add (hMint.const_mul δ)
  have hGint : Integrable (termG38 m β δ) γ := integrable_termG38 B O hm hβ hδ0 hδ
  have hGeq : termG38 m β δ = Real.exp ∘ Xf := rfl
  -- conditional Jensen
  have hJ := ConvexOn.map_condExp_le (m := NlsGge.Ramer.windowSigma N) (μ := γ) hsle convexOn_exp
    (Real.continuous_exp.lowerSemicontinuous.lowerSemicontinuousOn _)
    (Eventually.of_forall fun _ => Set.mem_univ _) isClosed_univ hXint
    (by rw [← hGeq]; exact hGint)
  -- linearity of conditional expectation
  have e1 : γ[Xf | (NlsGge.Ramer.windowSigma N)] =ᵐ[γ] γ[fun ω => -Vg ω | (NlsGge.Ramer.windowSigma N)] + γ[fun ω => δ * Mg ω | (NlsGge.Ramer.windowSigma N)] :=
    condExp_add hVint.neg (hMint.const_mul δ) (NlsGge.Ramer.windowSigma N)
  have e2 : γ[fun ω => -Vg ω | (NlsGge.Ramer.windowSigma N)] =ᵐ[γ] -γ[Vg | (NlsGge.Ramer.windowSigma N)] := condExp_neg Vg (NlsGge.Ramer.windowSigma N)
  have e3 : γ[fun ω => δ * Mg ω | (NlsGge.Ramer.windowSigma N)] =ᵐ[γ] δ • γ[Mg | (NlsGge.Ramer.windowSigma N)] := condExp_smul δ Mg (NlsGge.Ramer.windowSigma N)
  -- the low-mode mass
  set aN : (ℤ → ℂ) → ℝ := fun ω => (massN38 N ω) ^ m with haN
  have haNm : @Measurable (ℤ → ℂ) ℝ (NlsGge.Ramer.windowSigma N) _ aN := by
    have : aN = (fun z : FourierPlane N => (‖planeL2 N z‖ ^ 2) ^ m) ∘ NlsGge.Ramer.windowProj N := rfl
    rw [this]
    refine Measurable.comp ?_ (comap_measurable (NlsGge.Ramer.windowProj N))
    simp_rw [planeL2_norm_sq]
    exact (Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).norm).pow_const 2).pow_const m
  have haNle : ∀ᵐ ω ∂γ, aN ω ≤ Mg ω := by
    filter_upwards [ae_massN_le_mass38 hm hβ N] with ω hω
    exact pow_le_pow_left₀ (massN38_nonneg N ω) hω m
  have haNint : Integrable aN γ :=
    hMint.mono' ((measurable_massN38 N).pow_const m).aestronglyMeasurable
      (by filter_upwards [haNle] with ω hω
          rw [Real.norm_of_nonneg (pow_nonneg (massN38_nonneg N ω) _)]; exact hω)
  have hmono : γ[aN | (NlsGge.Ramer.windowSigma N)] ≤ᵐ[γ] γ[Mg | (NlsGge.Ramer.windowSigma N)] := condExp_mono haNint hMint haNle
  have hself : γ[aN | (NlsGge.Ramer.windowSigma N)] = aN := condExp_of_stronglyMeasurable hsle haNm.stronglyMeasurable haNint
  rw [hself] at hmono
  filter_upwards [hJ, e1, e2, e3, hmono, condExp_V_gr38 hm hβ N] with ω hJω e1ω e2ω e3ω hmω hLω
  have hC := (hcon N hN1 (NlsGge.Ramer.windowProj N ω)).2.1
  have hC2 := (hcon N hN1 (NlsGge.Ramer.windowProj N ω)).2.2
  have hCle : |contractionCorrection38 m β N (NlsGge.Ramer.windowProj N ω)| ≤
      δ * (1 + aN ω) := by
    refine hC.trans (hC2.trans ?_)
    have : Bc / N ≤ δ := by
      rw [div_le_iff₀ (by exact_mod_cast hN1 : (0 : ℝ) < N)]; linarith
    have h1 : 0 ≤ 1 + (‖planeL2 N (NlsGge.Ramer.windowProj N ω)‖ ^ 2) ^ m := by positivity
    exact mul_le_mul_of_nonneg_right this h1
  have hXω : γ[Xf | (NlsGge.Ramer.windowSigma N)] ω = -γ[Vg | (NlsGge.Ramer.windowSigma N)] ω + δ * γ[Mg | (NlsGge.Ramer.windowSigma N)] ω := by
    rw [e1ω, Pi.add_apply, e2ω, e3ω]
    rfl
  have hexp : Real.exp (-(vSobolev38 m β (PN38 m N ω))) ≤ Real.exp (γ[Xf | (NlsGge.Ramer.windowSigma N)] ω + δ) := by
    refine Real.exp_le_exp.2 ?_
    rw [hXω]
    have hCl := (abs_le.1 hCle).2
    have h3 : δ * aN ω ≤ δ * γ[Mg | (NlsGge.Ramer.windowSigma N)] ω := mul_le_mul_of_nonneg_left hmω hδ0.le
    nlinarith [hLω, hCl, h3]
  calc Real.exp (-(vSobolev38 m β (PN38 m N ω))) ≤ Real.exp (γ[Xf | (NlsGge.Ramer.windowSigma N)] ω + δ) := hexp
    _ = Real.exp δ * Real.exp (γ[Xf | (NlsGge.Ramer.windowSigma N)] ω) := by rw [add_comm, Real.exp_add]
    _ ≤ Real.exp δ * γ[termG38 m β δ | (NlsGge.Ramer.windowSigma N)] ω := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have : γ[termG38 m β δ | (NlsGge.Ramer.windowSigma N)] = γ[Real.exp ∘ Xf | (NlsGge.Ramer.windowSigma N)] := by rw [hGeq]
        rw [this]
        exact hJω

end BirkhoffInput38

end NlsGge.Birkhoff

end
