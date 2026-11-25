import Mathlib
import QuantumNLS.RC05Statement

/-!
# RC05Parts: bridges for R-C05E2420 `thm:global-full-transform` (`principal_global.tex:2`)

Every theorem here only connects the printed statements of the predecessors to the explicit statements of `RC05Statement`:

* `clauses_of_statement`, `statement_of_clauses`: `RF535Final.GlobalStatement` (R-F5355ABD, accepted) is
  `(torus part) ∧ ∃ Y F Φ Ψ, ..`; `RC05Statement.GlobalClauses` is exactly the second conjunct with `(Φ, Ψ)` explicit
  (both directions type-check by `exact`).
* `global_clauses_of_family`: for any extension family `Φ, Ψ` of the reviewed local maps (`GlobalCompatR47a.Family`,
  R-CA92819A) the explicit global-map conclusions hold, because the `Φ_κ` of `thm:global-actual-chart` and the family
  member agree on the entire local ball and both are real analytic (the identity principle `GlobalCompatR47a.identity`).
* `printedChartLocal`: the hypotheses of the physical-dynamics headline (R-EF8C2837) hold for every family member, from
  `Extension` and the accepted `GlobalCompatR47a.Compatibility` (Fourier differential, real identity).
* `physDyn_of`: `PhysDyn` is exactly `REF88Final.global_physical_dynamics`.
* `period_conversion`: R-71F7DDC8 for the printed characterization `IsGlobalChart` via the accepted uniqueness
  (`PeriodChartR42b.selected_unique`, i.e. `global_compatibility`) and `IndependentScalingConversionR42b.independent_scaling_conversion`.
* `rephasing_freedom`: the action-dependent phase freedom of R-8DD5AE6E acting on the global map.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology ComplexConjugate
open Filter Set Metric

namespace QuantumNLS.RC05Parts

open QuantumNLS.StrongSymplectic QuantumNLS.REF88PrintedChartLocal QuantumNLS.RC05Statement
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.RF535Final (Local023Body GlobalStatement)
open QuantumNLS.GlobalCompatR47a (Extension Family Compatibility)
open QuantumNLS.ResetNormalizationUniqueness (Cphys)
open QuantumNLS.Fourier (fourierL2 modeLp)

variable {L : ℝ} [Fact (0 < L)] {κ d CL : ℝ}

/-! ## R-F5355ABD -/

theorem clauses_of_statement (hκ : 0 < κ) {Φl : L2T L → K} {Ψl : K → L2T L}
    (h : GlobalStatement L κ hκ d Φl Ψl) : ∃ (Φ : L2T L → K) (Ψ : K → L2T L), GlobalClauses L κ hκ d Φl Ψl Φ Ψ := by
  obtain ⟨-, Y, F, Φ, Ψ, hB⟩ := h
  exact ⟨Φ, Ψ, Y, F, hB⟩

theorem statement_of_clauses (hκ : 0 < κ) {Φl : L2T L → K} {Ψl : K → L2T L}
    (h0 : GlobalStatement L κ hκ d Φl Ψl) {Φ : L2T L → K} {Ψ : K → L2T L}
    (h : GlobalClauses L κ hκ d Φl Ψl Φ Ψ) : GlobalStatement L κ hκ d Φl Ψl := by
  obtain ⟨Y, F, hB⟩ := h
  exact ⟨h0.1, Y, F, Φ, Ψ, hB⟩

theorem global_clauses_of_family {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
    {Φ : ℝ → L2T L → K} {Ψ : ℝ → K → L2T L}
    (hd : 0 < d) (hCL : 0 ≤ CL) (hl : Local023Body L d CL Φl Ψl) (hf : Family d Φl Ψl Φ Ψ)
    (hκ : 0 < κ) : GlobalClauses L κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ) := by
  have h0 := (QuantumNLS.RF535Final.global_actual_chart L).2 d CL Φl Ψl hd hCL hl κ hκ
  obtain ⟨-, Y, F, Φ0, Ψ0, hY1, hY2, hF0, hFd, hFu, hform, hiform, hΦan, hΨan, hΨΦ, hΦΨ, hq, hn, hs, he,
    hl0, hl1, hsurj, hfib, hint1, hint2, hper, hper0⟩ := h0
  have hext := hf κ hκ
  have hr : 0 < d / Real.sqrt κ := div_pos hd (Real.sqrt_pos.2 hκ)
  have hΦeq : Φ0 = Φ κ :=
    QuantumNLS.GlobalCompatR47a.identity hΦan hext.analytic hr
      (fun u hu => (hl0 u hu).trans (hext.local_eq u hu).symm)
  subst hΦeq
  have hΨeq : Ψ0 = Ψ κ := by
    funext z
    calc Ψ0 z = Ψ0 (Φ κ (Ψ κ z)) := by rw [hext.right_inv]
      _ = Ψ κ z := hΨΦ _
  subst hΨeq
  exact ⟨Y, F, hY1, hY2, hF0, hFd, hFu, hform, hiform, hΦan, hΨan, hΨΦ, hΦΨ, hq, hn, hs, he,
    hl0, hl1, hsurj, hfib, hint1, hint2, hper, hper0⟩

/-! ## R-CA92819A and R-EF8C2837 -/

theorem printedChartLocal {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
    {Φ : ℝ → L2T L → K} {Ψ : ℝ → K → L2T L}
    (hf : Family d Φl Ψl Φ Ψ) (hc : Compatibility d CL Φ Ψ) (hκ : 0 < κ) :
    PrintedChartLocal hκ (Φ κ) := by
  have hext := hf κ hκ
  obtain ⟨-, hD, -, hreal, -⟩ := hc.1 κ hκ
  refine ⟨hext.strong, hext.analytic, hext.moduli, fun v => ?_, Filter.Eventually.of_forall (hreal)⟩
  have := congrArg (fun A : L2T L →L[ℝ] K => A v) hD
  exact this

theorem physDyn_of {Φ : L2T L → K} (hκ : 0 < κ) (hΦ : PrintedChartLocal hκ Φ) : PhysDyn hκ hΦ.symp :=
  QuantumNLS.REF88Final.global_physical_dynamics hκ hΦ

/-! ## R-71F7DDC8 -/

theorem period_conversion : PeriodConversion := by
  intro L κ _ hκ G G1 G11 hG hG1 hG11 u
  have hκL : 0 < κ * L := mul_pos hκ (Fact.out : 0 < L)
  have e1 : G = QuantumNLS.Def021ChartR41b.Phi L κ :=
    QuantumNLS.PeriodChartR42b.selected_unique hκ G hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2
  have e2 : G1 = QuantumNLS.Def021ChartR41b.Phi 1 (κ * L) :=
    QuantumNLS.PeriodChartR42b.selected_unique (L := 1) hκL G1 hG1.1 hG1.2.1 hG1.2.2.1 hG1.2.2.2.1 hG1.2.2.2.2
  have e3 : G11 = QuantumNLS.Def021ChartR41b.Phi 1 1 :=
    QuantumNLS.PeriodChartR42b.selected_unique (L := 1) (κ := 1) one_pos G11 hG11.1 hG11.2.1 hG11.2.2.1
      hG11.2.2.2.1 hG11.2.2.2.2
  subst e1 e2 e3
  exact QuantumNLS.IndependentScalingConversionR42b.independent_scaling_conversion L κ hκ u

/-! ## R-8DD5AE6E -/

open QuantumNLS.RephasingFlow in
theorem strong_of_diffeo {f : E → E} (h : IsStrongSymplecticDiffeo f) : IsStronglySymplectic f :=
  ⟨h.exists_inverse, fun z => h.differentiable z, h.deriv_iso, h.symplectic⟩

theorem rephasing_freedom {Φ : L2T L → K} (hκ : 0 < κ) (hΦ : PrintedChartLocal hκ Φ)
    (hplane : ∀ (a : ℂ) (k : ℤ), Φ (a • modeLp L k) = a • lp.single 2 k (1 : ℂ))
    (hnorm : ∀ u, ‖Φ u‖ ^ 2 = ‖u‖ ^ 2)
    (hsurj : ∀ z : K, ∃ u : L2T L, Φ u = z) (hreal : ∀ u, Φ (Cphys L u) = star (Φ u))
    (c : ℝ) (hc : c ≠ 0) : RephasingFreedom hκ Φ c := by
  have hΦ0 : Φ 0 = 0 := by
    have := hplane 0 0
    simpa using this
  obtain ⟨-, ⟨hUapp, -⟩, hall, ⟨hd0, hsingle, -, -, -, -⟩, ⟨hconj, -⟩⟩ :=
    QuantumNLS.RephasingFlow.norm_rephasing c κ hc hκ
  obtain ⟨hUs, -, -, hUn, -⟩ := hall 1
  have hU := strong_of_diffeo hUs
  have hbad : ∃ u : L2T L, (QuantumNLS.RephasingFlow.U c κ 1 ∘ Φ) (Cphys L u) ≠
      star ((QuantumNLS.RephasingFlow.U c κ 1 ∘ Φ) u) := by
    obtain ⟨z, hz⟩ := hconj
    obtain ⟨u, hu⟩ := hsurj z
    refine ⟨u, ?_⟩
    simp only [Function.comp_apply]
    rw [hreal u, hu]
    have hs : ∀ w : K, star w = QuantumNLS.RephasingFlow.conjE w := fun w => lp.ext (funext fun n => rfl)
    rw [hs, hs]
    exact hz
  refine ⟨QuantumNLS.RephasingFlow.U c κ 1 ∘ Φ, hΦ.symp.comp hU, fun u => ?_, fun u n => ?_, fun v => ?_,
    fun a k => ?_, fun u n => ?_, hbad, ?_⟩
  · exact (QuantumNLS.RephasingFlow.U_analyticAt c κ 1 _).comp (hΦ.analytic u)
  · simp only [Function.comp_apply]
    rw [hUn, hΦ.moduli]
  · have hdiff : DifferentiableAt ℝ Φ 0 := (hΦ.analytic 0).differentiableAt
    have hUd : DifferentiableAt ℝ (QuantumNLS.RephasingFlow.U c κ 1) (Φ 0) :=
      (QuantumNLS.RephasingFlow.U_analyticAt c κ 1 _).differentiableAt
    have := fderiv_comp (𝕜 := ℝ) (0 : L2T L) hUd hdiff
    rw [this]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hΦ0, hd0, ContinuousLinearMap.id_apply, hΦ.fourier]
  · simp only [Function.comp_apply]
    rw [hplane a k]
    have h1 : a • lp.single 2 k (1 : ℂ) = lp.single (E := fun _ : ℤ => ℂ) 2 k a := by
      rw [← lp.single_smul]; simp
    rw [h1, hsingle k a]
  · simp only [Function.comp_apply]
    rw [hUapp, hnorm, hΦ.moduli, Complex.ofReal_one, mul_one]
  · rintro hG
    obtain ⟨u, hu⟩ := hbad
    apply hu
    have h1 : (QuantumNLS.RephasingFlow.U c κ 1 ∘ Φ) (Cphys L u) = Φ (Cphys L u) := by rw [hG]
    have h2 : (QuantumNLS.RephasingFlow.U c κ 1 ∘ Φ) u = Φ u := by rw [hG]
    rw [h1, h2, hreal u]

end QuantumNLS.RC05Parts

#print axioms QuantumNLS.RC05Parts.clauses_of_statement
#print axioms QuantumNLS.RC05Parts.statement_of_clauses
#print axioms QuantumNLS.RC05Parts.global_clauses_of_family
#print axioms QuantumNLS.RC05Parts.printedChartLocal
#print axioms QuantumNLS.RC05Parts.physDyn_of
#print axioms QuantumNLS.RC05Parts.period_conversion
#print axioms QuantumNLS.RC05Parts.strong_of_diffeo
#print axioms QuantumNLS.RC05Parts.rephasing_freedom
