import Mathlib
import QuantumNLS.REF88PrintedChart
import QuantumNLS.AnalyticIdentity

/-!
# REF88PrintedChartLocal: the printed LOCAL normalization implies the global conjugation-reflection identity

Source: `source-text/chapters/global/physical_cubic.tex:28-36` ("Assume it has the local normalization of Theorem
`thm:reset-open-transform`"); Theorem `thm:reset-open-transform` (uniqueness "among canonical exact-modulus charts on a common
ball by its Fourier derivative and the conjugation-reflection identity").

Interface fix requested by the independent interim review (review record r67, defect 1): the frozen
`REF88PrintedChart.PrintedChart` carries the identity `Φ ∘ Cphys = star ∘ Φ` at EVERY field.  Here the printed local
hypothesis is recorded as `PrintedChartLocal` (the identity only on a neighbourhood of `0`), and
`printedChart_of_local` proves the global identity from the global real analyticity: both `Φ ∘ Cphys` and `star ∘ Φ` are
real analytic on the connected space `L²`, their difference vanishes near `0`, so it vanishes everywhere
(accepted `AnalyticIdentity.identity_of_vanishing_ball_direct`, Mathlib's identity theorem on a connected space).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open Filter Topology

namespace QuantumNLS.REF88PrintedChartLocal

open QuantumNLS.StrongSymplectic QuantumNLS.REF88Chart QuantumNLS.REF88PrintedChart
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RootIndexedMasses
open QuantumNLS.ResetNormalizationUniqueness (Cphys)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The printed hypotheses with the LOCAL conjugation-reflection normalization (on a neighbourhood of `0`). -/
structure PrintedChartLocal (hκ : 0 < κ) (Φ : L2T L → K) : Prop where
  symp : IsStronglySymplectic Φ
  analytic : ∀ u, AnalyticAt ℝ Φ u
  moduli : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (masses hκ u).1 n
  fourier : ∀ v, fderiv ℝ Φ 0 v = QuantumNLS.Fourier.fourierL2 L v
  conj_local : ∀ᶠ u in 𝓝 (0 : L2T L), Φ (Cphys L u) = star (Φ u)

/-- Conjugation of `ℓ²` as a continuous real-linear map. -/
def starCLM : K →L[ℝ] K where
  toFun := star
  map_add' := star_add
  map_smul' := fun c z => by simp [star_smul]
  cont := continuous_star

theorem printedChart_of_local (hκ : 0 < κ) {Φ : L2T L → K} (hΦ : PrintedChartLocal hκ Φ) :
    PrintedChart hκ Φ := by
  have hA : ∀ x : L2T L, AnalyticAt ℝ (fun u : L2T L => Φ (Cphys L u) - starCLM (Φ u)) x := by
    intro x
    have h1 : AnalyticAt ℝ (fun u : L2T L => Φ (Cphys L u)) x :=
      (hΦ.analytic (Cphys L x)).comp ((Cphys L).toContinuousLinearMap.analyticAt x)
    have h2 : AnalyticAt ℝ (fun u : L2T L => starCLM (Φ u)) x :=
      starCLM.analyticAt (Φ x) |>.comp (hΦ.analytic x)
    exact h1.sub h2
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hΦ.conj_local
  have hzero := AnalyticIdentity.identity_of_vanishing_ball_direct
    (fun u : L2T L => Φ (Cphys L u) - starCLM (Φ u)) hA hρ (fun y hy => by
      have := hball y hy
      simp only [starCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      rw [this, sub_self])
  exact ⟨hΦ.symp, hΦ.analytic, hΦ.moduli, hΦ.fourier, fun u => by
    have := hzero u
    simpa [starCLM, sub_eq_zero] using this⟩

theorem printedChart_to_local (hκ : 0 < κ) {Φ : L2T L → K} (hΦ : PrintedChart hκ Φ) :
    PrintedChartLocal hκ Φ :=
  ⟨hΦ.symp, hΦ.analytic, hΦ.moduli, hΦ.fourier, Eventually.of_forall hΦ.conj⟩

end QuantumNLS.REF88PrintedChartLocal

#print axioms QuantumNLS.REF88PrintedChartLocal.printedChart_of_local
