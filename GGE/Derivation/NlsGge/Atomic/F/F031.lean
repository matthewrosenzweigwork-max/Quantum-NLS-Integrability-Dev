/- F031 PRODUCTION01 (proof development, AUTHOR; uncompiled draft).
   Target NlsGge/Atomic/F/F031.lean, namespace NlsGge.ThirdConsultation.F.
   Head: followup13 STATEMENTS/F.md §F-031, lines 684-702; retained unchanged
   by the round-17 BINDING_INDEX_FP80_17 ruling.
   Route: v2 C:eq:domination followed by pointwise convergence and Vitali.
   Imports list every direct landed provider used by this proof. -/
import Mathlib
import NlsGge.Atomic.F.F003
import NlsGge.Atomic.F.F025Host
import NlsGge.Atomic.F.F027
import NlsGge.Atomic.F.F028
import NlsGge.Atomic.F.F029
import NlsGge.Atomic.F.F030
import NlsGge.Birkhoff.F05Identity38f
import NlsGge.Birkhoff.F08Bare38f
import NlsGge.Hierarchy.RiccatiSmoothDenseSobolev38

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
open NlsGge.GKDefinitionDesign

/-- **F-031** (head verbatim): bare finite-order densities converge in L¹
on their common physical Gaussian space. -/
theorem f031 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    (∀ u : Hm1 m, Tendsto (fun N => truncSobolev38 _ N u) atTop (nhds u)) ∧
    (∀ u : Hm1 m, Tendsto (fun N => weightFN38 m β N u)
      atTop (nhds (weightFInf38 m β u))) ∧
    (∀ N : ℕ, Integrable (weightFN38 m β N) (gammaFM38 m β)) ∧
    Integrable (weightFInf38 m β) (gammaFM38 m β) ∧
    UniformIntegrable (weightFN38 m β) 1 (gammaFM38 m β) ∧
    Tendsto (fun N => eLpNorm (weightFN38 m β N - weightFInf38 m β)
      1 (gammaFM38 m β)) atTop (nhds 0) := by
  haveI : IsProbabilityMeasure (gammaFM38 m β) :=
    NlsGge.Birkhoff.isProbabilityMeasure_gammaFM38 hm hβ
  have htrunc : ∀ u : Hm1 m,
      Tendsto (fun N => truncSobolev38 _ N u) atTop (nhds u) := by
    intro u
    exact NlsGge.HierarchyRiccati.Core.tendsto_truncSobolev38 _ u
  have hVmContinuous : Continuous (Vm38 m β) := (f003 m hm β hβ).1
  have hweightPointwise : ∀ u : Hm1 m,
      Tendsto (fun N => weightFN38 m β N u) atTop (nhds (weightFInf38 m β u)) := by
    intro u
    have hVm : Tendsto (fun N => Vm38 m β (truncSobolev38 _ N u)) atTop
        (nhds (Vm38 m β u)) :=
      (hVmContinuous.tendsto u).comp (htrunc u)
    have hExp : Tendsto (fun N => Real.exp (-(Vm38 m β (truncSobolev38 _ N u))))
        atTop (nhds (Real.exp (-(Vm38 m β u)))) :=
      (Real.continuous_exp.tendsto (-(Vm38 m β u))).comp hVm.neg
    simpa [weightFN38, weightFInf38] using hExp
  have hweightInt : ∀ N : ℕ,
      Integrable (weightFN38 m β N) (gammaFM38 m β) := by
    intro N
    exact (f030 m hm β hβ N).2.2.2.1
  let δ : ℝ := β (m - 1) / 2
  have hβlast : 0 < β (m - 1) := hβ (m - 1) (Nat.sub_le m 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hδβ : δ < β (m - 1) := by
    dsimp [δ]
    linarith
  obtain ⟨B, hB, _, hBound⟩ := f028 m hm β hβ
  have hTilt := hBound δ hδ hδβ
  have hTerminalInt : Integrable (tiltedTerminal m β δ) (gammaFM38 m β) := hTilt.1
  have hTerminalNonneg : ∀ᵐ u ∂(gammaFM38 m β),
      0 ≤ tiltedTerminal m β δ u :=
    Filter.Eventually.of_forall fun u => (Real.exp_pos _).le
  obtain ⟨N₀, hCut⟩ := exists_nat_gt (B / δ)
  have hCutNonneg : 0 ≤ B / δ := div_nonneg hB hδ.le
  have hN₀posReal : 0 < (N₀ : ℝ) := lt_of_le_of_lt hCutNonneg hCut
  have hN₀pos : 0 < N₀ := by exact_mod_cast hN₀posReal
  have hN₀one : 1 ≤ N₀ := by omega
  have hBoundTail : ∀ N : ℕ, N₀ ≤ N → B / (N : ℝ) ≤ δ := by
    intro N hN
    have hNreal : B / δ < (N : ℝ) := hCut.trans_le (Nat.cast_le.mpr hN)
    have hNrealPos : 0 < (N : ℝ) := lt_of_le_of_lt hCutNonneg hNreal
    rw [div_le_iff₀ hNrealPos]
    apply le_of_lt
    calc
      B = (B / δ) * δ := by field_simp [hδ.ne']
      _ < (N : ℝ) * δ := mul_lt_mul_of_pos_right hNreal hδ
      _ = δ * (N : ℝ) := mul_comm _ _
  have hDomTail : ∀ N : ℕ, N₀ ≤ N →
      ∀ᵐ u ∂(gammaFM38 m β),
        ‖weightFN38 m β N u‖ ≤
          Real.exp δ * (gammaFM38 m β)[tiltedTerminal m β δ | lowModeSigma m N] u := by
    intro N hN
    have hDom := hTilt.2 N (hN₀one.trans hN) (hBoundTail N hN)
    filter_upwards [hDom] with u hu
    change ‖Real.exp (-(Vm38 m β (truncSobolev38 _ N u)))‖ ≤
      Real.exp δ * (gammaFM38 m β)[tiltedTerminal m β δ | lowModeSigma m N] u
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hu
  have hUI : UniformIntegrable (weightFN38 m β) 1 (gammaFM38 m β) :=
    NlsGge.Atomic.F029.f029_clause3
      (gammaFM38 m β) (fun N => lowModeSigma m N) (fun N => lowModeSigma_le m N)
      (tiltedTerminal m β δ) hTerminalInt hTerminalNonneg
      (weightFN38 m β) (Real.exp δ) N₀ (Real.exp_pos δ).le hweightInt hDomTail
  have hLimitInt : Integrable (weightFInf38 m β) (gammaFM38 m β) :=
    hUI.integrable_of_ae_tendsto (Filter.Eventually.of_forall hweightPointwise)
  have hL1 : Tendsto
      (fun N => eLpNorm (weightFN38 m β N - weightFInf38 m β) 1 (gammaFM38 m β))
      atTop (nhds 0) :=
    MeasureTheory.tendsto_Lp_finite_of_tendsto_ae
      (p := 1) le_rfl ENNReal.one_ne_top
      (fun N => (hweightInt N).aestronglyMeasurable)
      (memLp_one_iff_integrable.mpr hLimitInt) hUI.1
      (Filter.Eventually.of_forall hweightPointwise)
  exact ⟨htrunc, hweightPointwise, hweightInt, hLimitInt, hUI, hL1⟩

end NlsGge.ThirdConsultation.F

end
