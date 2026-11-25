import Mathlib
import NlsGge.Atomic.F.F021
import NlsGge.Atomic.F.F024
import NlsGge.Atomic.F.F025
import NlsGge.Atomic.F.F025Host
import NlsGge.Atomic.F.F026
import NlsGge.Atomic.F.F027
import NlsGge.Atomic.LIB.LIB060
import NlsGge.Atomic.LIB.LIB061
import NlsGge.Birkhoff.F05Identity38f
import NlsGge.Birkhoff.F08Bare38f

/- F028 PRODUCTION04 (codex_luna09, AUTHOR; not independently reviewed).
   Numbered repair after root main-probe request 1beb36d5-1536-4fb8-82c3-4be593a29a30.
   Target NlsGge/Atomic/F/F028.lean, namespace NlsGge.ThirdConsultation.F.
   Head source: followup13 STATEMENTS/F.md §F-028, retained unchanged by round 17.
   `tiltedTerminal` is provided by F025Host; `weightFN38` is provided by F08Bare38f.
   The proof follows v2 C:eq:domination on the concrete physical Gaussian carrier:
   f021 supplies the common correction constant, f025 supplies terminal integrability,
   f026 supplies the actual conditional expectation identity, f027 supplies conditional
   mass monotonicity, and LIB061 supplies conditional Jensen. LIB060 is imported as a
   listed TASK_INDEX prerequisite; its UI conclusion is not part of this head.
   Repairs from PRODUCTION02: retain the F-025 integrability term at its declared form;
   write the exponent as a function sum to match condExp_add; use the pointwise hM/hJ
   hypotheses after filter_upwards; normalize Pi neg/smul application by change.
   Repair from PRODUCTION03: close the Pi.neg_apply equality after rewriting hneg_u and hsmul_u. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
open NlsGge.GKDefinitionDesign

/-- The uniform correction bound also supplies the cutoff constant used below. -/
theorem f028 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ N : ℕ, 1 ≤ N → ∀ z : FourierPlane N,
        |contractionCorrection38 m β N z| ≤
          B / (N : ℝ) * (1 + (‖planeL2 N z‖ ^ 2) ^ m)) ∧
      ∀ δ : ℝ, 0 < δ → δ < β (m - 1) →
        Integrable (tiltedTerminal m β δ) (gammaFM38 m β) ∧
        ∀ N : ℕ, 1 ≤ N → B / (N : ℝ) ≤ δ →
          weightFN38 m β N ≤ᵐ[gammaFM38 m β]
            (fun u => Real.exp δ *
              (gammaFM38 m β)[tiltedTerminal m β δ | lowModeSigma m N] u) := by
  obtain ⟨_, B, _, hB, hraw⟩ := f021 m hm β hβ
  have hcorrection : ∀ N : ℕ, 1 ≤ N → ∀ z : FourierPlane N,
      |contractionCorrection38 m β N z| ≤
        B / (N : ℝ) * (1 + (‖planeL2 N z‖ ^ 2) ^ m) := by
    intro N hN z
    obtain ⟨_, hA, hB'⟩ := hraw N hN z
    exact hA.trans hB'
  refine ⟨B, hB, hcorrection, ?_⟩
  intro δ hδ hδβ
  have h025 := f025 m hm β hβ δ hδ hδβ
  refine ⟨h025.2.1, ?_⟩
  intro N hN hBN
  haveI : IsProbabilityMeasure (gammaFM38 m β) :=
    NlsGge.Birkhoff.isProbabilityMeasure_gammaFM38 hm hβ
  let Mpow : Hm1 m → ℝ := fun u => (chargeSobolev38 m 0 u) ^ m
  let X : Hm1 m → ℝ := -Vm38 m β + fun u => δ * Mpow u
  have h26 := f026 m hm β hβ
  have h27 := f027 m hm β hβ
  have hσ : lowModeSigma m N ≤ (inferInstance : MeasurableSpace (Hm1 m)) :=
    (h26.2 N).1
  have hVint : Integrable (Vm38 m β) (gammaFM38 m β) := h26.1
  have hVcond : (gammaFM38 m β)[Vm38 m β | lowModeSigma m N] =ᵐ[gammaFM38 m β]
      (fun u => Vm38 m β (truncSobolev38 _ N u) +
        contractionCorrection38 m β N (NlsGge.Ramer.windowProj N (sobolevCoe _ u))) :=
    (h26.2 N).2
  have hMpowInt : Integrable Mpow (gammaFM38 m β) := by
    simpa [Mpow] using (h27.1 m)
  have hMmono : (fun u : Hm1 m =>
      (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m) ≤ᵐ[gammaFM38 m β]
      (gammaFM38 m β)[Mpow | lowModeSigma m N] := by
    simpa [Mpow] using ((h27.2 N).2)
  have hXint : Integrable X (gammaFM38 m β) := by
    change Integrable (-Vm38 m β + fun u => δ * Mpow u) (gammaFM38 m β)
    exact hVint.neg.add (hMpowInt.const_mul δ)
  have hTerminalInt : Integrable (fun u : Hm1 m => Real.exp (X u))
      (gammaFM38 m β) := by
    change Integrable (tiltedTerminal m β δ) (gammaFM38 m β)
    exact h025.2.1
  have hExpFun : (fun u : Hm1 m => Real.exp (X u)) = tiltedTerminal m β δ := by
    funext u
    rfl
  have hJensen : (fun u : Hm1 m =>
      Real.exp ((gammaFM38 m β)[X | lowModeSigma m N] u)) ≤ᵐ[gammaFM38 m β]
      (gammaFM38 m β)[tiltedTerminal m β δ | lowModeSigma m N] := by
    simpa only [hExpFun] using
      (NlsGge.Atomic.LIB061.exp_condExp_le hXint hTerminalInt hσ)
  have hadd : (gammaFM38 m β)[(-Vm38 m β + fun u => δ * Mpow u) | lowModeSigma m N] =ᵐ[gammaFM38 m β]
      (gammaFM38 m β)[(fun u : Hm1 m => -Vm38 m β u) | lowModeSigma m N] +
      (gammaFM38 m β)[(fun u : Hm1 m => δ * Mpow u) | lowModeSigma m N] :=
    condExp_add hVint.neg (hMpowInt.const_mul δ) (lowModeSigma m N)
  have hneg : (gammaFM38 m β)[(fun u : Hm1 m => -Vm38 m β u) | lowModeSigma m N] =ᵐ[gammaFM38 m β]
      -(gammaFM38 m β)[Vm38 m β | lowModeSigma m N] :=
    condExp_neg (Vm38 m β) (lowModeSigma m N)
  have hsmul : (gammaFM38 m β)[(fun u : Hm1 m => δ * Mpow u) | lowModeSigma m N] =ᵐ[gammaFM38 m β]
      δ • (gammaFM38 m β)[Mpow | lowModeSigma m N] :=
    condExp_smul δ Mpow (lowModeSigma m N)
  have hlin : (gammaFM38 m β)[X | lowModeSigma m N] =ᵐ[gammaFM38 m β]
      (fun u => -((gammaFM38 m β)[Vm38 m β | lowModeSigma m N] u) +
        δ * ((gammaFM38 m β)[Mpow | lowModeSigma m N] u)) := by
    change (gammaFM38 m β)[(-Vm38 m β + fun u => δ * Mpow u) | lowModeSigma m N] =ᵐ[gammaFM38 m β] _
    filter_upwards [hadd, hneg, hsmul] with u hadd_u hneg_u hsmul_u
    calc
      (gammaFM38 m β)[(-Vm38 m β + fun u => δ * Mpow u) | lowModeSigma m N] u =
          ((gammaFM38 m β)[(fun u : Hm1 m => -Vm38 m β u) | lowModeSigma m N] +
            (gammaFM38 m β)[(fun u : Hm1 m => δ * Mpow u) | lowModeSigma m N]) u := hadd_u
      _ = (gammaFM38 m β)[(fun u : Hm1 m => -Vm38 m β u) | lowModeSigma m N] u +
          (gammaFM38 m β)[(fun u : Hm1 m => δ * Mpow u) | lowModeSigma m N] u := rfl
      _ = -((gammaFM38 m β)[Vm38 m β | lowModeSigma m N] u) +
          (δ • (gammaFM38 m β)[Mpow | lowModeSigma m N]) u := by
        rw [hneg_u, hsmul_u]
        rfl
      _ = -((gammaFM38 m β)[Vm38 m β | lowModeSigma m N] u) +
          δ * ((gammaFM38 m β)[Mpow | lowModeSigma m N] u) := by
        change -((gammaFM38 m β)[Vm38 m β | lowModeSigma m N] u) +
          δ * ((gammaFM38 m β)[Mpow | lowModeSigma m N] u) =
          -((gammaFM38 m β)[Vm38 m β | lowModeSigma m N] u) +
          δ * ((gammaFM38 m β)[Mpow | lowModeSigma m N] u)
        rfl
  filter_upwards [hVcond, hMmono, hJensen, hlin] with u hV hM hJ hL
  let z : FourierPlane N := NlsGge.Ramer.windowProj N (sobolevCoe _ u)
  have hPlaneMass : ‖planeL2 N z‖ ^ 2 =
      chargeSobolev38 m 0 (truncSobolev38 _ N u) := by
    rw [planeL2_norm_sq]
    simpa [z] using (charge_trunc_eq_window m N u).symm
  have hCorrection : contractionCorrection38 m β N z ≤
      δ * (1 + (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m) := by
    calc
      contractionCorrection38 m β N z ≤ |contractionCorrection38 m β N z| := le_abs_self _
      _ ≤ B / (N : ℝ) * (1 + (‖planeL2 N z‖ ^ 2) ^ m) := hcorrection N hN z
      _ ≤ δ * (1 + (‖planeL2 N z‖ ^ 2) ^ m) :=
        mul_le_mul_of_nonneg_right hBN (by positivity)
      _ = δ * (1 + (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m) := by
        rw [hPlaneMass]
  have hMassDelta : δ * (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m ≤
      δ * ((gammaFM38 m β)[Mpow | lowModeSigma m N] u) :=
    mul_le_mul_of_nonneg_left hM hδ.le
  have hKey : -(Vm38 m β (truncSobolev38 _ N u)) ≤
      (gammaFM38 m β)[X | lowModeSigma m N] u + δ := by
    rw [hL, hV]
    nlinarith [hCorrection, hMassDelta]
  calc
    weightFN38 m β N u = Real.exp (-(Vm38 m β (truncSobolev38 _ N u))) := rfl
    _ ≤ Real.exp ((gammaFM38 m β)[X | lowModeSigma m N] u + δ) :=
      Real.exp_le_exp.mpr hKey
    _ = Real.exp δ * Real.exp ((gammaFM38 m β)[X | lowModeSigma m N] u) := by
      rw [Real.exp_add, mul_comm]
    _ ≤ Real.exp δ * (gammaFM38 m β)[tiltedTerminal m β δ | lowModeSigma m N] u :=
      mul_le_mul_of_nonneg_left hJ (Real.exp_pos δ).le

end NlsGge.ThirdConsultation.F

end
