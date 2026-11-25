import NlsGge.Spectral.ActualTraceFormulaE02_38
import NlsGge.Hierarchy.RiccatiQ6Negative38
import NlsGge.Hierarchy.RiccatiSmoothPeriodicSobolevCarrierFromFourierDecayRecovery30Third
import Mathlib.Tactic

/-! Batch 38, A01 with the paper's SPECTRAL charges.

`C:prop:negative` (paper/v2.tex l.2427-2433) is stated with the charges
`Q_{2j}` normalized by the trace formula `A:eq:trace` (l.145):
`Q_{2j}(u) = (2/π)∫ (2λ)^{2j} v(λ;u) dλ`. Here `v = actualGapHeightE02_38`.
For every smooth period-one field `U` we take the physical `L²` field of `U`
(`smoothL2_38`), verify the hypotheses of the E02 trace theorem
`actualTraceFormula_E02_38` (H¹ summability, cover identification), and
deduce that the spectral remainder `V₃` equals the local-charge remainder
`remainderV38`. A01 for the spectral `V₃` then follows from
`realQ6Remainder_unbounded_below38`.

Fields used in A01's argument: `V₃` is only ever evaluated at real
trigonometric polynomials `ofReal ∘ P(k·)` (smooth, 1-periodic). The periodic
cusp and its trigonometric approximants enter only through the local quartic
functional `F`, never through `V₃`; the cusp is smooth anyway (`ε > 0`). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur NlsGge.SpectralFoundations MeasureTheory
open scoped ENNReal ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The physical `L²` field of a smooth period-one function. -/
def smoothL2_38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    PhysicalL2 :=
  ContinuousMap.toLp 2 spatialMeasure ℂ
    (riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper)

theorem smoothL2_38_sobolev (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) :
    SobolevSquareSummable 1 (physicalFourier (smoothL2_38 U hU hper)) := by
  obtain ⟨x, hx⟩ := riccatiSmoothPeriodic_hasSobolevCarrierWithExactFourierCoefficientsRecovery30
    1 U hU hper
  have hs := (weightedHilbert_hasSum (sobolevModeWeight ((1 : ℕ) : ℝ))
    (show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from x)).summable
  unfold SobolevSquareSummable
  refine hs.congr (fun n => ?_)
  have := hx n
  simp only [sobolevModeWeight, Nat.cast_one] at this ⊢
  rw [this]
  rfl

theorem liftIoc_eq_of_mem_Ioc02_38 (f : ℝ → ℂ) (hper : Function.Periodic f 1) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) 2) :
    AddCircle.liftIoc 1 0 f (s : PhysicalCircle) = f s := by
  by_cases h1 : s ≤ 1
  · exact AddCircle.liftIoc_coe_apply ⟨hs.1, by simpa using h1⟩
  · have hmem : s - 1 ∈ Set.Ioc (0 : ℝ) (0 + 1) := ⟨by linarith, by linarith [hs.2]⟩
    have hcoe : ((s : ℝ) : PhysicalCircle) = ((s - 1 : ℝ) : PhysicalCircle) := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    rw [hcoe, AddCircle.liftIoc_coe_apply hmem]
    have := hper (s - 1)
    simp only [sub_add_cancel] at this
    exact this.symm

theorem smoothL2_38_cover_ae (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) :
    (fun s : ℝ => (naturalPhysicalCoverL2 (smoothL2_38 U hU hper) : SpectralCircle → ℂ)
        (s : SpectralCircle)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 2)] U := by
  set F := riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper
  have h1 := naturalPhysicalCoverL2_ae (smoothL2_38 U hU hper)
  have h2 := naturalPhysicalCover_preserving.quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure F)
  have h : (naturalPhysicalCoverL2 (smoothL2_38 U hU hper) : SpectralCircle → ℂ)
      =ᵐ[spectralHaar] ((F : PhysicalCircle → ℂ) ∘ naturalPhysicalCover) := h1.trans h2
  have hv : (naturalPhysicalCoverL2 (smoothL2_38 U hU hper) : SpectralCircle → ℂ)
      =ᵐ[(volume : Measure SpectralCircle)] ((F : PhysicalCircle → ℂ) ∘ naturalPhysicalCover) := by
    rw [NlsGge.Schur.spectral_volume_eq_two_smul]
    exact Measure.ae_smul_measure h (2 : ℝ≥0∞)
  have hr := (AddCircle.measurePreserving_mk (2 : ℝ) 0).quasiMeasurePreserving.ae_eq_comp hv
  have h02 : (0 : ℝ) + 2 = 2 := by norm_num
  rw [h02] at hr
  filter_upwards [hr, ae_restrict_mem measurableSet_Ioc] with s hs hmem
  refine hs.trans ?_
  exact liftIoc_eq_of_mem_Ioc02_38 U hper hmem

/-- The paper's spectral charge `Q_{2j}(U) = (2/π)∫(2λ)^{2j} v(λ;U) dλ`. -/
def spectralCharge38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (j : ℕ) : ℝ :=
  (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 (smoothL2_38 U hU hper) t

/-- Local = spectral charge, from the E02 trace theorem (all `j`). -/
theorem localCharge_eq_spectralCharge38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) (j : ℕ) :
    (∫ x in (0:ℝ)..1, riccatiJetEvaluation U x (formalChargeIntegrand j)).re =
      spectralCharge38 U hU hper j :=
  (NlsGge.SpectralFoundations.actualTraceFormula_E02_38 (smoothL2_38 U hU hper)
    (smoothL2_38_sobolev U hU hper) U hU hper (smoothL2_38_cover_ae U hU hper) j).2

/-- The spectral finite-order remainder of `C:prop:negative`:
`V_M = Σ_{j≤M} β_j Q_{2j} - Σ_n W_M(2πn)|û(n)|²` with spectral `Q_{2j}`. -/
def spectralRemainderV38 (M : ℕ) (β : ℕ → ℝ) (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) : ℝ :=
  (∑ j ∈ Finset.range (M + 1), β j * spectralCharge38 U hU hper j) -
    ∑' n : ℤ, finiteHierarchyRate38 M β n * ‖smoothFourier38 U hU hper n‖ ^ 2

theorem spectralRemainderV38_eq_remainderV38 (M : ℕ) (β : ℕ → ℝ) (U : ℝ → ℂ)
    (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    spectralRemainderV38 M β U hU hper = remainderV38 M β U hU hper := by
  unfold spectralRemainderV38 remainderV38 localEnergy38
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [localCharge_eq_spectralCharge38]

/-- A01 (`C:prop:negative`) with the paper's spectral charges: for arbitrary
positive `β₀,…,β₃` the remainder `V₃` is unbounded below on the union of the
real trigonometric polynomial spaces. -/
theorem realQ6SpectralRemainder_unbounded_below38 (β : ℕ → ℝ) (hβ : ∀ j ≤ 3, 0 < β j)
    (C : ℝ) :
    ∃ (P : ℝ → ℝ) (hP : IsRealTrigPoly38 P),
      spectralRemainderV38 3 β (fun y => ((P y : ℝ) : ℂ))
        (Complex.ofRealCLM.contDiff.comp hP.contDiff)
        (fun y => by simp only [hP.periodic y]) < C := by
  obtain ⟨P, hP, hlt⟩ := realQ6Remainder_unbounded_below38 β hβ C
  exact ⟨P, hP, (spectralRemainderV38_eq_remainderV38 3 β _ _ _).trans_lt hlt⟩

end NlsGge.HierarchyRiccati.Core

end
