import Mathlib
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4032
import NlsGge.GK38.Defs
import NlsGge.GK38.TauGamma
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.DirichletRealGapIndex
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import Armstrong.Work.ActualCartesianRealTraceAction

/- G4-040 PRODUCTION01 (proof development, AUTHOR; not semantically reviewed by its author; not accepted).
   Target NlsGge/Atomic/G4/G4040.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G4040` VERBATIM from design STATEMENTS/G4.md (G4-040 section; byte-identical in followup1..10; no Pro round 4-12 entry
   touches G4-040). Lexical: the opens `NlsGge.SpectralFoundations` (for actualGapLower/UpperAllE02_38) is added; the head text is unchanged.
   Route (G4040_ROUTE.md): (1,2) Armstrong.Work.ActualCartesianRealTraceAction.gk16_same_family_xy_real_trace_action38 applied to the
   fields of the single selected family `sourceFamily` (the same call as landed ThirdConsultation/G4/RealTrace.lean; X-006 closure line 33).
   (3) collapsed real gap: lamPlus/lamMinus of realSlice u are the real gap endpoints (lamPlus_real); equal endpoints give gamma2 = 0 and,
   since gkMu lies in the closed gap, muSeq = tauN; then landed G4-032 gives cartesianZExtended n a (realSlice u) = 0 for a = +-1. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G4040Aux

theorem real_slice_mem (u : PhysicalL2) : realSlice u ∈ sourceBetaW :=
  sourceFamily.V_real (mem_range_self u)

theorem collapse_data (u : PhysicalL2) (n : ℤ)
    (h : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n) :
    gamma2 (realSlice u) n = 0 ∧ muSeq (realSlice u) n = tauN (realSlice u) n := by
  have hgk : realSlice u ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W (real_slice_mem u))
  obtain ⟨hp, hm⟩ := lamPlus_real u n
  have hg := gamma2_value38 (realSlice u) hgk n
  have ht := tauN_value38 (realSlice u) hgk n
  have hmu := muSeq_eq_gkMu38 u n
  have hmem := gkMu_mem_gap38 u n
  have hpm : lamPlus (realSlice u) n = lamMinus (realSlice u) n := by
    rw [hp, hm, h]
  have hmuL : gkMu u n = actualGapLowerAllE02_38 u n :=
    le_antisymm (by rw [h]; exact hmem.2) hmem.1
  refine ⟨?_, ?_⟩
  · rw [hg, hpm, sub_self]; ring
  · rw [hmu, ht, hpm, hmuL, hm]
    ring

end G4040Aux

theorem G4040 (u : PhysicalL2) (n : ℤ) :
  (cartesianX n (realSlice u)).im = 0 ∧
  (cartesianY n (realSlice u)).im = 0 ∧
  (actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n →
    cartesianZExtended n 1 (realSlice u) = 0 ∧
    cartesianZExtended n (-1) (realSlice u) = 0) := by
  obtain ⟨hXim, hYim, _⟩ :=
    NlsGge.GK38.gk16_same_family_xy_real_trace_action38 sourceFamily.W sourceFamily.W_open
      sourceFamily.W_real sourceFamily.W_gk sourceFamily.F sourceFamily.F_analytic
      sourceFamily.F_zero sourceFamily.F_period sourceFamily.F_real sourceFamily.V
      sourceFamily.V_real sourceFamily.beta sourceFamily.beta_spec n u
  refine ⟨hXim, hYim, fun h => ?_⟩
  obtain ⟨hg, hmu⟩ := G4040Aux.collapse_data u n h
  exact ⟨(G4032 n 1 (Or.inl rfl) (realSlice u) (G4040Aux.real_slice_mem u) hg hmu).1,
    (G4032 n (-1) (Or.inr rfl) (realSlice u) (G4040Aux.real_slice_mem u) hg hmu).1⟩

end
end NlsGge.GKDefinitionDesign
