import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRaw
import NlsGge.Atomic.G6.G6023

/- BKRAWB support (proof development, AUTHOR; not reviewed).  Target NlsGge/ThirdConsultation/PDE/BirkhoffRawG6.lean.
   Head VERBATIM from BIRKHOFF_REALIZATION.lean.md ("Literal raw sequence maps"): actualT38_mapsTo.  Route as Pro: G6-023 (landed G6023) applied to
   the Fourier preimage physInv38 x hx0, then unfold the raw map.  Split from BKRAW (A) only because the G6023 import closure is too large
   for the worker lane (memory abort, req 4f6ef4e1). -/
set_option autoImplicit false
open Set
open scoped ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem actualT38_mapsTo (m : ℕ) :
    ∀ x ∈ seqSobolev38 (m : ℝ), actualT38 x ∈ seqSobolev38 (m : ℝ) := by
  intro x hx
  have hx0 : x ∈ seqSobolev38 0 := seqSobolev38_natCast_mono hx
  have hxu : fourierSeq38 (physInv38 x hx0) = x := fourierSeq38_physInv38 x hx0
  have hF : fourierSeq38 (physInv38 x hx0) ∈ seqSobolev38 (m : ℝ) := by
    rw [hxu]; exact hx
  have hP := (G6023 (physInv38 x hx0) m).1 hF
  unfold actualT38
  rw [dif_pos hx0]
  exact hP

end
end NlsGge.ThirdConsultation.PDE
