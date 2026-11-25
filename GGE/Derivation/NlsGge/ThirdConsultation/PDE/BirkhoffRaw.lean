import Mathlib
import NlsGge.Birkhoff.BirkhoffInput38
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G6.BirkhoffBasic

/- BKRAW support (proof development, AUTHOR; not reviewed).  Target NlsGge/ThirdConsultation/PDE/BirkhoffRaw.lean.
   Round 14 BIRKHOFF_REALIZATION: the two literal raw sequence maps (verbatim), the two COMMON alias bodies they need
   (verbatim from COMMON.lean.md "Shared remaining-family interfaces"; NOT landed anywhere else -- the COMMON host must import this
   module or move these two names, never redeclare them), and the support theorems provable from LANDED results only:
   actualTinv38_mapsTo_zero (level 0 only), actualT38_action (X-006 Phi_action),
   and two coordinate-compatibility lemmas.  Everything needing G6-013/014/027 (bijectivity, inverse levels m>=1, analyticity)
   is NOT here. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.Common
noncomputable section

/-- The single physical Birkhoff map already selected and frozen in G6. -/
def actualPhi : NlsGge.Pilot.PhysicalL2 → NlsGge.GK38.Lib.L2Z :=
  NlsGge.GKDefinitionDesign.physicalBirkhoff

/-- Its literal inverse, earned by G6-013/G6-014. -/
def actualPhiInv : NlsGge.GK38.Lib.L2Z → NlsGge.Pilot.PhysicalL2 :=
  NlsGge.GKDefinitionDesign.physicalInverseBirkhoff

end
end NlsGge.ThirdConsultation.Common

section BirkhoffRaw
set_option autoImplicit false
open Set
open scoped ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

open scoped Classical in
def actualT38 (x : ℤ → ℂ) : ℤ → ℂ :=
  if hx : x ∈ seqSobolev38 0 then
    (actualPhi (physInv38 x hx) : ℤ → ℂ)
  else 0

open scoped Classical in
def actualTinv38 (z : ℤ → ℂ) : ℤ → ℂ :=
  if hz : z ∈ seqSobolev38 0 then
    fourierSeq38 (actualPhiInv (seqToLp38 z hz))
  else 0

/-- Forward map on the Fourier image: `actualT38 (F u) = Phi u` coordinatewise (support lemma). -/
theorem actualT38_fourierSeq38 (u : PhysicalL2) :
    actualT38 (fourierSeq38 u) = (actualPhi u : ℤ → ℂ) := by
  unfold actualT38
  rw [dif_pos (fourierSeq38_mem_zero u), physInv38_fourierSeq38]

/-- Clean inverse on its actual domain `h0` (support lemma, by `dif_pos`). -/
theorem actualTinv38_of_mem (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) :
    actualTinv38 z = fourierSeq38 (actualPhiInv (seqToLp38 z hz)) := by
  unfold actualTinv38
  rw [dif_pos hz]

/-- The level-zero case of the inverse mapping property (levels `m ≥ 1` need G6-027). -/
theorem actualTinv38_mapsTo_zero :
    ∀ z ∈ seqSobolev38 ((0 : ℕ) : ℝ), actualTinv38 z ∈ seqSobolev38 ((0 : ℕ) : ℝ) := by
  intro z hz
  have hz0 : z ∈ seqSobolev38 0 := (mem_seqSobolev38_natCast_zero_iff z).1 hz
  rw [actualTinv38_of_mem z hz0, mem_seqSobolev38_natCast_zero_iff]
  exact fourierSeq38_mem_zero _

theorem actualT38_action (u : PhysicalL2) (n : ℤ) :
    ‖actualT38 (fourierSeq38 u) n‖ ^ 2 = actualGapActionAllE02_38 u n := by
  rw [actualT38_fourierSeq38]
  exact sourceFamily.Phi_action u n

end
end NlsGge.ThirdConsultation.PDE
end BirkhoffRaw
