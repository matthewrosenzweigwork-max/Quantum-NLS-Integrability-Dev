import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRaw

                                                                                                                         
                                                                                                             
                                                                                                               
                                                                                                               
                                                                                                                    
                                               
set_option autoImplicit false
open Set
open scoped ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

namespace BirkhoffRawInvCore

/-- Coefficient form of the actual inverse on its domain h0 (conditional on the G6-013 right-inverse equation)
    and the reverse G6-023 implication: actualTinv38 maps h^m into h^m. -/
theorem tinv_mapsTo_of
    (hR : ∀ w : NlsGge.GK38.Lib.L2Z, actualPhi (actualPhiInv w) = w)
    (hG : ∀ (u : PhysicalL2) (m : ℕ),
      (actualPhi u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ) → fourierSeq38 u ∈ seqSobolev38 (m : ℝ))
    (m : ℕ) : ∀ z ∈ seqSobolev38 (m : ℝ), actualTinv38 z ∈ seqSobolev38 (m : ℝ) := by
  intro z hz
  have hz0 : z ∈ seqSobolev38 0 := seqSobolev38_natCast_mono hz
  rw [actualTinv38_of_mem z hz0]
  apply hG
  rw [hR]
  exact hz

/-- Left inverse on h0, from the G6-013 left-inverse equation and Fourier inversion. -/
theorem left_inv_of
    (hL : ∀ u : PhysicalL2, actualPhiInv (actualPhi u) = u) :
    ∀ x ∈ seqSobolev38 0, actualTinv38 (actualT38 x) = x := by
  intro x hx
  have hT : actualT38 x = (actualPhi (physInv38 x hx) : ℤ → ℂ) := by
    unfold actualT38
    rw [dif_pos hx]
  have hmem : (actualPhi (physInv38 x hx) : ℤ → ℂ) ∈ seqSobolev38 0 :=
    (mem_seqSobolev38_zero_iff _).2 (lp.memℓp _)
  rw [hT, actualTinv38_of_mem _ hmem]
  have hseq : seqToLp38 _ hmem = actualPhi (physInv38 x hx) := rfl
  rw [hseq, hL]
  exact fourierSeq38_physInv38 x hx

/-- Right inverse on h0, from the G6-013 right-inverse equation. -/
theorem right_inv_of
    (hR : ∀ w : NlsGge.GK38.Lib.L2Z, actualPhi (actualPhiInv w) = w) :
    ∀ z ∈ seqSobolev38 0, actualT38 (actualTinv38 z) = z := by
  intro z hz
  rw [actualTinv38_of_mem z hz, actualT38_fourierSeq38, hR]
  rfl

end BirkhoffRawInvCore

end
end NlsGge.ThirdConsultation.PDE
