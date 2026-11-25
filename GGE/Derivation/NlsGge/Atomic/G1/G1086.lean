import Mathlib
import NlsGge.Atomic.G1.G1062
import NlsGge.Atomic.KST.KST065
import NlsGge.Atomic.KST.KST066
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Birkhoff.BirkhoffInput38
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev38.SobolevCarrier38
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.ThirdConsultation.KST.KST066Host
import NlsGge.ThirdConsultation.KST.KST066Support
import NlsGge.ThirdConsultation.Sobolev.Round5

/- G1-086 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/G1/G1086.lean,
   namespace NlsGge.GKDefinitionDesign.  Head VERBATIM from design STATEMENTS/G1.md "## G1-086"
   (gpt6pro_followup10; no Pro round 4-12 entry touches G1-086).  No repair of the head.
   Route (packet skeleton, transfer of KST): (1) regularity at every integer exponent from the third conjunct of the landed `kst065`
   (u = physicalSobolevEmbed m v, so the reflected Fourier sequence lies in h^m); (2) density from the landed `kst066` at s = r applied to the
   preimage v0 of u under physicalSobolevEmbedRealExponent (`KST066S.exists_recover`), and the isometry identity
   physicalSobolevNorm r (embed a - embed b) = ‖a - b‖ (carrier_hasSum_norm_sq38). -/
set_option autoImplicit false

open Filter Topology
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G1086S

theorem physicalSobolev_iff (r : ℝ) (u : PhysicalL2) :
    physicalSobolev r u ↔ fourierSeq38 u ∈ seqSobolev38 r :=
  (mem_seqSobolev38_iff r _).symm

theorem fourierSeq_embed_sub (s : ℝ) (hs : 0 ≤ s) (a b : PhysicalSobolev38 s) :
    fourierSeq38 (physicalSobolevEmbedRealExponent s hs a - physicalSobolevEmbedRealExponent s hs b) =
      carrierCoe38 s (physicalSobolevFourierEquiv38 s (a - b)) := by
  funext n
  rw [fourierSeq38_sub, Pi.sub_apply, NlsGge.ThirdConsultation.KST.KST066S.embed_fourierSeq,
    NlsGge.ThirdConsultation.KST.KST066S.embed_fourierSeq, map_sub]
  rfl

theorem physicalSobolevNorm_embed_sub (s : ℝ) (hs : 0 ≤ s) (a b : PhysicalSobolev38 s) :
    physicalSobolevNorm s (physicalSobolevEmbedRealExponent s hs a -
      physicalSobolevEmbedRealExponent s hs b) = ‖a - b‖ := by
  have hcoe := fourierSeq_embed_sub s hs a b
  have hnorm : ‖a - b‖ = ‖physicalSobolevFourierEquiv38 s (a - b)‖ :=
    ((physicalSobolevFourierEquiv38 s).norm_map _).symm
  have hsum := carrier_hasSum_norm_sq38 s (physicalSobolevFourierEquiv38 s (a - b))
  unfold physicalSobolevNorm
  have hfun : (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * s) *
      ‖reflectedFourierL2 (physicalSobolevEmbedRealExponent s hs a -
        physicalSobolevEmbedRealExponent s hs b) n‖ ^ 2) =
      fun n : ℤ => sobolevModeWeight s n *
        ‖carrierCoe38 s (physicalSobolevFourierEquiv38 s (a - b)) n‖ ^ 2 := by
    funext n
    rw [← hcoe]
    rfl
  rw [hfun, hsum.tsum_eq, Real.sqrt_sq (norm_nonneg _), hnorm]

end G1086S

theorem G1_086 :
    (∀ u : PhysicalL2, NlsGge.ThirdConsultation.finiteGap u →
      ∀ m : ℕ, physicalSobolev (m : ℝ) u) ∧
    (∀ r : ℝ, 0 ≤ r → ∀ u : PhysicalL2,
      physicalSobolev r u → ∀ ε : ℝ, 0 < ε →
      ∃ v : PhysicalL2,
        NlsGge.ThirdConsultation.finiteGap v ∧ physicalSobolev r v ∧
        physicalSobolevNorm r (v-u) < ε) := by
  refine ⟨fun u hu m => ?_, fun r hr u hu ε hε => ?_⟩
  · obtain ⟨-, -, h⟩ := NlsGge.ThirdConsultation.KST.kst065 u hu
    obtain ⟨v, hv⟩ := h m
    rw [G1086S.physicalSobolev_iff, ← hv]
    have hf : fourierSeq38 (physicalSobolevEmbed m v) =
        carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) v) :=
      funext (physicalSobolevEmbed_fourier m v)
    rw [hf]
    exact carrierCoe38_mem _ _
  · obtain ⟨v0, hv0, -⟩ := NlsGge.ThirdConsultation.KST.KST066S.exists_recover r hr u
      ((G1086S.physicalSobolev_iff r u).1 hu)
    obtain ⟨v, hlim, hv⟩ := NlsGge.ThirdConsultation.KST.kst066 r hr v0
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
    have hN' := hN N le_rfl
    have hvN := hv N
    refine ⟨physicalSobolevEmbedRealExponent r hr (v N), hvN.1, ?_, ?_⟩
    · rw [G1086S.physicalSobolev_iff]
      have hf : fourierSeq38 (physicalSobolevEmbedRealExponent r hr (v N)) =
          carrierCoe38 r (physicalSobolevFourierEquiv38 r (v N)) :=
        funext (NlsGge.ThirdConsultation.KST.KST066S.embed_fourierSeq r hr (v N))
      rw [hf]
      exact carrierCoe38_mem _ _
    · conv_lhs => rw [← hv0]
      rw [G1086S.physicalSobolevNorm_embed_sub]
      simpa [dist_eq_norm] using hN'

end
end NlsGge.GKDefinitionDesign
