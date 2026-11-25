import Mathlib
import NlsGge.Atomic.G6.G6030Host
import NlsGge.Atomic.G6.G6029Core
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore

/- G6030 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6030Core.lean,
   namespace NlsGge.ThirdConsultation.G6030S.  SUPPORT (no packet increment).
   G6030_of = the G6-030 head body (followup13 STATEMENTS/G6.md, verbatim) from hypotheses with EXACT producer types:
   h29 = G6029 clause 3 (proof development), hcoe = birkhoffSobolev_coe m, hemb = inverseBirkhoffSobolev_embed m,
   hleft = (birkhoffSobolev_inverse_compatible_all m).1 (all landed, SobolevBirkhoffCompat), hcont = continuity of the
   literal inverseBirkhoffSobolev m.
   Route (Pro r15 Q5 row G6-030: "A fixed input and Sobolev index; convergence follows from the inverse's continuity at
   the limiting sequence. No bounded-set uniform estimate is inferred."):  with v = physicalSobolevRecover m u and
   z = birkhoffSobolev m v, the H^m truncation is inverseBirkhoffSobolev m (projC38 m N z) (seqEmbed_projC: the carrier
   projection is the coordinate truncation, symmetricModes N = Lib.win N), projC38 m N z → z (landed tendsto_projC38),
   and inverseBirkhoffSobolev m z = v.
   inv_continuous: m ≥ 1 from G6-027's analyticity of inverseBirkhoffSobolev m; m = 0 (the head allows every m : ℕ)
   from G6-014's analyticity of physicalInverseBirkhoff through the level-zero isometry l2Carrier0 (inv0_continuous). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace
open NlsGge.ThirdConsultation (finiteGap)
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6030S
noncomputable section

theorem seqEmbed_projC (m N : ℕ) (z : SobolevCarrier38 (m : ℝ)) :
    sequenceSobolevEmbed m (projC38 (m : ℝ) N z) =
      truncatePhysicalCoordinates N (sequenceSobolevEmbed m z) := by
  apply lp.ext
  funext n
  rw [G6029Aux.truncate_apply, sequenceSobolevEmbed_coe, sequenceSobolevEmbed_coe, carrierCoe38_projC38]
  rfl

theorem inv0_continuous (hΨ : Continuous physicalInverseBirkhoff) :
    Continuous (inverseBirkhoffSobolev 0) := by
  have hS : ∀ z : SobolevCarrier38 ((0 : ℕ) : ℝ),
      sequenceSobolevEmbed 0 z = NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore.l2Carrier0.symm z := by
    intro z
    apply lp.ext
    rw [sequenceSobolevEmbed_coe, NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore.l2Carrier0_symm_coe]
  have hR : ∀ w : PhysicalL2, physicalSobolevRecover 0 w =
      (physicalSobolevFourierEquiv38 ((0 : ℕ) : ℝ)).symm
        (NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore.l2Carrier0 (reflectedFourierL2 w)) := by
    intro w
    have hmem : fourierSeq38 w ∈ seqSobolev38 ((0 : ℕ) : ℝ) := by
      have h := carrierCoe38_mem ((0 : ℕ) : ℝ)
        (NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore.l2Carrier0 (reflectedFourierL2 w))
      rwa [NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore.l2Carrier0_coe] at h
    unfold physicalSobolevRecover
    rw [dif_pos hmem]
    congr 1
  have heq : inverseBirkhoffSobolev 0 = fun z =>
      (physicalSobolevFourierEquiv38 ((0 : ℕ) : ℝ)).symm
        (NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore.l2Carrier0 (reflectedFourierL2
          (physicalInverseBirkhoff (NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore.l2Carrier0.symm z)))) := by
    funext z
    unfold inverseBirkhoffSobolev
    rw [hS, hR]
  rw [heq]
  exact (physicalSobolevFourierEquiv38 ((0 : ℕ) : ℝ)).symm.continuous.comp
    (NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore.l2Carrier0.continuous.comp
      (reflectedFourierL2.continuous.comp
        (hΨ.comp NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore.l2Carrier0.symm.continuous)))

theorem inv_continuous (m : ℕ)
    (hΨ : AnalyticOnNhd ℝ physicalInverseBirkhoff Set.univ)
    (h27 : 1 ≤ m → AnalyticOnNhd ℝ (inverseBirkhoffSobolev m) Set.univ) :
    Continuous (inverseBirkhoffSobolev m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact inv0_continuous (continuousOn_univ.1 hΨ.continuousOn)
  · exact continuousOn_univ.1 (h27 hm).continuousOn

theorem G6030_of (u : PhysicalL2) (m : ℕ)
    (hu : fourierSeq38 u ∈ seqSobolev38 (m : ℝ))
    (h29 : ∀ N : ℕ, finiteGap (finiteGapTruncation N u) ∧
      ∀ k : ℕ, fourierSeq38 (finiteGapTruncation N u) ∈ seqSobolev38 (k : ℝ))
    (hcoe : ∀ v : PhysicalSobolev38 (m : ℝ),
      sequenceSobolevEmbed m (birkhoffSobolev m v) = physicalBirkhoff (physicalSobolevEmbed m v))
    (hemb : ∀ z : SobolevCarrier38 (m : ℝ),
      physicalSobolevEmbed m (inverseBirkhoffSobolev m z) =
        physicalInverseBirkhoff (sequenceSobolevEmbed m z))
    (hleft : Function.LeftInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m))
    (hcont : Continuous (inverseBirkhoffSobolev m)) :
  (∀ N : ℕ, finiteGap (finiteGapTruncation N u) ∧
    ∀ k : ℕ, fourierSeq38 (finiteGapTruncation N u) ∈ seqSobolev38 (k : ℝ)) ∧
  (∀ N : ℕ, physicalSobolevEmbed m (finiteGapTruncationSobolev m N u) =
    finiteGapTruncation N u) ∧
  Tendsto (fun N : ℕ => finiteGapTruncationSobolev m N u) atTop
    (𝓝 (physicalSobolevRecover m u)) := by
  have hE : ∀ N : ℕ, physicalSobolevEmbed m (finiteGapTruncationSobolev m N u) =
      finiteGapTruncation N u := fun N => by
    unfold finiteGapTruncationSobolev
    exact (physicalSobolevEmbed_recover m).2 _ ((h29 N).2 m)
  refine ⟨h29, hE, ?_⟩
  have hv : physicalSobolevEmbed m (physicalSobolevRecover m u) = u :=
    (physicalSobolevEmbed_recover m).2 u hu
  have key : ∀ N : ℕ, finiteGapTruncationSobolev m N u =
      inverseBirkhoffSobolev m (projC38 (m : ℝ) N (birkhoffSobolev m (physicalSobolevRecover m u))) := by
    intro N
    apply physicalSobolevEmbed_injective m
    rw [hE N, hemb, seqEmbed_projC, hcoe, hv]
    rfl
  have hlim : inverseBirkhoffSobolev m (birkhoffSobolev m (physicalSobolevRecover m u)) =
      physicalSobolevRecover m u := hleft _
  rw [show (fun N : ℕ => finiteGapTruncationSobolev m N u) = fun N : ℕ =>
      inverseBirkhoffSobolev m (projC38 (m : ℝ) N (birkhoffSobolev m (physicalSobolevRecover m u)))
    from funext key]
  conv => rhs; rw [← hlim]
  exact (hcont.tendsto _).comp (tendsto_projC38 (m : ℝ) _)

end
end NlsGge.ThirdConsultation.G6030S
