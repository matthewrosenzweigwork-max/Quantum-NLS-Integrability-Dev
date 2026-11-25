import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

/- G6SBC core (proof development, AUTHOR; not reviewed).  Target NlsGge/ThirdConsultation/G6/SobolevBirkhoffCompatCore.lean.
   Pro round 15 Q6 section 4 support leaves.  Unconditional leaves (VERBATIM heads, namespace NlsGge.GKDefinitionDesign):
   sequenceSobolevEmbed_coe, sequenceSobolevEmbed_injective, physicalSobolevEmbed_injective, physicalSobolevEmbed_mem,
   physicalSobolevEmbed_recover.  The G6-013/G6-023-dependent leaves are proved here as conditional cores (sub-namespace
   SobolevBirkhoffCompatCore) whose hypotheses have EXACTLY the types of landed G6013 conjuncts 5/6 and of G6023; the glue
   module SobolevBirkhoffCompat discharges them.  Split only because the G6013/G6023 closure overflows the worker lane
   (as for BirkhoffRawInv).  Route = Pro's Q6 section 4 proof. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

theorem sequenceSobolevEmbed_coe (m : ℕ)
    (z : SobolevCarrier38 (m : ℝ)) :
  (sequenceSobolevEmbed m z : ℤ → ℂ) = carrierCoe38 (m : ℝ) z := by
  unfold sequenceSobolevEmbed
  exact carrierCoe38_incl38 (Nat.cast_nonneg m) z

theorem sequenceSobolevEmbed_injective (m : ℕ) :
  Function.Injective (sequenceSobolevEmbed m) := by
  intro a b h
  apply carrierExt38
  rw [← sequenceSobolevEmbed_coe m a, ← sequenceSobolevEmbed_coe m b, h]

theorem physicalSobolevEmbed_injective (m : ℕ) :
  Function.Injective (physicalSobolevEmbed m) := by
  intro a b h
  apply (physicalSobolevFourierEquiv38 (m : ℝ)).injective
  apply sequenceSobolevEmbed_injective m
  apply reflectedFourierL2.symm.injective
  exact h

theorem physicalSobolevEmbed_mem (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
  fourierSeq38 (physicalSobolevEmbed m u) ∈ seqSobolev38 (m : ℝ) := by
  have hf : fourierSeq38 (physicalSobolevEmbed m u) =
      carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) :=
    funext (physicalSobolevEmbed_fourier m u)
  rw [hf]
  exact carrierCoe38_mem _ _

theorem physicalSobolevEmbed_recover (m : ℕ) :
  Function.LeftInverse (physicalSobolevRecover m) (physicalSobolevEmbed m) ∧
  ∀ u : PhysicalL2, fourierSeq38 u ∈ seqSobolev38 (m : ℝ) →
    physicalSobolevEmbed m (physicalSobolevRecover m u) = u := by
  refine ⟨fun u => ?_, fun u hu => ?_⟩
  · unfold physicalSobolevRecover
    rw [dif_pos (physicalSobolevEmbed_mem m u), LinearIsometryEquiv.symm_apply_eq]
    apply carrierExt38
    rw [carrierCoe38_mk]
    exact funext (physicalSobolevEmbed_fourier m u)
  · unfold physicalSobolevRecover
    rw [dif_pos hu]
    apply fourierSeq38_injective
    funext n
    rw [physicalSobolevEmbed_fourier, LinearIsometryEquiv.apply_symm_apply, carrierCoe38_mk]

namespace SobolevBirkhoffCompatCore

/-- Unfolded positive branch of the forward Sobolev restriction. -/
theorem birkhoffSobolev_eq_mk (m : ℕ) (u : PhysicalSobolev38 (m : ℝ))
    (h : (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ)) :
    birkhoffSobolev m u =
      carrierMk38 (m : ℝ) (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) h := by
  simp only [birkhoffSobolev]
  rw [dif_pos h]

theorem birkhoffSobolev_mem_of
    (hG : ∀ (u : PhysicalL2) (m : ℕ), fourierSeq38 u ∈ seqSobolev38 (m : ℝ) ↔
      (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ) :=
  (hG (physicalSobolevEmbed m u) m).1 (physicalSobolevEmbed_mem m u)

theorem inverseBirkhoffSobolev_mem_of
    (hR : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (hG : ∀ (u : PhysicalL2) (m : ℕ), fourierSeq38 u ∈ seqSobolev38 (m : ℝ) ↔
      (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) :
    fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed m z)) ∈
      seqSobolev38 (m : ℝ) := by
  apply (hG (physicalInverseBirkhoff (sequenceSobolevEmbed m z)) m).2
  rw [hR (sequenceSobolevEmbed m z), sequenceSobolevEmbed_coe]
  exact carrierCoe38_mem _ z

theorem birkhoffSobolev_coe_of
    (hG : ∀ (u : PhysicalL2) (m : ℕ), fourierSeq38 u ∈ seqSobolev38 (m : ℝ) ↔
      (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    sequenceSobolevEmbed m (birkhoffSobolev m u) =
      physicalBirkhoff (physicalSobolevEmbed m u) := by
  rw [birkhoffSobolev_eq_mk m u (birkhoffSobolev_mem_of hG m u)]
  apply lp.ext
  rw [sequenceSobolevEmbed_coe, carrierCoe38_mk]

theorem inverseBirkhoffSobolev_embed_of
    (hR : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (hG : ∀ (u : PhysicalL2) (m : ℕ), fourierSeq38 u ∈ seqSobolev38 (m : ℝ) ↔
      (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) :
    physicalSobolevEmbed m (inverseBirkhoffSobolev m z) =
      physicalInverseBirkhoff (sequenceSobolevEmbed m z) := by
  unfold inverseBirkhoffSobolev
  exact (physicalSobolevEmbed_recover m).2 _ (inverseBirkhoffSobolev_mem_of hR hG m z)

theorem birkhoffSobolev_inverse_compatible_all_of
    (hL : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (hR : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (hG : ∀ (u : PhysicalL2) (m : ℕ), fourierSeq38 u ∈ seqSobolev38 (m : ℝ) ↔
      (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (m : ℕ) :
  Function.LeftInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m) ∧
  Function.RightInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m) ∧
  (∀ u : PhysicalSobolev38 (m : ℝ),
    (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈
      seqSobolev38 (m : ℝ) ∧
    sequenceSobolevEmbed m (birkhoffSobolev m u) =
      physicalBirkhoff (physicalSobolevEmbed m u)) ∧
  (∀ z : SobolevCarrier38 (m : ℝ),
    fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed m z)) ∈
      seqSobolev38 (m : ℝ) ∧
    physicalSobolevEmbed m (inverseBirkhoffSobolev m z) =
      physicalInverseBirkhoff (sequenceSobolevEmbed m z)) := by
  refine ⟨fun u => ?_, fun z => ?_, fun u => ⟨birkhoffSobolev_mem_of hG m u,
    birkhoffSobolev_coe_of hG m u⟩, fun z => ⟨inverseBirkhoffSobolev_mem_of hR hG m z,
    inverseBirkhoffSobolev_embed_of hR hG m z⟩⟩
  · apply physicalSobolevEmbed_injective m
    rw [inverseBirkhoffSobolev_embed_of hR hG, birkhoffSobolev_coe_of hG, hL]
  · apply sequenceSobolevEmbed_injective m
    rw [birkhoffSobolev_coe_of hG, inverseBirkhoffSobolev_embed_of hR hG, hR]

end SobolevBirkhoffCompatCore

end NlsGge.GKDefinitionDesign

end
