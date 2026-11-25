import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA6Real
import NlsGge.Atomic.KSN.KSN021Host
import NlsGge.Atomic.KSN.KSN022Host
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

/-! # Track A, step A6: transport helpers for the physical form and cross-index compatibility

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.  Helper lemmas only; the
final approved-statement theorems are NOT stated here.

* the reflected Fourier sequence of `physicalSobolevEmbedRealExponent s hs u` is the carrier
  sequence of `physicalSobolevFourierEquiv38 s u`; the sequence embedding has the carrier sequence;
* `physicalBirkhoff_embed_mem`, `fourierSeq38_inverse_embed_mem`: the `if` conditions of the
  totalized definitions `birkhoffSobolevRealExponent` / `inverseBirkhoffSobolevRealExponent`
  (through `physicalSobolevRecoverRealExponent`) hold, so their `else 0` junk branches are never taken;
* `birkhoffSobolevRealExponent_eq`, `inverseBirkhoffSobolevRealExponent_eq`: both definitions are
  the sequence-carrier maps conjugated by the Fourier isometry `physicalSobolevFourierEquiv38 s`;
* the two embedding identities (each level is a literal restriction of the global maps);
* `carrierIncl38_carrierMap38`: cross-index compatibility through `carrierIncl38` for any map;
* the integer-level identifications with G6027's `birkhoffSobolev m`, `inverseBirkhoffSobolev m`. -/

set_option autoImplicit false
noncomputable section

open Set NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE

namespace NlsGge.ALLS.TransA

/-- Cross-index compatibility of carrier maps through the inclusion `h^{s'} → h^s`. -/
theorem carrierIncl38_carrierMap38 {s s' : ℝ} (hss' : s ≤ s') (f : (ℤ → ℂ) → (ℤ → ℂ))
    (hf : ∀ x ∈ seqSobolev38 s, f x ∈ seqSobolev38 s)
    (hf' : ∀ x ∈ seqSobolev38 s', f x ∈ seqSobolev38 s') (x : SobolevCarrier38 s') :
    carrierIncl38 hss' (carrierMap38 s' s' f hf' x) = carrierMap38 s s f hf (carrierIncl38 hss' x) := by
  apply carrierExt38
  rw [carrierCoe38_incl38, carrierMap38_coe, carrierMap38_coe, carrierCoe38_incl38]

/-- The sequence embedding `h^s → ℓ²` has the carrier sequence. -/
theorem coe_sequenceSobolevEmbedRealExponent (s : ℝ) (hs : 0 ≤ s) (z : SobolevCarrier38 s) :
    (sequenceSobolevEmbedRealExponent s hs z : ℤ → ℂ) = carrierCoe38 s z := by
  show carrierCoe38 0 (carrierIncl38 hs z) = _
  exact carrierCoe38_incl38 hs z

/-- The reflected Fourier sequence of the physical embedding is the carrier sequence. -/
theorem fourierSeq38_physicalSobolevEmbedRealExponent (s : ℝ) (hs : 0 ≤ s)
    (u : PhysicalSobolev38 s) :
    fourierSeq38 (physicalSobolevEmbedRealExponent s hs u) =
      carrierCoe38 s (physicalSobolevFourierEquiv38 s u) := by
  show (reflectedFourierL2 (reflectedFourierL2.symm _) : ℤ → ℂ) = _
  rw [LinearIsometryEquiv.apply_symm_apply, coe_sequenceSobolevEmbedRealExponent]

/-- Forward condition: `Φ(u) ∈ h^s` for every `u ∈ H^s` (junk branch not taken). -/
theorem physicalBirkhoff_embed_mem (s : ℝ) (hs : 0 ≤ s)
    (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s)
    (u : PhysicalSobolev38 s) :
    (physicalBirkhoff (physicalSobolevEmbedRealExponent s hs u) : ℤ → ℂ) ∈ seqSobolev38 s := by
  rw [physicalBirkhoff_coe_eq_T, fourierSeq38_physicalSobolevEmbedRealExponent]
  exact hT _ (carrierCoe38_mem s _)

/-- Inverse condition: `𝓕(Ψ(z)) ∈ h^s` for every `z ∈ h^s` (junk branch not taken). -/
theorem fourierSeq38_inverse_embed_mem (s : ℝ) (hs : 0 ≤ s)
    (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s)
    (z : SobolevCarrier38 s) :
    fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbedRealExponent s hs z)) ∈
      seqSobolev38 s := by
  rw [fourierSeq38_physicalInverseBirkhoff, coe_sequenceSobolevEmbedRealExponent]
  exact hTinv _ (carrierCoe38_mem s z)

/-- `birkhoffSobolevRealExponent s hs = T_s ∘ 𝓕_s`. -/
theorem birkhoffSobolevRealExponent_eq (s : ℝ) (hs : 0 ≤ s)
    (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s) :
    birkhoffSobolevRealExponent s hs =
      carrierMap38 s s actualBirkhoffTop38.T hT ∘ physicalSobolevFourierEquiv38 s := by
  funext u
  unfold birkhoffSobolevRealExponent
  rw [dif_pos (physicalBirkhoff_embed_mem s hs hT u)]
  apply carrierExt38
  rw [carrierCoe38_mk, Function.comp_apply, carrierMap38_coe, physicalBirkhoff_coe_eq_T,
    fourierSeq38_physicalSobolevEmbedRealExponent]

/-- `inverseBirkhoffSobolevRealExponent s hs = 𝓕_s⁻¹ ∘ Tinv_s`. -/
theorem inverseBirkhoffSobolevRealExponent_eq (s : ℝ) (hs : 0 ≤ s)
    (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s) :
    inverseBirkhoffSobolevRealExponent s hs =
      (physicalSobolevFourierEquiv38 s).symm ∘ carrierMap38 s s actualBirkhoffTop38.Tinv hTinv := by
  funext z
  unfold inverseBirkhoffSobolevRealExponent physicalSobolevRecoverRealExponent
  rw [dif_pos (fourierSeq38_inverse_embed_mem s hs hTinv z), Function.comp_apply]
  congr 1
  apply carrierExt38
  rw [carrierCoe38_mk, carrierMap38_coe, fourierSeq38_physicalInverseBirkhoff,
    coe_sequenceSobolevEmbedRealExponent]

/-- Forward embedding identity: the level-`s` map is the literal value of the global map. -/
theorem sequenceEmbed_birkhoffSobolevRealExponent (s : ℝ) (hs : 0 ≤ s)
    (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s)
    (u : PhysicalSobolev38 s) :
    sequenceSobolevEmbedRealExponent s hs (birkhoffSobolevRealExponent s hs u) =
      physicalBirkhoff (physicalSobolevEmbedRealExponent s hs u) := by
  apply lp.ext
  rw [coe_sequenceSobolevEmbedRealExponent]
  unfold birkhoffSobolevRealExponent
  rw [dif_pos (physicalBirkhoff_embed_mem s hs hT u), carrierCoe38_mk]

/-- Inverse embedding identity. -/
theorem physicalEmbed_inverseBirkhoffSobolevRealExponent (s : ℝ) (hs : 0 ≤ s)
    (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s)
    (z : SobolevCarrier38 s) :
    physicalSobolevEmbedRealExponent s hs (inverseBirkhoffSobolevRealExponent s hs z) =
      physicalInverseBirkhoff (sequenceSobolevEmbedRealExponent s hs z) := by
  apply fourierSeq38_injective
  rw [fourierSeq38_physicalSobolevEmbedRealExponent, inverseBirkhoffSobolevRealExponent_eq s hs hTinv,
    Function.comp_apply, LinearIsometryEquiv.apply_symm_apply, carrierMap38_coe,
    fourierSeq38_physicalInverseBirkhoff, coe_sequenceSobolevEmbedRealExponent]

/-- Analyticity transfers through the Fourier isometry (forward). -/
theorem analyticOnNhd_birkhoffSobolevRealExponent (s : ℝ) (hs : 0 ≤ s)
    (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s)
    (han : AnalyticOnNhd ℝ (carrierMap38 s s actualBirkhoffTop38.T hT) Set.univ) :
    AnalyticOnNhd ℝ (birkhoffSobolevRealExponent s hs) Set.univ := by
  rw [birkhoffSobolevRealExponent_eq s hs hT]
  intro u _
  exact (han _ trivial).comp
    ((physicalSobolevFourierEquiv38 s).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt u)

/-- Analyticity transfers through the Fourier isometry (inverse). -/
theorem analyticOnNhd_inverseBirkhoffSobolevRealExponent (s : ℝ) (hs : 0 ≤ s)
    (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s)
    (han : AnalyticOnNhd ℝ (carrierMap38 s s actualBirkhoffTop38.Tinv hTinv) Set.univ) :
    AnalyticOnNhd ℝ (inverseBirkhoffSobolevRealExponent s hs) Set.univ := by
  rw [inverseBirkhoffSobolevRealExponent_eq s hs hTinv]
  intro z _
  exact ((physicalSobolevFourierEquiv38 s).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt
    _).comp (han z trivial)

/-- Integer levels: the real-exponent forward map is G6027's `birkhoffSobolev m`. -/
theorem birkhoffSobolevRealExponent_natCast (m : ℕ) :
    birkhoffSobolevRealExponent (m : ℝ) (Nat.cast_nonneg m) = birkhoffSobolev m := rfl

/-- Integer levels: the real-exponent inverse map is G6027's `inverseBirkhoffSobolev m`. -/
theorem inverseBirkhoffSobolevRealExponent_natCast (m : ℕ) :
    inverseBirkhoffSobolevRealExponent (m : ℝ) (Nat.cast_nonneg m) = inverseBirkhoffSobolev m := rfl

end NlsGge.ALLS.TransA
