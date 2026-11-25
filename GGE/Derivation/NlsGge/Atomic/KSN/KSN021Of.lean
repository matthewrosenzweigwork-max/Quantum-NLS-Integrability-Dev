import Mathlib
import NlsGge.ThirdConsultation.PDE.ForwardSmoothing
import NlsGge.Atomic.KSN.KSN021Host
import NlsGge.Atomic.KSN.KSN022Asm
import NlsGge.Atomic.M.M049Core
import NlsGge.Atomic.M.M049Coef
import NlsGge.ThirdConsultation.M.BirkhoffInverseHost
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6027

/- KSN021 OF PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/KSN/KSN021Of.lean. Needs ROOT MAIN PROBE. KSN-021 (`inverseSmoothing`): the printed head body (Pro r16
   L1494-1504) VERBATIM as the conclusion of `KSN021_main_of`, CONDITIONAL on `h49` = EXACTLY the M-049 main head body
   at m = N (M-049 waits on M-048; as in batch 7). Route (r16 L1292, L1443):
   * u = Φ⁻¹(sE z) ∈ H^N (G6-027); Φ(u) = sE z (G6-013 right inverse); hence F(u − F⁻¹ sE z) = −(T(Fu) − Fu), the
     forward smoothing at Fu (ForwardSmoothing.smooth_coord) — membership at N+1 earned first, recovery takes its valid
     branch (embed_recover_real), no fallback;
   * analyticity: inverseSmoothing = F⁻¹_{N+1} ∘ (−fromPairEq) ∘ complexSmoothing ∘ toPair ∘ actualTinvC38, with
     complexSmoothing ℂ-analytic on complexDomain (KSN-019) restricted to ℝ and actualTinvC38 analytic (G6-027);
   * ball bound: for ‖z‖ ≤ B, ‖Fu‖ = ‖birkhoffInverse N z‖ ≤ 2D(1+B)^{4N−2} by M-049 (h49) and the norm-one inclusions;
     KSN-019's real-pair ball bound at radius ‖toPair‖·2D(1+B)^{4N−2} gives C — chosen after B, before z.
   The index cast ((N+1:ℕ):ℝ) = (N:ℝ)+1 is handled by proving the s-statement for a variable s and `subst`. -/

set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.KSN NlsGge.ThirdConsultation.Common NlsGge.ThirdConsultation.PDE
open NlsGge.ThirdConsultation.G6024S

namespace NlsGge.GKDefinitionDesign

theorem embed_recover_real (s : ℝ) (hs : 0 ≤ s) (v : PhysicalL2) (hv : fourierSeq38 v ∈ seqSobolev38 s) :
    physicalSobolevEmbedRealExponent s hs (physicalSobolevRecoverRealExponent s v) = v := by
  unfold physicalSobolevEmbedRealExponent physicalSobolevRecoverRealExponent
  rw [dif_pos hv, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_eq]
  apply lp.ext
  funext n
  show carrierCoe38 0 (carrierIncl38 hs (carrierMk38 s (fourierSeq38 v) hv)) n =
    (reflectedFourierL2 v : ℤ → ℂ) n
  rw [carrierCoe38_incl38, carrierCoe38_mk]
  rfl

theorem KSN021_main_of (N : ℕ) (hN : 1 ≤ N)
    (h49 : ∃ D : ℝ, 0 < D ∧ ∀ z : NlsGge.ThirdConsultation.M.RealSobolevSequence N,
      ‖NlsGge.ThirdConsultation.M.birkhoffInverse N z‖ ≤
        D * (‖z‖ +
          (1 + ‖NlsGge.Birkhoff.carrierIncl38
            (r := 1) (s := (N : ℝ)) (by exact_mod_cast hN) z‖) ^ (4 * N - 3) *
            ‖NlsGge.Birkhoff.carrierIncl38
              (r := 0) (s := (N : ℝ)) (by positivity) z‖)) :
  AnalyticOnNhd ℝ (inverseSmoothing N) Set.univ ∧
  (∀ z : SobolevCarrier38 (N : ℝ),
    fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed N z) -
      reflectedFourierL2.symm (sequenceSobolevEmbed N z)) ∈ seqSobolev38 ((N : ℝ) + 1) ∧
    physicalSobolevEmbedRealExponent ((N : ℝ) + 1) (by positivity) (inverseSmoothing N z) =
      physicalInverseBirkhoff (sequenceSobolevEmbed N z) -
        reflectedFourierL2.symm (sequenceSobolevEmbed N z)) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : SobolevCarrier38 (N : ℝ), ‖z‖ ≤ B → ‖inverseSmoothing N z‖ ≤ C) := by
  let U : SobolevCarrier38 (N : ℝ) → PhysicalL2 := fun z =>
    physicalInverseBirkhoff (sequenceSobolevEmbed N z)
  let V : SobolevCarrier38 (N : ℝ) → PhysicalL2 := fun z =>
    U z - reflectedFourierL2.symm (sequenceSobolevEmbed N z)
  have hFu : ∀ z, fourierSeq38 (U z) ∈ seqSobolev38 (N : ℝ) := fun z => ((G6027 N hN).2.2.2.2.2 z).1
  have hX : ∀ z, carrierMk38 (N : ℝ) (fourierSeq38 (U z)) (hFu z) = actualTinvC38 N z := fun z => by
    apply carrierExt38
    funext n
    rw [carrierCoe38_mk]
    show fourierSeq38 (U z) n =
      carrierCoe38 (N : ℝ) (physicalSobolevFourierEquiv38 (N : ℝ) (inverseBirkhoffSobolev N z)) n
    rw [← physicalSobolevEmbed_fourier, ((G6027 N hN).2.2.2.2.2 z).2]
  have hFv : ∀ z n, fourierSeq38 (V z) n =
      -(fromSeqEq (N + 1) (complexSmoothing N (toPair N (actualTinvC38 N z))) n) := by
    intro z n
    have hc := smooth_coord N hN (fourierSeq38 (U z)) (hFu z) n
    rw [hX z] at hc
    rw [← hc]
    have hTw : actualT38 (fourierSeq38 (U z)) = (sequenceSobolevEmbed N z : ℤ → ℂ) := by
      rw [actualT38_fourierSeq38]
      show ((physicalBirkhoff (physicalInverseBirkhoff (sequenceSobolevEmbed N z))) : ℤ → ℂ) = _
      rw [G6013.2.2.2.2.2]
    rw [hTw]
    show fourierSeq38 (U z - reflectedFourierL2.symm (sequenceSobolevEmbed N z)) n = _
    rw [fourierSeq38_sub]
    show fourierSeq38 (U z) n -
      (reflectedFourierL2 (reflectedFourierL2.symm (sequenceSobolevEmbed N z)) : ℤ → ℂ) n = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    ring
  have hgen : ∀ s : ℝ, ((N + 1 : ℕ) : ℝ) = s →
      (∀ z, fourierSeq38 (V z) ∈ seqSobolev38 s) ∧
      (∀ z, ‖physicalSobolevRecoverRealExponent s (V z)‖ =
        ‖fromPairEq (N + 1) (complexSmoothing N (toPair N (actualTinvC38 N z)))‖) ∧
      AnalyticOnNhd ℝ (fun z => physicalSobolevRecoverRealExponent s (V z)) Set.univ := by
    intro s hs
    subst hs
    have hmem : ∀ z, fourierSeq38 (V z) ∈ seqSobolev38 ((N + 1 : ℕ) : ℝ) := fun z => by
      have h : fourierSeq38 (V z) =
          -(carrierCoe38 _ (fromPairEq (N + 1) (complexSmoothing N (toPair N (actualTinvC38 N z))))) :=
        funext fun n => by rw [hFv z n]; rfl
      rw [h]
      exact (weightedSubmodule _).neg_mem (carrierCoe38_mem _ _)
    have hcar : ∀ z, carrierMk38 ((N + 1 : ℕ) : ℝ) (fourierSeq38 (V z)) (hmem z) =
        -(fromPairEq (N + 1) (complexSmoothing N (toPair N (actualTinvC38 N z)))) := fun z => by
      apply carrierExt38
      funext n
      rw [carrierCoe38_mk, hFv z n]
      rfl
    have hrec : ∀ z, physicalSobolevRecoverRealExponent ((N + 1 : ℕ) : ℝ) (V z) =
        (physicalSobolevFourierEquiv38 _).symm
          (-(fromPairEq (N + 1) (complexSmoothing N (toPair N (actualTinvC38 N z))))) := fun z => by
      unfold physicalSobolevRecoverRealExponent
      rw [dif_pos (hmem z), hcar z]
    refine ⟨hmem, fun z => ?_, ?_⟩
    · rw [hrec z, LinearIsometryEquiv.norm_map, norm_neg]
    · have hf : (fun z => physicalSobolevRecoverRealExponent ((N + 1 : ℕ) : ℝ) (V z)) =
          fun z => (physicalSobolevFourierEquiv38 _).symm
            (-(fromPairEq (N + 1) (complexSmoothing N (toPair N (actualTinvC38 N z))))) := funext hrec
      rw [hf]
      intro z _
      have hinv : AnalyticAt ℝ (actualTinvC38 N) z := by
        have hB : AnalyticAt ℝ (inverseBirkhoffSobolev N) z := (G6027 N hN).2.1 z (mem_univ z)
        exact ((physicalSobolevFourierEquiv38 (N : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp hB
      have hdom : toPair N (actualTinvC38 N z) ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N) :=
        toPair_mem_complexDomain N (inverseBirkhoffSobolev N z)
      have hC : AnalyticAt ℝ (complexSmoothing N) (toPair N (actualTinvC38 N z)) :=
        ((KSN019_main N hN).1 _ hdom).restrictScalars
      have h1 : AnalyticAt ℝ (fun z => toPair N (actualTinvC38 N z)) z :=
        AnalyticAt.comp (g := fun y => toPair N y) (f := actualTinvC38 N) ((toPair N).analyticAt _) hinv
      have h2 : AnalyticAt ℝ (fun z => complexSmoothing N (toPair N (actualTinvC38 N z))) z :=
        AnalyticAt.comp (g := complexSmoothing N) (f := fun z => toPair N (actualTinvC38 N z)) hC h1
      have h3 : AnalyticAt ℝ
          (fun z => fromPairEq (N + 1) (complexSmoothing N (toPair N (actualTinvC38 N z)))) z :=
        AnalyticAt.comp (g := fun y => fromPairEq (N + 1) y)
          (f := fun z => complexSmoothing N (toPair N (actualTinvC38 N z))) ((fromPairEq (N + 1)).analyticAt _) h2
      exact AnalyticAt.comp
        (g := fun y => (physicalSobolevFourierEquiv38 ((N + 1 : ℕ) : ℝ)).symm y)
        (f := fun z => -(fromPairEq (N + 1) (complexSmoothing N (toPair N (actualTinvC38 N z)))))
        ((physicalSobolevFourierEquiv38 ((N + 1 : ℕ) : ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _)
        h3.neg
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  obtain ⟨hmem, hnorm, hana⟩ := hgen _ hcast
  have hIS : inverseSmoothing N = fun z => physicalSobolevRecoverRealExponent ((N : ℝ) + 1) (V z) := rfl
  refine ⟨?_, fun z => ⟨hmem z, ?_⟩, ?_⟩
  · rw [hIS]; exact hana
  · exact embed_recover_real _ _ (V z) (hmem z)
  · intro B hB
    obtain ⟨D, hD, hb⟩ := h49
    have hB0 : 0 ≤ 2 * D * (1 + B) ^ (4 * N - 2) := by positivity
    obtain ⟨C1, hC1, hc1⟩ := (KSN019_main N hN).2.2.2 (‖toPair N‖ * (2 * D * (1 + B) ^ (4 * N - 2)))
      (mul_nonneg (norm_nonneg _) hB0)
    refine ⟨‖fromPairEq (N + 1)‖ * C1, mul_nonneg (norm_nonneg _) hC1, fun z hz => ?_⟩
    show ‖physicalSobolevRecoverRealExponent ((N : ℝ) + 1) (V z)‖ ≤ _
    rw [hnorm z]
    have hX0 : ‖actualTinvC38 N z‖ ≤ 2 * D * (1 + B) ^ (4 * N - 2) := by
      have e : ‖actualTinvC38 N z‖ = ‖NlsGge.ThirdConsultation.M.birkhoffInverse N z‖ :=
        (physicalSobolevFourierEquiv38 (N : ℝ)).norm_map _
      rw [e]
      have h1 := NlsGge.ThirdConsultation.M049Aux.incl_norm_le (r := 1) (s := (N : ℝ))
        (by exact_mod_cast hN) z
      have h0 := NlsGge.ThirdConsultation.M049Aux.incl_norm_le (r := 0) (s := (N : ℝ))
        (by positivity) z
      have hp := NlsGge.ThirdConsultation.M049Aux.poly_alg ‖z‖ _ _ (4 * N - 3)
        (norm_nonneg _) (norm_nonneg _) h1 h0
      rw [show 4 * N - 3 + 1 = 4 * N - 2 by omega] at hp
      have hmono : (1 + ‖z‖) ^ (4 * N - 2) ≤ (1 + B) ^ (4 * N - 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      calc _ ≤ _ := hb z
        _ ≤ D * (2 * (1 + ‖z‖) ^ (4 * N - 2)) := mul_le_mul_of_nonneg_left hp hD.le
        _ ≤ D * (2 * (1 + B) ^ (4 * N - 2)) := by nlinarith
        _ = 2 * D * (1 + B) ^ (4 * N - 2) := by ring
    have hP : ‖toPair N (actualTinvC38 N z)‖ ≤ ‖toPair N‖ * (2 * D * (1 + B) ^ (4 * N - 2)) :=
      ((toPair N).le_opNorm _).trans (mul_le_mul_of_nonneg_left hX0 (norm_nonneg _))
    have hcs := hc1 _ (NlsGge.ThirdConsultation.KSN022S.toPair_isReal N _) hP
    exact ((fromPairEq (N + 1)).le_opNorm _).trans (mul_le_mul_of_nonneg_left hcs (norm_nonneg _))

end NlsGge.GKDefinitionDesign
