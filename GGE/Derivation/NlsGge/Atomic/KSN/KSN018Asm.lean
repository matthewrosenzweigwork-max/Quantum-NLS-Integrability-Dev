import Mathlib
import NlsGge.Atomic.KSN.KSN018Sum
import NlsGge.Atomic.KSN.KSN018Link
import NlsGge.Atomic.KSN.KSN018Sup3
import NlsGge.Atomic.KSN.KSN012Sup4

/- KSN018 ASM PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN018Asm.lean.
   SUPPORT (no packet increment): KSN018_of = the KSN-018 head body (Pro, followup13 STATEMENTS/KSN.md, verbatim) from
   hypotheses whose types are EXACTLY landed/packet conclusions: KSN012_main, KSN014_main, KSN017_main (order-one heads;
   applied to x ∈ PairScale N through the lowering ksn018_lower, same pairPotential), the first conjunct of KSN010_main,
   G4014Aux.cartZ_plus/minus, and Pro r15 KSPS.midpoint_dirichlet_difference_uniform / KSPS.antitrace_at_dirichlet_uniform.
   Clause 1: U = lower⁻¹(U12 ∩ U14 ∩ U17) ∩ ball(x₀,1), H = ‖x₀‖+1; clause 2: real x ↦ real lower x, H = B.
   Per x: KSN018Sum.ksn018_smooth_l2 with K = C12 + C14 + C17 and the KSN018Link remainders at B₀ = 2ᴺH.
   Route = Pro r15 L858. No hypothesis added to the head. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

/-- One point: Memℓp and the norm bound from the per-label bounds at the lowered point. -/
theorem ksn018_point (N : ℕ) (hN : 1 ≤ N) (x : PairScale (N : ℝ)) (K H CE1 CE2 : ℝ) (hK : 0 ≤ K)
    (hxH : ‖x‖ ≤ H) (hS : pairPotential (N : ℝ) (Nat.cast_nonneg N) x ∈ sourceBetaW)
    (h10 : ∀ φ ∈ sourceBetaW, ∀ n a : ℤ, (a = 1 ∨ a = -1) →
      deltaFactor n φ (muSeq φ n) ≠ 0 ∧
      sourceZ n a φ =
        ((tauN φ n - muSeq φ n) - (a : ℂ) * Complex.I *
          antiDiscrim φ (muSeq φ n) / (2 * deltaFactor n φ (muSeq φ n))) * eta n a φ)
    (hcp : ∀ (n : ℤ) (φ : PotPair), φ ∈ gkW → cartesianZExtended n 1 φ = gk16ActualScalarZPlus38 sourceF n φ)
    (hcm : ∀ (n : ℤ) (φ : PotPair), φ ∈ gkW → cartesianZExtended n (-1) φ = gk16ActualScalarZMinus38 sourceF n φ)
    (hrem : (∀ F : Finset ℤ, ∑ n ∈ F, (bracket n ^ (N + 1) *
          ‖tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
            muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n +
            (rawCoefficient (N : ℝ) x true (-n) + rawCoefficient (N : ℝ) x false n) / 2‖) ^ 2 ≤ CE1) ∧
      (∀ F : Finset ℤ, ∑ n ∈ F, (bracket n ^ (N + 1) *
          ‖antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
              (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
            Complex.I * (-1 : ℂ) ^ n *
              (rawCoefficient (N : ℝ) x true (-n) - rawCoefficient (N : ℝ) x false n)‖) ^ 2 ≤ CE2))
    (hb : ∀ n : ℤ, ‖betaSum n (pairPotential 1 (by norm_num) (ksn018_lower N hN x))‖ ≤ K / bracket n ∧
      ∀ a : ℤ, (a = 1 ∨ a = -1) →
        ‖eta n a (pairPotential 1 (by norm_num) (ksn018_lower N hN x)) - 1‖ ≤ K / bracket n)
    (hx : ∀ n : ℤ, ‖xiN38 n (pairPotential 1 (by norm_num) (ksn018_lower N hN x)) - 1‖ ≤ K / bracket n)
    (hd : ∀ n : ℤ,
      deltaFactor n (pairPotential 1 (by norm_num) (ksn018_lower N hN x))
          (muSeq (pairPotential 1 (by norm_num) (ksn018_lower N hN x)) n) ≠ 0 ∧
        ‖(deltaFactor n (pairPotential 1 (by norm_num) (ksn018_lower N hN x))
          (muSeq (pairPotential 1 (by norm_num) (ksn018_lower N hN x)) n))⁻¹ - (-1 : ℂ)^n‖ ≤ K / bracket n) :
    Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
      ‖complexSmoothing N x‖ ≤ Real.sqrt (2 * ((4 * (1 + ((2 + Real.exp K) * K + K)) ^ 4 * (1 + ((2 + Real.exp K) * K + K))) ^ 2 *
        (((4 : ℕ) : ℝ) * (H ^ 2 + H ^ 2 + CE1 + CE2)))) := by
  have hpl := ksn018_pairPotential_lower N hN x
  rw [hpl] at hb hx hd
  have hW : pairPotential (N : ℝ) (Nat.cast_nonneg N) x ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hS)
  obtain ⟨hm, hn⟩ := ksn018_smooth_l2 N x K hK (fun n => hx n) (fun n => (hb n).1) (fun n => (hb n).2)
    (fun n => (hd n).2) (fun n => hcp n _ hW) (fun n => hcm n _ hW)
    (fun n a ha => (h10 _ hS n a ha).2) CE1 CE2 hrem.1 hrem.2
  refine ⟨hm, hn.trans (Real.sqrt_le_sqrt ?_)⟩
  have hx2 : ‖x‖ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxH 2
  have hc : 0 ≤ (4 * (1 + ((2 + Real.exp K) * K + K)) ^ 4 * (1 + ((2 + Real.exp K) * K + K))) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left (show ((4 : ℕ) : ℝ) * (‖x‖ ^ 2 + ‖x‖ ^ 2 + CE1 + CE2) ≤
    ((4 : ℕ) : ℝ) * (H ^ 2 + H ^ 2 + CE1 + CE2) by push_cast; linarith) hc
  linarith

theorem KSN018_of (N : ℕ) (hN : 1 ≤ N)
    (h12 :
        (∀ x₀ ∈ complexDomain 1 (by norm_num),
          ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
            U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
            ∀ x ∈ U, ∀ n : ℤ,
              ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ C / bracket n ∧
              ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) ∧
        (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
          ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
            ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ C / bracket n ∧
              ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n))
    (h14 :
        (∀ x₀ ∈ complexDomain 1 (by norm_num),
          ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
            U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
            ∀ x ∈ U, ∀ n : ℤ,
              ‖xiN38 n (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) ∧
        (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
          ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
            ‖xiN38 n (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n))
    (h17 :
        (∀ x₀ ∈ complexDomain 1 (by norm_num),
          ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
            U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
            ∀ x ∈ U, ∀ n : ℤ,
              deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n) ≠ 0 ∧
              ‖(deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n))⁻¹ - (-1 : ℂ)^n‖ ≤ C / bracket n) ∧
        (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
          ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
            deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n) ≠ 0 ∧
              ‖(deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n))⁻¹ - (-1 : ℂ)^n‖ ≤ C / bracket n))
    (h10 : ∀ φ ∈ sourceBetaW, ∀ n a : ℤ, (a = 1 ∨ a = -1) →
      deltaFactor n φ (muSeq φ n) ≠ 0 ∧
      sourceZ n a φ =
        ((tauN φ n - muSeq φ n) - (a : ℂ) * Complex.I *
          antiDiscrim φ (muSeq φ n) / (2 * deltaFactor n φ (muSeq φ n))) * eta n a φ)
    (hcp : ∀ (n : ℤ) (φ : PotPair), φ ∈ gkW → cartesianZExtended n 1 φ = gk16ActualScalarZPlus38 sourceF n φ)
    (hcm : ∀ (n : ℤ) (φ : PotPair), φ ∈ gkW → cartesianZExtended n (-1) φ = gk16ActualScalarZMinus38 sourceF n φ)
    (hmd : ∀ (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, NlsGge.ThirdConsultation.KSPS.sobolevNorm N φ ≤ B₀ →
          NlsGge.ThirdConsultation.KSPS.WeightedL2Error ((N + 1 : ℕ) : ℝ)
            (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - NlsGge.ThirdConsultation.KSPS.mu φ n +
              (physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 (-n) +
               physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 n) / 2) ∧
          ∀ F : Finset ℤ,
            (∑ n ∈ F,
              (NlsGge.ThirdConsultation.KSPS.indexWeight n ^ (N + 1) *
                ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - NlsGge.ThirdConsultation.KSPS.mu φ n +
                  (physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 (-n) +
                   physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 n) / 2‖)^2) ≤ C^2)
    (hat : ∀ (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, NlsGge.ThirdConsultation.KSPS.sobolevNorm N φ ≤ B₀ →
          NlsGge.ThirdConsultation.KSPS.WeightedL2Error ((N + 1 : ℕ) : ℝ)
            (fun n => NlsGge.ThirdConsultation.KSPSWKB.antitrace φ (NlsGge.ThirdConsultation.KSPS.mu φ n) -
              Complex.I * (-1 : ℂ)^n *
                (physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 (-n) -
                 physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 n)) ∧
          ∀ F : Finset ℤ,
            (∑ n ∈ F,
              (NlsGge.ThirdConsultation.KSPS.indexWeight n ^ (N + 1) *
                ‖NlsGge.ThirdConsultation.KSPSWKB.antitrace φ (NlsGge.ThirdConsultation.KSPS.mu φ n) -
                  Complex.I * (-1 : ℂ)^n *
                    (physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 (-n) -
                     physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 n)‖)^2) ≤ C^2) :
  (∀ x₀ ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
    ∃ (U : Set (PairScale (N : ℝ))) (C : ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ complexDomain (N : ℝ) (Nat.cast_nonneg N) ∧ 0 ≤ C ∧
      ∀ x ∈ U, Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
        ‖complexSmoothing N x‖ ≤ C) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale (N : ℝ), IsRealPair (N : ℝ) x → ‖x‖ ≤ B →
      Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
      ‖complexSmoothing N x‖ ≤ C) := by
  have hrem := fun H : ℝ => fun hH : 0 ≤ H => ksn018_remainders N H
    (hmd N hN (2 ^ N * H) (by positivity)) (hat N hN (2 ^ N * H) (by positivity))
  constructor
  · intro x₀ hx₀
    have hy₀ := ksn018_lower_mem_complexDomain N hN x₀ hx₀
    obtain ⟨U12, C12, hU12o, hy12, hU12s, hC12, hU12⟩ := h12.1 _ hy₀
    obtain ⟨U14, C14, hU14o, hy14, -, hC14, hU14⟩ := h14.1 _ hy₀
    obtain ⟨U17, C17, hU17o, hy17, -, hC17, hU17⟩ := h17.1 _ hy₀
    obtain ⟨CE1, CE2, hR⟩ := hrem (‖x₀‖ + 1) (by positivity)
    set K : ℝ := C12 + C14 + C17 with hKdef
    have hK : 0 ≤ K := by positivity
    have hb12 : C12 ≤ K := by linarith
    have hb14 : C14 ≤ K := by linarith
    have hb17 : C17 ≤ K := by linarith
    refine ⟨ksn018_lower N hN ⁻¹' (U12 ∩ U14 ∩ U17) ∩ ball x₀ 1,
      Real.sqrt (2 * ((4 * (1 + ((2 + Real.exp K) * K + K)) ^ 4 * (1 + ((2 + Real.exp K) * K + K))) ^ 2 *
        (((4 : ℕ) : ℝ) * ((‖x₀‖ + 1) ^ 2 + (‖x₀‖ + 1) ^ 2 + CE1 + CE2)))),
      (((hU12o.inter hU14o).inter hU17o).preimage (ksn018_lower N hN).continuous).inter isOpen_ball,
      ⟨⟨⟨hy12, hy14⟩, hy17⟩, mem_ball_self one_pos⟩, ?_, Real.sqrt_nonneg _, ?_⟩
    · intro x hx
      have h1 := hU12s hx.1.1.1
      show pairPotential (N : ℝ) (Nat.cast_nonneg N) x ∈ sourceBetaW
      rw [← ksn018_pairPotential_lower N hN x]; exact h1
    · intro x hx
      have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
        have h1 := norm_sub_norm_le x x₀
        have h2 := mem_ball_iff_norm.mp hx.2
        linarith
      have hS : pairPotential (N : ℝ) (Nat.cast_nonneg N) x ∈ sourceBetaW := by
        rw [← ksn018_pairPotential_lower N hN x]; exact hU12s hx.1.1.1
      have hW : pairPotential (N : ℝ) (Nat.cast_nonneg N) x ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hS)
      have hbr : ∀ n : ℤ, 0 < bracket n := fun n => lt_of_lt_of_le one_pos (le_max_left _ _)
      have mono : ∀ (C : ℝ) (n : ℤ), C ≤ K → C / bracket n ≤ K / bracket n := fun C n h =>
        div_le_div_of_nonneg_right h (hbr n).le
      exact ksn018_point N hN x K (‖x₀‖ + 1) CE1 CE2 hK hxn hS h10 hcp hcm (hR x hxn hW)
        (fun n => ⟨((hU12 _ hx.1.1.1 n).1).trans (mono _ n hb12),
          fun a ha => ((hU12 _ hx.1.1.1 n).2 a ha).trans (mono _ n hb12)⟩)
        (fun n => (hU14 _ hx.1.1.2 n).trans (mono _ n hb14))
        (fun n => ⟨(hU17 _ hx.1.2 n).1, (hU17 _ hx.1.2 n).2.trans (mono _ n hb17)⟩)
  · intro B hB
    obtain ⟨C12, hC12, h12B⟩ := h12.2 B hB
    obtain ⟨C14, hC14, h14B⟩ := h14.2 B hB
    obtain ⟨C17, hC17, h17B⟩ := h17.2 B hB
    obtain ⟨CE1, CE2, hR⟩ := hrem B hB
    set K : ℝ := C12 + C14 + C17 with hKdef
    have hK : 0 ≤ K := by positivity
    have hb12 : C12 ≤ K := by linarith
    have hb14 : C14 ≤ K := by linarith
    have hb17 : C17 ≤ K := by linarith
    refine ⟨Real.sqrt (2 * ((4 * (1 + ((2 + Real.exp K) * K + K)) ^ 4 * (1 + ((2 + Real.exp K) * K + K))) ^ 2 *
        (((4 : ℕ) : ℝ) * (B ^ 2 + B ^ 2 + CE1 + CE2)))), Real.sqrt_nonneg _, fun x hxr hx => ?_⟩
    have hyr := ksn018_lower_isRealPair N hN x hxr
    have hy := (ksn018_lower_norm_le N hN x).trans hx
    have hS : pairPotential (N : ℝ) (Nat.cast_nonneg N) x ∈ sourceBetaW := by
      rw [← ksn018_pairPotential_lower N hN x]; exact realPair_mem_sourceBetaW _ hyr
    have hW : pairPotential (N : ℝ) (Nat.cast_nonneg N) x ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hS)
    have hbr : ∀ n : ℤ, 0 < bracket n := fun n => lt_of_lt_of_le one_pos (le_max_left _ _)
    have mono : ∀ (C : ℝ) (n : ℤ), C ≤ K → C / bracket n ≤ K / bracket n := fun C n h =>
      div_le_div_of_nonneg_right h (hbr n).le
    exact ksn018_point N hN x K B CE1 CE2 hK hx hS h10 hcp hcm (hR x hx hW)
      (fun n => ⟨((h12B _ hyr hy n).1).trans (mono _ n hb12),
        fun a ha => ((h12B _ hyr hy n).2 a ha).trans (mono _ n hb12)⟩)
      (fun n => (h14B _ hyr hy n).trans (mono _ n hb14))
      (fun n => ⟨(h17B _ hyr hy n).1, (h17B _ hyr hy n).2.trans (mono _ n hb17)⟩)

end
end NlsGge.ThirdConsultation.KSN
