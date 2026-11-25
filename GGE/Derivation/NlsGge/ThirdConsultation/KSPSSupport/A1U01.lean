import Mathlib
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.ThirdConsultation.KSPSSupport.EXP01
import NlsGge.ThirdConsultation.KSPSSupport.UNI01
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.KSPSSupport
import NlsGge.ThirdConsultation.KSPSSupport.CORE01
import NlsGge.ThirdConsultation.KSPSSupport.ANA01

/- KSPS-010 supporting module R4 = A1U01 (proof development, AUTHOR; not reviewed).
   Uniform L2 bound of a1 on the ball: eLpNorm (a1 psi b) 2 intervalMeasure <= ofReal Ca.
   a1 = coverRep(quadratic(N+1)) + sigma coverRep(coefficient(N+1)) massPrefix (definition),
   with |massPrefix| <= K^2 on [0,1] (R1 prefix bound and the embedding norm bound),
   the quadratic in H1 uniformly (R3 h161_quad_H1) and the order-(N+1) coefficient in L2 (R3 h161_coef_top).
   Helpers: h161_norm_eq_psn0 (L2 norm equals index-0 Sobolev norm; the proof of g35_psn_zero, copied),
   h161_L2_le_psn1, h161_embed_norm_le, h161_intervalIntegrable_sq (from MemLp). -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-- The L2 norm of a physical field is its index-0 Sobolev norm (proof of g35_psn_zero). -/
theorem h161_norm_eq_psn0 (u : PhysicalL2) : physicalSobolevNorm 0 u = ‖u‖ := by
  have h : physicalSobolevNorm ((0 : ℕ) : ℝ) u = ‖u‖ := by
    have h0 := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) (reflectedFourierL2 u)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h0
    rw [← reflectedFourierL2.norm_map u, ← Real.sqrt_sq (norm_nonneg (reflectedFourierL2 u)), h0]
    unfold physicalSobolevNorm
    congr 1
    refine tsum_congr (fun n => ?_)
    simp
  simpa using h

/-- Index-0 norm is at most the index-1 norm. -/
theorem h161_L2_le_psn1 (u : PhysicalL2) (hu : physicalSobolev 1 u) :
    ‖u‖ ≤ physicalSobolevNorm 1 u := by
  rw [← h161_norm_eq_psn0]
  exact (h161_index0_of1 u hu).2

/-- The L2 norm of the physical embedding is at most the carrier norm. -/
theorem h161_embed_norm_le (N : ℕ) (u : PhysicalSobolev38 (N : ℝ)) :
    ‖physicalSobolevEmbed N u‖ ≤ ‖u‖ := by
  rw [← h161_norm_eq_psn0]
  have h := psn_mono (m := 0) (m' := N) (Nat.zero_le N) (physicalSobolevEmbed_mem N u)
  rw [h161_psn_embed] at h
  simpa using h.2

/-- The square of the norm of an L2-on-[0,1] function is interval integrable. -/
theorem h161_intervalIntegrable_sq (f : ℝ → ℂ) (hf : MemLp f 2 KSPSRiccati.intervalMeasure) :
    IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 1 := by
  have h := hf.norm.integrable_sq
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
  unfold KSPSRiccati.intervalMeasure at h
  exact h

/-- Massprefix on the ball and the unit interval. -/
theorem h161_massPrefix_ball {N : ℕ} (ψ : SobolevC N) (K : ℝ) (hS : ‖ψ.1‖ + ‖ψ.2‖ ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖KSPSRiccati.massPrefix ψ t‖ ≤ K ^ 2 := by
  have h := h161_massPrefix_bound ψ ht
  have ha : ‖(toPotPair ψ).1‖ ≤ K :=
    (h161_embed_norm_le N ψ.1).trans (by linarith [norm_nonneg ψ.2])
  have hb : ‖(toPotPair ψ).2‖ ≤ K :=
    (h161_embed_norm_le N ψ.2).trans (by linarith [norm_nonneg ψ.1])
  nlinarith [norm_nonneg (toPotPair ψ).1, norm_nonneg (toPotPair ψ).2]

/-- Pointwise square bound for a1 with the mass prefix bounded by K^2. -/
theorem h161_a1_sq_pointwise {N : ℕ} (ψ : SobolevC N) (b : Bool) (t K : ℝ)
    (hm : ‖KSPSRiccati.massPrefix ψ t‖ ≤ K ^ 2) :
    ‖KSPSRiccati.a1 ψ b t‖ ^ 2 ≤
      2 * ‖coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) t‖ ^ 2 +
        2 * K ^ 4 * ‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ ^ 2 := by
  unfold KSPSRiccati.a1
  set q := coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) t with hq
  set c := coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t with hc
  set m := KSPSRiccati.massPrefix ψ t with hmdef
  have hσ : ‖(if b then (1 : ℂ) else -1)‖ = 1 := by
    cases b <;> simp
  have h1 : ‖q + (if b then (1 : ℂ) else -1) * c * m‖ ≤ ‖q‖ + ‖c‖ * K ^ 2 := by
    calc ‖q + (if b then (1 : ℂ) else -1) * c * m‖
        ≤ ‖q‖ + ‖(if b then (1 : ℂ) else -1) * c * m‖ := norm_add_le _ _
      _ = ‖q‖ + ‖c‖ * ‖m‖ := by rw [norm_mul, norm_mul, hσ, one_mul]
      _ ≤ ‖q‖ + ‖c‖ * K ^ 2 := by gcongr
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖q‖ - ‖c‖ * K ^ 2), h2]

/-- R4: the uniform L2 bound of a1 on the ball, for both sides. -/
theorem h161_a1_uniform (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ ψ : SobolevC N, ‖ψ.1‖ + ‖ψ.2‖ ≤ K → ∀ b : Bool,
      MemLp (KSPSRiccati.a1 ψ b) 2 KSPSRiccati.intervalMeasure ∧
      eLpNorm (KSPSRiccati.a1 ψ b) 2 KSPSRiccati.intervalMeasure ≤
        ENNReal.ofReal Ca := by
  obtain ⟨Dq, hDq, hQ⟩ := h161_quad_H1 N hN K hK
  obtain ⟨Dc, hDc, hC⟩ := h161_coef_top N hN K hK
  have hCa0 : 0 ≤ 2 * (Dq + K ^ 2 * Dc) :=
    mul_nonneg (by norm_num) (add_nonneg hDq (mul_nonneg (sq_nonneg K) hDc))
  refine ⟨2 * (Dq + K ^ 2 * Dc), hCa0, fun ψ hS b => ?_⟩
  have hmem := h150_a1_memLp ψ b
  refine ⟨hmem, ?_⟩
  apply h161_eLp2_le _ hmem _ hCa0
  -- the quadratic and the top coefficient, in L2
  have hQn : ‖KSPSRiccati.quadratic ψ b (N + 1)‖ ≤ Dq :=
    (h161_L2_le_psn1 _ (quadratic_H1 ψ b (N + 1) hN)).trans (hQ ψ hS b (N + 1))
  have hCn : ‖KSPSRiccati.coefficient ψ b (N + 1)‖ ≤ Dc := by
    have h := hC ψ hS b
    rw [Nat.sub_self, Nat.cast_zero, h161_norm_eq_psn0] at h
    exact h
  have hQ2 : ‖KSPSRiccati.quadratic ψ b (N + 1)‖ ^ 2 ≤ Dq ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hQn 2
  have hC2 : ‖KSPSRiccati.coefficient ψ b (N + 1)‖ ^ 2 ≤ Dc ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hCn 2
  have hint1 := h161_intervalIntegrable_sq _ hmem
  have hint2 := intervalIntegrable_coverRep38_sq_one (KSPSRiccati.quadratic ψ b (N + 1))
  have hint3 := intervalIntegrable_coverRep38_sq_one (KSPSRiccati.coefficient ψ b (N + 1))
  have hint4 : IntervalIntegrable (fun t =>
      2 * ‖coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) t‖ ^ 2 +
        2 * K ^ 4 * ‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ ^ 2) volume 0 1 :=
    (hint2.const_mul 2).add (hint3.const_mul _)
  have hmono : ∫ t in (0 : ℝ)..1, ‖KSPSRiccati.a1 ψ b t‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, (2 * ‖coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) t‖ ^ 2 +
        2 * K ^ 4 * ‖coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) t‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on zero_le_one hint1 hint4
    intro t ht
    exact h161_a1_sq_pointwise ψ b t K
      (h161_massPrefix_ball ψ K hS ⟨ht.1, ht.2⟩)
  rw [intervalIntegral.integral_add (hint2.const_mul 2) (hint3.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sq_coverRep38_one, integral_sq_coverRep38_one] at hmono
  have hK4 : 0 ≤ 2 * K ^ 4 := by positivity
  have hfin : 2 * ‖KSPSRiccati.quadratic ψ b (N + 1)‖ ^ 2 +
      2 * K ^ 4 * ‖KSPSRiccati.coefficient ψ b (N + 1)‖ ^ 2 ≤
        (2 * (Dq + K ^ 2 * Dc)) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hC2 hK4, mul_nonneg hDq (mul_nonneg (sq_nonneg K) hDc),
      mul_le_mul_of_nonneg_left hQ2 (by norm_num : (0 : ℝ) ≤ 2), sq_nonneg (K ^ 2 * Dc)]
  linarith

end
end NlsGge.ThirdConsultation.KSPSSupport
