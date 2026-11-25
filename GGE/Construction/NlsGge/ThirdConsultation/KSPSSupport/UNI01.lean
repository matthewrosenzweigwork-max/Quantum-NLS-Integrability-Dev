import Mathlib
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.ThirdConsultation.KSPSSupport.EXP01
import NlsGge.ThirdConsultation.KSPSSupport
import NlsGge.ThirdConsultation.KSPSSupport.CORE01
import NlsGge.ThirdConsultation.KSPSSupport.RHO01
import NlsGge.ThirdConsultation.KSPSSupport.CLAUSES01
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.Atomic.G1.G1034
import NlsGge.NLS38.NonlinCarrier38

                                                                             
                                                                                                
                                                                                                                
                                                                                                     
                                                                                                 
                                                                                                             
                                                                                                     
                                                                                                   
                                                                                      
                                                                                  
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-- R3a: the Sobolev norm of the physical embedding is the carrier norm of the field. -/
theorem h161_psn_embed (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    physicalSobolevNorm (m : ℝ) (physicalSobolevEmbed m u) = ‖u‖ := by
  rw [psn_eq_hn]
  have hf : fourierSeq38 (physicalSobolevEmbed m u) =
      carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) := by
    funext n
    exact physicalSobolevEmbed_fourier m u n
  rw [hf, hn_coe38, LinearIsometryEquiv.norm_map]

/-- R3b: the pair norm of the toPotPair of a Sobolev field. -/
theorem h161_pair_toPotPair_norm (N : ℕ) (φ : SobolevC N) :
    pairSobolevNorm (N : ℝ) (toPotPair φ) = Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) := by
  unfold pairSobolevNorm
  show Real.sqrt (physicalSobolevNorm (N : ℝ) (physicalSobolevEmbed N φ.1) ^ 2 +
    physicalSobolevNorm (N : ℝ) (physicalSobolevEmbed N φ.2) ^ 2) = _
  rw [h161_psn_embed, h161_psn_embed]

/-- R3b (swap): the swapped pair has the same norm up to the order of the summands. -/
theorem h161_pair_swap_norm (N : ℕ) (φ : SobolevC N) :
    pairSobolevNorm (N : ℝ) (Prod.swap (toPotPair φ)) = Real.sqrt (‖φ.2‖ ^ 2 + ‖φ.1‖ ^ 2) := by
  unfold pairSobolevNorm
  show Real.sqrt (physicalSobolevNorm (N : ℝ) (physicalSobolevEmbed N φ.2) ^ 2 +
    physicalSobolevNorm (N : ℝ) (physicalSobolevEmbed N φ.1) ^ 2) = _
  rw [h161_psn_embed, h161_psn_embed]

theorem h161_sqrt_le_sum (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b := by
  calc Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((a + b) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg ha hb])
    _ = a + b := Real.sqrt_sq (by positivity)

theorem h161_pair_nonneg (N : ℕ) (φ : PotPair) :
    0 ≤ pairSobolevNorm (N : ℝ) φ :=
  Real.sqrt_nonneg _

theorem h161_pair_le (N : ℕ) (φ : SobolevC N) :
    pairSobolevNorm (N : ℝ) (toPotPair φ) ≤ ‖φ.1‖ + ‖φ.2‖ := by
  rw [h161_pair_toPotPair_norm]
  exact h161_sqrt_le_sum _ _ (norm_nonneg _) (norm_nonneg _)

theorem h161_pair_swap_le (N : ℕ) (φ : SobolevC N) :
    pairSobolevNorm (N : ℝ) (Prod.swap (toPotPair φ)) ≤ ‖φ.1‖ + ‖φ.2‖ := by
  rw [h161_pair_swap_norm]
  exact (h161_sqrt_le_sum _ _ (norm_nonneg _) (norm_nonneg _)).trans_eq (add_comm _ _)

/-- R3c: the ball of radius one has a uniform bound on the component norms. -/
theorem h161_ball_sum {N : ℕ} (φ ψ : SobolevC N) (h : ‖ψ - φ‖ < 1) :
    ‖ψ.1‖ + ‖ψ.2‖ ≤ ‖φ.1‖ + ‖φ.2‖ + 2 := by
  have h1 : ‖ψ.1 - φ.1‖ ≤ ‖ψ - φ‖ := by
    have := norm_fst_le (ψ - φ)
    simpa using this
  have h2 : ‖ψ.2 - φ.2‖ ≤ ‖ψ - φ‖ := by
    have := norm_snd_le (ψ - φ)
    simpa using this
  have h3 := norm_sub_norm_le ψ.1 φ.1
  have h4 := norm_sub_norm_le ψ.2 φ.2
  linarith

theorem h161_neg_one_pow_norm (k : ℕ) : ‖(-1 : ℂ) ^ k‖ = 1 := by
  simp

/-- Scalar multiples: the Sobolev norm scales by the modulus of the scalar. -/
theorem h161_psn_smul (m : ℕ) (c : ℂ) (u : PhysicalL2) :
    physicalSobolevNorm (m : ℝ) (c • u) = ‖c‖ * physicalSobolevNorm (m : ℝ) u := by
  rw [psn_eq_hn, psn_eq_hn]
  have hf : fourierSeq38 (c • u) = fun n => c * fourierSeq38 u n :=
    funext (fun n => fourierSeq38_smul38 c u n)
  rw [hf]
  unfold hn
  beta_reduce
  have key : ∑' n : ℤ, (japaneseBracket n) ^ (2 * m) * ‖c * fourierSeq38 u n‖ ^ 2 =
      ‖c‖ ^ 2 * ∑' n : ℤ, (japaneseBracket n) ^ (2 * m) * ‖fourierSeq38 u n‖ ^ 2 := by
    rw [← tsum_mul_left]
    congr 1
    funext n
    rw [norm_mul]
    ring
  rw [key, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The Sobolev norm of the zero field vanishes. -/
theorem h161_psn_zero (m : ℕ) : physicalSobolevNorm (m : ℝ) (0 : PhysicalL2) = 0 := by
  have h := h161_psn_smul m 0 0
  simpa using h

/-- R3b (embedding): index-1 membership and norm bound of a physical embedding. -/
theorem h161_embed_psn1 (N : ℕ) (hN : 1 ≤ N) (u : PhysicalSobolev38 (N : ℝ)) :
    physicalSobolev 1 (physicalSobolevEmbed N u) ∧
      physicalSobolevNorm 1 (physicalSobolevEmbed N u) ≤ ‖u‖ := by
  have h := psn_mono (m := 1) (m' := N) hN (physicalSobolevEmbed_mem N u)
  rw [h161_psn_embed] at h
  simp only [Nat.cast_one] at h
  exact h

/-- Side potential: index-1 membership and norm bound by the component norms. -/
theorem h161_side_psn1 {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) :
    physicalSobolev 1 (KSPSRiccati.sidePotential φ b) ∧
      physicalSobolevNorm 1 (KSPSRiccati.sidePotential φ b) ≤ ‖φ.1‖ + ‖φ.2‖ := by
  cases b
  · show physicalSobolev 1 (physicalSobolevEmbed N φ.1) ∧
      physicalSobolevNorm 1 (physicalSobolevEmbed N φ.1) ≤ ‖φ.1‖ + ‖φ.2‖
    exact ⟨(h161_embed_psn1 N hN φ.1).1,
      by linarith [(h161_embed_psn1 N hN φ.1).2, norm_nonneg φ.2]⟩
  · show physicalSobolev 1 (physicalSobolevEmbed N φ.2) ∧
      physicalSobolevNorm 1 (physicalSobolevEmbed N φ.2) ≤ ‖φ.1‖ + ‖φ.2‖
    exact ⟨(h161_embed_psn1 N hN φ.2).1,
      by linarith [(h161_embed_psn1 N hN φ.2).2, norm_nonneg φ.1]⟩

/-- Sums of finitely many fields with a common index-1 bound. -/
theorem h161_sum_bound {ι : Type*} (s : Finset ι) (f : ι → PhysicalL2) (T : ℝ)
    (hf : ∀ i ∈ s, physicalSobolev 1 (f i) ∧ physicalSobolevNorm 1 (f i) ≤ T) :
    physicalSobolev 1 (∑ i ∈ s, f i) ∧
      physicalSobolevNorm 1 (∑ i ∈ s, f i) ≤ (s.card : ℝ) * T := by
  have h := psn_sum 1 s f (fun i hi => by simpa using (hf i hi).1)
  simp only [Nat.cast_one] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have h2 := Finset.sum_le_card_nsmul s (fun i => physicalSobolevNorm 1 (f i)) T
    (fun i hi => (hf i hi).2)
  rw [nsmul_eq_mul] at h2
  exact h2

/-- R3d: the order-k coefficients for k in [1,N], both sides, are bounded on the ball. -/
theorem h161_coef_low (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ψ : SobolevC N, ‖ψ.1‖ + ‖ψ.2‖ ≤ K → ∀ (b : Bool) (k : ℕ),
      1 ≤ k → k ≤ N →
      physicalSobolevNorm ((N + 1 - k : ℕ) : ℝ) (KSPSRiccati.coefficient ψ b k) ≤ D := by
  obtain ⟨C0, hC0, p0, hG⟩ := G1_034 N hN
  refine ⟨C0 * (1 + K) ^ p0, by positivity, fun ψ hS b k hk1 hkN => ?_⟩
  have hpair : pairSobolevNorm (N : ℝ) (toPotPair ψ) ≤ K := (h161_pair_le N ψ).trans hS
  have hpairS : pairSobolevNorm (N : ℝ) (Prod.swap (toPotPair ψ)) ≤ K :=
    (h161_pair_swap_le N ψ).trans hS
  have hpow : ∀ x : ℝ, 0 ≤ x → x ≤ K → C0 * (1 + x) ^ p0 ≤ C0 * (1 + K) ^ p0 := by
    intro x hx0 hxK
    apply mul_le_mul_of_nonneg_left _ hC0.le
    have hle : 1 + x ≤ 1 + K := by linarith
    exact pow_le_pow_left₀ (by linarith) hle p0
  cases b
  · have hA := (hG (toPotPair ψ) (pairSobolev_toPotPair ψ)).2.2.1 k hk1 hkN
    rw [h150_coef_false]
    exact hA.2.trans (hpow _ (h161_pair_nonneg N _) hpair)
  · have hA := (hG (Prod.swap (toPotPair ψ)) (pairSobolev_swap_toPotPair ψ)).2.2.1 k hk1 hkN
    rw [h150_coef_true, h161_psn_smul, h161_neg_one_pow_norm, one_mul]
    exact hA.2.trans (hpow _ (h161_pair_nonneg N _) hpairS)

/-- R3d (H1 form): the coefficients for k in [1,N] lie in H1 with a uniform bound on the ball. -/
theorem h161_coef_H1 (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ψ : SobolevC N, ‖ψ.1‖ + ‖ψ.2‖ ≤ K → ∀ (b : Bool) (k : ℕ),
      1 ≤ k → k ≤ N →
      physicalSobolev 1 (KSPSRiccati.coefficient ψ b k) ∧
        physicalSobolevNorm 1 (KSPSRiccati.coefficient ψ b k) ≤ D := by
  obtain ⟨D, hD, hL⟩ := h161_coef_low N hN K hK
  refine ⟨D, hD, fun ψ hS b k hk1 hkN => ?_⟩
  have hm := h150_coef_mem_le N hN ψ b k hk1 hkN
  have h := psn_mono (m := 1) (m' := N + 1 - k) (by omega) hm
  simp only [Nat.cast_one] at h
  exact ⟨h.1, h.2.trans (hL ψ hS b k hk1 hkN)⟩

/-- Nonnegativity of the index-1 norm. -/
theorem h161_psn_nonneg1 (u : PhysicalL2) : 0 ≤ physicalSobolevNorm 1 u := by
  have h := psn_nonneg 1 u
  simpa using h

/-- Zero field has zero index-1 norm. -/
theorem h161_psn1_zero : physicalSobolevNorm 1 (0 : PhysicalL2) = 0 := by
  simpa using h161_psn_zero 1

/-- Index-1 membership and norm give index-0 membership and the index-0 norm bound. -/
theorem h161_index0_of1 (u : PhysicalL2) (hu : physicalSobolev 1 u) :
    physicalSobolev 0 u ∧ physicalSobolevNorm 0 u ≤ physicalSobolevNorm 1 u := by
  have h := psn_mono (m := 0) (m' := 1) (Nat.zero_le 1) (u := u) (by simpa using hu)
  simpa using h

/-- A product constant: the H1 product bound of psn_prod, with the constant named. -/
def h161_ProdBound (C : ℝ) : Prop :=
  ∀ (u v : PhysicalL2) (A B : ℝ), 0 ≤ A → 0 ≤ B →
    physicalSobolev 1 u → physicalSobolevNorm 1 u ≤ A →
    physicalSobolev 1 v → physicalSobolevNorm 1 v ≤ B →
    physicalSobolev 1 (physicalProduct u v) ∧
      physicalSobolevNorm 1 (physicalProduct u v) ≤ C * A * B

theorem h161_prod_bound : ∃ C : ℝ, 0 ≤ C ∧ h161_ProdBound C := by
  obtain ⟨C, hC, h⟩ := psn_prod 1 le_rfl
  simp only [Nat.cast_one] at h
  refine ⟨C, hC.le, ?_⟩
  unfold h161_ProdBound
  intro u v A B hA hB hu huA hv hvB
  obtain ⟨hp1, hp2⟩ := h u v hu hv
  refine ⟨hp1, hp2.trans ?_⟩
  have hvn := h161_psn_nonneg1 v
  calc C * physicalSobolevNorm 1 u * physicalSobolevNorm 1 v
      ≤ C * A * physicalSobolevNorm 1 v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huA hC.le) hvn
    _ ≤ C * A * B := mul_le_mul_of_nonneg_left hvB (mul_nonneg hC.le hA)

/-- Derivative term: signedDerivative of an H1 field is in L2 with the index-0 bound. -/
theorem h161_deriv_bound (D : ℝ) (hD : 0 ≤ D) (b : Bool) (f : PhysicalL2)
    (hf : physicalSobolev 1 f) (hfD : physicalSobolevNorm 1 f ≤ D) :
    physicalSobolev 0 (KSPSRiccati.signedDerivative b f) ∧
      physicalSobolevNorm 0 (KSPSRiccati.signedDerivative b f) ≤ 2 * Real.pi * D := by
  have hd := psn_deriv 0 (u := f) (by simpa using hf)
  simp only [Nat.cast_zero, zero_add, Nat.cast_one] at hd
  have hbound : physicalSobolevNorm 0 (weakDerivative f) ≤ 2 * Real.pi * D :=
    hd.2.trans (mul_le_mul_of_nonneg_left hfD (by positivity))
  cases b
  · show physicalSobolev 0 (weakDerivative f) ∧ physicalSobolevNorm 0 (weakDerivative f) ≤ _
    exact ⟨hd.1, hbound⟩
  · show physicalSobolev 0 (-weakDerivative f) ∧ physicalSobolevNorm 0 (-weakDerivative f) ≤ _
    have hw : physicalSobolev ((0 : ℕ) : ℝ) (weakDerivative f) := by simpa using hd.1
    have hn := (psn_neg 0 hw).2
    simp only [Nat.cast_zero] at hn
    refine ⟨?_, by rw [hn]; exact hbound⟩
    have hneg := (psn_neg 0 hw).1
    simpa using hneg

/-- Recurrence product at order N: its H1 norm, with the product constant. -/
theorem h161_rec_bound (N : ℕ) (hN : 1 ≤ N) (C : ℝ) (hC : 0 ≤ C) (hCp : h161_ProdBound C)
    (D1 : ℝ) (hD1 : 0 ≤ D1) (ψ : SobolevC N) (b : Bool)
    (hH1 : ∀ k : ℕ, 1 ≤ k → k ≤ N → physicalSobolev 1 (KSPSRiccati.coefficient ψ b k) ∧
      physicalSobolevNorm 1 (KSPSRiccati.coefficient ψ b k) ≤ D1) :
    physicalSobolev 1 (KSPSRiccati.recurrenceProduct ψ b N) ∧
      physicalSobolevNorm 1 (KSPSRiccati.recurrenceProduct ψ b N) ≤
        (N : ℝ) * (C * (D1 * D1)) := by
  have hT0 : 0 ≤ C * (D1 * D1) := mul_nonneg hC (mul_nonneg hD1 hD1)
  have hc : (Finset.Icc 1 (N - 1)).card ≤ N := by
    rw [Nat.card_Icc]
    omega
  have hsum := h161_sum_bound (Finset.Icc 1 (N - 1))
    (fun j => physicalProduct (KSPSRiccati.coefficient ψ b j)
      (KSPSRiccati.coefficient ψ b (N - j))) (C * (D1 * D1)) (by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
      have hA := hH1 j hj1 (by omega)
      have hB' := hH1 (N - j) (by omega) (by omega)
      obtain ⟨hp1, hp2⟩ := hCp _ _ D1 D1 hD1 hD1 hA.1 hA.2 hB'.1 hB'.2
      exact ⟨hp1, hp2.trans (le_of_eq (mul_assoc _ _ _))⟩)
  unfold KSPSRiccati.recurrenceProduct
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hT0

/-- The side potential times the recurrence product at order N, in L2 with the bound. -/
theorem h161_side_rec_bound (N : ℕ) (hN : 1 ≤ N) (C : ℝ) (hC : 0 ≤ C)
    (hCp : h161_ProdBound C) (K : ℝ) (hK : 0 ≤ K) (D1 : ℝ) (hD1 : 0 ≤ D1)
    (ψ : SobolevC N) (b : Bool) (hS : ‖ψ.1‖ + ‖ψ.2‖ ≤ K)
    (hH1 : ∀ k : ℕ, 1 ≤ k → k ≤ N → physicalSobolev 1 (KSPSRiccati.coefficient ψ b k) ∧
      physicalSobolevNorm 1 (KSPSRiccati.coefficient ψ b k) ≤ D1) :
    physicalSobolev 0 (physicalProduct (KSPSRiccati.sidePotential ψ b)
        (KSPSRiccati.recurrenceProduct ψ b N)) ∧
      physicalSobolevNorm 0 (physicalProduct (KSPSRiccati.sidePotential ψ b)
        (KSPSRiccati.recurrenceProduct ψ b N)) ≤ C * K * ((N : ℝ) * (C * (D1 * D1))) := by
  have hSide := h161_side_psn1 hN ψ b
  have hR := h161_rec_bound N hN C hC hCp D1 hD1 ψ b hH1
  have hT0 : 0 ≤ (N : ℝ) * (C * (D1 * D1)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC (mul_nonneg hD1 hD1))
  have hp := hCp _ _ K ((N : ℝ) * (C * (D1 * D1))) hK hT0 hSide.1 (hSide.2.trans hS) hR.1 hR.2
  have hm := h161_index0_of1 _ hp.1
  exact ⟨hm.1, hm.2.trans hp.2⟩

/-- R3e: the order-(N+1) coefficient is in L2 on the ball, through the recursion. -/
theorem h161_coef_top (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ψ : SobolevC N, ‖ψ.1‖ + ‖ψ.2‖ ≤ K → ∀ b : Bool,
      physicalSobolevNorm ((N + 1 - (N + 1) : ℕ) : ℝ)
        (KSPSRiccati.coefficient ψ b (N + 1)) ≤ D := by
  obtain ⟨D1, hD1, hH1⟩ := h161_coef_H1 N hN K hK
  obtain ⟨C, hC, hCp⟩ := h161_prod_bound
  have hT0 : 0 ≤ C * K * ((N : ℝ) * (C * (D1 * D1))) :=
    mul_nonneg (mul_nonneg hC hK) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC (mul_nonneg hD1 hD1)))
  refine ⟨2 * Real.pi * D1 + C * K * ((N : ℝ) * (C * (D1 * D1))),
    add_nonneg (mul_nonneg (by positivity) hD1) hT0, fun ψ hS b => ?_⟩
  rw [Nat.sub_self, Nat.cast_zero]
  have hB := hH1 ψ hS b N hN le_rfl
  have hX1 := h161_deriv_bound D1 hD1 b (KSPSRiccati.coefficient ψ b N) hB.1 hB.2
  have hX2 := h161_side_rec_bound N hN C hC hCp K hK D1 hD1 ψ b hS
    (fun k hk1 hk2 => hH1 ψ hS b k hk1 hk2)
  have hC3 := h150_C3 hN ψ b N hN le_rfl
  have hsum := psn_add (u := KSPSRiccati.signedDerivative b (KSPSRiccati.coefficient ψ b N))
    (v := physicalProduct (KSPSRiccati.sidePotential ψ b)
      (KSPSRiccati.recurrenceProduct ψ b N)) 0
    (by simpa using hX1.1) (by simpa using hX2.1)
  simp only [Nat.cast_zero] at hsum
  rw [hC3.2.2]
  exact hsum.2.trans (add_le_add hX1.2 hX2.2)

/-- R3 (quadratic): every quadratic term is uniformly in H1 on the ball, for all j. -/
theorem h161_quad_H1 (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ψ : SobolevC N, ‖ψ.1‖ + ‖ψ.2‖ ≤ K → ∀ (b : Bool) (j : ℕ),
      physicalSobolevNorm 1 (KSPSRiccati.quadratic ψ b j) ≤ D := by
  obtain ⟨D1, hD1, hH1⟩ := h161_coef_H1 N hN K hK
  obtain ⟨Cpr, hCpr, hpr⟩ := h161_prod_bound
  unfold h161_ProdBound at hpr
  have hT : 0 ≤ Cpr * D1 * D1 := mul_nonneg (mul_nonneg hCpr hD1) hD1
  have hcard : ((Finset.Icc 1 N).card : ℝ) = N := by simp
  refine ⟨Cpr * K * ((N : ℝ) * ((N : ℝ) * (Cpr * D1 * D1))), ?_, fun ψ hS b j => ?_⟩
  · exact mul_nonneg (mul_nonneg hCpr hK)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hT))
  · have hinner : ∀ k ∈ Finset.Icc 1 N,
        physicalSobolev 1 (∑ l ∈ Finset.Icc 1 N,
          if k + l = j then physicalProduct (KSPSRiccati.coefficient ψ b k)
            (KSPSRiccati.coefficient ψ b l) else 0) ∧
        physicalSobolevNorm 1 (∑ l ∈ Finset.Icc 1 N,
          if k + l = j then physicalProduct (KSPSRiccati.coefficient ψ b k)
            (KSPSRiccati.coefficient ψ b l) else 0) ≤ (N : ℝ) * (Cpr * D1 * D1) := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
      have h1 := h161_sum_bound (Finset.Icc 1 N)
        (fun l => if k + l = j then physicalProduct (KSPSRiccati.coefficient ψ b k)
          (KSPSRiccati.coefficient ψ b l) else 0) (Cpr * D1 * D1) (by
          intro l hl
          obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.1 hl
          by_cases h : k + l = j
          · simp only [if_pos h]
            exact hpr _ _ D1 D1 hD1 hD1 (hH1 ψ hS b k hk1 hk2).1 (hH1 ψ hS b k hk1 hk2).2
              (hH1 ψ hS b l hl1 hl2).1 (hH1 ψ hS b l hl1 hl2).2
          · simp only [if_neg h]
            exact ⟨h150_zero_mem 1, by rw [h161_psn1_zero]; exact hT⟩)
      rw [hcard] at h1
      exact h1
    have hout := h161_sum_bound (Finset.Icc 1 N)
      (fun k => ∑ l ∈ Finset.Icc 1 N,
        if k + l = j then physicalProduct (KSPSRiccati.coefficient ψ b k)
          (KSPSRiccati.coefficient ψ b l) else 0) ((N : ℝ) * (Cpr * D1 * D1)) hinner
    rw [hcard] at hout
    unfold KSPSRiccati.quadratic
    have hB : 0 ≤ (N : ℝ) * ((N : ℝ) * (Cpr * D1 * D1)) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hT)
    exact (hpr _ _ K ((N : ℝ) * ((N : ℝ) * (Cpr * D1 * D1))) hK hB
      (h161_side_psn1 hN ψ b).1 ((h161_side_psn1 hN ψ b).2.trans hS) hout.1 hout.2).2

/-- R3f: the combined uniform coefficient clause on the ball (both sides, every k in [1,N+1]). -/
theorem h161_coef_uniform (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ψ : SobolevC N, ‖ψ.1‖ + ‖ψ.2‖ ≤ K → ∀ (b : Bool) (k : ℕ),
      1 ≤ k → k ≤ N + 1 →
      physicalSobolev ((N + 1 - k : ℕ) : ℝ) (KSPSRiccati.coefficient ψ b k) ∧
        physicalSobolevNorm ((N + 1 - k : ℕ) : ℝ) (KSPSRiccati.coefficient ψ b k) ≤ D := by
  obtain ⟨D1, hD1, hL⟩ := h161_coef_low N hN K hK
  obtain ⟨D2, hD2, hT⟩ := h161_coef_top N hN K hK
  refine ⟨D1 + D2, add_nonneg hD1 hD2, fun ψ hS b k hk1 hk2 => ?_⟩
  refine ⟨h150_coef_mem N hN ψ b k hk1 hk2, ?_⟩
  by_cases hk : k = N + 1
  · subst hk
    have := hT ψ hS b
    linarith
  · have := hL ψ hS b k hk1 (by omega)
    linarith

end
end NlsGge.ThirdConsultation.KSPSSupport
