import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.WkbStructure
import NlsGge.ThirdConsultation.G1.Wkb035A
import NlsGge.Atomic.G1.G1034
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.ThirdConsultation.KSPSSupport
import NlsGge.ThirdConsultation.KSPSSupport.CORE01

/- KSPS-010 RHO01 (proof development, AUTHOR; not reviewed).
   S6: rho phi b lam = rhoTail phi b lam for lam ≠ 0, both sides.
   Left side: definitional identification with wkbResidual, S5 (g35_identity_ne) for wkbResidual = tail,
   then a finite reindexing of the tail (the k+m = N terms are moved into the top weak derivative through the
   G1 recurrence at n = N). Right side: the signed swap gives partial true lam = -(wkbPartial (-lam) swap),
   hence rho true lam = wkbResidual (-lam) swap, and rhoTail true lam = rhoTail-form of the swap at -lam. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-! Sign and scalar identities for the inverse powers of 2 i lam. -/

theorem h150_neg_one_pow_inv (k : ℕ) : ((-1 : ℂ) ^ k)⁻¹ = (-1 : ℂ) ^ k := by
  rw [← inv_pow, inv_neg, inv_one]

theorem h150_neg_inv_pow (x : ℂ) (k : ℕ) : ((-x) ^ k)⁻¹ = (-1 : ℂ) ^ k * (x ^ k)⁻¹ := by
  rw [neg_pow, mul_inv, h150_neg_one_pow_inv]

theorem h150_neg_arg (lam : ℂ) : 2 * Complex.I * (-lam) = -(2 * Complex.I * lam) := by ring

theorem h150_sign_pair (k m j : ℕ) (h : k + m = j) :
    (-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ (m + 1) = (-1 : ℂ) ^ j := by
  rw [← pow_add, show k + 1 + (m + 1) = j + 2 by omega, pow_add]
  norm_num

/-! Membership and H^1 facts for the pair attached to φ and for the WKB sequences. -/

theorem h150_fst_H1 (N : ℕ) (hN : 1 ≤ N) (p : PotPair) (hp : pairSobolev (N : ℝ) p) :
    physicalSobolev 1 p.1 := by
  obtain ⟨h1, _⟩ := hp
  exact g35_H1_nat _ (psn_mono hN h1).1

theorem h150_wkbR_H1 (N : ℕ) (hN : 1 ≤ N) (p : PotPair) (hp : pairSobolev (N : ℝ) p)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    physicalSobolev 1 (wkbR p k) := by
  obtain ⟨_, _, _, h⟩ := G1_034 N hN
  exact g35_H1_nat _ (psn_mono (show 1 ≤ N + 1 - k by omega) ((h p hp).2.2.1 k hk1 hkN).1).1

/-- S5 use: the left residual equals its finite tail (for every nonzero spectral parameter). -/
theorem h150_residual_tail (N : ℕ) (hN : 1 ≤ N) (p : PotPair) (hp : pairSobolev (N : ℝ) p)
    (l : ℂ) (hl : l ≠ 0) :
    wkbResidual N l p = wkbResidualTail N l p := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact g35_identity_ne M p l hl (fun k hk1 hkN => h150_wkbR_H1 (M + 1) hN p hp k hk1 hkN)
    (h150_fst_H1 (M + 1) hN p hp)

/-! Finite reindexing. -/

/-- A finite sum of products with a fixed H^1 first factor distributes over the summation. -/
theorem h150_P_dsum (u : PhysicalL2) (hu : physicalSobolev 1 u) (W : ℕ → PhysicalL2)
    (s : Finset ℕ) (j : ℕ) :
    physicalProduct u (∑ k ∈ s, ∑ m ∈ s, if k + m = j then physicalProduct (W k) (W m) else 0) =
      ∑ k ∈ s, ∑ m ∈ s, if k + m = j then physicalProduct u (physicalProduct (W k) (W m)) else 0 := by
  rw [g35_P_sum_right u hu]
  apply Finset.sum_congr rfl
  intro k _
  rw [g35_P_sum_right u hu]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs
  · rfl
  · exact physicalProduct_zero' u

/-- The anti-diagonal k + m = N over [1,N]^2 reduces to the one-variable sum over [1,N-1]. -/
theorem h150_antidiag_W (N : ℕ) (hN : 1 ≤ N) (W : ℕ → PhysicalL2) :
    ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (if k + m = N then physicalProduct (W k) (W m) else 0) =
      ∑ k ∈ Finset.Icc 1 (N - 1), physicalProduct (W k) (W (N - k)) := by
  have hin : ∀ k ∈ Finset.Icc 1 N,
      (∑ m ∈ Finset.Icc 1 N, (if k + m = N then physicalProduct (W k) (W m) else 0)) =
        if k < N then physicalProduct (W k) (W (N - k)) else 0 := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    by_cases hlt : k < N
    · rw [if_pos hlt, Finset.sum_eq_single (N - k)]
      · rw [if_pos (show k + (N - k) = N by omega)]
      · intro m _ hm
        rw [if_neg (show ¬ (k + m = N) by omega)]
      · intro h
        exact absurd (Finset.mem_Icc.2 ⟨show 1 ≤ N - k by omega, show N - k ≤ N by omega⟩) h
    · rw [if_neg hlt]
      apply Finset.sum_eq_zero
      intro m hm
      obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.1 hm
      rw [if_neg (show ¬ (k + m = N) by omega)]
  rw [Finset.sum_congr rfl hin]
  have h2 : ∑ k ∈ Finset.Icc 1 N, (if k < N then physicalProduct (W k) (W (N - k)) else 0) =
      ∑ k ∈ Finset.Icc 1 (N - 1), (if k < N then physicalProduct (W k) (W (N - k)) else 0) := by
    symm
    apply Finset.sum_subset
    · intro x hx
      obtain ⟨h1, _⟩ := Finset.mem_Icc.1 hx
      exact Finset.mem_Icc.2 ⟨h1, by omega⟩
    · intro x hx hnot
      obtain ⟨h1, _⟩ := Finset.mem_Icc.1 hx
      rw [if_neg]
      intro h
      exact hnot (Finset.mem_Icc.2 ⟨h1, by omega⟩)
  rw [h2]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
  rw [if_pos (show k < N by omega)]

/-- Pointwise splitting of the tail threshold N <= k+m into N+1 <= k+m and k+m = N. -/
theorem h150_tail_split (N : ℕ) (T : ℕ → ℕ → PhysicalL2) (c : ℕ → ℂ) :
    ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (if N ≤ k + m then c (k + m) • T k m else 0) =
      ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (if N + 1 ≤ k + m then c (k + m) • T k m else 0) +
      c N • ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, (if k + m = N then T k m else 0) := by
  simp only [Finset.smul_sum, smul_ite, smul_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h1 : N + 1 ≤ k + m
  · rw [if_pos (show N ≤ k + m by omega), if_pos h1,
      if_neg (show ¬ (k + m = N) by omega), add_zero]
  · by_cases h2 : k + m = N
    · rw [if_pos (show N ≤ k + m by omega), if_neg h1, if_pos h2, zero_add, h2]
    · rw [if_neg (show ¬ (N ≤ k + m) by omega), if_neg h1, if_neg h2, add_zero]

/-- The quadratic tail in the rhoTail form, reindexed to the threshold N+1 <= k+m. -/
theorem h150_quad_reindex (u : PhysicalL2) (hu : physicalSobolev 1 u) (W : ℕ → PhysicalL2)
    (c : ℕ → ℂ) (N : ℕ) :
    ∑ j ∈ Finset.Icc (N + 1) (2 * N), c j •
        physicalProduct u (∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          if k + m = j then physicalProduct (W k) (W m) else 0) =
      ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (if N + 1 ≤ k + m then c (k + m) • physicalProduct u (physicalProduct (W k) (W m)) else 0) := by
  have step1 : ∀ j : ℕ, c j • physicalProduct u (∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      if k + m = j then physicalProduct (W k) (W m) else 0) =
      ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (if k + m = j then c j • physicalProduct u (physicalProduct (W k) (W m)) else 0) := by
    intro j
    rw [h150_P_dsum u hu W _ j, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs
    · rfl
    · exact smul_zero _
  rw [Finset.sum_congr rfl (fun j _ => step1 j), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_ite_eq]
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.1 hm
  by_cases h : N + 1 ≤ k + m
  · rw [if_pos (Finset.mem_Icc.2 ⟨h, show k + m ≤ 2 * N by omega⟩), if_pos h]
  · rw [if_neg (fun h' => h (Finset.mem_Icc.1 h').1), if_neg h]

/-! The rhoTail form for an arbitrary pair p at spectral parameter l. -/

/-- The rhoTail expression of a pair (the left sequence is `toPotPair φ`, the right one its swap). -/
def h150_rhoOf (N : ℕ) (p : PotPair) (l : ℂ) : PhysicalL2 :=
  ((2 * Complex.I * l) ^ N)⁻¹ • wkbR p (N + 1) +
    ∑ j ∈ Finset.Icc (N + 1) (2 * N), ((2 * Complex.I * l) ^ j)⁻¹ •
      physicalProduct p.1 (∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        if k + m = j then physicalProduct (wkbR p k) (wkbR p m) else 0)

/-- The residual tail of a pair equals the rhoTail form of the pair (no nonvanishing hypothesis). -/
theorem h150_tail_eq (N : ℕ) (hN : 1 ≤ N) (p : PotPair) (hu : physicalSobolev 1 p.1) (l : ℂ) :
    wkbResidualTail N l p = h150_rhoOf N p l := by
  unfold wkbResidualTail h150_rhoOf
  have hQ := h150_quad_reindex p.1 hu (wkbR p) (fun s => ((2 * Complex.I * l) ^ s)⁻¹) N
  have hS := h150_tail_split N (fun k j => physicalProduct p.1 (physicalProduct (wkbR p k) (wkbR p j)))
    (fun s => ((2 * Complex.I * l) ^ s)⁻¹)
  have hA : ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      (if k + m = N then physicalProduct p.1 (physicalProduct (wkbR p k) (wkbR p m)) else 0) =
      physicalProduct p.1 (∑ k ∈ Finset.Icc 1 (N - 1), physicalProduct (wkbR p k) (wkbR p (N - k))) := by
    rw [← h150_P_dsum p.1 hu (wkbR p) _ N, h150_antidiag_W N hN (wkbR p)]
  have hW : wkbR p (N + 1) = weakDerivative (wkbR p N) +
      physicalProduct p.1 (∑ k ∈ Finset.Icc 1 (N - 1), physicalProduct (wkbR p k) (wkbR p (N - k))) :=
    wkbR_succ p N hN
  beta_reduce at hQ hS
  rw [hS, hA, hQ, hW, smul_add]
  abel

/-- The left rho equals its rhoTail form. -/
theorem h150_rho_false (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (lam : ℂ) (hlam : lam ≠ 0) :
    KSPSRiccati.rho φ false lam = KSPSRiccati.rhoTail φ false lam := by
  have h1 : KSPSRiccati.rho φ false lam = wkbResidual N lam (toPotPair φ) := rfl
  rw [h1, h150_residual_tail N hN (toPotPair φ) (pairSobolev_toPotPair φ) lam hlam,
    h150_tail_eq N hN (toPotPair φ) (h150_fst_H1 N hN _ (pairSobolev_toPotPair φ)) lam]
  rfl


/-! Right side: the signed swap. -/

theorem h150_prod_neg (P : PhysicalL2) :
    physicalProduct ((-1 : ℂ) • P) ((-1 : ℂ) • P) = physicalProduct P P := by
  rw [physicalProduct_smul_left, physicalProduct_smul_right, smul_smul]
  norm_num

theorem h150_smul_partial (lam : ℂ) (P : PhysicalL2) :
    (2 * Complex.I * lam) • ((-1 : ℂ) • P) = (2 * Complex.I * (-lam)) • P := by
  rw [smul_smul, h150_neg_arg]
  congr 1
  ring

theorem h150_neg_neg (P : PhysicalL2) :
    -((-1 : ℂ) • weakDerivative P) = weakDerivative P := by
  simp

/-- The quadratic term of the right side is the swap quadratic term times (-1)^j. -/
theorem h150_quad_true (N : ℕ) (φ : SobolevC N) (j : ℕ) :
    KSPSRiccati.quadratic φ true j =
      (-1 : ℂ) ^ j • physicalProduct (Prod.swap (toPotPair φ)).1
        (∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          if k + m = j then physicalProduct (wkbR (Prod.swap (toPotPair φ)) k)
            (wkbR (Prod.swap (toPotPair φ)) m) else 0) := by
  unfold KSPSRiccati.quadratic
  have hterm : ∀ k ∈ Finset.Icc 1 N, ∀ m ∈ Finset.Icc 1 N,
      (if k + m = j then physicalProduct (KSPSRiccati.coefficient φ true k)
          (KSPSRiccati.coefficient φ true m) else 0) =
        (-1 : ℂ) ^ j • (if k + m = j then physicalProduct (wkbR (Prod.swap (toPotPair φ)) k)
          (wkbR (Prod.swap (toPotPair φ)) m) else 0) := by
    intro k _ m _
    by_cases h : k + m = j
    · rw [if_pos h, if_pos h]
      show physicalProduct (((-1 : ℂ) ^ (k + 1)) • wkbR (Prod.swap (toPotPair φ)) k)
        (((-1 : ℂ) ^ (m + 1)) • wkbR (Prod.swap (toPotPair φ)) m) = _
      rw [physicalProduct_smul_left, physicalProduct_smul_right, smul_smul, h150_sign_pair k m j h]
    · rw [if_neg h, if_neg h, smul_zero]
  have hsum : (∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      (if k + m = j then physicalProduct (KSPSRiccati.coefficient φ true k)
        (KSPSRiccati.coefficient φ true m) else 0)) =
      ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, (-1 : ℂ) ^ j •
        (if k + m = j then physicalProduct (wkbR (Prod.swap (toPotPair φ)) k)
          (wkbR (Prod.swap (toPotPair φ)) m) else 0) :=
    Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun m hm => hterm k hk m hm))
  rw [hsum]
  simp only [← Finset.smul_sum]
  exact physicalProduct_smul_right _ _ _

/-- The partial sum of the right side is the negated swap partial sum at -lam. -/
theorem h150_partial_true (N : ℕ) (φ : SobolevC N) (lam : ℂ) :
    KSPSRiccati.«partial» φ true lam =
      (-1 : ℂ) • wkbPartial N (-lam) (Prod.swap (toPotPair φ)) := by
  unfold KSPSRiccati.«partial» wkbPartial
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  show ((2 * Complex.I * lam) ^ k)⁻¹ • (((-1 : ℂ) ^ (k + 1)) • wkbR (Prod.swap (toPotPair φ)) k) =
    (-1 : ℂ) • (((2 * Complex.I * (-lam)) ^ k)⁻¹ • wkbR (Prod.swap (toPotPair φ)) k)
  rw [smul_smul, smul_smul, h150_neg_arg, h150_neg_inv_pow]
  congr 1
  ring

/-- The right rho is the residual of the swap pair at -lam. -/
theorem h150_rho_true_resid (N : ℕ) (φ : SobolevC N) (lam : ℂ) :
    KSPSRiccati.rho φ true lam = wkbResidual N (-lam) (Prod.swap (toPotPair φ)) := by
  show -weakDerivative (KSPSRiccati.«partial» φ true lam) -
      (2 * Complex.I * lam) • KSPSRiccati.«partial» φ true lam +
      physicalProduct (toPotPair φ).2
        (physicalProduct (KSPSRiccati.«partial» φ true lam) (KSPSRiccati.«partial» φ true lam)) -
      (toPotPair φ).1 = _
  rw [h150_partial_true N φ lam, weakDerivative_smul, h150_prod_neg, h150_smul_partial, h150_neg_neg]
  rfl

/-- The coefficient of the right side, as an equality of definitions (no unfolding of wkbR). -/
theorem h150_coef_true {N : ℕ} (φ : SobolevC N) (k : ℕ) :
    KSPSRiccati.coefficient φ true k = ((-1 : ℂ) ^ (k + 1)) • wkbR (Prod.swap (toPotPair φ)) k := rfl

/-- The right rhoTail is the rhoTail form of the swap pair at -lam. -/
theorem h150_rhoTail_true (N : ℕ) (φ : SobolevC N) (lam : ℂ) :
    KSPSRiccati.rhoTail φ true lam = h150_rhoOf N (Prod.swap (toPotPair φ)) (-lam) := by
  have hA : ((2 * Complex.I * lam) ^ N)⁻¹ • KSPSRiccati.coefficient φ true (N + 1) =
      ((2 * Complex.I * (-lam)) ^ N)⁻¹ • wkbR (Prod.swap (toPotPair φ)) (N + 1) := by
    rw [h150_coef_true, smul_smul, h150_neg_arg, h150_neg_inv_pow,
      show ((2 * Complex.I * lam) ^ N)⁻¹ * (-1 : ℂ) ^ (N + 1 + 1) =
        (-1 : ℂ) ^ N * ((2 * Complex.I * lam) ^ N)⁻¹ by ring]
  have hB : ∀ j ∈ Finset.Icc (N + 1) (2 * N),
      ((2 * Complex.I * lam) ^ j)⁻¹ • KSPSRiccati.quadratic φ true j =
        ((2 * Complex.I * (-lam)) ^ j)⁻¹ • physicalProduct (Prod.swap (toPotPair φ)).1
          (∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
            if k + m = j then physicalProduct (wkbR (Prod.swap (toPotPair φ)) k)
              (wkbR (Prod.swap (toPotPair φ)) m) else 0) := by
    intro j _
    rw [h150_quad_true N φ j, smul_smul, h150_neg_arg, h150_neg_inv_pow,
      show ((2 * Complex.I * lam) ^ j)⁻¹ * (-1 : ℂ) ^ j =
        (-1 : ℂ) ^ j * ((2 * Complex.I * lam) ^ j)⁻¹ by ring]
  unfold KSPSRiccati.rhoTail h150_rhoOf
  rw [hA, Finset.sum_congr rfl hB]

/-- The right rho equals its rhoTail form for lam ≠ 0. -/
theorem h150_rho_true (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (lam : ℂ) (hlam : lam ≠ 0) :
    KSPSRiccati.rho φ true lam = KSPSRiccati.rhoTail φ true lam := by
  have hS : pairSobolev (N : ℝ) (Prod.swap (toPotPair φ)) := pairSobolev_swap_toPotPair φ
  rw [h150_rho_true_resid N φ lam, h150_residual_tail N hN _ hS (-lam) (neg_ne_zero.2 hlam),
    h150_tail_eq N hN _ (h150_fst_H1 N hN _ hS) (-lam), h150_rhoTail_true N φ lam]

/-- S6: the rho of the packet equals its rhoTail, for both sides and every lam ≠ 0. -/
theorem h150_rho_eq_rhoTail (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (lam : ℂ)
    (hlam : lam ≠ 0) :
    KSPSRiccati.rho φ b lam = KSPSRiccati.rhoTail φ b lam := by
  cases b
  · exact h150_rho_false N hN φ lam hlam
  · exact h150_rho_true N hN φ lam hlam

end
end NlsGge.ThirdConsultation.KSPSSupport
