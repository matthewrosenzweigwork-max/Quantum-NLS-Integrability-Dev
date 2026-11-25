import NlsGge.Atomic.KST.KST026
import Mathlib
import NlsGge.Atomic.KSTPath
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST023
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST025
import NlsGge.Atomic.KST.KST021
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST007
import NlsGge.Atomic.KST.KST016

/- KST-027 production kit (proof development, AUTHOR, building on proof development's parked leaves L1/L2/L5; not reviewed; target NlsGge/Atomic/KST/KST027.lean).
   Heads: PRO_DEFINITION_RESPONSE_FP80_02_03.md KST-027 (kst027, kst027_locally_uniform), with Real.sqrt retained.  Definitions hosted verbatim from
   DEFINITIONS/KST.lean.md: patternBlock, weightedMajorantTail, source51RHS, weightFact, Weighted, weightedPotential.
   Route: pattern split (L2), patternBlock^2 <= denominatorPattern * sourcePatternFourierEnergy (Cauchy-Schwarz over paths),
   weighted Cauchy-Schwarz over (length, pattern) with geometric weights, the per-pattern bounds kst025/kst026, the uniform real bounds
   bq_zero/bq_one under the smallness Cw^2 (T_N + E/sqrt N) <= 1/60, giving sqrt(weightedMajorantTail) <= sqrt(15) Cw (T_N/w_N^2 + E/sqrt N) <= 4 sqrt2 Cw^2 (...);
   the locally uniform form uses proof development's L5 energy/tail estimates on the Weighted ball (radius 1/(62 Cw), N2 from tail smallness at 2*Cw). -/
/- KST-027 core stage B (proof development). `patternBlock` is hosted verbatim from DEFINITIONS/KST.lean.md (via proof development KST027_L2). -/
set_option autoImplicit false
open scoped ENNReal BigOperators
open NlsGge.Atomic.KSTPath NlsGge.Atomic.KST

namespace NlsGge.ThirdConsultation.KST
noncomputable section

open Classical in
def patternBlock {k : ℕ} (hk : 0 < k) (A : ℤ → ℝ)
    (n : ℤ) (σ : Pattern k) : ℝ≥0∞ :=
  ∑' ell : Path k, if admissiblePath n ell ∧
    (∀ i, nearFarBit n (ell i) = σ i) then
    ENNReal.ofReal (pathProduct hk A n ell) else 0



def weightedMajorantTail (w A : ℤ → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑' n : ℤ, if N ≤ n.natAbs then
    ENNReal.ofReal (w (2*n)^2) * pathMajorant A n ^ 2 else 0

namespace K027A

theorem ennreal_cs_tsum {ι : Type*} (g h : ι → ℝ≥0∞) :
    (∑' i, g i * h i) ^ 2 ≤ (∑' i, g i ^ 2) * (∑' i, h i ^ 2) := by
  have key : ∑' i, g i * h i ≤ (∑' i, g i ^ 2) ^ (1 / 2 : ℝ) * (∑' i, h i ^ 2) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun s => ?_)
    have hc := ENNReal.inner_le_Lp_mul_Lq s g h (p := 2) (q := 2) (by
      exact Real.HolderConjugate.two_two)
    refine hc.trans ?_
    simp only [ENNReal.rpow_two] at hc ⊢
    refine mul_le_mul' (ENNReal.rpow_le_rpow ?_ (by norm_num)) (ENNReal.rpow_le_rpow ?_ (by norm_num))
    · exact ENNReal.sum_le_tsum s
    · exact ENNReal.sum_le_tsum s
  calc (∑' i, g i * h i) ^ 2 ≤ ((∑' i, g i ^ 2) ^ (1 / 2 : ℝ) * (∑' i, h i ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' key 2
    _ = (∑' i, g i ^ 2) * (∑' i, h i ^ 2) := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

theorem ennreal_wcs {ι : Type*} (x : ι → ℝ≥0∞) (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    (∑' i, x i) ^ 2 ≤ (∑' i, ENNReal.ofReal (c i)) * (∑' i, x i ^ 2 * ENNReal.ofReal (1 / c i)) := by
  have h := ennreal_cs_tsum (fun i => ENNReal.ofReal (Real.sqrt (c i)))
    (fun i => x i * ENNReal.ofReal (1 / Real.sqrt (c i)))
  have e1 : ∀ i, ENNReal.ofReal (Real.sqrt (c i)) * (x i * ENNReal.ofReal (1 / Real.sqrt (c i))) = x i := by
    intro i
    have hs : 0 < Real.sqrt (c i) := Real.sqrt_pos.2 (hc i)
    rw [mul_left_comm, ← ENNReal.ofReal_mul hs.le, mul_one_div_cancel hs.ne', ENNReal.ofReal_one, mul_one]
  have e2 : ∀ i, ENNReal.ofReal (Real.sqrt (c i)) ^ 2 = ENNReal.ofReal (c i) := by
    intro i
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hc i).le]
  have e3 : ∀ i, (x i * ENNReal.ofReal (1 / Real.sqrt (c i))) ^ 2 = x i ^ 2 * ENNReal.ofReal (1 / c i) := by
    intro i
    have hs : 0 ≤ 1 / Real.sqrt (c i) := by positivity
    rw [mul_pow, ← ENNReal.ofReal_pow hs, div_pow, one_pow, Real.sq_sqrt (hc i).le]
  simpa only [e1, e2, e3] using h


end K027A

namespace K027L2

theorem pathBlock_eq_sum_patternBlock {k : ℕ} (hk : 0 < k) (A : ℤ → ℝ) (n : ℤ) :
    pathBlock hk A n = ∑ σ : Pattern k, patternBlock hk A n σ := by
  classical
  have hpt : ∀ ell : Path k,
      (if admissiblePath n ell then ENNReal.ofReal (pathProduct hk A n ell) else 0) =
        ∑ σ : Pattern k, (if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then
          ENNReal.ofReal (pathProduct hk A n ell) else 0) := by
    intro ell
    by_cases hadm : admissiblePath n ell
    · rw [Finset.sum_eq_single (fun i => nearFarBit n (ell i))]
      · simp [hadm]
      · intro σ _ hσ
        rw [if_neg]
        rintro ⟨-, hall⟩
        exact hσ (funext fun i => (hall i).symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp [hadm]
  unfold pathBlock patternBlock
  rw [tsum_congr hpt, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]

theorem pathMajorant_eq_sum_patternBlock (A : ℤ → ℝ) (n : ℤ) :
    pathMajorant A n = ∑' j : ℕ, ∑ σ : Pattern (j + 1), patternBlock (Nat.succ_pos j) A n σ := by
  unfold pathMajorant
  exact tsum_congr fun j => pathBlock_eq_sum_patternBlock (Nat.succ_pos j) A n


theorem patternBlock_sq_le {k : ℕ} (hk : 0 < k) (A : ℤ → ℝ) (hA : ∀ j, 0 ≤ A j) (n : ℤ) (σ : Pattern k) :
    patternBlock hk A n σ ^ 2 ≤ denominatorPattern n σ * sourcePatternFourierEnergy hk A n σ := by
  classical
  have hprod : ∀ ell : Path k, 0 ≤ ∏ j : Fin (2*k+1), A (pathArgument hk n ell j) :=
    fun ell => Finset.prod_nonneg (fun j _ => hA _)
  have hterm : ∀ ell : Path k, (if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (pathProduct hk A n ell) else 0) =
      (if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (1 / ∏ i : Fin (2*k), ((ell i - n).natAbs : ℝ)) else 0) *
      (if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (∏ j : Fin (2*k+1), A (pathArgument hk n ell j)) else 0) := by
    intro ell
    by_cases h : admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i)
    · simp only [if_pos h]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold pathProduct
      ring
    · simp [h]
  have hg : ∀ ell : Path k, (if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (1 / ∏ i : Fin (2*k), ((ell i - n).natAbs : ℝ)) else 0) ^ 2 =
      if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (∏ i : Fin (2*k), (1 / ((ell i - n).natAbs : ℝ)^2)) else 0 := by
    intro ell
    by_cases h : admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i)
    · simp only [if_pos h]
      rw [← ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [div_pow, one_pow, ← Finset.prod_pow, one_div, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [one_div]
    · simp [h]
  have hh : ∀ ell : Path k, (if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (∏ j : Fin (2*k+1), A (pathArgument hk n ell j)) else 0) ^ 2 =
      if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (∏ j : Fin (2*k+1), A (pathArgument hk n ell j) ^ 2) else 0 := by
    intro ell
    by_cases h : admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i)
    · simp only [if_pos h]
      rw [← ENNReal.ofReal_pow (hprod ell)]
      congr 1
      rw [Finset.prod_pow]
    · simp [h]
  have hcs := K027A.ennreal_cs_tsum
    (fun ell : Path k => if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (1 / ∏ i : Fin (2*k), ((ell i - n).natAbs : ℝ)) else 0)
    (fun ell : Path k => if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (∏ j : Fin (2*k+1), A (pathArgument hk n ell j)) else 0)
  have e1 : patternBlock hk A n σ = ∑' ell : Path k, (if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (1 / ∏ i : Fin (2*k), ((ell i - n).natAbs : ℝ)) else 0) *
      (if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (∏ j : Fin (2*k+1), A (pathArgument hk n ell j)) else 0) :=
    tsum_congr hterm
  have e2 : ∑' ell : Path k, (if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (1 / ∏ i : Fin (2*k), ((ell i - n).natAbs : ℝ)) else 0) ^ 2 = denominatorPattern n σ :=
    tsum_congr hg
  have e3 : ∑' ell : Path k, (if admissiblePath n ell ∧ (∀ i, nearFarBit n (ell i) = σ i) then ENNReal.ofReal (∏ j : Fin (2*k+1), A (pathArgument hk n ell j)) else 0) ^ 2 = sourcePatternFourierEnergy hk A n σ :=
    tsum_congr hh
  rw [e1]
  rw [e2, e3] at hcs
  exact hcs


theorem weightedPattern_le_cauchy {k : ℕ} (hk : 0 < k) (w A : ℤ → ℝ) (hA : ∀ j, 0 ≤ A j) (N : ℕ)
    (σ : Pattern k) :
    (∑' n : ℤ, if N ≤ n.natAbs then ENNReal.ofReal (w (2*n)^2) * patternBlock hk A n σ ^ 2 else 0) ≤
      weightedCauchyPatternSum hk w A N σ := by
  unfold weightedCauchyPatternSum
  refine ENNReal.tsum_le_tsum (fun n => ?_)
  by_cases h : N ≤ n.natAbs
  · simp only [h, if_true]
    rw [mul_assoc]
    exact mul_le_mul' le_rfl (patternBlock_sq_le hk A hA n σ)
  · simp [h]

/-- the index type of all (length, pattern) pairs -/
abbrev IdxP : Type := Σ j : ℕ, Pattern (j + 1)

theorem pathMajorant_eq_tsum_idx (A : ℤ → ℝ) (n : ℤ) :
    pathMajorant A n = ∑' i : IdxP, patternBlock (Nat.succ_pos i.1) A n i.2 := by
  rw [pathMajorant_eq_sum_patternBlock, ENNReal.tsum_sigma']
  exact tsum_congr (fun j => (tsum_fintype _).symm)

theorem S_le (w A : ℤ → ℝ) (hA : ∀ j, 0 ≤ A j) (N : ℕ) (b : ℕ → ℝ) (hb : ∀ j, 0 < b j)
    (hW : ∀ j (σ : Pattern (j+1)),
      (∑' n : ℤ, if N ≤ n.natAbs then ENNReal.ofReal (w (2*n)^2) *
        patternBlock (Nat.succ_pos j) A n σ ^ 2 else 0) ≤ ENNReal.ofReal (b j ^ 2)) :
    weightedMajorantTail w A N ≤
      (∑' j : ℕ, (4 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal (b j)) ^ 2 := by
  classical
  set total : ℝ≥0∞ := ∑' j : ℕ, (4 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal (b j) with htot
  have htot' : ∑' i : IdxP, ENNReal.ofReal (b i.1) = total := by
    rw [ENNReal.tsum_sigma']
    refine tsum_congr (fun j => ?_)
    rw [tsum_fintype]
    show ∑ σ : Pattern (j+1), ENNReal.ofReal (b j) = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    have : Fintype.card (Pattern (j+1)) = 4 ^ (j+1) := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      rw [show 2 * (j+1) = 2 * (j+1) from rfl, pow_mul]; norm_num
    rw [this]; push_cast; rfl
  have hpt : ∀ n : ℤ, ENNReal.ofReal (w (2*n)^2) * pathMajorant A n ^ 2 ≤
      total * ∑' i : IdxP, ENNReal.ofReal (w (2*n)^2) *
        (patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 * ENNReal.ofReal (1 / b i.1)) := by
    intro n
    rw [pathMajorant_eq_tsum_idx]
    have hcs := K027A.ennreal_wcs (fun i : IdxP => patternBlock (Nat.succ_pos i.1) A n i.2)
      (fun i => b i.1) (fun i => hb i.1)
    rw [htot'] at hcs
    calc ENNReal.ofReal (w (2*n)^2) * (∑' i : IdxP, patternBlock (Nat.succ_pos i.1) A n i.2) ^ 2
        ≤ ENNReal.ofReal (w (2*n)^2) * (total * ∑' i : IdxP, patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 * ENNReal.ofReal (1 / b i.1)) :=
          mul_le_mul' le_rfl hcs
      _ = total * ∑' i : IdxP, ENNReal.ofReal (w (2*n)^2) *
            (patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 * ENNReal.ofReal (1 / b i.1)) := by
          rw [mul_left_comm, ENNReal.tsum_mul_left]
  unfold weightedMajorantTail
  calc (∑' n : ℤ, if N ≤ n.natAbs then ENNReal.ofReal (w (2*n)^2) * pathMajorant A n ^ 2 else 0)
      ≤ ∑' n : ℤ, if N ≤ n.natAbs then total * ∑' i : IdxP, ENNReal.ofReal (w (2*n)^2) *
          (patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 * ENNReal.ofReal (1 / b i.1)) else 0 := by
        refine ENNReal.tsum_le_tsum (fun n => ?_)
        by_cases h : N ≤ n.natAbs
        · simp only [h, if_true]; exact hpt n
        · simp [h]
    _ = total * ∑' i : IdxP, ENNReal.ofReal (1 / b i.1) *
          ∑' n : ℤ, (if N ≤ n.natAbs then ENNReal.ofReal (w (2*n)^2) *
            patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 else 0) := by
        have hswap : (∑' n : ℤ, if N ≤ n.natAbs then ∑' i : IdxP, ENNReal.ofReal (w (2*n)^2) *
            (patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 * ENNReal.ofReal (1 / b i.1)) else 0) =
            ∑' i : IdxP, ENNReal.ofReal (1 / b i.1) *
              ∑' n : ℤ, (if N ≤ n.natAbs then ENNReal.ofReal (w (2*n)^2) *
                patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 else 0) := by
          have h1 : ∀ n : ℤ, (if N ≤ n.natAbs then ∑' i : IdxP, ENNReal.ofReal (w (2*n)^2) *
              (patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 * ENNReal.ofReal (1 / b i.1)) else 0) =
              ∑' i : IdxP, (if N ≤ n.natAbs then ENNReal.ofReal (w (2*n)^2) *
              (patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 * ENNReal.ofReal (1 / b i.1)) else 0) := by
            intro n
            by_cases h : N ≤ n.natAbs <;> simp [h]
          simp_rw [h1]
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun i => ?_)
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun n => ?_)
          by_cases h : N ≤ n.natAbs
          · simp only [h, if_true]; ring
          · simp [h]
        calc (∑' n : ℤ, if N ≤ n.natAbs then total * ∑' i : IdxP, ENNReal.ofReal (w (2*n)^2) *
            (patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 * ENNReal.ofReal (1 / b i.1)) else 0)
            = ∑' n : ℤ, total * (if N ≤ n.natAbs then ∑' i : IdxP, ENNReal.ofReal (w (2*n)^2) *
            (patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 * ENNReal.ofReal (1 / b i.1)) else 0) :=
              tsum_congr (fun n => by by_cases h : N ≤ n.natAbs <;> simp [h])
          _ = total * ∑' n : ℤ, (if N ≤ n.natAbs then ∑' i : IdxP, ENNReal.ofReal (w (2*n)^2) *
            (patternBlock (Nat.succ_pos i.1) A n i.2 ^ 2 * ENNReal.ofReal (1 / b i.1)) else 0) :=
              ENNReal.tsum_mul_left
          _ = _ := by rw [hswap]
    _ ≤ total * ∑' i : IdxP, ENNReal.ofReal (1 / b i.1) * ENNReal.ofReal (b i.1 ^ 2) := by
        refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum (fun i => mul_le_mul' le_rfl (hW i.1 i.2)))
    _ = total * total := by
        congr 1
        rw [← htot']
        refine tsum_congr (fun i => ?_)
        rw [← ENNReal.ofReal_mul (by have := hb i.1; positivity)]
        congr 1
        have := (hb i.1).ne'
        field_simp
    _ = total ^ 2 := (sq total).symm

end K027L2
end
end NlsGge.ThirdConsultation.KST

namespace NlsGge.ThirdConsultation.KST
namespace K027D

theorem bq_zero (C y T a U : ℝ) (j : ℕ) (hC : 1 ≤ C) (hy : 0 ≤ y) (hT : 0 ≤ T) (ha : 0 ≤ a)
    (hs : C ^ 2 * (T + y) ≤ 1 / 60) (hU : a + y ≤ U) :
    (5 * C ^ 2) ^ (2 * (j + 1)) * y ^ (2 * (j + 1) + 1) ≤
      25 * C ^ 2 * U ^ 2 / 60 * (1 / 144) ^ j := by
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have ht0 : 0 ≤ C ^ 2 * y := by positivity
  have ht1 : C ^ 2 * y ≤ 1 / 60 := by nlinarith [mul_nonneg hC2 hT]
  have e : (5 * C ^ 2) ^ (2 * (j + 1)) * y ^ (2 * (j + 1) + 1) =
      25 ^ (j + 1) * ((C ^ 2 * y) ^ (2 * j) * ((C ^ 2 * y) ^ 2 * y)) := by
    have h25 : (5 : ℝ) ^ (2 * (j + 1)) = 25 ^ (j + 1) := by rw [pow_mul]; norm_num
    rw [mul_pow, h25]
    ring
  have h1 : (C ^ 2 * y) ^ (2 * j) ≤ (1 / 3600) ^ j := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) j
  have h2 : (C ^ 2 * y) ^ 2 * y ≤ C ^ 2 * U ^ 2 / 60 := by
    have hyU : y ≤ U := by linarith
    have : (C ^ 2 * y) ^ 2 * y = C ^ 2 * (C ^ 2 * y) * y ^ 2 := by ring
    rw [this]
    have h3 : C ^ 2 * (C ^ 2 * y) * y ^ 2 ≤ C ^ 2 * (1 / 60) * y ^ 2 := by
      have := mul_le_mul_of_nonneg_left ht1 hC2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg y)
    have h4 : y ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hy hyU 2
    nlinarith [mul_le_mul_of_nonneg_left h4 hC2]
  rw [e]
  have h5 : (C ^ 2 * y) ^ (2 * j) * ((C ^ 2 * y) ^ 2 * y) ≤ (1 / 3600) ^ j * (C ^ 2 * U ^ 2 / 60) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  calc 25 ^ (j + 1) * ((C ^ 2 * y) ^ (2 * j) * ((C ^ 2 * y) ^ 2 * y))
      ≤ 25 ^ (j + 1) * ((1 / 3600) ^ j * (C ^ 2 * U ^ 2 / 60)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = 25 * C ^ 2 * U ^ 2 / 60 * (1 / 144) ^ j := by
        have : (25 : ℝ) ^ (j + 1) * (1 / 3600) ^ j = 25 * (1 / 144) ^ j := by
          have h25 : (25 : ℝ) ^ j * (1 / 3600) ^ j = (1 / 144) ^ j := by
            rw [← mul_pow]; norm_num
          calc (25 : ℝ) ^ (j + 1) * (1 / 3600) ^ j = 25 * ((25 : ℝ) ^ j * (1 / 3600) ^ j) := by ring
            _ = _ := by rw [h25]
        calc (25 : ℝ) ^ (j + 1) * ((1 / 3600) ^ j * (C ^ 2 * U ^ 2 / 60))
            = (25 ^ (j + 1) * (1 / 3600) ^ j) * (C ^ 2 * U ^ 2 / 60) := by ring
          _ = _ := by rw [this]; ring


theorem bq_one (C y T a U : ℝ) (j τ : ℕ) (hC : 1 ≤ C) (hy : 0 ≤ y) (hT : 0 ≤ T) (ha : 0 ≤ a)
    (haT : a ≤ T) (hs : C ^ 2 * (T + y) ≤ 1 / 60) (hU : a + y ≤ U)
    (hτ1 : 1 ≤ τ) (hτ2 : τ ≤ 2 * (j + 1) + 1) :
    5 ^ (2 * (j + 1)) * C ^ 2 * T * a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ) ≤
      25 * C ^ 2 * U ^ 2 / 60 * (1 / 144) ^ j := by
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hCT : C ^ 2 * T ≤ 1 / 60 := by nlinarith [mul_nonneg (sq_nonneg C) hy]
  set M := max a y with hM
  have hM0 : 0 ≤ M := le_max_of_le_left ha
  have hMU : M ≤ U := max_le (by linarith) (by linarith)
  have hMs : M ≤ 1 / 60 := by
    have hay : a ≤ 1 / 60 := by nlinarith [mul_nonneg (sq_nonneg C) hy, mul_nonneg (sq_nonneg C) hT]
    have hyy : y ≤ 1 / 60 := by nlinarith [mul_nonneg (sq_nonneg C) hT]
    exact max_le hay hyy
  have hpq : (τ - 1) + (2 * (j + 1) + 1 - τ) = 2 * j + 2 := by omega
  have hap : a ^ (τ - 1) ≤ M ^ (τ - 1) := pow_le_pow_left₀ ha (le_max_left _ _) _
  have hyq : y ^ (2 * (j + 1) + 1 - τ) ≤ M ^ (2 * (j + 1) + 1 - τ) :=
    pow_le_pow_left₀ hy (le_max_right _ _) _
  have hprod : a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ) ≤ M ^ (2 * j + 2) := by
    calc a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ) ≤ M ^ (τ - 1) * M ^ (2 * (j + 1) + 1 - τ) :=
          mul_le_mul hap hyq (by positivity) (by positivity)
      _ = M ^ (2 * j + 2) := by rw [← pow_add, hpq]
  have hM2 : M ^ (2 * j + 2) ≤ U ^ 2 * (1 / 3600) ^ j := by
    have : M ^ (2 * j + 2) = M ^ 2 * (M ^ 2) ^ j := by rw [← pow_mul]; ring
    rw [this]
    refine mul_le_mul (pow_le_pow_left₀ hM0 hMU 2) ?_ (by positivity) (by positivity)
    calc (M ^ 2) ^ j ≤ ((1 / 60) ^ 2) ^ j := pow_le_pow_left₀ (by positivity)
          (pow_le_pow_left₀ hM0 hMs 2) j
      _ = (1 / 3600) ^ j := by norm_num
  have h25 : (5 : ℝ) ^ (2 * (j + 1)) = 25 ^ (j + 1) := by rw [pow_mul]; norm_num
  rw [h25]
  have hU0 : 0 ≤ U := le_trans hM0 hMU
  have hmain : 25 ^ (j + 1) * C ^ 2 * T * (a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ)) ≤
      25 ^ (j + 1) * (1 / 60) * (U ^ 2 * (1 / 3600) ^ j) := by
    have h1 : C ^ 2 * T * (a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ)) ≤ (1 / 60) * (U ^ 2 * (1 / 3600) ^ j) :=
      mul_le_mul hCT (hprod.trans hM2) (by positivity) (by norm_num)
    calc 25 ^ (j + 1) * C ^ 2 * T * (a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ))
        = 25 ^ (j + 1) * (C ^ 2 * T * (a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ))) := by ring
      _ ≤ 25 ^ (j + 1) * ((1 / 60) * (U ^ 2 * (1 / 3600) ^ j)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have h25b : (25 : ℝ) ^ (j + 1) * (1 / 3600) ^ j = 25 * (1 / 144) ^ j := by
    have h : (25 : ℝ) ^ j * (1 / 3600) ^ j = (1 / 144) ^ j := by
      rw [← mul_pow]; norm_num
    calc (25 : ℝ) ^ (j + 1) * (1 / 3600) ^ j = 25 * ((25 : ℝ) ^ j * (1 / 3600) ^ j) := by ring
      _ = _ := by rw [h]
  calc 25 ^ (j + 1) * C ^ 2 * T * a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ)
      = 25 ^ (j + 1) * C ^ 2 * T * (a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ)) := by ring
    _ ≤ 25 ^ (j + 1) * (1 / 60) * (U ^ 2 * (1 / 3600) ^ j) := hmain
    _ = 25 * U ^ 2 / 60 * (1 / 144) ^ j := by
        calc 25 ^ (j + 1) * (1 / 60) * (U ^ 2 * (1 / 3600) ^ j)
            = (25 ^ (j + 1) * (1 / 3600) ^ j) * (U ^ 2 / 60) := by ring
          _ = _ := by rw [h25b]; ring
    _ ≤ 25 * C ^ 2 * U ^ 2 / 60 * (1 / 144) ^ j := by
        have : 25 * U ^ 2 / 60 * (1 / 144 : ℝ) ^ j * 1 ≤ 25 * U ^ 2 / 60 * (1 / 144) ^ j * C ^ 2 :=
          mul_le_mul_of_nonneg_left hC2 (by positivity)
        nlinarith [this]

end K027D
end NlsGge.ThirdConsultation.KST

section K027L1Sec
open Filter Topology
open scoped ENNReal
namespace NlsGge.ThirdConsultation.KST
namespace K027L1

theorem mem_Ioo_iff_natAbs (N : ℕ) (x : ℤ) :
    x ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ) ↔ N ≤ x.natAbs := by
  rcases Int.natAbs_eq x with h | h <;> simp only [Finset.mem_Ioo, not_and_or, not_lt] <;> omega

theorem scalarTail_eq_compl (w A : ℤ → ℝ) (N : ℕ) :
    scalarTailEnergy w A N =
      ∑' b : {x : ℤ // x ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ)},
        ENNReal.ofReal (w b.1 ^ 2 * A b.1 ^ 2) := by
  unfold scalarTailEnergy
  have h := tsum_subtype {x : ℤ | x ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ)}
    (fun x => ENNReal.ofReal (w x ^ 2 * A x ^ 2))
  rw [show (∑' b : {x : ℤ // x ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ)},
      ENNReal.ofReal (w b.1 ^ 2 * A b.1 ^ 2)) =
      ∑' b : ({x : ℤ | x ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ)} : Set ℤ),
        ENNReal.ofReal (w b.1 ^ 2 * A b.1 ^ 2) from rfl, h]
  refine tsum_congr fun x => ?_
  by_cases hx : N ≤ x.natAbs
  · have hm : x ∈ ({x : ℤ | x ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ)} : Set ℤ) :=
      (mem_Ioo_iff_natAbs N x).2 hx
    rw [if_pos hx, Set.indicator_of_mem hm]
  · have hm : x ∉ ({x : ℤ | x ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ)} : Set ℤ) := fun h' =>
      hx ((mem_Ioo_iff_natAbs N x).1 h')
    rw [if_neg hx, Set.indicator_of_notMem hm]

theorem tail_tendsto (w A : ℤ → ℝ) (hE : scalarEnergy w A < ⊤) :
    Tendsto (fun N : ℕ => scalarTailEnergy w A N) atTop (𝓝 0) := by
  have hf : ∑' x : ℤ, ENNReal.ofReal (w x ^ 2 * A x ^ 2) ≠ ⊤ := hE.ne
  have hg : Tendsto (fun N : ℕ => Finset.Ioo (-(N : ℤ)) (N : ℤ)) atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · intro N M hNM x hx
      have hNM' : (N : ℤ) ≤ (M : ℤ) := by exact_mod_cast hNM
      simp only [Finset.mem_Ioo] at hx ⊢
      omega
    · intro x
      refine ⟨x.natAbs + 1, ?_⟩
      rcases Int.natAbs_eq x with h | h <;> simp only [Finset.mem_Ioo] <;> omega
  have hc := (ENNReal.tendsto_tsum_compl_atTop_zero hf).comp hg
  exact Tendsto.congr (fun N => (scalarTail_eq_compl w A N).symm) hc

theorem kst027_tail_eventually (w A : ℤ → ℝ) (Cw : ℝ) (hE : scalarEnergy w A < ⊤) :
    ∃ N₂ : ℕ, 5 ≤ N₂ ∧ ∀ N : ℕ, N₂ ≤ N →
      Cw ^ 2 * ((scalarTailEnergy w A N).toReal +
        (scalarEnergy w A).toReal / Real.sqrt (N : ℝ)) ≤ (1 / 60 : ℝ) := by
  have hT : Tendsto (fun N : ℕ => (scalarTailEnergy w A N).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tail_tendsto w A hE)
    rw [ENNReal.toReal_zero] at h
    exact h
  have hS : Tendsto (fun N : ℕ => (scalarEnergy w A).toReal / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hall : Tendsto (fun N : ℕ => Cw ^ 2 * ((scalarTailEnergy w A N).toReal +
      (scalarEnergy w A).toReal / Real.sqrt (N : ℝ))) atTop (𝓝 (Cw ^ 2 * (0 + 0))) :=
    tendsto_const_nhds.mul (hT.add hS)
  rw [show Cw ^ 2 * ((0 : ℝ) + 0) = 0 by ring] at hall
  have hev := (tendsto_order.1 hall).2 (1 / 60 : ℝ) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max N₀ 5, le_max_right _ _, fun N hN => (hN₀ N ((le_max_left _ _).trans hN)).le⟩

end K027L1
end NlsGge.ThirdConsultation.KST
end K027L1Sec

namespace NlsGge.ThirdConsultation.KST
noncomputable section
open scoped ENNReal BigOperators
open NlsGge.Atomic.KSTPath NlsGge.Atomic.KST

/-- RHS of Proposition 4.1, equation (51), in squared-norm notation (DEFINITIONS/KST.lean.md, verbatim). -/
def source51RHS (w A : ℤ → ℝ) (Cw : ℝ) (N : ℕ) : ℝ :=
  4 * Real.sqrt 2 * Cw^2 *
    ((scalarTailEnergy w A N).toReal / w (N : ℤ)^2 +
      (scalarEnergy w A).toReal / Real.sqrt (N : ℝ))

namespace K027Core


theorem total_eq (c0 : ℝ) (hc0 : 0 < c0) :
    ∑' j : ℕ, (4 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal (c0 * (1 / 12) ^ j) = ENNReal.ofReal (6 * c0) := by
  have hterm : ∀ j : ℕ, (4 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal (c0 * (1 / 12) ^ j) =
      ENNReal.ofReal (4 * c0 * (1 / 3) ^ j) := by
    intro j
    have h4 : (4 : ℝ≥0∞) ^ (j + 1) = ENNReal.ofReal ((4 : ℝ) ^ (j + 1)) := by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp
    rw [h4, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h : (4 : ℝ) ^ j * (1 / 12) ^ j = (1 / 3) ^ j := by rw [← mul_pow]; norm_num
    calc (4 : ℝ) ^ (j + 1) * (c0 * (1 / 12) ^ j) = 4 * c0 * ((4 : ℝ) ^ j * (1 / 12) ^ j) := by ring
      _ = _ := by rw [h]
  simp_rw [hterm]
  have hs : Summable (fun j : ℕ => 4 * c0 * (1 / 3 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs, tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  congr 1
  norm_num
  ring

theorem forcedTailCount_le {k : ℕ} (hk : 0 < k) (σ : Pattern k) : forcedTailCount hk σ ≤ 2 * k + 1 := by
  classical
  unfold forcedTailCount
  calc (Finset.univ.filter (forcedAt hk σ)).card ≤ (Finset.univ : Finset (Fin (2*k+1))).card :=
        Finset.card_filter_le _ _
    _ = 2 * k + 1 := by simp

theorem kst027_core (w A : ℤ → ℝ) (Cw : ℝ) (hw : SlowWeight w Cw) (hA : ∀ j, 0 ≤ A j)
    (hE : scalarEnergy w A < ⊤) (N : ℕ) (hN : 1 ≤ N)
    (hs : Cw ^ 2 * ((scalarTailEnergy w A N).toReal +
      (scalarEnergy w A).toReal / Real.sqrt (N : ℝ)) ≤ (1 / 60 : ℝ)) :
    weightedMajorantTail w A N < ⊤ ∧
      Real.sqrt (weightedMajorantTail w A N).toReal ≤ source51RHS w A Cw N := by
  classical
  have hC : 1 ≤ Cw := slowWeight_Cw_one_le hw
  set T : ℝ := (scalarTailEnergy w A N).toReal with hT
  set E : ℝ := (scalarEnergy w A).toReal with hEdef
  set y : ℝ := E / Real.sqrt (N : ℝ) with hy
  set a : ℝ := T / w (N : ℤ) ^ 2 with ha
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hsqN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hy0 : 0 ≤ y := div_nonneg hE0 hsqN.le
  have hwN : 1 ≤ w (N : ℤ) := hw.one_le _
  have ha0 : 0 ≤ a := div_nonneg hT0 (sq_nonneg _)
  have haT : a ≤ T := by
    rw [ha]
    exact div_le_self hT0 (by nlinarith)
  have hsmall : Cw ^ 2 * (T + y) ≤ 1 / 60 := hs
  have hbound : ∀ ε : ℝ, 0 < ε → weightedMajorantTail w A N ≤
      ENNReal.ofReal (15 * Cw ^ 2 * (a + y + ε) ^ 2) := by
    intro ε hε
    set U : ℝ := a + y + ε with hU
    have hU0 : 0 < U := by positivity
    set c0 : ℝ := 5 * Cw * U / Real.sqrt 60 with hc0
    have hc0pos : 0 < c0 := by positivity
    set b : ℕ → ℝ := fun j => c0 * (1 / 12) ^ j with hb
    have hbpos : ∀ j, 0 < b j := fun j => by positivity
    have hb2 : ∀ j, b j ^ 2 = 25 * Cw ^ 2 * U ^ 2 / 60 * (1 / 144) ^ j := by
      intro j
      simp only [hb, hc0]
      rw [mul_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← pow_mul, mul_comm j 2, pow_mul]
      norm_num
    have hW : ∀ j (σ : Pattern (j+1)),
        (∑' n : ℤ, if N ≤ n.natAbs then ENNReal.ofReal (w (2*n)^2) *
          patternBlock (Nat.succ_pos j) A n σ ^ 2 else 0) ≤ ENNReal.ofReal (b j ^ 2) := by
      intro j σ
      refine (K027L2.weightedPattern_le_cauchy (Nat.succ_pos j) w A hA N σ).trans ?_
      rw [hb2]
      by_cases hτ : forcedTailCount (Nat.succ_pos j) σ = 0
      · refine (kst025 w A Cw hw hA hE N (j+1) hN (Nat.succ_pos j) σ hτ).2.2.trans ?_
        exact ENNReal.ofReal_le_ofReal (K027D.bq_zero Cw y T a U j hC hy0 hT0 ha0 hsmall (by linarith))
      · have hτ1 : 1 ≤ forcedTailCount (Nat.succ_pos j) σ := Nat.one_le_iff_ne_zero.2 hτ
        refine (kst026 w A Cw hw hA hE N (j+1) hN (Nat.succ_pos j) σ hτ1).2.trans ?_
        exact ENNReal.ofReal_le_ofReal (K027D.bq_one Cw y T a U j _ hC hy0 hT0 ha0 haT hsmall
          (by linarith) hτ1 (forcedTailCount_le (Nat.succ_pos j) σ))
    refine (K027L2.S_le w A hA N b hbpos hW).trans ?_
    have htot : ∑' j : ℕ, (4 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal (b j) = ENNReal.ofReal (6 * c0) :=
      total_eq c0 hc0pos
    rw [htot, ← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hsq : c0 ^ 2 = 25 * Cw ^ 2 * U ^ 2 / 60 := by
      simp only [hc0]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    calc (6 * c0) ^ 2 = 36 * c0 ^ 2 := by ring
      _ = 15 * Cw ^ 2 * U ^ 2 := by rw [hsq]; ring
  have hlim : weightedMajorantTail w A N ≤ ENNReal.ofReal (15 * Cw ^ 2 * (a + y) ^ 2) := by
    have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), weightedMajorantTail w A N ≤
        ENNReal.ofReal (15 * Cw ^ 2 * (a + y + ε) ^ 2) :=
      eventually_nhdsWithin_of_forall (fun ε hε => hbound ε hε)
    have hcont : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (15 * Cw ^ 2 * (a + y + ε) ^ 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ENNReal.ofReal (15 * Cw ^ 2 * (a + y + 0) ^ 2))) := by
      have : Continuous (fun ε : ℝ => ENNReal.ofReal (15 * Cw ^ 2 * (a + y + ε) ^ 2)) :=
        ENNReal.continuous_ofReal.comp (by fun_prop)
      exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ge_of_tendsto hcont hev
  have hu0 : 0 ≤ a + y := by positivity
  have hR : 15 * Cw ^ 2 * (a + y) ^ 2 ≤ source51RHS w A Cw N ^ 2 := by
    have hRe : source51RHS w A Cw N = 4 * Real.sqrt 2 * Cw ^ 2 * (a + y) := rfl
    rw [hRe, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    have hC2 : 1 ≤ Cw ^ 2 := by nlinarith
    have hu2 : 0 ≤ (a + y) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hu2 (sub_nonneg.2 hC2), mul_nonneg (mul_nonneg hu2 (sq_nonneg Cw)) (sub_nonneg.2 hC2)]
  have hRpos : 0 ≤ source51RHS w A Cw N := by
    have hRe : source51RHS w A Cw N = 4 * Real.sqrt 2 * Cw ^ 2 * (a + y) := rfl
    rw [hRe]; positivity
  have hS : weightedMajorantTail w A N ≤ ENNReal.ofReal (source51RHS w A Cw N ^ 2) :=
    hlim.trans (ENNReal.ofReal_le_ofReal hR)
  refine ⟨lt_of_le_of_lt hS ENNReal.ofReal_lt_top, ?_⟩
  have := ENNReal.toReal_le_of_le_ofReal (by positivity) hS
  calc Real.sqrt (weightedMajorantTail w A N).toReal ≤ Real.sqrt (source51RHS w A Cw N ^ 2) :=
        Real.sqrt_le_sqrt this
    _ = source51RHS w A Cw N := Real.sqrt_sq hRpos

end K027Core

theorem kst027 (w A : ℤ → ℝ) (Cw : ℝ)
    (hw : SlowWeight w Cw) (hA : ∀ j, 0 ≤ A j)
    (hE : scalarEnergy w A < ⊤) :
    ∃ N₂ : ℕ, 5 ≤ N₂ ∧ ∀ N : ℕ, N₂ ≤ N →
      Cw ^ 2 * ((scalarTailEnergy w A N).toReal +
        (scalarEnergy w A).toReal / Real.sqrt (N : ℝ)) ≤ (1 / 60 : ℝ) ∧
      weightedMajorantTail w A N < ⊤ ∧
      Real.sqrt (weightedMajorantTail w A N).toReal ≤ source51RHS w A Cw N := by
  obtain ⟨N₂, h5, hN₂⟩ := K027L1.kst027_tail_eventually w A Cw hE
  refine ⟨N₂, h5, fun N hN => ?_⟩
  have hs := hN₂ N hN
  exact ⟨hs, K027Core.kst027_core w A Cw hw hA hE N (by omega) hs⟩

end
end NlsGge.ThirdConsultation.KST

section
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST007 NlsGge.Pilot
namespace NlsGge.ThirdConsultation.KST
namespace K027L5b4

theorem abs_norm_sub_le_norm_sub {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    |‖x‖ - ‖y‖| ≤ ‖x - y‖ :=
  abs_norm_sub_norm_le x y

theorem majorantCoeff_sub_le (φ ψ : PhysicalPairLp) (k : ℤ) :
    |majorantCoeff φ k - majorantCoeff ψ k| ≤
      ‖potentialCoeff φ true k - potentialCoeff ψ true k‖ +
      ‖potentialCoeff φ true (-k) - potentialCoeff ψ true (-k)‖ +
      ‖potentialCoeff φ false k - potentialCoeff ψ false k‖ +
      ‖potentialCoeff φ false (-k) - potentialCoeff ψ false (-k)‖ := by
  set u1 := ‖potentialCoeff φ true k - potentialCoeff ψ true k‖
  set u2 := ‖potentialCoeff φ true (-k) - potentialCoeff ψ true (-k)‖
  set u3 := ‖potentialCoeff φ false k - potentialCoeff ψ false k‖
  set u4 := ‖potentialCoeff φ false (-k) - potentialCoeff ψ false (-k)‖
  have n1 : 0 ≤ u1 := norm_nonneg _
  have n2 : 0 ≤ u2 := norm_nonneg _
  have n3 : 0 ≤ u3 := norm_nonneg _
  have n4 : 0 ≤ u4 := norm_nonneg _
  have e1 : |‖potentialCoeff φ true k‖ - ‖potentialCoeff ψ true k‖| ≤ u1 :=
    abs_norm_sub_le_norm_sub _ _
  have e2 : |‖potentialCoeff φ true (-k)‖ - ‖potentialCoeff ψ true (-k)‖| ≤ u2 :=
    abs_norm_sub_le_norm_sub _ _
  have e3 : |‖potentialCoeff φ false k‖ - ‖potentialCoeff ψ false k‖| ≤ u3 :=
    abs_norm_sub_le_norm_sub _ _
  have e4 : |‖potentialCoeff φ false (-k)‖ - ‖potentialCoeff ψ false (-k)‖| ≤ u4 :=
    abs_norm_sub_le_norm_sub _ _
  have h1 : |max ‖potentialCoeff φ true k‖ ‖potentialCoeff φ true (-k)‖ -
      max ‖potentialCoeff ψ true k‖ ‖potentialCoeff ψ true (-k)‖| ≤ u1 + u2 + u3 + u4 :=
    (abs_max_sub_max_le_max _ _ _ _).trans
      (max_le (by linarith) (by linarith))
  have h2 : |max ‖potentialCoeff φ false k‖ ‖potentialCoeff φ false (-k)‖ -
      max ‖potentialCoeff ψ false k‖ ‖potentialCoeff ψ false (-k)‖| ≤ u1 + u2 + u3 + u4 :=
    (abs_max_sub_max_le_max _ _ _ _).trans
      (max_le (by linarith) (by linarith))
  unfold majorantCoeff
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le h1 h2)

theorem potentialCoeff_wpp_even (W : ℤ → ℝ) (hW : ∀ m, 1 ≤ W m)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)] (x : WeightedPairHilbert W) (b : Bool) (p : ℤ) :
    potentialCoeff (weightedPairPhysical W hW x) b (2 * p) = (x b : ℤ → ℂ) p := by
  unfold potentialCoeff
  rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_even]
  exact weightedPairPhysical_fourier W hW x b p

theorem potentialCoeff_wpp_odd (W : ℤ → ℝ) (hW : ∀ m, 1 ≤ W m)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)] (x : WeightedPairHilbert W) (b : Bool) (k : ℤ)
    (hk : k % 2 ≠ 0) :
    potentialCoeff (weightedPairPhysical W hW x) b k = 0 := by
  unfold potentialCoeff
  exact NlsGge.Analysis.naturalPhysicalCoverL2_fourier_odd _ k hk

/-- (i) pointwise even-index majorant difference, squared: at k = 2m the four potential
coefficient differences are the Weighted coordinates at m and -m. -/
theorem majorant_even_diff_sq_le (W : ℤ → ℝ) (hW : ∀ m, 1 ≤ W m)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)] (x y : WeightedPairHilbert W) (m : ℤ) :
    (majorantCoeff (weightedPairPhysical W hW x) (2 * m) -
        majorantCoeff (weightedPairPhysical W hW y) (2 * m)) ^ 2 ≤
      4 * (‖(x true : ℤ → ℂ) m - (y true : ℤ → ℂ) m‖ ^ 2 +
        ‖(x true : ℤ → ℂ) (-m) - (y true : ℤ → ℂ) (-m)‖ ^ 2 +
        ‖(x false : ℤ → ℂ) m - (y false : ℤ → ℂ) m‖ ^ 2 +
        ‖(x false : ℤ → ℂ) (-m) - (y false : ℤ → ℂ) (-m)‖ ^ 2) := by
  have h := majorantCoeff_sub_le (weightedPairPhysical W hW x) (weightedPairPhysical W hW y) (2 * m)
  have hneg : -(2 * m) = 2 * (-m) := by ring
  rw [hneg] at h
  simp only [potentialCoeff_wpp_even] at h
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at hsq
  refine hsq.trans ?_
  nlinarith [sq_nonneg (‖(x true : ℤ → ℂ) m - (y true : ℤ → ℂ) m‖ -
      ‖(x true : ℤ → ℂ) (-m) - (y true : ℤ → ℂ) (-m)‖),
    sq_nonneg (‖(x true : ℤ → ℂ) m - (y true : ℤ → ℂ) m‖ -
      ‖(x false : ℤ → ℂ) m - (y false : ℤ → ℂ) m‖),
    sq_nonneg (‖(x true : ℤ → ℂ) m - (y true : ℤ → ℂ) m‖ -
      ‖(x false : ℤ → ℂ) (-m) - (y false : ℤ → ℂ) (-m)‖),
    sq_nonneg (‖(x true : ℤ → ℂ) (-m) - (y true : ℤ → ℂ) (-m)‖ -
      ‖(x false : ℤ → ℂ) m - (y false : ℤ → ℂ) m‖),
    sq_nonneg (‖(x true : ℤ → ℂ) (-m) - (y true : ℤ → ℂ) (-m)‖ -
      ‖(x false : ℤ → ℂ) (-m) - (y false : ℤ → ℂ) (-m)‖),
    sq_nonneg (‖(x false : ℤ → ℂ) m - (y false : ℤ → ℂ) m‖ -
      ‖(x false : ℤ → ℂ) (-m) - (y false : ℤ → ℂ) (-m)‖)]

/-- (ii) an even-supported summand: a tsum over ℤ of a function vanishing at odd labels is the
tsum over the even labels 2m. -/
theorem tsum_eq_even_tsum {f : ℤ → ℝ} (hf : ∀ k : ℤ, k % 2 ≠ 0 → f k = 0) :
    ∑' k : ℤ, f k = ∑' m : ℤ, f (2 * m) := by
  have hinj : Function.Injective (fun m : ℤ => 2 * m) := fun a b hab => by
    simp only at hab
    omega
  have hsupp : Function.support f ⊆ Set.range (fun m : ℤ => 2 * m) := by
    intro k hk
    rcases eq_or_ne (k % 2) 0 with h0 | h0
    · exact ⟨k / 2, by simp only; omega⟩
    · exact absurd (hf k h0) hk
  exact (hinj.tsum_eq hsupp).symm


theorem weighted_coord_sub (W : ℤ → ℝ) [Fact (∀ k : ℤ, 0 < W k ^ 2)]
    (x y : NlsGge.Atomic.DM048.WeightedPairHilbert W) (b : Bool) (k : ℤ) :
    ((x - y) b : ℤ → ℂ) k = (x b : ℤ → ℂ) k - (y b : ℤ → ℂ) k := by
  rw [PiLp.sub_apply]
  rfl

/-- General weight W with the period-one relation ω(2m) = W m and W even. -/
theorem majorant_energy_diff_gen (ω W : ℤ → ℝ) (hω1 : ∀ k, 1 ≤ ω k)
    (hWω : ∀ m : ℤ, ω (2 * m) = W m) (hWe : ∀ m : ℤ, W (-m) = W m)
    (hW : ∀ m, 1 ≤ W m) [Fact (∀ k : ℤ, 0 < W k ^ 2)]
    (x y : NlsGge.Atomic.DM048.WeightedPairHilbert W) :
    ∑' k : ℤ, ω k ^ 2 *
        (majorantCoeff (weightedPairPhysical W hW x) k -
          majorantCoeff (weightedPairPhysical W hW y) k) ^ 2 ≤
      8 * ‖x - y‖ ^ 2 := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Bool → ℤ → ℝ,
      δ = fun b m => ‖(x b : ℤ → ℂ) m - (y b : ℤ → ℂ) m‖ := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℝ,
      g = fun m => W m ^ 2 * (δ true m ^ 2 + δ false m ^ 2) := ⟨_, rfl⟩
  have hWsum : ∀ b : Bool, Summable (fun m : ℤ => W m ^ 2 * ‖(x b : ℤ → ℂ) m‖ ^ 2) :=
    fun b => (weightedHilbert_hasSum (fun k => W k ^ 2) (x b)).summable
  have hWsumY : ∀ b : Bool, Summable (fun m : ℤ => W m ^ 2 * ‖(y b : ℤ → ℂ) m‖ ^ 2) :=
    fun b => (weightedHilbert_hasSum (fun k => W k ^ 2) (y b)).summable
  have hδsum : ∀ b : Bool, Summable (fun m : ℤ => W m ^ 2 * δ b m ^ 2) := by
    intro b
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun m => ?_) (Summable.mul_left 2 ((hWsum b).add (hWsumY b)))
    rw [hδ]
    have h2 : ‖(x b : ℤ → ℂ) m - (y b : ℤ → ℂ) m‖ ^ 2 ≤
        2 * (‖(x b : ℤ → ℂ) m‖ ^ 2 + ‖(y b : ℤ → ℂ) m‖ ^ 2) := by
      nlinarith [sq_nonneg (‖(x b : ℤ → ℂ) m‖ - ‖(y b : ℤ → ℂ) m‖),
        norm_nonneg ((x b : ℤ → ℂ) m - (y b : ℤ → ℂ) m),
        norm_nonneg ((x b : ℤ → ℂ) m), norm_nonneg ((y b : ℤ → ℂ) m),
        norm_sub_le ((x b : ℤ → ℂ) m) ((y b : ℤ → ℂ) m)]
    have hW2 : 0 ≤ W m ^ 2 := sq_nonneg _
    have h3 := mul_le_mul_of_nonneg_left h2 hW2
    simp only
    nlinarith [h3]
  have hgsum : Summable g := by
    have h := (hδsum true).add (hδsum false)
    rw [hg]
    refine Summable.congr h (fun m => ?_)
    ring
  have hgneg : Summable (fun m : ℤ => g (-m)) := hgsum.comp_injective neg_injective
  have hnorm : ‖x - y‖ ^ 2 = ∑' m : ℤ, g m := by
    rw [NlsGge.Atomic.DM048.weightedPairHilbert_norm_sq W (x - y)]
    refine tsum_congr fun m => ?_
    rw [hg, hδ]
    simp only [weighted_coord_sub]
  have hodd : ∀ k : ℤ, k % 2 ≠ 0 →
      ω k ^ 2 * (majorantCoeff (weightedPairPhysical W hW x) k -
        majorantCoeff (weightedPairPhysical W hW y) k) ^ 2 = 0 := by
    intro k hk
    rw [majorant_odd_eq_zero (weightedPairPhysical W hW x) k hk,
      majorant_odd_eq_zero (weightedPairPhysical W hW y) k hk]
    ring
  have hterm : ∀ m : ℤ,
      ω (2 * m) ^ 2 * (majorantCoeff (weightedPairPhysical W hW x) (2 * m) -
        majorantCoeff (weightedPairPhysical W hW y) (2 * m)) ^ 2 ≤ 4 * g m + 4 * g (-m) := by
    intro m
    have h := majorant_even_diff_sq_le W hW x y m
    have hw2 : ω (2 * m) ^ 2 = W m ^ 2 := by rw [hWω m]
    rw [hw2]
    have hg1 : g m = W m ^ 2 * (δ true m ^ 2 + δ false m ^ 2) := by rw [hg]
    have hg2 : g (-m) = W m ^ 2 * (δ true (-m) ^ 2 + δ false (-m) ^ 2) := by
      rw [hg]
      show W (-m) ^ 2 * (δ true (-m) ^ 2 + δ false (-m) ^ 2) = _
      rw [hWe m]
    rw [hg1, hg2, hδ]
    have hW2 : 0 ≤ W m ^ 2 := sq_nonneg _
    have h' := mul_le_mul_of_nonneg_left h hW2
    simp only
    nlinarith [h']
  have hbsum : Summable (fun m : ℤ => 4 * g m + 4 * g (-m)) :=
    (hgsum.mul_left 4).add (hgneg.mul_left 4)
  have hLsum : Summable (fun m : ℤ => ω (2 * m) ^ 2 *
      (majorantCoeff (weightedPairPhysical W hW x) (2 * m) -
        majorantCoeff (weightedPairPhysical W hW y) (2 * m)) ^ 2) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hterm hbsum
  rw [tsum_eq_even_tsum hodd]
  have hneg : ∑' m : ℤ, g (-m) = ∑' m : ℤ, g m := (Equiv.neg ℤ).tsum_eq g
  calc ∑' m : ℤ, ω (2 * m) ^ 2 *
        (majorantCoeff (weightedPairPhysical W hW x) (2 * m) -
          majorantCoeff (weightedPairPhysical W hW y) (2 * m)) ^ 2
      ≤ ∑' m : ℤ, (4 * g m + 4 * g (-m)) := Summable.tsum_le_tsum hterm hLsum hbsum
    _ = 4 * ∑' m : ℤ, g m + 4 * ∑' m : ℤ, g (-m) := by
        rw [Summable.tsum_add (hgsum.mul_left 4) (hgneg.mul_left 4), tsum_mul_left, tsum_mul_left]
    _ = 8 * ‖x - y‖ ^ 2 := by
        rw [hneg, ← hnorm]
        ring

-- #print axioms NlsGge.ThirdConsultation.KST.K027L5b4.majorant_energy_diff_gen

end K027L5b4
end NlsGge.ThirdConsultation.KST
end

section
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST007 NlsGge.Pilot
namespace NlsGge.ThirdConsultation.KST
namespace K027L5c

theorem potentialCoeff_wpp_even' (W : ℤ → ℝ) (hW : ∀ m, 1 ≤ W m)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)] (x : NlsGge.Atomic.DM048.WeightedPairHilbert W) (b : Bool) (p : ℤ) :
    potentialCoeff (weightedPairPhysical W hW x) b (2 * p) = (x b : ℤ → ℂ) p := by
  unfold potentialCoeff
  rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_even]
  exact weightedPairPhysical_fourier W hW x b p

/-- (c1) summability of the weighted majorant energy of one Weighted element. -/
theorem summable_majorant_energy (ω W : ℤ → ℝ) (hWω : ∀ m : ℤ, ω (2 * m) = W m)
    (hWe : ∀ m : ℤ, W (-m) = W m) (hW : ∀ m, 1 ≤ W m) [Fact (∀ k : ℤ, 0 < W k ^ 2)]
    (x : NlsGge.Atomic.DM048.WeightedPairHilbert W) :
    Summable (fun k : ℤ => ω k ^ 2 * (majorantCoeff (weightedPairPhysical W hW x) k) ^ 2) := by
  have hinj : Function.Injective (fun m : ℤ => 2 * m) := by
    intro a b h
    simp only at h
    omega
  have hrange : ∀ k : ℤ, k ∉ Set.range (fun m : ℤ => 2 * m) →
      ω k ^ 2 * (majorantCoeff (weightedPairPhysical W hW x) k) ^ 2 = 0 := by
    intro k hk
    have hodd : k % 2 ≠ 0 := by
      intro h0
      exact hk ⟨k / 2, by simp only; omega⟩
    rw [majorant_odd_eq_zero (weightedPairPhysical W hW x) k hodd]
    ring
  have hchan : ∀ b : Bool, Summable (fun m : ℤ => W m ^ 2 * ‖(x b : ℤ → ℂ) m‖ ^ 2) :=
    fun b => (weightedHilbert_hasSum (fun k => W k ^ 2) (x b)).summable
  have hchanN : ∀ b : Bool, Summable (fun m : ℤ => W m ^ 2 * ‖(x b : ℤ → ℂ) (-m)‖ ^ 2) := by
    intro b
    have h := (hchan b).comp_injective neg_injective
    refine Summable.congr h (fun m => ?_)
    show W (-m) ^ 2 * ‖(x b : ℤ → ℂ) (-m)‖ ^ 2 = W m ^ 2 * ‖(x b : ℤ → ℂ) (-m)‖ ^ 2
    rw [hWe m]
  have hbound : Summable (fun m : ℤ => 4 * (W m ^ 2 * ‖(x true : ℤ → ℂ) m‖ ^ 2 +
      W m ^ 2 * ‖(x true : ℤ → ℂ) (-m)‖ ^ 2 + W m ^ 2 * ‖(x false : ℤ → ℂ) m‖ ^ 2 +
      W m ^ 2 * ‖(x false : ℤ → ℂ) (-m)‖ ^ 2)) :=
    (((hchan true).add (hchanN true)).add (hchan false) |>.add (hchanN false)).mul_left 4
  have h2m : Summable (fun m : ℤ => ω (2 * m) ^ 2 *
      (majorantCoeff (weightedPairPhysical W hW x) (2 * m)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (fun m => ?_) hbound
    have hA : majorantCoeff (weightedPairPhysical W hW x) (2 * m) ≤
        ‖(x true : ℤ → ℂ) m‖ + ‖(x true : ℤ → ℂ) (-m)‖ + ‖(x false : ℤ → ℂ) m‖ +
          ‖(x false : ℤ → ℂ) (-m)‖ := by
      have hneg : (-(2 * m) : ℤ) = 2 * (-m) := by ring
      unfold majorantCoeff
      have e1 : ‖potentialCoeff (weightedPairPhysical W hW x) true (2 * m)‖ = ‖(x true : ℤ → ℂ) m‖ := by
        rw [potentialCoeff_wpp_even']
      have e2 : ‖potentialCoeff (weightedPairPhysical W hW x) true (-(2 * m))‖ =
          ‖(x true : ℤ → ℂ) (-m)‖ := by
        rw [hneg, potentialCoeff_wpp_even']
      have e3 : ‖potentialCoeff (weightedPairPhysical W hW x) false (2 * m)‖ =
          ‖(x false : ℤ → ℂ) m‖ := by
        rw [potentialCoeff_wpp_even']
      have e4 : ‖potentialCoeff (weightedPairPhysical W hW x) false (-(2 * m))‖ =
          ‖(x false : ℤ → ℂ) (-m)‖ := by
        rw [hneg, potentialCoeff_wpp_even']
      rw [e1, e2, e3, e4]
      have n1 := norm_nonneg ((x true : ℤ → ℂ) m)
      have n2 := norm_nonneg ((x true : ℤ → ℂ) (-m))
      have n3 := norm_nonneg ((x false : ℤ → ℂ) m)
      have n4 := norm_nonneg ((x false : ℤ → ℂ) (-m))
      exact max_le (max_le (by linarith) (by linarith)) (max_le (by linarith) (by linarith))
    have hA0 : 0 ≤ majorantCoeff (weightedPairPhysical W hW x) (2 * m) := majorant_nonneg _ _
    have hsq : (majorantCoeff (weightedPairPhysical W hW x) (2 * m)) ^ 2 ≤
        4 * (‖(x true : ℤ → ℂ) m‖ ^ 2 + ‖(x true : ℤ → ℂ) (-m)‖ ^ 2 +
          ‖(x false : ℤ → ℂ) m‖ ^ 2 + ‖(x false : ℤ → ℂ) (-m)‖ ^ 2) := by
      have hs := pow_le_pow_left₀ hA0 hA 2
      nlinarith [sq_nonneg (‖(x true : ℤ → ℂ) m‖ - ‖(x true : ℤ → ℂ) (-m)‖),
        sq_nonneg (‖(x true : ℤ → ℂ) m‖ - ‖(x false : ℤ → ℂ) m‖),
        sq_nonneg (‖(x true : ℤ → ℂ) m‖ - ‖(x false : ℤ → ℂ) (-m)‖),
        sq_nonneg (‖(x true : ℤ → ℂ) (-m)‖ - ‖(x false : ℤ → ℂ) m‖),
        sq_nonneg (‖(x true : ℤ → ℂ) (-m)‖ - ‖(x false : ℤ → ℂ) (-m)‖),
        sq_nonneg (‖(x false : ℤ → ℂ) m‖ - ‖(x false : ℤ → ℂ) (-m)‖)]
    have hW2 : 0 ≤ ω (2 * m) ^ 2 := sq_nonneg _
    rw [hWω m] at hW2 ⊢
    have h3 := mul_le_mul_of_nonneg_left hsq hW2
    nlinarith [h3]
  have hfull := (hinj.summable_iff hrange).mp h2m
  exact hfull

end K027L5c
end NlsGge.ThirdConsultation.KST
end

section

namespace NlsGge.ThirdConsultation.KST
namespace K027L5c2

/-- A pointwise square inequality: A² ≤ 2B² + 2(A−B)². -/
theorem sq_le_two_sq_add (A B : ℝ) : A ^ 2 ≤ 2 * B ^ 2 + 2 * (A - B) ^ 2 := by
  nlinarith [sq_nonneg (B - (A - B))]

/-- Restriction of a nonnegative summable family to {N ≤ |k|} is summable. -/
theorem summable_ite_natAbs (f : ℤ → ℝ) (hf0 : ∀ k, 0 ≤ f k) (hf : Summable f) (N : ℕ) :
    Summable (fun k : ℤ => if N ≤ k.natAbs then f k else 0) :=
  Summable.of_nonneg_of_le
    (fun k => by split_ifs <;> simp [hf0 k])
    (fun k => by split_ifs
                 · exact le_rfl
                 · exact hf0 k)
    hf

/-- (c2) energy inequality: Σ ω²A² ≤ 2 Σ ω²B² + 16·dist2 whenever Σ ω²(A−B)² ≤ 8·dist2. -/
theorem energy_majorant_le (ω : ℤ → ℝ) (A B : ℤ → ℝ) (dist2 : ℝ)
    (hsA : Summable (fun k => ω k ^ 2 * (A k) ^ 2))
    (hsB : Summable (fun k => ω k ^ 2 * (B k) ^ 2))
    (hdiff : ∑' k, ω k ^ 2 * (A k - B k) ^ 2 ≤ 8 * dist2) :
    ∑' k, ω k ^ 2 * (A k) ^ 2 ≤ 2 * ∑' k, ω k ^ 2 * (B k) ^ 2 + 16 * dist2 := by
  have hsd : Summable (fun k => ω k ^ 2 * (A k - B k) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun k => ?_) ((hsA.add hsB).mul_left 2)
    have h2 : (A k - B k) ^ 2 ≤ 2 * (A k) ^ 2 + 2 * (B k) ^ 2 := by
      nlinarith [sq_nonneg (A k + B k)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg (ω k))]
  have hpt : ∀ k, ω k ^ 2 * (A k) ^ 2 ≤
      2 * (ω k ^ 2 * (B k) ^ 2) + 2 * (ω k ^ 2 * (A k - B k) ^ 2) := by
    intro k
    nlinarith [mul_le_mul_of_nonneg_left (sq_le_two_sq_add (A k) (B k)) (sq_nonneg (ω k))]
  calc ∑' k, ω k ^ 2 * (A k) ^ 2
      ≤ ∑' k, (2 * (ω k ^ 2 * (B k) ^ 2) + 2 * (ω k ^ 2 * (A k - B k) ^ 2)) :=
        Summable.tsum_le_tsum hpt hsA ((hsB.mul_left 2).add (hsd.mul_left 2))
    _ = 2 * ∑' k, ω k ^ 2 * (B k) ^ 2 + 2 * ∑' k, ω k ^ 2 * (A k - B k) ^ 2 := by
        rw [Summable.tsum_add (hsB.mul_left 2) (hsd.mul_left 2), tsum_mul_left, tsum_mul_left]
    _ ≤ 2 * ∑' k, ω k ^ 2 * (B k) ^ 2 + 2 * (8 * dist2) := by linarith [hdiff]
    _ = 2 * ∑' k, ω k ^ 2 * (B k) ^ 2 + 16 * dist2 := by ring

/-- (c3) tail inequality over {N ≤ |k|}. -/
theorem tail_majorant_le (ω : ℤ → ℝ) (A B : ℤ → ℝ) (dist2 : ℝ) (N : ℕ)
    (hsA : Summable (fun k => ω k ^ 2 * (A k) ^ 2))
    (hsB : Summable (fun k => ω k ^ 2 * (B k) ^ 2))
    (hdiff : ∑' k, ω k ^ 2 * (A k - B k) ^ 2 ≤ 8 * dist2) :
    ∑' k, (if N ≤ k.natAbs then ω k ^ 2 * (A k) ^ 2 else 0) ≤
      2 * ∑' k, (if N ≤ k.natAbs then ω k ^ 2 * (B k) ^ 2 else 0) + 16 * dist2 := by
  have hsd : Summable (fun k => ω k ^ 2 * (A k - B k) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun k => ?_) ((hsA.add hsB).mul_left 2)
    have h2 : (A k - B k) ^ 2 ≤ 2 * (A k) ^ 2 + 2 * (B k) ^ 2 := by
      nlinarith [sq_nonneg (A k + B k)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg (ω k))]
  have hsA' := summable_ite_natAbs (fun k => ω k ^ 2 * (A k) ^ 2)
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsA N
  have hsB' := summable_ite_natAbs (fun k => ω k ^ 2 * (B k) ^ 2)
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsB N
  have hsd' := summable_ite_natAbs (fun k => ω k ^ 2 * (A k - B k) ^ 2)
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsd N
  have hpt : ∀ k, (if N ≤ k.natAbs then ω k ^ 2 * (A k) ^ 2 else 0) ≤
      2 * (if N ≤ k.natAbs then ω k ^ 2 * (B k) ^ 2 else 0) +
        2 * (if N ≤ k.natAbs then ω k ^ 2 * (A k - B k) ^ 2 else 0) := by
    intro k
    by_cases hN : N ≤ k.natAbs
    · simp only [hN, if_true]
      nlinarith [mul_le_mul_of_nonneg_left (sq_le_two_sq_add (A k) (B k)) (sq_nonneg (ω k))]
    · simp [hN]
  have hle : ∀ k, (if N ≤ k.natAbs then ω k ^ 2 * (A k - B k) ^ 2 else 0) ≤
      ω k ^ 2 * (A k - B k) ^ 2 := by
    intro k
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsdsum : ∑' k, (if N ≤ k.natAbs then ω k ^ 2 * (A k - B k) ^ 2 else 0) ≤ 8 * dist2 :=
    (Summable.tsum_le_tsum hle hsd' hsd).trans hdiff
  calc ∑' k, (if N ≤ k.natAbs then ω k ^ 2 * (A k) ^ 2 else 0)
      ≤ ∑' k, (2 * (if N ≤ k.natAbs then ω k ^ 2 * (B k) ^ 2 else 0) +
          2 * (if N ≤ k.natAbs then ω k ^ 2 * (A k - B k) ^ 2 else 0)) :=
        Summable.tsum_le_tsum hpt hsA' ((hsB'.mul_left 2).add (hsd'.mul_left 2))
    _ = 2 * ∑' k, (if N ≤ k.natAbs then ω k ^ 2 * (B k) ^ 2 else 0) +
          2 * ∑' k, (if N ≤ k.natAbs then ω k ^ 2 * (A k - B k) ^ 2 else 0) := by
        rw [Summable.tsum_add (hsB'.mul_left 2) (hsd'.mul_left 2), tsum_mul_left, tsum_mul_left]
    _ ≤ 2 * ∑' k, (if N ≤ k.natAbs then ω k ^ 2 * (B k) ^ 2 else 0) + 2 * (8 * dist2) := by
        linarith [hsdsum]
    _ = 2 * ∑' k, (if N ≤ k.natAbs then ω k ^ 2 * (B k) ^ 2 else 0) + 16 * dist2 := by ring

-- #print axioms NlsGge.ThirdConsultation.KST.K027L5c2.energy_majorant_le
-- #print axioms NlsGge.ThirdConsultation.KST.K027L5c2.tail_majorant_le

end K027L5c2
end NlsGge.ThirdConsultation.KST
end


namespace NlsGge.ThirdConsultation.KST
noncomputable section
open scoped ENNReal BigOperators
open NlsGge.Atomic.KSTPath NlsGge.Atomic.KST NlsGge.Atomic.KST002 NlsGge.Atomic.KST007 NlsGge.Atomic.KST016 NlsGge.Pilot

def weightFact (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k) :
    Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2) :=
  ⟨fun m => sq_pos_of_pos (lt_of_lt_of_le zero_lt_one (hω (2*m)))⟩

abbrev Weighted (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] :=
  NlsGge.Atomic.DM048.WeightedPairHilbert (periodOneWeight ω)

def weightedPotential (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x : Weighted ω) : Potential :=
  weightedPairPhysical (periodOneWeight ω) (fun m => hω (2*m)) x

namespace K027Loc

theorem sc_toReal (w A : ℤ → ℝ) (hs : Summable (fun k => w k ^ 2 * (A k) ^ 2)) :
    scalarEnergy w A = ENNReal.ofReal (∑' k, w k ^ 2 * (A k) ^ 2) := by
  unfold scalarEnergy
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs]

theorem tail_toReal (w A : ℤ → ℝ) (N : ℕ) (hs : Summable (fun k => w k ^ 2 * (A k) ^ 2)) :
    scalarTailEnergy w A N =
      ENNReal.ofReal (∑' k, if N ≤ k.natAbs then w k ^ 2 * (A k) ^ 2 else 0) := by
  have hs' := K027L5c2.summable_ite_natAbs (fun k => w k ^ 2 * (A k) ^ 2)
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs N
  unfold scalarTailEnergy
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by split_ifs <;> first | positivity | exact le_rfl) hs']
  refine tsum_congr (fun k => ?_)
  split_ifs <;> simp

theorem majorantCoeff_nonneg' (φ : PhysicalPairLp) (k : ℤ) : 0 ≤ majorantCoeff φ k :=
  le_max_of_le_left (le_max_of_le_left (norm_nonneg _))

end K027Loc

theorem kst027_locally_uniform (w : ℤ → ℝ) (Cw : ℝ)
    (hw : SlowWeight w Cw) :
    let hω := hw.one_le
    letI := weightFact w hω
    ∀ x₀ : Weighted w, ∃ e : ℝ, 0 < e ∧ ∃ N₂ : ℕ, 5 ≤ N₂ ∧
      ∀ x : Weighted w, ‖x - x₀‖ < e →
        let A := majorantCoeff (weightedPotential w hω x)
        ∀ N : ℕ, N₂ ≤ N →
          weightedMajorantTail w A N < ⊤ ∧
          Real.sqrt (weightedMajorantTail w A N).toReal ≤
            source51RHS w A Cw N := by
  intro hω
  letI := weightFact w hω
  intro x₀
  have hC : 1 ≤ Cw := slowWeight_Cw_one_le hw
  have hWω : ∀ m : ℤ, w (2 * m) = periodOneWeight w m := fun m => rfl
  have hWe : ∀ m : ℤ, periodOneWeight w (-m) = periodOneWeight w m := by
    intro m
    show w (2 * (-m)) = w (2 * m)
    rw [show 2 * (-m) = -(2 * m) by ring]
    exact hw.even _
  have hW1 : ∀ m : ℤ, 1 ≤ periodOneWeight w m := fun m => hω (2 * m)
  have hs0 := K027L5c.summable_majorant_energy w (periodOneWeight w) hWω hWe hW1 x₀
  set A0 : ℤ → ℝ := majorantCoeff (weightedPotential w hω x₀) with hA0
  have hE0 : scalarEnergy w A0 < ⊤ := by
    rw [K027Loc.sc_toReal w A0 hs0]; exact ENNReal.ofReal_lt_top
  obtain ⟨N₂, h5, hN₂⟩ := K027L1.kst027_tail_eventually w A0 (2 * Cw) hE0
  refine ⟨1 / (62 * Cw), by positivity, N₂, h5, fun x hx => ?_⟩
  intro A N hN
  have hsx := K027L5c.summable_majorant_energy w (periodOneWeight w) hWω hWe hW1 x
  have hdiff := K027L5b4.majorant_energy_diff_gen w (periodOneWeight w) hω hWω hWe hW1 x x₀
  have hAx : ∀ j, 0 ≤ A j := fun j => K027Loc.majorantCoeff_nonneg' _ j
  have Epr := K027L5c2.energy_majorant_le w A A0 (‖x - x₀‖ ^ 2) hsx hs0 hdiff
  have Tpr := K027L5c2.tail_majorant_le w A A0 (‖x - x₀‖ ^ 2) N hsx hs0 hdiff
  have hEx : scalarEnergy w A < ⊤ := by
    rw [K027Loc.sc_toReal w A hsx]; exact ENNReal.ofReal_lt_top
  have hEreal : (scalarEnergy w A).toReal = ∑' k, w k ^ 2 * (A k) ^ 2 := by
    rw [K027Loc.sc_toReal w A hsx, ENNReal.toReal_ofReal (tsum_nonneg (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
  have hE0real : (scalarEnergy w A0).toReal = ∑' k, w k ^ 2 * (A0 k) ^ 2 := by
    rw [K027Loc.sc_toReal w A0 hs0, ENNReal.toReal_ofReal (tsum_nonneg (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
  have hTreal : (scalarTailEnergy w A N).toReal = ∑' k, (if N ≤ k.natAbs then w k ^ 2 * (A k) ^ 2 else 0) := by
    rw [K027Loc.tail_toReal w A N hsx, ENNReal.toReal_ofReal (tsum_nonneg (fun k => by split_ifs <;> first | positivity | exact le_rfl))]
  have hT0real : (scalarTailEnergy w A0 N).toReal = ∑' k, (if N ≤ k.natAbs then w k ^ 2 * (A0 k) ^ 2 else 0) := by
    rw [K027Loc.tail_toReal w A0 N hs0, ENNReal.toReal_ofReal (tsum_nonneg (fun k => by split_ifs <;> first | positivity | exact le_rfl))]
  have hsm := hN₂ N hN
  have hN1 : 1 ≤ N := by omega
  have hsq1 : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN1)
  have hsqpos : 0 < Real.sqrt (N : ℝ) := by linarith
  have hd : ‖x - x₀‖ ^ 2 < (1 / (62 * Cw)) ^ 2 := by
    exact pow_lt_pow_left₀ hx (norm_nonneg _) (by norm_num)
  have hd2 : 0 ≤ ‖x - x₀‖ ^ 2 := sq_nonneg _
  have hC2 : 1 ≤ Cw ^ 2 := by nlinarith
  have hCd : Cw ^ 2 * ‖x - x₀‖ ^ 2 ≤ 1 / 3844 := by
    have : Cw ^ 2 * (1 / (62 * Cw)) ^ 2 = 1 / 3844 := by
      field_simp; ring
    nlinarith
  have hT0nn : 0 ≤ (scalarTailEnergy w A0 N).toReal := ENNReal.toReal_nonneg
  have hE0nn : 0 ≤ (scalarEnergy w A0).toReal := ENNReal.toReal_nonneg
  have hsmall : Cw ^ 2 * ((scalarTailEnergy w A N).toReal + (scalarEnergy w A).toReal / Real.sqrt (N : ℝ)) ≤ 1 / 60 := by
    rw [hEreal, hTreal]
    have hEp : ∑' k, w k ^ 2 * (A k) ^ 2 ≤ 2 * (scalarEnergy w A0).toReal + 16 * ‖x - x₀‖ ^ 2 := by
      rw [hE0real]; exact Epr
    have hTp : ∑' k, (if N ≤ k.natAbs then w k ^ 2 * (A k) ^ 2 else 0) ≤ 2 * (scalarTailEnergy w A0 N).toReal + 16 * ‖x - x₀‖ ^ 2 := by
      rw [hT0real]; exact Tpr
    have hdiv : (∑' k, w k ^ 2 * (A k) ^ 2) / Real.sqrt (N : ℝ) ≤
        (2 * (scalarEnergy w A0).toReal + 16 * ‖x - x₀‖ ^ 2) / Real.sqrt (N : ℝ) :=
      div_le_div_of_nonneg_right hEp hsqpos.le
    have h16 : 16 * ‖x - x₀‖ ^ 2 / Real.sqrt (N : ℝ) ≤ 16 * ‖x - x₀‖ ^ 2 :=
      div_le_self (by positivity) hsq1
    have hsm' : 4 * Cw ^ 2 * ((scalarTailEnergy w A0 N).toReal + (scalarEnergy w A0).toReal / Real.sqrt (N : ℝ)) ≤ 1 / 60 := by
      have : (2 * Cw) ^ 2 = 4 * Cw ^ 2 := by ring
      rw [this] at hsm; exact hsm
    have e1 : (2 * (scalarEnergy w A0).toReal + 16 * ‖x - x₀‖ ^ 2) / Real.sqrt (N : ℝ) =
        2 * ((scalarEnergy w A0).toReal / Real.sqrt (N : ℝ)) + 16 * ‖x - x₀‖ ^ 2 / Real.sqrt (N : ℝ) := by
      ring
    have hmul : Cw ^ 2 * ((∑' k, (if N ≤ k.natAbs then w k ^ 2 * (A k) ^ 2 else 0)) +
        (∑' k, w k ^ 2 * (A k) ^ 2) / Real.sqrt (N : ℝ)) ≤
        Cw ^ 2 * ((2 * (scalarTailEnergy w A0 N).toReal + 16 * ‖x - x₀‖ ^ 2) +
          (2 * ((scalarEnergy w A0).toReal / Real.sqrt (N : ℝ)) + 16 * ‖x - x₀‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith [e1]) (sq_nonneg Cw)
    nlinarith [hmul, hsm', hCd]
  exact K027Core.kst027_core w A Cw hw hAx hEx N hN1 hsmall

end
end NlsGge.ThirdConsultation.KST
