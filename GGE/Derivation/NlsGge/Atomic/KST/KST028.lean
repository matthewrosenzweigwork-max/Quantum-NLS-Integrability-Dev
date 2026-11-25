import Mathlib
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.Atomic.KST.KST027

/- KST-028 PRODUCTION01 (proof development, AUTHOR). Target NlsGge/Atomic/KST/KST028.lean, namespace NlsGge.ThirdConsultation.KST.
   Hosts (in KST/Basic.lean): SecondaryWeight, sourceCorollary41RHS (and KST-local AdmissibleWeight).
   Heads verbatim from STATEMENTS/KST.md KST-028 (kst028, kst028_corollary).
   kst028: the 2k+1 path arguments have alternating sum 2n; v even + submultiplicative gives v(2n) <= prod v(arg);
   termwise comparison of pathBlock, then tsum_le_tsum.
   kst028_corollary: constant-weight reduction w = 1, A' = v*A. kst027 only gives constant 4*sqrt2; the sharper
   intermediate bound weightedMajorantTail <= 15 (a+y)^2 inside kst027_core is not exported, so its proof (hbound/hlim,
   specialised no further) is re-run verbatim as K028.core_hlim from the exported K027 lemmas. -/
set_option autoImplicit false
open scoped ENNReal BigOperators
open NlsGge.Atomic.KSTPath NlsGge.Atomic.KST NlsGge.Atomic.DM046

namespace NlsGge.ThirdConsultation.KST
noncomputable section

namespace K028

theorem alt_sum (y : ℕ → ℤ) : ∀ m : ℕ,
    ∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ j * (y j + y (j + 1)) =
      y 0 - (-1) ^ (m + 1) * y (m + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem sub_prod {v : ℤ → ℝ} (hv0 : ∀ k, 1 ≤ v k) (hev : ∀ k, v (-k) = v k)
    (hsub : SubmultiplicativeWeight v) (s : ℕ → ℤ) : ∀ m : ℕ,
    v (∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ j * s j) ≤ ∏ j ∈ Finset.range (m + 1), v (s j) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hs : v ((-1 : ℤ) ^ (m + 1) * s (m + 1)) = v (s (m + 1)) := by
      rcases neg_one_pow_eq_or ℤ (m + 1) with h | h
      · rw [h, one_mul]
      · rw [h, neg_one_mul, hev]
    have hnn : 0 ≤ v (s (m + 1)) := by linarith [hv0 (s (m + 1))]
    calc _ ≤ v (∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ j * s j) * v ((-1 : ℤ) ^ (m + 1) * s (m + 1)) :=
          hsub _ _
      _ ≤ (∏ j ∈ Finset.range (m + 1), v (s j)) * v (s (m + 1)) := by
          rw [hs]; exact mul_le_mul_of_nonneg_right ih hnn

def yseq {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) (i : ℕ) : ℤ :=
  if i = 0 then n else if i ≤ 2 * k then ℓ (vertexIndex hk (i - 1)) else n

theorem pathArgument_eq {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) (j : Fin (2 * k + 1)) :
    pathArgument hk n ℓ j = yseq hk n ℓ j + yseq hk n ℓ (j + 1) := by
  have hj := j.isLt
  unfold pathArgument yseq
  by_cases h0 : (j : ℕ) = 0
  · simp [h0]
    omega
  · by_cases h1 : (j : ℕ) < 2 * k
    · simp [h0, h1]
      omega
    · have e : (j : ℕ) = 2 * k := by omega
      simp [h0, h1, e]
      omega

theorem v_le_prod {v : ℤ → ℝ} (hv0 : ∀ k, 1 ≤ v k) (hev : ∀ k, v (-k) = v k)
    (hsub : SubmultiplicativeWeight v) {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) :
    v (2 * n) ≤ ∏ j : Fin (2 * k + 1), v (pathArgument hk n ℓ j) := by
  simp_rw [pathArgument_eq]
  rw [Fin.prod_univ_eq_prod_range (fun j => v (yseq hk n ℓ j + yseq hk n ℓ (j + 1))) (2 * k + 1)]
  have h := sub_prod hv0 hev hsub (fun j => yseq hk n ℓ j + yseq hk n ℓ (j + 1)) (2 * k)
  have e := alt_sum (yseq hk n ℓ) (2 * k)
  have y0 : yseq hk n ℓ 0 = n := by simp [yseq]
  have y1 : yseq hk n ℓ (2 * k + 1) = n := by
    unfold yseq
    have : ¬ (2 * k + 1 ≤ 2 * k) := by omega
    simp [this]
  rw [y0, y1, (Odd.neg_one_pow (⟨k, rfl⟩ : Odd (2 * k + 1)))] at e
  have e2 : 2 * n = ∑ j ∈ Finset.range (2 * k + 1),
      (-1 : ℤ) ^ j * (yseq hk n ℓ j + yseq hk n ℓ (j + 1)) := by rw [e]; ring
  rw [e2]
  exact h

theorem pathProduct_ge {v A : ℤ → ℝ} (hv0 : ∀ k, 1 ≤ v k) (hev : ∀ k, v (-k) = v k)
    (hsub : SubmultiplicativeWeight v) (hA : ∀ j, 0 ≤ A j) {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) :
    v (2 * n) * pathProduct hk A n ℓ ≤ pathProduct hk (fun j => v j * A j) n ℓ := by
  unfold pathProduct
  rw [Finset.prod_mul_distrib, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => by positivity)
  exact mul_le_mul_of_nonneg_right (v_le_prod hv0 hev hsub hk n ℓ)
    (Finset.prod_nonneg fun i _ => hA _)

open Classical in
theorem pathBlock_ge {v A : ℤ → ℝ} (hv0 : ∀ k, 1 ≤ v k) (hev : ∀ k, v (-k) = v k)
    (hsub : SubmultiplicativeWeight v) (hA : ∀ j, 0 ≤ A j) {k : ℕ} (hk : 0 < k) (n : ℤ) :
    ENNReal.ofReal (v (2 * n)) * pathBlock hk A n ≤ pathBlock hk (fun j => v j * A j) n := by
  unfold pathBlock
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ℓ => ?_
  split_ifs with h
  · rw [← ENNReal.ofReal_mul (by linarith [hv0 (2 * n)])]
    exact ENNReal.ofReal_le_ofReal (pathProduct_ge hv0 hev hsub hA hk n ℓ)
  · simp

end K028

theorem kst028 (v A : ℤ → ℝ) (hv : SecondaryWeight v)
    (hA : ∀ j, 0 ≤ A j) (n : ℤ) :
  ENNReal.ofReal (v (2*n)) * pathMajorant A n ≤
    pathMajorant (fun j => v j*A j) n := by
  obtain ⟨⟨hv0, hev, -⟩, hsub⟩ := hv
  unfold pathMajorant
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun j => K028.pathBlock_ge hv0 hev hsub hA (Nat.succ_pos j) n

namespace K028

theorem core_hlim (w A : ℤ → ℝ) (Cw : ℝ) (hw : SlowWeight w Cw) (hA : ∀ j, 0 ≤ A j)
    (hE : scalarEnergy w A < ⊤) (N : ℕ) (hN : 1 ≤ N)
    (hs : Cw ^ 2 * ((scalarTailEnergy w A N).toReal +
      (scalarEnergy w A).toReal / Real.sqrt (N : ℝ)) ≤ (1 / 60 : ℝ)) :
    weightedMajorantTail w A N ≤ ENNReal.ofReal (15 * Cw ^ 2 *
      ((scalarTailEnergy w A N).toReal / w (N : ℤ) ^ 2 +
        (scalarEnergy w A).toReal / Real.sqrt (N : ℝ)) ^ 2) := by
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
          (by linarith) hτ1 (K027Core.forcedTailCount_le (Nat.succ_pos j) σ))
    refine (K027L2.S_le w A hA N b hbpos hW).trans ?_
    have htot : ∑' j : ℕ, (4 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal (b j) = ENNReal.ofReal (6 * c0) :=
      K027Core.total_eq c0 hc0pos
    rw [htot, ← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hsq : c0 ^ 2 = 25 * Cw ^ 2 * U ^ 2 / 60 := by
      simp only [hc0]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    calc (6 * c0) ^ 2 = 36 * c0 ^ 2 := by ring
      _ = 15 * Cw ^ 2 * U ^ 2 := by rw [hsq]; ring
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), weightedMajorantTail w A N ≤
      ENNReal.ofReal (15 * Cw ^ 2 * (a + y + ε) ^ 2) :=
    eventually_nhdsWithin_of_forall (fun ε hε => hbound ε hε)
  have hcont : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (15 * Cw ^ 2 * (a + y + ε) ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ENNReal.ofReal (15 * Cw ^ 2 * (a + y + 0) ^ 2))) := by
    have : Continuous (fun ε : ℝ => ENNReal.ofReal (15 * Cw ^ 2 * (a + y + ε) ^ 2)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa using ge_of_tendsto hcont hev

end K028

theorem kst028_corollary (v A : ℤ → ℝ)
    (hv : SecondaryWeight v) (hA : ∀ j, 0 ≤ A j)
    (hE : scalarEnergy v A < ⊤) :
  ∃ N₂ : ℕ, 5 ≤ N₂ ∧ ∀ N : ℕ, N₂ ≤ N →
    weightedMajorantTail v A N < ⊤ ∧
    Real.sqrt (weightedMajorantTail v A N).toReal ≤
      sourceCorollary41RHS v A N := by
  have hv' := hv
  obtain ⟨⟨hv0, -, -⟩, -⟩ := hv'
  set A' : ℤ → ℝ := fun j => v j * A j with hA'def
  have hA' : ∀ j, 0 ≤ A j → 0 ≤ A' j := fun j h => mul_nonneg (by linarith [hv0 j]) h
  have hA'0 : ∀ j, 0 ≤ A' j := fun j => hA' j (hA j)
  set w1 : ℤ → ℝ := fun _ => 1 with hw1
  have hw : SlowWeight w1 1 :=
    ⟨fun _ => le_rfl, fun _ => rfl, fun _ _ _ => le_rfl, fun _ => by simp [hw1]⟩
  have hEn : scalarEnergy w1 A' = scalarEnergy v A := by
    unfold scalarEnergy
    refine tsum_congr fun j => ?_
    simp only [hw1, hA'def]
    congr 1; ring
  have hTn : ∀ N, scalarTailEnergy w1 A' N = scalarTailEnergy v A N := by
    intro N
    unfold scalarTailEnergy
    refine tsum_congr fun j => ?_
    simp only [hw1, hA'def]
    congr 2; ring
  have hE' : scalarEnergy w1 A' < ⊤ := by rw [hEn]; exact hE
  obtain ⟨N₂, h5, hN₂⟩ := K027L1.kst027_tail_eventually w1 A' 1 hE'
  refine ⟨N₂, h5, fun N hN => ?_⟩
  have hs := hN₂ N hN
  have hh := K028.core_hlim w1 A' 1 hw hA'0 hE' N (by omega) hs
  have hcmp : weightedMajorantTail v A N ≤ weightedMajorantTail w1 A' N := by
    unfold weightedMajorantTail
    refine ENNReal.tsum_le_tsum fun n => ?_
    split_ifs
    · have h28 := kst028 v A hv hA n
      have hsq : ENNReal.ofReal (v (2 * n) ^ 2) = ENNReal.ofReal (v (2 * n)) ^ 2 :=
        ENNReal.ofReal_pow (by linarith [hv0 (2 * n)]) 2
      rw [hsq, ← mul_pow]
      calc _ ≤ _ := pow_le_pow_left' h28 2
        _ = _ := by simp [hw1, hA'def]
    · exact le_rfl
  set T : ℝ := (scalarTailEnergy v A N).toReal with hT
  set y : ℝ := (scalarEnergy v A).toReal / Real.sqrt (N : ℝ) with hy
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hy0 : 0 ≤ y := div_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)
  have hh' : weightedMajorantTail v A N ≤ ENNReal.ofReal (15 * (T + y) ^ 2) := by
    refine hcmp.trans (hh.trans (le_of_eq ?_))
    rw [hTn N, hEn]
    congr 1
    simp only [hw1, hT, hy]
    ring
  have hR : 15 * (T + y) ^ 2 ≤ sourceCorollary41RHS v A N ^ 2 := by
    have hRe : sourceCorollary41RHS v A N = 4 * (T + y) := rfl
    rw [hRe]
    nlinarith [sq_nonneg (T + y)]
  have hRpos : 0 ≤ sourceCorollary41RHS v A N := by
    have hRe : sourceCorollary41RHS v A N = 4 * (T + y) := rfl
    rw [hRe]; positivity
  have hS : weightedMajorantTail v A N ≤ ENNReal.ofReal (sourceCorollary41RHS v A N ^ 2) :=
    hh'.trans (ENNReal.ofReal_le_ofReal hR)
  refine ⟨lt_of_le_of_lt hS ENNReal.ofReal_lt_top, ?_⟩
  have := ENNReal.toReal_le_of_le_ofReal (by positivity) hS
  calc Real.sqrt (weightedMajorantTail v A N).toReal ≤ Real.sqrt (sourceCorollary41RHS v A N ^ 2) :=
        Real.sqrt_le_sqrt this
    _ = sourceCorollary41RHS v A N := Real.sqrt_sq hRpos

end
end NlsGge.ThirdConsultation.KST
