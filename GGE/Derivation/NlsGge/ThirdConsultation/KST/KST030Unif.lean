import Mathlib
import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST003
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST006
import NlsGge.Atomic.KST.KST007
import NlsGge.Atomic.KST.KST011
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST013
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST021
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST029
import NlsGge.Atomic.KST.KST030
import NlsGge.Atomic.KST.KST059
import NlsGge.Atomic.KSTPath
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST033Support

/- KST030Unif PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST030Unif.lean.
   SUPPORTING module for G2-043 (no packet increment).  Locally uniform version of the KST-030 gap estimate:
   `kst021_uniform` (the path-remainder bound of KST-021 with one radius/threshold on an L2 ball, proof of kst021 with the ball),
   `K030U.tail_le` (the pointwise estimate of K030.gapEnergy_lt_top with the thresholds supplied, tail sum),
   `K030U.gap_tail_uniform` (for a SlowWeight w and phi0 with finite w-energy: radius e, threshold N1 and bound B with
   sum_{|n|>=N} w(2n)^2 |gap_n(phi)|^2 <= B for every pair phi with w-energy distance < e from phi0 and every N >= N1),
   via the landed kst027_locally_uniform, kst029 and the weighted-potential bridge KST033S.  Source proof of Theorem 4.1 /
   Corollary 4.1 made uniform; no new hypothesis, no changed statement of any landed theorem. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NlsGge.ThirdConsultation.KST

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003
open NlsGge.Atomic.KST004 NlsGge.Atomic.KST006 NlsGge.Atomic.KST007
open NlsGge.Atomic.KST012 NlsGge.Atomic.KST013 NlsGge.Atomic.KST016
open NlsGge.Analysis NlsGge.Pilot NlsGge.Schur NlsGge.Atomic.KSTPath
open NlsGge.GK38 NlsGge.Atomic.KST001 NlsGge.Atomic.KST059 NlsGge.Atomic.DM046
open NlsGge.Atomic.KST NlsGge.Atomic.KST002

/-- Locally uniform version of the path-remainder part of `kst021`: one radius and one threshold
serve every potential in the ball. -/
theorem kst021_uniform (φ₀ : Potential) :
  ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, 5 ≤ N₀ ∧ ∀ ψ : Potential, ‖ψ - φ₀‖ < ε →
    ∀ n : ℤ, N₀ ≤ n.natAbs →
    pathMajorant (majorantCoeff ψ) n < ⊤ ∧
    ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
      ‖reducedB ψ n z hz - coveredCoeff ψ false (2*n)‖ ≤ (pathMajorant (majorantCoeff ψ) n).toReal ∧
      ‖reducedC ψ n z hz - coveredCoeff ψ true (-2*n)‖ ≤ (pathMajorant (majorantCoeff ψ) n).toReal := by
  obtain ⟨ε, hε, N₁, hN₁, hloc⟩ := reducedBC_uniform_local φ₀
  obtain ⟨ε2, hε2, N₂, hN₂, hhs⟩ := NlsGge.Atomic.KST011.hs_qOperator_sq_decay φ₀
  refine ⟨min ε ε2, lt_min hε hε2, max N₁ N₂, le_trans hN₁ (le_max_left _ _), ?_⟩
  intro ψ hψ n hn
  have hψ1 : ‖ψ - φ₀‖ < ε := lt_of_lt_of_le hψ (min_le_left _ _)
  have hψ2 : ‖ψ - φ₀‖ < ε2 := lt_of_lt_of_le hψ (min_le_right _ _)
  have hn1 : N₁ ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n.natAbs := le_trans (le_max_right _ _) hn
  have hM : ‖(positiveBlock ψ n false) * (positiveBlock ψ n true)‖ ≤ 1 / 4 :=
    hsNorm_block_le ψ n ((hhs ψ hψ2 n hn2).1 false)
  have hsum := ppt_summable ψ n hM
  have hpp : ∀ j : ℕ, positivePathTerm ψ n j = (Rv ψ n (2 * (j + 1)) n : ℂ) := ppt_eq_Rv ψ n
  have hr0 : ∀ j : ℕ, 0 ≤ Rv ψ n (2 * (j + 1)) n := fun j => Rv_nonneg ψ n _ _
  have hnorm : ∀ j : ℕ, ‖positivePathTerm ψ n j‖ = Rv ψ n (2 * (j + 1)) n := by
    intro j
    rw [hpp j, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 j)]
  have hsumR : Summable (fun j : ℕ => Rv ψ n (2 * (j + 1)) n) := hsum.congr hnorm
  have hmaj : pathMajorant (majorantCoeff ψ) n =
      ENNReal.ofReal (∑' j : ℕ, Rv ψ n (2 * (j + 1)) n) := by
    unfold pathMajorant
    rw [ENNReal.ofReal_tsum_of_nonneg hr0 hsumR]
    exact tsum_congr (fun j => pathBlock_eq_ofReal ψ n j)
  have hMtoReal : (pathMajorant (majorantCoeff ψ) n).toReal = ∑' j : ℕ, Rv ψ n (2 * (j + 1)) n := by
    rw [hmaj, ENNReal.toReal_ofReal (tsum_nonneg hr0)]
  refine ⟨by rw [hmaj]; exact ENNReal.ofReal_lt_top, fun z hz => ?_⟩
  have hq : ‖qOperator ψ n z hz ^ 2‖ ≤ 1 / 2 := (hloc ψ hψ1 n hn1 z hz).1
  have hlt : ‖qOperator ψ n z hz ^ 2‖ < 1 := lt_of_le_of_lt hq (by norm_num)
  have hsB : Summable (fun j : ℕ => ‖pathTerm ψ n z hz (2 * j + 2) false true‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => pathTerm_B_le ψ n z hz j) hsum
  have hsC : Summable (fun j : ℕ => ‖pathTerm ψ n z hz (2 * j + 2) true false‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => pathTerm_C_le ψ n z hz j) hsum
  have hremB : ‖remainderB ψ n z hz‖ ≤ (pathMajorant (majorantCoeff ψ) n).toReal := by
    rw [hMtoReal]
    calc ‖remainderB ψ n z hz‖ ≤ ∑' j : ℕ, ‖pathTerm ψ n z hz (2 * j + 2) false true‖ :=
          norm_tsum_le_tsum_norm hsB
      _ ≤ ∑' j : ℕ, ‖positivePathTerm ψ n j‖ :=
          hsB.tsum_le_tsum (fun j => pathTerm_B_le ψ n z hz j) hsum
      _ = _ := tsum_congr hnorm
  have hremC : ‖remainderC ψ n z hz‖ ≤ (pathMajorant (majorantCoeff ψ) n).toReal := by
    rw [hMtoReal]
    calc ‖remainderC ψ n z hz‖ ≤ ∑' j : ℕ, ‖pathTerm ψ n z hz (2 * j + 2) true false‖ :=
          norm_tsum_le_tsum_norm hsC
      _ ≤ ∑' j : ℕ, ‖positivePathTerm ψ n j‖ :=
          hsC.tsum_le_tsum (fun j => pathTerm_C_le ψ n z hz j) hsum
      _ = _ := tsum_congr hnorm
  obtain ⟨-, -, hB, hC⟩ := reducedBC_fourier_remainders ψ n z hz hlt
  refine ⟨?_, ?_⟩
  · rw [hB, add_sub_cancel_left]; exact hremB
  · rw [hC, add_sub_cancel_left]; exact hremC


namespace K030U

theorem scalarEnergy_le_two (ω : ℤ → ℝ) (hev : ∀ k, ω (-k) = ω k)
    (ψ : Potential) (φ : PotPair) (h1 : ψ true = φ.1) (h2 : ψ false = φ.2)
      :
    scalarEnergy ω (majorantCoeff ψ) ≤ weightedNormSq₂ ω φ + weightedNormSq₂ ω φ := by
  set W : ℤ → ℝ≥0∞ := fun k => weightedPairMode ω k (periodTwoPairCoeff φ k) with hW
  have hterm : ∀ j : ℤ, ENNReal.ofReal (ω j ^ 2 * majorantCoeff ψ j ^ 2) ≤ W j + W (-j) := by
    intro j
    have hs := K030.majorant_sq_le ψ j
    have hp : 0 ≤ ω j ^ 2 := sq_nonneg _
    have e1 : ENNReal.ofReal (ω j ^ 2 * majorantCoeff ψ j ^ 2) ≤
        ENNReal.ofReal (ω j ^ 2 * ((‖potentialCoeff ψ true j‖ ^ 2 + ‖potentialCoeff ψ false j‖ ^ 2) +
          (‖potentialCoeff ψ true (-j)‖ ^ 2 + ‖potentialCoeff ψ false (-j)‖ ^ 2))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) hp)
    refine e1.trans (le_of_eq ?_)
    rw [mul_add, ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [hW, weightedPairMode, K030.pc_true ψ φ h1, K030.pc_false ψ φ h2, hev j]
    rw [ENNReal.ofReal_mul hp, ENNReal.ofReal_mul hp,
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
  have hsum : ∑' j : ℤ, W j = weightedNormSq₂ ω φ := rfl
  have hneg : ∑' j : ℤ, W (-j) = ∑' j : ℤ, W j := (Equiv.neg ℤ).tsum_eq W
  unfold scalarEnergy
  calc ∑' j : ℤ, ENNReal.ofReal (ω j ^ 2 * majorantCoeff ψ j ^ 2)
      ≤ ∑' j : ℤ, (W j + W (-j)) := ENNReal.tsum_le_tsum hterm
    _ = weightedNormSq₂ ω φ + weightedNormSq₂ ω φ := by
        rw [ENNReal.tsum_add, hneg, hsum]

/-- Tail version of the pointwise gap estimate of `K030.gapEnergy_lt_top`, with the thresholds supplied. -/
theorem tail_le (ω : ℤ → ℝ) (hev : ∀ k, ω (-k) = ω k)
    (ψ : Potential) (φ : PotPair) (h1 : ψ true = φ.1) (h2 : ψ false = φ.2) (N : ℕ)
    (hN₀ : ∀ n : ℤ, N ≤ n.natAbs → pathMajorant (majorantCoeff ψ) n < ⊤ ∧
      ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
        ‖reducedB ψ n z hz - coveredCoeff ψ false (2*n)‖ ≤ (pathMajorant (majorantCoeff ψ) n).toReal ∧
        ‖reducedC ψ n z hz - coveredCoeff ψ true (-2*n)‖ ≤ (pathMajorant (majorantCoeff ψ) n).toReal)
    (h29 : ∀ n : ℤ, N ≤ n.natAbs →
      SmallCoefficients n (a ψ n) (b ψ n) (c ψ n) ∧
      Lib.zeroMultiset (determinant n (a ψ n) (b ψ n) (c ψ n))
        (Metric.ball (center n) (Real.pi / 3)) = {lamMinus φ n, lamPlus φ n}) :
    (∑' n : ℤ, if N ≤ n.natAbs then
        ENNReal.ofReal (ω (2 * n) ^ 2 * ‖actualGapSequence φ n‖ ^ 2) else 0) ≤
      9 * (weightedNormSq₂ ω φ + weightedNormSq₂ ω φ) +
        18 * weightedMajorantTail ω (majorantCoeff ψ) N := by
  set W : ℤ → ℝ≥0∞ := fun k => weightedPairMode ω k (periodTwoPairCoeff φ k) with hW
  set Fb : ℤ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (ω (2 * n) ^ 2 * ‖coveredCoeff ψ false (2 * n)‖ ^ 2) with hFb
  set Fc : ℤ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (ω (2 * n) ^ 2 * ‖coveredCoeff ψ true (-2 * n)‖ ^ 2) with hFc
  have hFb_le : ∀ n : ℤ, Fb n ≤ W (2 * n) := by
    intro n
    simp only [hFb, hW, weightedPairMode]
    have e : coveredCoeff ψ false (2 * n) = (periodTwoPairCoeff φ (2 * n)).2 :=
      K030.pc_false ψ φ h2 (2 * n)
    rw [e, ENNReal.ofReal_mul (sq_nonneg _)]
    exact mul_le_mul' le_rfl le_add_self
  have hFc_le : ∀ n : ℤ, Fc n ≤ W (-2 * n) := by
    intro n
    simp only [hFc, hW, weightedPairMode]
    have e : coveredCoeff ψ true (-2 * n) = (periodTwoPairCoeff φ (-2 * n)).1 :=
      K030.pc_true ψ φ h1 (-2 * n)
    have ew : ω (-2 * n) = ω (2 * n) := by
      have : (-2 : ℤ) * n = -(2 * n) := by ring
      rw [this, hev]
    rw [e, ew, ENNReal.ofReal_mul (sq_nonneg _)]
    exact mul_le_mul' le_rfl le_self_add
  have hFb_sum : ∑' n : ℤ, Fb n ≤ weightedNormSq₂ ω φ :=
    (ENNReal.tsum_le_tsum hFb_le).trans (ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun n : ℤ => 2 * n) (fun x y h => by simpa using h) W)
  have hFc_sum : ∑' n : ℤ, Fc n ≤ weightedNormSq₂ ω φ :=
    (ENNReal.tsum_le_tsum hFc_le).trans (ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun n : ℤ => -2 * n) (fun x y h => by simpa using h) W)
  set Fg : ℤ → ℝ≥0∞ := fun n =>
    if N ≤ n.natAbs then ENNReal.ofReal (ω (2 * n) ^ 2 * ‖actualGapSequence φ n‖ ^ 2) else 0 with hFg
  set Ft : ℤ → ℝ≥0∞ := fun n =>
    if N ≤ n.natAbs then ENNReal.ofReal (ω (2 * n) ^ 2) * pathMajorant (majorantCoeff ψ) n ^ 2
    else 0 with hFt
  have hpt : ∀ n : ℤ, Fg n ≤ 9 * (Fb n + Fc n) + 18 * Ft n := by
    intro n
    by_cases hn : N ≤ n.natAbs
    · have hFt0 : Ft n = ENNReal.ofReal (ω (2 * n) ^ 2) *
          pathMajorant (majorantCoeff ψ) n ^ 2 := by simp [hFt, hn]
      have hFg0 : Fg n = ENNReal.ofReal (ω (2 * n) ^ 2 * ‖actualGapSequence φ n‖ ^ 2) := by
        simp [hFg, hn]
      rw [hFt0, hFg0]
      obtain ⟨hpm, hz⟩ := hN₀ n hn
      obtain ⟨hsc, hzm⟩ := h29 n hn
      set P : ℝ := (pathMajorant (majorantCoeff ψ) n).toReal with hP
      have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
      have hb : ∀ z ∈ spectralStrip n, ‖b ψ n z‖ ≤ ‖coveredCoeff ψ false (2 * n)‖ + P := by
        intro z hzm'
        have hz' := (hz z hzm').1
        have e : b ψ n z = reducedB ψ n z hzm' := by
          show (abc ψ n z).2.1 = _
          rw [abc_eq_reduced ψ n z hzm']
        rw [e]
        have := norm_add_le (coveredCoeff ψ false (2 * n))
          (reducedB ψ n z hzm' - coveredCoeff ψ false (2 * n))
        rw [add_sub_cancel] at this
        linarith
      have hc : ∀ z ∈ spectralStrip n, ‖c ψ n z‖ ≤ ‖coveredCoeff ψ true (-2 * n)‖ + P := by
        intro z hzm'
        have hz' := (hz z hzm').2
        have e : c ψ n z = reducedC ψ n z hzm' := by
          show (abc ψ n z).2.2 = _
          rw [abc_eq_reduced ψ n z hzm']
        rw [e]
        have := norm_add_le (coveredCoeff ψ true (-2 * n))
          (reducedC ψ n z hzm' - coveredCoeff ψ true (-2 * n))
        rw [add_sub_cancel] at this
        linarith
      have hgap := K030.gap_sq_le n (a ψ n) (b ψ n) (c ψ n) hsc (lamMinus φ n) (lamPlus φ n) hzm
        (coveredCoeff ψ false (2 * n)) (coveredCoeff ψ true (-2 * n)) P hP0 hb hc
      have hnorm : ‖actualGapSequence φ n‖ = ‖lamMinus φ n - lamPlus φ n‖ := by
        unfold actualGapSequence
        exact norm_sub_rev _ _
      have hω0 : 0 ≤ ω (2 * n) ^ 2 := sq_nonneg _
      have hPpm : ENNReal.ofReal P = pathMajorant (majorantCoeff ψ) n :=
        ENNReal.ofReal_toReal hpm.ne
      simp only [hFb, hFc]
      calc ENNReal.ofReal (ω (2 * n) ^ 2 * ‖actualGapSequence φ n‖ ^ 2)
          ≤ ENNReal.ofReal (ω (2 * n) ^ 2 * (9 * (‖coveredCoeff ψ false (2 * n)‖ ^ 2 +
              ‖coveredCoeff ψ true (-2 * n)‖ ^ 2) + 18 * P ^ 2)) := by
            apply ENNReal.ofReal_le_ofReal
            apply mul_le_mul_of_nonneg_left _ hω0
            rw [hnorm]; exact hgap
        _ = ENNReal.ofReal (9 * (ω (2 * n) ^ 2 * ‖coveredCoeff ψ false (2 * n)‖ ^ 2 +
              ω (2 * n) ^ 2 * ‖coveredCoeff ψ true (-2 * n)‖ ^ 2) +
              18 * (ω (2 * n) ^ 2 * P ^ 2)) := by congr 1; ring
        _ = 9 * (ENNReal.ofReal (ω (2 * n) ^ 2 * ‖coveredCoeff ψ false (2 * n)‖ ^ 2) +
              ENNReal.ofReal (ω (2 * n) ^ 2 * ‖coveredCoeff ψ true (-2 * n)‖ ^ 2)) +
              18 * (ENNReal.ofReal (ω (2 * n) ^ 2) *
                pathMajorant (majorantCoeff ψ) n ^ 2) := by
            have hPterm : ENNReal.ofReal (ω (2 * n) ^ 2 * P ^ 2) =
                ENNReal.ofReal (ω (2 * n) ^ 2) * pathMajorant (majorantCoeff ψ) n ^ 2 := by
              rw [ENNReal.ofReal_mul hω0, ← hPpm, ENNReal.ofReal_pow hP0]
            have hx : 0 ≤ ω (2 * n) ^ 2 * ‖coveredCoeff ψ false (2 * n)‖ ^ 2 := by positivity
            have hy : 0 ≤ ω (2 * n) ^ 2 * ‖coveredCoeff ψ true (-2 * n)‖ ^ 2 := by positivity
            have hz2 : 0 ≤ ω (2 * n) ^ 2 * P ^ 2 := by positivity
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18),
              ENNReal.ofReal_add hx hy, hPterm]
            simp
    · have hFg0 : Fg n = 0 := by simp [hFg, hn]
      rw [hFg0]
      exact zero_le
  calc (∑' n : ℤ, if N ≤ n.natAbs then
        ENNReal.ofReal (ω (2 * n) ^ 2 * ‖actualGapSequence φ n‖ ^ 2) else 0)
      = ∑' n : ℤ, Fg n := rfl
    _ ≤ ∑' n : ℤ, (9 * (Fb n + Fc n) + 18 * Ft n) := ENNReal.tsum_le_tsum hpt
    _ = 9 * (∑' n : ℤ, Fb n + ∑' n : ℤ, Fc n) + 18 * weightedMajorantTail ω (majorantCoeff ψ) N := by
        have hs1 : ∑' n : ℤ, 9 * (Fb n + Fc n) = 9 * (∑' n : ℤ, Fb n + ∑' n : ℤ, Fc n) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        rw [ENNReal.tsum_add, hs1, ENNReal.tsum_mul_left]
        rfl
    _ ≤ 9 * (weightedNormSq₂ ω φ + weightedNormSq₂ ω φ) +
          18 * weightedMajorantTail ω (majorantCoeff ψ) N := by
        gcongr


theorem pop_add (ω : ℤ → ℝ) (hω : EvenWeight ω) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x y : WeightedPairHilbert (periodOneWeight ω)) :
    periodOnePhysicalPair ω hω (x + y) =
      periodOnePhysicalPair ω hω x + periodOnePhysicalPair ω hω y := by
  refine Prod.ext (KST033S.physical_ext fun m => ?_) (KST033S.physical_ext fun m => ?_)
  · rw [(periodOnePhysicalPair_fourier ω hω (x + y) m).1, Prod.fst_add, KST033S.physicalFourier_add,
      (periodOnePhysicalPair_fourier ω hω x m).1, (periodOnePhysicalPair_fourier ω hω y m).1]
    first | done | rfl | simp
  · rw [(periodOnePhysicalPair_fourier ω hω (x + y) m).2, Prod.snd_add, KST033S.physicalFourier_add,
      (periodOnePhysicalPair_fourier ω hω x m).2, (periodOnePhysicalPair_fourier ω hω y m).2]
    first | done | rfl | simp

theorem scalarTail_le_energy (w A : ℤ → ℝ) (N : ℕ) : scalarTailEnergy w A N ≤ scalarEnergy w A := by
  unfold scalarTailEnergy scalarEnergy
  exact ENNReal.tsum_le_tsum fun j => by split_ifs <;> simp


theorem gap_tail_uniform (w : ℤ → ℝ) (Cw : ℝ) (hw : SlowWeight w Cw) (φ₀ : PotPair)
    (h0 : weightedNormSq₂ w φ₀ < ⊤) :
    ∃ e : ℝ, 0 < e ∧ ∃ N₁ : ℕ, ∃ B : ℝ, ∀ φ : PotPair,
      weightedNormSq₂ w (φ - φ₀) < ENNReal.ofReal (e ^ 2) → ∀ N : ℕ, N₁ ≤ N →
      (∑' n : ℤ, if N ≤ n.natAbs then
        ENNReal.ofReal (w (2 * n) ^ 2 * ‖actualGapSequence φ n‖ ^ 2) else 0) ≤
          ENNReal.ofReal B := by
  have hwE : EvenWeight w := ⟨hw.one_le, hw.even⟩
  letI := weightFact w hw.one_le
  have hev : ∀ k, w (-k) = w k := hw.even
  have hC : 1 ≤ Cw := slowWeight_Cw_one_le hw
  obtain ⟨x₀, hx₀⟩ := periodOnePhysicalPair_exists_of_finite_energy w hwE φ₀ h0
  obtain ⟨e₁, he₁, N₂, hN₂5, hloc⟩ := kst027_locally_uniform w Cw hw x₀
  set ψ₀ : Potential := weightedPotential w hw.one_le x₀ with hψ₀
  obtain ⟨e₂, he₂, N₀, hN₀5, hpath⟩ := kst021_uniform ψ₀
  obtain ⟨e₃, he₃, N₃, hN₃5, h29⟩ := kst029 ψ₀
  set e : ℝ := min e₁ (min e₂ e₃) with he
  have he0 : 0 < e := lt_min he₁ (lt_min he₂ he₃)
  set R : ℝ := ‖x₀‖ + e with hR
  have hR0 : 0 ≤ R := by positivity
  set S : ℝ := 16 * Real.sqrt 2 * Cw ^ 2 * R ^ 2 with hS
  refine ⟨e, he0, max (max N₀ N₂) N₃, 18 * R ^ 2 + 18 * S ^ 2, ?_⟩
  intro φ hφ N hN
  have hN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₃ : N₃ ≤ N := le_trans (le_max_right _ _) hN
  have hfin : weightedNormSq₂ w (φ - φ₀) < ⊤ := lt_trans hφ ENNReal.ofReal_lt_top
  obtain ⟨y, hy⟩ := periodOnePhysicalPair_exists_of_finite_energy w hwE (φ - φ₀) hfin
  have hyn : ‖y‖ < e := by
    have h1 := periodOnePhysicalPair_full_doubled_energy_eq_norm w hwE y
    rw [← hy, h1] at hφ
    have h3 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hφ
    exact lt_of_pow_lt_pow_left₀ 2 he0.le h3
  set x : Weighted w := x₀ + y with hx
  have hxφ : periodOnePhysicalPair w hwE x = φ := by
    rw [hx, pop_add, hx₀, hy]; abel
  set ψ : Potential := weightedPotential w hw.one_le x with hψ
  have h1 : ψ true = φ.1 := congrArg Prod.fst hxφ
  have h2 : ψ false = φ.2 := congrArg Prod.snd hxφ
  have hpp : periodicPair ψ = φ := Prod.ext h1 h2
  have hψdiff : ψ - ψ₀ = weightedPotential w hw.one_le y := by
    rw [hψ, hx, KST033S.wp_add]; abel
  have hψn : ‖ψ - ψ₀‖ < e := by
    rw [hψdiff]
    exact lt_of_le_of_lt (KST033S.wp_norm_le w hw.one_le y) hyn
  have hxn : ‖x - x₀‖ < e₁ := by
    rw [hx, add_sub_cancel_left]
    exact lt_of_lt_of_le hyn (min_le_left _ _)
  have hψ2 : ‖ψ - ψ₀‖ < e₂ := lt_of_lt_of_le hψn ((min_le_right _ _).trans (min_le_left _ _))
  have hψ3 : ‖ψ - ψ₀‖ < e₃ := lt_of_lt_of_le hψn ((min_le_right _ _).trans (min_le_right _ _))
  have hpath' := hpath ψ hψ2
  have h29' : ∀ n : ℤ, N ≤ n.natAbs →
      SmallCoefficients n (a ψ n) (b ψ n) (c ψ n) ∧
      Lib.zeroMultiset (determinant n (a ψ n) (b ψ n) (c ψ n))
        (Metric.ball (center n) (Real.pi / 3)) = {lamMinus φ n, lamPlus φ n} := by
    intro n hn
    obtain ⟨hs, hz, -⟩ := h29 ψ hψ3 n (le_trans hN₃ hn)
    rw [hpp] at hz
    exact ⟨hs, hz⟩
  have hmain := tail_le w hev ψ φ h1 h2 N
    (fun n hn => hpath' n (le_trans hN₀ hn)) h29'
  -- energy of φ
  have hEn : weightedNormSq₂ w φ ≤ ENNReal.ofReal (R ^ 2) := by
    have h := periodOnePhysicalPair_full_doubled_energy_eq_norm w hwE x
    rw [hxφ] at h
    rw [h]
    apply ENNReal.ofReal_le_ofReal
    have : ‖x‖ ≤ R := by
      calc ‖x‖ ≤ ‖x₀‖ + ‖y‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  -- the path tail
  have hscal := scalarEnergy_le_two w hev ψ φ h1 h2
  have hE2 : scalarEnergy w (majorantCoeff ψ) ≤ ENNReal.ofReal (2 * R ^ 2) := by
    refine hscal.trans ?_
    calc weightedNormSq₂ w φ + weightedNormSq₂ w φ
        ≤ ENNReal.ofReal (R ^ 2) + ENNReal.ofReal (R ^ 2) := add_le_add hEn hEn
      _ = ENNReal.ofReal (2 * R ^ 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hEfin : scalarEnergy w (majorantCoeff ψ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE2
  have hEreal : (scalarEnergy w (majorantCoeff ψ)).toReal ≤ 2 * R ^ 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE2
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hTreal : (scalarTailEnergy w (majorantCoeff ψ) N).toReal ≤
      (scalarEnergy w (majorantCoeff ψ)).toReal :=
    ENNReal.toReal_mono hEfin (scalarTail_le_energy w _ N)
  have hl : weightedMajorantTail w (majorantCoeff ψ) N < ⊤ ∧
      Real.sqrt (weightedMajorantTail w (majorantCoeff ψ) N).toReal ≤
        source51RHS w (majorantCoeff ψ) Cw N := hloc x hxn N hN₂
  have hRHS : source51RHS w (majorantCoeff ψ) Cw N ≤ S := by
    unfold source51RHS
    set E : ℝ := (scalarEnergy w (majorantCoeff ψ)).toReal with hEdef
    set T : ℝ := (scalarTailEnergy w (majorantCoeff ψ) N).toReal with hTdef
    have hwN : 1 ≤ w (N : ℤ) := hw.one_le _
    have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
    have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
    have hN5 : (1 : ℝ) ≤ (N : ℝ) := by
      have : 5 ≤ N := le_trans hN₂5 hN₂
      exact_mod_cast (by omega : 1 ≤ N)
    have hsqN : 1 ≤ Real.sqrt (N : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hN5
    have h1 : T / w (N : ℤ) ^ 2 ≤ E :=
      (div_le_self hT0 (by nlinarith)).trans hTreal
    have h2 : E / Real.sqrt (N : ℝ) ≤ E := div_le_self hE0 hsqN
    have hc0 : 0 ≤ 4 * Real.sqrt 2 * Cw ^ 2 := by positivity
    calc 4 * Real.sqrt 2 * Cw ^ 2 * (T / w (N : ℤ) ^ 2 + E / Real.sqrt (N : ℝ))
        ≤ 4 * Real.sqrt 2 * Cw ^ 2 * (E + E) := by gcongr
      _ ≤ 4 * Real.sqrt 2 * Cw ^ 2 * (2 * R ^ 2 + 2 * R ^ 2) := by gcongr
      _ = S := by rw [hS]; ring
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hsqS : (weightedMajorantTail w (majorantCoeff ψ) N).toReal ≤ S ^ 2 :=
    (Real.sqrt_le_iff.1 (hl.2.trans hRHS)).2
  have htail : weightedMajorantTail w (majorantCoeff ψ) N ≤ ENNReal.ofReal (S ^ 2) :=
    (ENNReal.le_ofReal_iff_toReal_le hl.1.ne (by positivity)).2 hsqS
  calc (∑' n : ℤ, if N ≤ n.natAbs then
        ENNReal.ofReal (w (2 * n) ^ 2 * ‖actualGapSequence φ n‖ ^ 2) else 0)
      ≤ 9 * (weightedNormSq₂ w φ + weightedNormSq₂ w φ) +
        18 * weightedMajorantTail w (majorantCoeff ψ) N := hmain
    _ ≤ 9 * (ENNReal.ofReal (R ^ 2) + ENNReal.ofReal (R ^ 2)) + 18 * ENNReal.ofReal (S ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (18 * R ^ 2 + 18 * S ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18), ENNReal.ofReal_ofNat]
        ring

end K030U
end NlsGge.ThirdConsultation.KST
end
