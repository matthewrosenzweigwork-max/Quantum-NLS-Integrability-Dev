                                                                                                        
                                                                                                    
                                                                                                          
                                                                                                  
import Mathlib
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST020
import NlsGge.Atomic.KST.KST021
import NlsGge.Atomic.KST.KST028
import NlsGge.Atomic.KST.KST029
import NlsGge.Atomic.KST.KST059

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NlsGge.ThirdConsultation.KST

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003
open NlsGge.Atomic.KST004 NlsGge.Atomic.KST006 NlsGge.Atomic.KST007
open NlsGge.Atomic.KST012 NlsGge.Atomic.KST013 NlsGge.Atomic.KST016
open NlsGge.Analysis NlsGge.Pilot
open NlsGge.GK38 NlsGge.Atomic.KST001 NlsGge.Atomic.KST059 NlsGge.Atomic.DM046

namespace K030

theorem max_sq_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : max x y ^ 2 ≤ x ^ 2 + y ^ 2 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

theorem majorant_sq_le (ψ : Potential) (k : ℤ) :
    majorantCoeff ψ k ^ 2 ≤ ‖potentialCoeff ψ true k‖ ^ 2 + ‖potentialCoeff ψ true (-k)‖ ^ 2 +
      ‖potentialCoeff ψ false k‖ ^ 2 + ‖potentialCoeff ψ false (-k)‖ ^ 2 := by
  unfold majorantCoeff
  have h1 := max_sq_le ‖potentialCoeff ψ true k‖ ‖potentialCoeff ψ true (-k)‖
    (norm_nonneg _) (norm_nonneg _)
  have h2 := max_sq_le ‖potentialCoeff ψ false k‖ ‖potentialCoeff ψ false (-k)‖
    (norm_nonneg _) (norm_nonneg _)
  have h3 := max_sq_le (max ‖potentialCoeff ψ true k‖ ‖potentialCoeff ψ true (-k)‖)
    (max ‖potentialCoeff ψ false k‖ ‖potentialCoeff ψ false (-k)‖)
    (le_trans (norm_nonneg _) (le_max_left _ _)) (le_trans (norm_nonneg _) (le_max_left _ _))
  linarith

/-- The pair of period-two coefficients of the Hilbert potential `ψ` over the pair `φ`. -/
theorem pc_true (ψ : Potential) (φ : PotPair) (h1 : ψ true = φ.1) (k : ℤ) :
    potentialCoeff ψ true k = (periodTwoPairCoeff φ k).1 := by
  simp [potentialCoeff, periodTwoPairCoeff, h1]

theorem pc_false (ψ : Potential) (φ : PotPair) (h2 : ψ false = φ.2) (k : ℤ) :
    potentialCoeff ψ false k = (periodTwoPairCoeff φ k).2 := by
  simp [potentialCoeff, periodTwoPairCoeff, h2]

/-- Finite weighted pair energy gives finite scalar majorant energy. -/
theorem scalarEnergy_lt_top (ω : ℤ → ℝ) (hev : ∀ k, ω (-k) = ω k)
    (ψ : Potential) (φ : PotPair) (h1 : ψ true = φ.1) (h2 : ψ false = φ.2)
    (hφ : weightedNormSq₂ ω φ < ⊤) :
    scalarEnergy ω (majorantCoeff ψ) < ⊤ := by
  set W : ℤ → ℝ≥0∞ := fun k => weightedPairMode ω k (periodTwoPairCoeff φ k) with hW
  have hterm : ∀ j : ℤ, ENNReal.ofReal (ω j ^ 2 * majorantCoeff ψ j ^ 2) ≤ W j + W (-j) := by
    intro j
    have hs := majorant_sq_le ψ j
    have hp : 0 ≤ ω j ^ 2 := sq_nonneg _
    have e1 : ENNReal.ofReal (ω j ^ 2 * majorantCoeff ψ j ^ 2) ≤
        ENNReal.ofReal (ω j ^ 2 * ((‖potentialCoeff ψ true j‖ ^ 2 + ‖potentialCoeff ψ false j‖ ^ 2) +
          (‖potentialCoeff ψ true (-j)‖ ^ 2 + ‖potentialCoeff ψ false (-j)‖ ^ 2))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) hp)
    refine e1.trans (le_of_eq ?_)
    rw [mul_add, ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [hW, weightedPairMode, pc_true ψ φ h1, pc_false ψ φ h2, hev j]
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
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hφ, hφ⟩

/-- Pointwise bound of the squared gap through the leading Fourier coefficients and the
path remainder. -/
theorem gap_sq_le (n : ℤ) (a b c : ℂ → ℂ) (h : SmallCoefficients n a b c) (xp xm : ℂ)
    (hroots : Lib.zeroMultiset (determinant n a b c)
      (Metric.ball (center n) (Real.pi / 3)) = {xp, xm})
    (cb cc : ℂ) (P : ℝ) (hP : 0 ≤ P)
    (hb : ∀ z ∈ spectralStrip n, ‖b z‖ ≤ ‖cb‖ + P)
    (hc : ∀ z ∈ spectralStrip n, ‖c z‖ ≤ ‖cc‖ + P) :
    ‖xp - xm‖ ^ 2 ≤ 9 * (‖cb‖ ^ 2 + ‖cc‖ ^ 2) + 18 * P ^ 2 := by
  obtain ⟨-, hne, -, hgap⟩ := kst020 n a b c h xp xm hroots
  have hX : 0 ≤ (‖cb‖ + P) * (‖cc‖ + P) := by positivity
  have hsup : bcSup n b c ≤ (‖cb‖ + P) * (‖cc‖ + P) := by
    refine csSup_le hne ?_
    rintro t ⟨z, hz, rfl⟩
    calc ‖b z * c z‖ ≤ ‖b z‖ * ‖c z‖ := norm_mul_le _ _
      _ ≤ (‖cb‖ + P) * (‖cc‖ + P) :=
          mul_le_mul (hb z hz) (hc z hz) (norm_nonneg _) (by positivity)
  have hsq : Real.sqrt (bcSup n b c) ≤ Real.sqrt ((‖cb‖ + P) * (‖cc‖ + P)) :=
    Real.sqrt_le_sqrt hsup
  have h3 : ‖xp - xm‖ ≤ 3 * Real.sqrt ((‖cb‖ + P) * (‖cc‖ + P)) := by linarith
  have h4 : ‖xp - xm‖ ^ 2 ≤ (3 * Real.sqrt ((‖cb‖ + P) * (‖cc‖ + P))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h3 2
  rw [mul_pow, Real.sq_sqrt hX] at h4
  have hx := norm_nonneg cb
  have hy := norm_nonneg cc
  nlinarith [sq_nonneg ((‖cb‖ + P) - (‖cc‖ + P)), sq_nonneg (‖cb‖ - P), sq_nonneg (‖cc‖ - P)]

/-- The assembly: the packet proof from the localisation `h29` supplied by KST-029 for the
Hilbert potential `ψ` over the pair `φ`. -/
theorem gapEnergy_lt_top (ω : ℤ → ℝ) (hω : AdmissibleWeight ω)
    (hsub : SubmultiplicativeWeight ω) (ψ : Potential) (φ : PotPair)
    (h1 : ψ true = φ.1) (h2 : ψ false = φ.2)
    (hφ : weightedNormSq₂ ω φ < ⊤) (N₃ : ℕ)
    (h29 : ∀ n : ℤ, N₃ ≤ n.natAbs →
      SmallCoefficients n (a ψ n) (b ψ n) (c ψ n) ∧
      Lib.zeroMultiset (determinant n (a ψ n) (b ψ n) (c ψ n))
        (Metric.ball (center n) (Real.pi / 3)) = {lamMinus φ n, lamPlus φ n}) :
    weightedGapEnergy ω (actualGapSequence φ) < ⊤ := by
  have hev : ∀ k, ω (-k) = ω k := hω.2.1
  have hv : SecondaryWeight ω := ⟨hω, hsub⟩
  have hA0 : ∀ j, 0 ≤ majorantCoeff ψ j := majorant_nonneg ψ
  have hE := scalarEnergy_lt_top ω hev ψ φ h1 h2 hφ
  obtain ⟨N₂, -, hN₂⟩ := kst028_corollary ω (majorantCoeff ψ) hv hA0 hE
  obtain ⟨N₀, -, hN₀⟩ := kst021 ψ
  set N : ℕ := max (max N₀ N₂) N₃ with hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNN₂ : N₂ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNN₃ : N₃ ≤ N := le_max_right _ _
  have htail : weightedMajorantTail ω (majorantCoeff ψ) N < ⊤ := (hN₂ N hNN₂).1
  set W : ℤ → ℝ≥0∞ := fun k => weightedPairMode ω k (periodTwoPairCoeff φ k) with hW
  have hWfin : ∑' k : ℤ, W k < ⊤ := hφ
  -- leading Fourier coefficients
  set Fb : ℤ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (ω (2 * n) ^ 2 * ‖coveredCoeff ψ false (2 * n)‖ ^ 2) with hFb
  set Fc : ℤ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (ω (2 * n) ^ 2 * ‖coveredCoeff ψ true (-2 * n)‖ ^ 2) with hFc
  have hFb_le : ∀ n : ℤ, Fb n ≤ W (2 * n) := by
    intro n
    simp only [hFb, hW, weightedPairMode]
    have e : coveredCoeff ψ false (2 * n) = (periodTwoPairCoeff φ (2 * n)).2 :=
      pc_false ψ φ h2 (2 * n)
    rw [e, ENNReal.ofReal_mul (sq_nonneg _)]
    exact mul_le_mul' le_rfl le_add_self
  have hFc_le : ∀ n : ℤ, Fc n ≤ W (-2 * n) := by
    intro n
    simp only [hFc, hW, weightedPairMode]
    have e : coveredCoeff ψ true (-2 * n) = (periodTwoPairCoeff φ (-2 * n)).1 :=
      pc_true ψ φ h1 (-2 * n)
    have ew : ω (-2 * n) = ω (2 * n) := by
      have : (-2 : ℤ) * n = -(2 * n) := by ring
      rw [this, hev]
    rw [e, ew, ENNReal.ofReal_mul (sq_nonneg _)]
    exact mul_le_mul' le_rfl le_self_add
  have hFb_sum : ∑' n : ℤ, Fb n < ⊤ :=
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hFb_le)
      (lt_of_le_of_lt (ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun n : ℤ => 2 * n) (fun x y h => by simpa using h) W) hWfin)
  have hFc_sum : ∑' n : ℤ, Fc n < ⊤ :=
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hFc_le)
      (lt_of_le_of_lt (ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun n : ℤ => -2 * n) (fun x y h => by simpa using h) W) hWfin)
  -- the gap terms
  set Fg : ℤ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (ω (2 * n) ^ 2 * ‖actualGapSequence φ n‖ ^ 2) with hFg
  set Ft : ℤ → ℝ≥0∞ := fun n =>
    if N ≤ n.natAbs then ENNReal.ofReal (ω (2 * n) ^ 2) * pathMajorant (majorantCoeff ψ) n ^ 2
    else 0 with hFt
  set Fl : ℤ → ℝ≥0∞ := fun n => if N ≤ n.natAbs then 0 else Fg n with hFl
  have hpt : ∀ n : ℤ, Fg n ≤ 9 * (Fb n + Fc n) + 18 * Ft n + Fl n := by
    intro n
    by_cases hn : N ≤ n.natAbs
    · have hFl0 : Fl n = 0 := by simp [hFl, hn]
      have hFt0 : Ft n = ENNReal.ofReal (ω (2 * n) ^ 2) *
          pathMajorant (majorantCoeff ψ) n ^ 2 := by simp [hFt, hn]
      rw [hFl0, hFt0, add_zero]
      obtain ⟨hpm, -, -, -, hz⟩ := hN₀ n (le_trans hNN₀ hn)
      obtain ⟨hsc, hzm⟩ := h29 n (le_trans hNN₃ hn)
      set P : ℝ := (pathMajorant (majorantCoeff ψ) n).toReal with hP
      have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
      have hb : ∀ z ∈ spectralStrip n, ‖b ψ n z‖ ≤ ‖coveredCoeff ψ false (2 * n)‖ + P := by
        intro z hzm'
        have hz' := (hz z hzm').2.2.2.2.1
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
        have hz' := (hz z hzm').2.2.2.2.2
        have e : c ψ n z = reducedC ψ n z hzm' := by
          show (abc ψ n z).2.2 = _
          rw [abc_eq_reduced ψ n z hzm']
        rw [e]
        have := norm_add_le (coveredCoeff ψ true (-2 * n))
          (reducedC ψ n z hzm' - coveredCoeff ψ true (-2 * n))
        rw [add_sub_cancel] at this
        linarith
      have hgap := gap_sq_le n (a ψ n) (b ψ n) (c ψ n) hsc (lamMinus φ n) (lamPlus φ n) hzm
        (coveredCoeff ψ false (2 * n)) (coveredCoeff ψ true (-2 * n)) P hP0 hb hc
      have hnorm : ‖actualGapSequence φ n‖ = ‖lamMinus φ n - lamPlus φ n‖ := by
        unfold actualGapSequence
        exact norm_sub_rev _ _
      have hω0 : 0 ≤ ω (2 * n) ^ 2 := sq_nonneg _
      have hPpm : ENNReal.ofReal P = pathMajorant (majorantCoeff ψ) n :=
        ENNReal.ofReal_toReal hpm.ne
      simp only [hFg, hFb, hFc]
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
    · have hFl0 : Fl n = Fg n := by simp [hFl, hn]
      rw [hFl0]
      exact le_add_self
  have hFl_fin : ∑' n : ℤ, Fl n < ⊤ := by
    have hzero : ∀ n ∉ (Finset.Icc (-(N : ℤ)) (N : ℤ)), Fl n = 0 := by
      intro n hn
      have : N ≤ n.natAbs := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        omega
      simp [hFl, this]
    rw [tsum_eq_sum hzero]
    refine ENNReal.sum_lt_top.2 (fun n _ => ?_)
    simp only [hFl]
    split_ifs
    · simp
    · exact ENNReal.ofReal_lt_top
  unfold weightedGapEnergy
  change ∑' n : ℤ, Fg n < ⊤
  calc ∑' n : ℤ, Fg n ≤ ∑' n : ℤ, (9 * (Fb n + Fc n) + 18 * Ft n + Fl n) :=
        ENNReal.tsum_le_tsum hpt
    _ = 9 * (∑' n : ℤ, Fb n + ∑' n : ℤ, Fc n) + 18 * weightedMajorantTail ω (majorantCoeff ψ) N +
          ∑' n : ℤ, Fl n := by
        have hs1 : ∑' n : ℤ, 9 * (Fb n + Fc n) = 9 * (∑' n : ℤ, Fb n + ∑' n : ℤ, Fc n) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_add, hs1, ENNReal.tsum_mul_left]
        rfl
    _ < ⊤ := by
        refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨?_, ?_⟩, hFl_fin⟩
        · exact ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.2 ⟨hFb_sum, hFc_sum⟩)
        · exact ENNReal.mul_lt_top (by simp) htail

end K030

theorem kst030 (ω : ℤ → ℝ) (hω : AdmissibleWeight ω)
    (hsub : SubmultiplicativeWeight ω) (φ : PotPair)
    (hφ : weightedNormSq₂ ω φ < ⊤) :
  weightedGapEnergy ω (actualGapSequence φ) < ⊤ := by
  set ψ : Potential := WithLp.toLp 2 (fun b : Bool => if b then φ.1 else φ.2) with hψ
  have h1 : ψ true = φ.1 := by simp [hψ]
  have h2 : ψ false = φ.2 := by simp [hψ]
  obtain ⟨e, he, N₃, -, h⟩ := kst029 ψ
  refine K030.gapEnergy_lt_top ω hω hsub ψ φ h1 h2 hφ N₃ (fun n hn => ?_)
  obtain ⟨hs, hz, -⟩ := h ψ (by simpa using he) n hn
  have hpp : periodicPair ψ = φ := Prod.ext h1 h2
  rw [hpp] at hz
  exact ⟨hs, hz⟩

end NlsGge.ThirdConsultation.KST
end
