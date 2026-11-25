import Mathlib
import NlsGge.ThirdConsultation.M.M033Host
import NlsGge.ThirdConsultation.M.M031Energy
import NlsGge.ThirdConsultation.M.Round5b
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.ThirdConsultation.KSPS.KSPS032Host

                                                                                                                  
                                                                                           
                                                                                                     
                                                                                                                     
                                                                                                                       
                                                                                                               
                                                                                                                 
                                                                     
                                                                                                                    
                                                                                                                 
                                                                                                                  
                                                                                                                 
                                                                                                         
                                                                                            
                                                   
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Birkhoff
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.KSPS032S

theorem norm_reflected_star (w : PhysicalL2) (p : ℤ) :
    ‖reflectedFourierL2 (star w) p‖ = ‖reflectedFourierL2 w (-p)‖ := by
  rw [reflectedFourierL2_apply, reflectedFourierL2_apply]
  unfold reflectedFourier
  rw [norm_neg, norm_neg, NlsGge.Schur.physicalFourier_star38, norm_star]

theorem star_summable (w : PhysicalL2)
    (hw : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 w p‖ ^ 2)) :
    Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 (star w) p‖ ^ 2) ∧
    ∑' p : ℤ, (1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 (star w) p‖ ^ 2 =
      ∑' p : ℤ, (1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 w p‖ ^ 2 := by
  have he : (fun p : ℤ => (1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 (star w) p‖ ^ 2) =
      (fun p : ℤ => (1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 w p‖ ^ 2) ∘ (Equiv.neg ℤ) := by
    funext p
    simp only [Function.comp_apply, Equiv.neg_apply, norm_reflected_star, Int.cast_neg, neg_sq]
  rw [he]
  exact ⟨(Equiv.neg ℤ).summable_iff.mpr hw,
    (Equiv.neg ℤ).tsum_eq (fun p : ℤ => (1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 w p‖ ^ 2)⟩

theorem component_tsum_le (v : PhysicalL2)
    (hu : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 v p‖ ^ 2)) :
    ∑' k : ℤ, M.sourceH1Weight k ^ 2 *
        ‖fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 v) k‖ ^ 2 ≤
      2 * (1 + 4 * Real.pi ^ 2) *
        ∑' p : ℤ, (1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 v p‖ ^ 2 := by
  set F : ℤ → ℝ := fun k => M.sourceH1Weight k ^ 2 *
        ‖fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 v) k‖ ^ 2 with hF
  have hg : Function.Injective (fun p : ℤ => -2 * p) := by
    intro a b h
    simp only at h
    omega
  have hsupp : Function.support F ⊆ Set.range (fun p : ℤ => -2 * p) := by
    intro k hk
    by_contra hkr
    apply hk
    have hodd : k % 2 ≠ 0 := by
      intro h0
      exact hkr ⟨-(k / 2), by simp only; omega⟩
    simp only [hF]
    rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_odd v k hodd, norm_zero]
    ring
  have hpt : ∀ p : ℤ, F (-2 * p) ≤
      2 * (1 + 4 * Real.pi ^ 2) * ((1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 v p‖ ^ 2) := by
    intro p
    simp only [hF]
    have heven : (-2 * p) % 2 = 0 := by omega
    have hdiv : (-2 * p) / 2 = -p := by omega
    rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_even_index v _ heven, hdiv]
    have hn : ‖physicalFourier (v : PhysicalCircle → ℂ) (-p)‖ = ‖reflectedFourierL2 v p‖ := by
      rw [reflectedFourierL2_apply]
      unfold reflectedFourier
      rw [norm_neg]
    rw [hn, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (M.sourceH1Weight_sq_le p) (by positivity)
  have hsF : Summable (fun p : ℤ => F (-2 * p)) :=
    Summable.of_nonneg_of_le (fun p => by simp only [hF]; positivity) hpt (hu.mul_left _)
  rw [← hg.tsum_eq hsupp, ← tsum_mul_left]
  exact Summable.tsum_le_tsum hpt hsF (hu.mul_left _)

theorem embed_tsum_eq (u : NlsGge.ThirdConsultation.KSPS.SobolevR 1) :
    ∑' p : ℤ, (1 + (p : ℝ) ^ 2) *
        ‖reflectedFourierL2 (NlsGge.GKDefinitionDesign.physicalSobolevEmbed 1 u) p‖ ^ 2 =
      ‖u‖ ^ 2 := by
  have h := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ)
    (NlsGge.Atomic.Common.physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u)
  rw [LinearIsometryEquiv.norm_map] at h
  refine Eq.trans (tsum_congr (fun p => ?_)) h.tsum_eq
  have hf := NlsGge.GKDefinitionDesign.physicalSobolevEmbed_fourier 1 u p
  unfold fourierSeq38 at hf
  have hw : sobolevModeWeight ((1 : ℕ) : ℝ) p = 1 + (p : ℝ) ^ 2 := by
    rw [Nat.cast_one]
    exact NlsGge.NLS38.sobolevModeWeight_one_eq p
  rw [hf, hw]

theorem H1Norm_le (u : M.SobolevR 1) :
    MTwoMode.H1Norm u ≤ Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) * ‖u‖ := by
  have hwe : NlsGge.GKDefinitionDesign.physicalSobolevEmbed 1 u = M.physicalOfSobolev u :=
    NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M 1 u
  have hs1 := M.sobolevEmbed_one_summable u
  rw [hwe] at hs1
  have ht1 := embed_tsum_eq u
  rw [hwe] at ht1
  obtain ⟨hs2, ht2⟩ := star_summable (M.physicalOfSobolev u) hs1
  have c1 := component_tsum_le (M.physicalOfSobolev u) hs1
  have c2 := component_tsum_le (star (M.physicalOfSobolev u)) hs2
  have sum1 := M.sourceH1_component_summable (M.physicalOfSobolev u) hs1
  have sum2 := M.sourceH1_component_summable (star (M.physicalOfSobolev u)) hs2
  have hsum : Summable (fun k : ℤ => M.sourceH1Weight k ^ 2 *
      (‖MTwoMode.potentialCoefficientPair (realSlice (M.physicalOfSobolev u)) true k‖ ^ 2 +
        ‖MTwoMode.potentialCoefficientPair (realSlice (M.physicalOfSobolev u)) false k‖ ^ 2)) := by
    refine (sum1.add sum2).congr (fun k => ?_)
    simp only [MTwoMode.potentialCoefficientPair, realSlice_apply, ite_true, Bool.false_eq_true,
      ite_false]
    ring
  have hE : (MTwoMode.potentialCoefficientEnergy M.sourceH1Weight
        (realSlice (M.physicalOfSobolev u))).toReal =
      ∑' k : ℤ, M.sourceH1Weight k ^ 2 *
          ‖fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 (M.physicalOfSobolev u)) k‖ ^ 2 +
        ∑' k : ℤ, M.sourceH1Weight k ^ 2 *
          ‖fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2
            (star (M.physicalOfSobolev u))) k‖ ^ 2 := by
    unfold MTwoMode.potentialCoefficientEnergy
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum,
      ENNReal.toReal_ofReal (tsum_nonneg (fun k => by positivity)), ← sum1.tsum_add sum2]
    refine tsum_congr (fun k => ?_)
    simp only [MTwoMode.potentialCoefficientPair, realSlice_apply, ite_true, Bool.false_eq_true,
      ite_false]
    ring
  have hle : (MTwoMode.potentialCoefficientEnergy M.sourceH1Weight
        (realSlice (M.physicalOfSobolev u))).toReal ≤
      (Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) * ‖u‖) ^ 2 := by
    rw [hE, mul_pow, Real.sq_sqrt (by positivity)]
    rw [ht2, ht1] at c2
    rw [ht1] at c1
    linarith
  show Real.sqrt (MTwoMode.potentialCoefficientEnergy M.sourceH1Weight
      (realSlice (M.physicalOfSobolev u))).toReal ≤ _
  calc Real.sqrt (MTwoMode.potentialCoefficientEnergy M.sourceH1Weight
        (realSlice (M.physicalOfSobolev u))).toReal
      ≤ Real.sqrt ((Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) * ‖u‖) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) * ‖u‖ := Real.sqrt_sq (by positivity)

theorem indexWeight_le (n : ℤ) :
    NlsGge.ThirdConsultation.KSPS.indexWeight n ≤ NlsGge.Atomic.M.M054.indexWeight n := by
  unfold NlsGge.ThirdConsultation.KSPS.indexWeight NlsGge.Atomic.M.M054.indexWeight
  calc Real.sqrt (1 + (n : ℝ) ^ 2) ≤ Real.sqrt ((1 + |(n : ℝ)|) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [abs_nonneg (n : ℝ), sq_abs (n : ℝ)])
    _ = 1 + |(n : ℝ)| := Real.sqrt_sq (by positivity)

theorem indexWeight_pos (n : ℤ) : 0 < NlsGge.ThirdConsultation.KSPS.indexWeight n := by
  unfold NlsGge.ThirdConsultation.KSPS.indexWeight
  exact Real.sqrt_pos.mpr (by positivity)

theorem abs_cast_eq (n : ℤ) : |(n : ℝ)| = ((n.natAbs : ℕ) : ℝ) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

theorem closedGap_eq (u : NlsGge.ThirdConsultation.KSPS.SobolevR 1) (n : ℤ) :
    NlsGge.ThirdConsultation.KSPS.closedGap u n =
      Set.Icc (actualGapLowerAllE02_38 (M.physicalOfSobolev u) n)
        (actualGapUpperAllE02_38 (M.physicalOfSobolev u) n) := by
  unfold NlsGge.ThirdConsultation.KSPS.closedGap NlsGge.ThirdConsultation.KSPS.toPhysical
  rw [NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M]

theorem norm_ofReal_sub (n : ℤ) (x : ℝ) :
    ‖(x : ℂ) - (n : ℂ) * (Real.pi : ℂ)‖ = |x - (n : ℝ) * Real.pi| := by
  have e : (x : ℂ) - (n : ℂ) * (Real.pi : ℂ) = ((x - (n : ℝ) * Real.pi : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]

theorem gap_localization_of
    (hM : ∀ B : ℝ, 0 < B →
      ∃ N : ℕ, ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
      ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1,
        MTwoMode.potentialCoefficientNorm M.sourceH1Weight
            (NlsGge.ThirdConsultation.KSPS.toPotPair φ) ≤ B →
        NlsGge.ThirdConsultation.KSPS.toPotPair φ ∈ gkW →
        (∀ n : ℤ, N ≤ n.natAbs → ∀ plus : Bool,
          ‖(if plus then lamPlus (NlsGge.ThirdConsultation.KSPS.toPotPair φ) n
            else lamMinus (NlsGge.ThirdConsultation.KSPS.toPotPair φ) n) -
            (n : ℂ) * (Real.pi : ℂ)‖ ≤
              C / NlsGge.Atomic.M.M054.indexWeight n) ∧
        (∀ n : ℤ, n.natAbs < N → ∀ plus : Bool,
          let z : ℂ := if plus then lamPlus (NlsGge.ThirdConsultation.KSPS.toPotPair φ) n
            else lamMinus (NlsGge.ThirdConsultation.KSPS.toPotPair φ) n
          |z.re| ≤ R ∧ |z.im| ≤ B))
    (hex : ∀ u : M.SobolevR 1, ∃ φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1,
      NlsGge.ThirdConsultation.KSPS.toPotPair φ = realSlice (M.physicalOfSobolev u)) :
  ∀ B : ℝ, 0 < B →
    ∃ K : ℝ, 0 < K ∧
    ∀ u : NlsGge.ThirdConsultation.KSPS.SobolevR 1, ‖u‖ ≤ B →
      ∀ n : ℤ, ∀ lam : ℝ, lam ∈ NlsGge.ThirdConsultation.KSPS.closedGap u n →
        |lam-(n:ℝ)*Real.pi| ≤ K/NlsGge.ThirdConsultation.KSPS.indexWeight n := by
  intro B hB
  have hA0 : 0 ≤ Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) := Real.sqrt_nonneg _
  have hB' : 0 < Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) * B + 1 := by positivity
  obtain ⟨N, C, R, hC, hR, hL⟩ :=
    hM (Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) * B + 1) hB'
  have hNR : 0 ≤ (R + (N : ℝ) * Real.pi) * (1 + (N : ℝ)) := by positivity
  refine ⟨C + (R + (N : ℝ) * Real.pi) * (1 + (N : ℝ)) + 1, by positivity, ?_⟩
  intro u hu n lam hlam
  obtain ⟨φ, hφ⟩ := hex u
  have hW : NlsGge.ThirdConsultation.KSPS.toPotPair φ ∈ gkW := by
    rw [hφ]; exact realSlice_mem_gkW _
  have hnorm : MTwoMode.potentialCoefficientNorm M.sourceH1Weight
      (NlsGge.ThirdConsultation.KSPS.toPotPair φ) ≤
        Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) * B + 1 := by
    rw [hφ]
    show MTwoMode.H1Norm u ≤ _
    have h1 := H1Norm_le u
    have h2 : Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) * ‖u‖ ≤
        Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) * B := mul_le_mul_of_nonneg_left hu hA0
    linarith
  obtain ⟨Lhi, Llo⟩ := hL φ hnorm hW
  obtain ⟨hp, hm⟩ := lamPlus_real (M.physicalOfSobolev u) n
  rw [closedGap_eq] at hlam
  have hiw := indexWeight_pos n
  have hiwle := indexWeight_le n
  suffices hab :
      |actualGapLowerAllE02_38 (M.physicalOfSobolev u) n - (n : ℝ) * Real.pi| ≤
          (C + (R + (N : ℝ) * Real.pi) * (1 + (N : ℝ)) + 1) /
            NlsGge.ThirdConsultation.KSPS.indexWeight n ∧
        |actualGapUpperAllE02_38 (M.physicalOfSobolev u) n - (n : ℝ) * Real.pi| ≤
          (C + (R + (N : ℝ) * Real.pi) * (1 + (N : ℝ)) + 1) /
            NlsGge.ThirdConsultation.KSPS.indexWeight n by
    obtain ⟨h1, h2⟩ := hab
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [hlam.1, hlam.2, h1.1, h1.2, h2.1, h2.2]
  by_cases hn : N ≤ n.natAbs
  · have ep := Lhi n hn true
    have em := Lhi n hn false
    rw [if_pos rfl] at ep
    rw [if_neg (by decide)] at em
    rw [hφ, hp, norm_ofReal_sub] at ep
    rw [hφ, hm, norm_ofReal_sub] at em
    have hCK : C / NlsGge.Atomic.M.M054.indexWeight n ≤
        (C + (R + (N : ℝ) * Real.pi) * (1 + (N : ℝ)) + 1) /
          NlsGge.ThirdConsultation.KSPS.indexWeight n := by
      have hCK' : C ≤ C + (R + (N : ℝ) * Real.pi) * (1 + (N : ℝ)) + 1 := by linarith
      calc C / NlsGge.Atomic.M.M054.indexWeight n
          ≤ C / NlsGge.ThirdConsultation.KSPS.indexWeight n :=
            div_le_div_of_nonneg_left hC hiw hiwle
        _ ≤ _ := div_le_div_of_nonneg_right hCK' hiw.le
    exact ⟨em.trans hCK, ep.trans hCK⟩
  · have hn' : n.natAbs < N := by omega
    have ep := Llo n hn' true
    have em := Llo n hn' false
    dsimp only at ep em
    rw [if_pos rfl] at ep
    rw [if_neg (by decide)] at em
    rw [hφ, hp, Complex.ofReal_re] at ep
    rw [hφ, hm, Complex.ofReal_re] at em
    have hnN : |(n : ℝ)| ≤ (N : ℝ) := by
      rw [abs_cast_eq]; exact_mod_cast hn'.le
    have hw1 : NlsGge.ThirdConsultation.KSPS.indexWeight n ≤ 1 + (N : ℝ) := by
      have h := hiwle
      unfold NlsGge.Atomic.M.M054.indexWeight at h
      linarith
    have hbox : R + (N : ℝ) * Real.pi ≤
        (C + (R + (N : ℝ) * Real.pi) * (1 + (N : ℝ)) + 1) /
          NlsGge.ThirdConsultation.KSPS.indexWeight n := by
      rw [le_div_iff₀ hiw]
      have h0 : 0 ≤ R + (N : ℝ) * Real.pi := by positivity
      have h3 := mul_le_mul_of_nonneg_left hw1 h0
      linarith
    have hnpi : |(n : ℝ) * Real.pi| ≤ (N : ℝ) * Real.pi := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      exact mul_le_mul_of_nonneg_right hnN Real.pi_pos.le
    obtain ⟨ea, eb⟩ := abs_le.mp ep.1
    obtain ⟨fa, fb⟩ := abs_le.mp em.1
    obtain ⟨ga, gb⟩ := abs_le.mp hnpi
    refine ⟨?_, ?_⟩
    · exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans hbox
    · exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans hbox

end NlsGge.ThirdConsultation.KSPS032S

end
