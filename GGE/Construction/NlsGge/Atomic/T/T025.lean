import NlsGge.Atomic.T.T024
import NlsGge.Weights.UniformSymbolBound38
import NlsGge.Spectral.ActualGapLocalizationAllUE02_38

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.T.T025

open NlsGge.Pilot NlsGge.SpectralFoundations

private lemma lowerWeight_high_lambda (K : ℝ) (hK : 0 < K) (M : ℕ)
    (hcut : 2 * K < Real.pi * (M : ℝ) ^ 2) (n : ℤ) («λ» : ℝ)
    (hn : M ≤ n.natAbs) (hloc : |«λ» - (n : ℝ) * Real.pi| ≤ K / japaneseBracket n) :
    Real.pi * |(n : ℝ)| ≤ |2 * «λ»| := by
  have habs : (M : ℝ) ≤ |(n : ℝ)| := by
    have hcast : (Int.natAbs n : ℝ) = |(n : ℝ)| := by
      calc
        (Int.natAbs n : ℝ) = ((Int.natAbs n : ℤ) : ℝ) := by simp
        _ = ((|n| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
        _ = |(n : ℝ)| := by rw [Int.cast_abs]
    rw [← hcast]
    exact_mod_cast hn
  have hMpos : 0 < (M : ℝ) := by
    by_contra h
    have hMzero : (M : ℝ) = 0 := by
      have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    have hMnat : M = 0 := by exact_mod_cast hMzero
    subst M
    norm_num at hcut
    linarith [hK]
  have hnabspos : 0 < |(n : ℝ)| := lt_of_lt_of_le hMpos habs
  have hJpos : 0 < japaneseBracket n := NlsGge.Pilot.japaneseBracket_pos n
  have hJabs : |(n : ℝ)| ≤ japaneseBracket n := by
    have hJ2 := NlsGge.Weights.bracket_sq38 n
    apply (sq_le_sq₀ (abs_nonneg _) hJpos.le).1
    rw [hJ2, sq_abs]
    nlinarith
  have hdist : |2 * «λ» - 2 * Real.pi * n| ≤ 2 * K / japaneseBracket n := by
    calc
      |2 * «λ» - 2 * Real.pi * n| = 2 * |«λ» - (n : ℝ) * Real.pi| := by
        rw [show 2 * «λ» - 2 * Real.pi * n = 2 * («λ» - (n : ℝ) * Real.pi) by ring, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (K / japaneseBracket n) := mul_le_mul_of_nonneg_left hloc (by norm_num)
      _ = 2 * K / japaneseBracket n := by ring
  have htriangle : |2 * Real.pi * (n : ℝ)| - |2 * «λ»| ≤
      |2 * Real.pi * (n : ℝ) - 2 * «λ»| := by
    exact abs_sub_abs_le_abs_sub (2 * Real.pi * (n : ℝ)) (2 * «λ»)
  have hpiabs : |2 * Real.pi * (n : ℝ)| = 2 * Real.pi * |(n : ℝ)| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hdist' : |2 * Real.pi * (n : ℝ) - 2 * «λ»| =
      |2 * «λ» - 2 * Real.pi * (n : ℝ)| := abs_sub_comm _ _
  rw [hpiabs] at htriangle
  rw [hdist'] at htriangle
  have hKbound : 2 * K / japaneseBracket n ≤ Real.pi * |(n : ℝ)| := by
    apply (div_le_iff₀ hJpos).2
    have hMprod : 0 ≤ (|(n : ℝ)| - (M : ℝ)) * (|(n : ℝ)| + (M : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr habs)
        (add_nonneg (abs_nonneg _) (Nat.cast_nonneg M))
    have hMle : (M : ℝ) ^ 2 ≤ |(n : ℝ)| ^ 2 := by nlinarith [hMprod]
    have hKlt : 2 * K < Real.pi * |(n : ℝ)| ^ 2 := by
      calc
        2 * K < Real.pi * (M : ℝ) ^ 2 := hcut
        _ ≤ Real.pi * |(n : ℝ)| ^ 2 := mul_le_mul_of_nonneg_left hMle Real.pi_pos.le
    have hprod : |(n : ℝ)| ^ 2 ≤ |(n : ℝ)| * japaneseBracket n := by
      calc
        |(n : ℝ)| ^ 2 = |(n : ℝ)| * |(n : ℝ)| := by ring
        _ ≤ |(n : ℝ)| * japaneseBracket n :=
          mul_le_mul_of_nonneg_left hJabs (abs_nonneg (n : ℝ))
    have hprodPi := mul_le_mul_of_nonneg_left hprod Real.pi_pos.le
    nlinarith [mul_pos Real.pi_pos hnabspos, hprodPi]
  linarith

private lemma lowerWeight_high_inverse_square (K : ℝ) (hK : 0 < K) (M : ℕ)
    (hcut : 2 * K < Real.pi * (M : ℝ) ^ 2) (n : ℤ) («λ» : ℝ)
    (hn : M ≤ n.natAbs) (hloc : |«λ» - (n : ℝ) * Real.pi| ≤ K / japaneseBracket n) :
    0 < (2 * «λ») ^ 2 ∧
      ((2 * «λ») ^ 2)⁻¹ ≤ (2 / Real.pi ^ 2) * japaneseBracket n ^ (-2 : ℝ) := by
  have «hλ» := lowerWeight_high_lambda K hK M hcut n «λ» hn hloc
  have hJ2 := NlsGge.Weights.bracket_sq38 n
  have habs2 : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
  have hnabsge : 1 ≤ |(n : ℝ)| := by
    have habs : (M : ℝ) ≤ |(n : ℝ)| := by
      have hcast : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
        calc
          (Int.natAbs n : ℝ) = ((Int.natAbs n : ℤ) : ℝ) := by simp
          _ = ((|n| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
          _ = |(n : ℝ)| := by rw [Int.cast_abs]
      rw [← hcast]
      exact_mod_cast hn
    have hMpos : 0 < (M : ℝ) := by
      by_contra h
      have hMzero : (M : ℝ) = 0 := by
        have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
        linarith
      have hMnat : M = 0 := by exact_mod_cast hMzero
      subst M
      norm_num at hcut
      linarith [hK]
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      have hMzero : M = 0 := by omega
      subst M
      norm_num at hcut
      linarith [hK]
    have hnat : 1 ≤ n.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hn0)
    have hcast : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
      calc
        (Int.natAbs n : ℝ) = ((Int.natAbs n : ℤ) : ℝ) := by simp
        _ = ((|n| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
        _ = |(n : ℝ)| := by rw [Int.cast_abs]
    rw [← hcast]
    exact_mod_cast hnat
  have hnabspos : 0 < |(n : ℝ)| := lt_of_lt_of_le (by norm_num) hnabsge
  have hJle : japaneseBracket n ^ 2 ≤ 2 * |(n : ℝ)| ^ 2 := by
    rw [hJ2, habs2]
    have hprod := mul_nonneg (sub_nonneg.mpr hnabsge)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg (n : ℝ)))
    nlinarith [hprod]
  have hsq : Real.pi ^ 2 * |(n : ℝ)| ^ 2 ≤ (2 * «λ») ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr «hλ»)
      (add_nonneg (abs_nonneg (2 * «λ»))
        (mul_nonneg Real.pi_pos.le (abs_nonneg (n : ℝ))))
    nlinarith [hprod, sq_abs (2 * «λ»), habs2]
  have «hλpos» : 0 < |2 * «λ»| :=
    lt_of_lt_of_le (mul_pos Real.pi_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hnabsge)) «hλ»
  have hden : 0 < (2 * «λ») ^ 2 := by
    rw [← sq_abs]
    positivity
  have hJpos : 0 < japaneseBracket n := NlsGge.Pilot.japaneseBracket_pos n
  have hpow : japaneseBracket n ^ (-2 : ℝ) = 1 / japaneseBracket n ^ 2 := by
    rw [Real.rpow_neg hJpos.le (2 : ℝ), Real.rpow_two]
    simp [div_eq_mul_inv]
  have hrecip : ((2 * «λ») ^ 2)⁻¹ ≤ 1 / (Real.pi ^ 2 * |(n : ℝ)| ^ 2) := by
    simpa [one_div] using
      (inv_anti₀ (mul_pos (sq_pos_of_ne_zero Real.pi_pos.ne')
        (sq_pos_of_ne_zero hnabspos.ne')) hsq)
  constructor
  · exact hden
  ·
    have hrecip' : 1 / (Real.pi ^ 2 * |(n : ℝ)| ^ 2) ≤ 2 / (Real.pi ^ 2 * japaneseBracket n ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hJlePi := mul_le_mul_of_nonneg_left hJle (sq_nonneg Real.pi)
      nlinarith [hJlePi, sq_pos_of_ne_zero Real.pi_pos.ne', sq_pos_of_ne_zero hnabspos.ne']
    calc
      ((2 * «λ») ^ 2)⁻¹ ≤ 1 / (Real.pi ^ 2 * |(n : ℝ)| ^ 2) := hrecip
      _ ≤ 2 / (Real.pi ^ 2 * japaneseBracket n ^ 2) := hrecip'
      _ = (2 / Real.pi ^ 2) * (1 / japaneseBracket n ^ 2) := by ring
      _ = (2 / Real.pi ^ 2) * japaneseBracket n ^ (-2 : ℝ) := by rw [hpow]

theorem lowerWeight_gap_bound
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus)
    (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : PhysicalL2)
        (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ R →
        ∀ (n : ℤ) («λ» : ℝ),
          «λ» ∈ Set.Icc (actualGapLowerAllE02_38 u n)
            (actualGapUpperAllE02_38 u n) →
          NlsGge.Atomic.T.T024.B c (2 * «λ») ≤
            C * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := by
  have hcRange : cMinus ≤ cPlus := (hcBounds 0).1.trans (hcBounds 0).2
  let B0 : ℝ := max 1 R
  have hB0 : 1 ≤ B0 := le_max_left _ _
  have hR0 : R ≤ B0 := le_max_right _ _
  obtain ⟨K, hK, hloc⟩ :=
    actualGapLocalization_allU_E02_38 B0 hB0
  obtain ⟨CB, hCB, hsymbol⟩ :=
    NlsGge.Weights.uniformSymbolGap38 cMinus cPlus hcMinus hcRange B0 hB0
  obtain ⟨hIdentity, hZero, hBpos, hAnalytic, hCompat, _, _⟩ :=
    NlsGge.Atomic.T.T024.lowerWeight_identity_rates cMinus cPlus c hcMinus hcBounds
  obtain ⟨M, hMgt⟩ := exists_nat_gt (Real.sqrt (2 * K / Real.pi))
  have hMpos : 0 < (M : ℝ) := by
    have hsqrt : 0 < Real.sqrt (2 * K / Real.pi) := by positivity
    exact lt_trans hsqrt hMgt
  have hcut : 2 * K < Real.pi * (M : ℝ) ^ 2 := by
    have hsqrt := Real.sq_sqrt (show 0 ≤ 2 * K / Real.pi by positivity)
    have hsum : 0 < Real.sqrt (2 * K / Real.pi) + (M : ℝ) := by positivity
    have hprod := mul_pos (sub_pos.mpr hMgt) hsum
    have hsq : (2 * K / Real.pi) < (M : ℝ) ^ 2 := by nlinarith [hprod, hsqrt]
    simpa [mul_comm] using (div_lt_iff₀ Real.pi_pos).mp hsq
  have hcontC : Continuous (fun r : ℝ => NlsGge.Atomic.T.T024.BComplex c (r : ℂ)) :=
    (continuous_iff_continuousAt).2 fun r =>
      (hAnalytic (r : ℂ)).continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hcontCast : Continuous (fun r : ℝ => (NlsGge.Atomic.T.T024.B c r : ℂ)) :=
    hcontC.congr hCompat
  have hcontB : Continuous fun r : ℝ => NlsGge.Atomic.T.T024.B c r := by
    have hreal : (fun r : ℝ => Complex.re (NlsGge.Atomic.T.T024.B c r : ℂ)) =
        fun r => NlsGge.Atomic.T.T024.B c r := by
      funext r
      simp
    rw [← hreal]
    exact Complex.continuous_re.comp hcontCast
  let S : ℝ := 2 * Real.pi * (M : ℝ) + 2 * K
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨L0, hL⟩ :=
    (isCompact_Icc (a := -S) (b := S)).exists_bound_of_continuousOn hcontB.continuousOn
  let L : ℝ := max L0 0
  have hLnonneg : 0 ≤ L := le_max_right _ _
  have hLbound : ∀ r : ℝ, |r| ≤ S → NlsGge.Atomic.T.T024.B c r ≤ L := by
    intro r hr
    have hrIcc : r ∈ Set.Icc (-S) S := by
      rw [Set.mem_Icc]
      exact ⟨(abs_le.mp hr).1, (abs_le.mp hr).2⟩
    have hb := hL r hrIcc
    have hbpos := hBpos r
    rw [Real.norm_of_nonneg hbpos.le] at hb
    exact hb.trans (le_max_left _ _)
  let C_hi : ℝ := (1 + CB) * (2 / Real.pi ^ 2)
  let C_lo : ℝ := (L + 1) * (1 + (M : ℝ) ^ 2) / cMinus
  let C : ℝ := max C_hi C_lo
  have hChi : 0 < C_hi := by dsimp [C_hi]; positivity
  have hClo : 0 < C_lo := by
    dsimp [C_lo]
    apply div_pos
    · positivity
    · exact hcMinus
  have hC : 0 < C := by dsimp [C]; exact lt_of_lt_of_le hChi (le_max_left _ _)
  refine ⟨C, hC, fun u hu huR n «λ» hgap => ?_⟩
  have huB0 : ‖physicalSobolevL2 1 u hu‖ ≤ B0 := huR.trans hR0
  have «hlocλ» := hloc u hu huB0 n «λ» hgap
  have «hsymbolλ» := hsymbol c (fun j => (hcBounds j).1) (fun j => (hcBounds j).2)
    u hu huB0 n «λ» hgap
  have hWdiff := «hsymbolλ».2
  have hApos : 0 < NlsGge.Atomic.T.T024.a c n := by
    change 0 < NlsGge.Weights.weight c (2 * Real.pi * (n : ℝ))
    exact NlsGge.Weights.weight_pos cMinus cPlus c hcMinus (fun j => (hcBounds j).1)
      (fun j => (hcBounds j).2) _
  have hWbound : NlsGge.Weights.weight c (2 * «λ») ≤
      (1 + CB) * NlsGge.Atomic.T.T024.a c n := by
    have hWdiff' : NlsGge.Weights.weight c (2 * «λ») -
        NlsGge.Atomic.T.T024.a c n ≤
        CB * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-(3 / 2 : ℝ)) := by
      have hdiff := (abs_le.mp hWdiff).2
      simpa [NlsGge.Atomic.T.T024.a, NlsGge.Measure.fullWeightRate] using hdiff
    have hterm : japaneseBracket n ^ (-(3 / 2 : ℝ)) ≤ 1 := by
      have hJ := NlsGge.Weights.bracket_pos38 n
      have hx := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        (NlsGge.Weights.bracket_pos38 n) (by norm_num : (-(3 / 2 : ℝ)) ≤ 0)
      simpa using hx
    have hmul := mul_le_mul_of_nonneg_left hterm (mul_nonneg hCB.le hApos.le)
    calc
      NlsGge.Weights.weight c (2 * «λ») =
          (NlsGge.Weights.weight c (2 * «λ») - NlsGge.Atomic.T.T024.a c n) +
            NlsGge.Atomic.T.T024.a c n := by
          simp [NlsGge.Atomic.T.T024.a, NlsGge.Measure.fullWeightRate]
      _ ≤ CB * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-(3 / 2 : ℝ)) +
            NlsGge.Atomic.T.T024.a c n := add_le_add hWdiff' le_rfl
      _ ≤ CB * NlsGge.Atomic.T.T024.a c n + NlsGge.Atomic.T.T024.a c n := by
        simpa only [mul_one] using add_le_add hmul le_rfl
      _ = (1 + CB) * NlsGge.Atomic.T.T024.a c n := by ring
  have hgridle :
      NlsGge.Atomic.T.T024.B c (2 * «λ») ≤ C * NlsGge.Atomic.T.T024.a c n *
        japaneseBracket n ^ (-2 : ℝ) := by
    by_cases hn : M ≤ n.natAbs
    · have hinv := lowerWeight_high_inverse_square K hK M hcut n «λ» hn «hlocλ»
      have hrId := hIdentity (2 * «λ»)
      have hBhigh : NlsGge.Atomic.T.T024.B c (2 * «λ») ≤
          NlsGge.Weights.weight c (2 * «λ») / (2 * «λ») ^ 2 := by
        apply (le_div_iff₀ hinv.1).2
        rw [mul_comm, hrId]
        exact sub_le_self _ (le_trans hcMinus.le (hcBounds 0).1)
      have hrecipmul :
          ((1 + CB) * NlsGge.Atomic.T.T024.a c n) * ((2 * «λ») ^ 2)⁻¹ ≤
            C_hi * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := by
        dsimp [C_hi]
        have hscale : 0 ≤ (1 + CB) * NlsGge.Atomic.T.T024.a c n := by positivity
        calc
          ((1 + CB) * NlsGge.Atomic.T.T024.a c n) * ((2 * «λ») ^ 2)⁻¹ ≤
              ((1 + CB) * NlsGge.Atomic.T.T024.a c n) *
                ((2 / Real.pi ^ 2) * japaneseBracket n ^ (-2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv.2 hscale
          _ = ((1 + CB) * (2 / Real.pi ^ 2)) *
                NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := by ring
      calc
        NlsGge.Atomic.T.T024.B c (2 * «λ») ≤
            NlsGge.Weights.weight c (2 * «λ») / (2 * «λ») ^ 2 := hBhigh
        _ ≤ ((1 + CB) * NlsGge.Atomic.T.T024.a c n) * ((2 * «λ») ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hWbound (inv_nonneg.mpr (sq_nonneg _))
        _ ≤ C_hi * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := hrecipmul
        _ ≤ C * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := by
          dsimp [C]
          have hfactor : 0 ≤ NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) :=
            mul_nonneg hApos.le (Real.rpow_nonneg (NlsGge.Pilot.japaneseBracket_pos n).le _)
          calc
            C_hi * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) =
                C_hi * (NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ)) := by ring
            _ ≤
                C * (NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hfactor
            _ = C * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := by ring
    · have hnlt : n.natAbs < M := Nat.lt_of_not_ge hn
      have hnabs : |(n : ℝ)| < (M : ℝ) := by
        have hcast : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
          calc
            (Int.natAbs n : ℝ) = ((Int.natAbs n : ℤ) : ℝ) := by simp
            _ = ((|n| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
            _ = |(n : ℝ)| := by rw [Int.cast_abs]
        rw [← hcast]
        exact_mod_cast hnlt
      have hJone : 1 ≤ japaneseBracket n := NlsGge.Weights.bracket_pos38 n
      have hlambda : |2 * «λ»| ≤ S := by
        have hdist := «hlocλ»
        have hJpos := NlsGge.Pilot.japaneseBracket_pos n
        have hlocal : |«λ»| ≤ Real.pi * |(n : ℝ)| + K := by
          have hJinv : K / japaneseBracket n ≤ K := by
            apply (div_le_iff₀ hJpos).2
            nlinarith [mul_le_mul_of_nonneg_left hJone hK.le]
          have hpiabs : |(n : ℝ) * Real.pi| = |(n : ℝ)| * Real.pi := by
            rw [abs_mul, abs_of_pos Real.pi_pos]
          have hloc' : |«λ» - (n : ℝ) * Real.pi| ≤ K := hdist.trans hJinv
          calc
            |«λ»| = |(«λ» - (n : ℝ) * Real.pi) + (n : ℝ) * Real.pi| := by congr 1 <;> ring
            _ ≤ |«λ» - (n : ℝ) * Real.pi| + |(n : ℝ) * Real.pi| := abs_add_le _ _
            _ ≤ K + (Real.pi * |(n : ℝ)|) := by
              calc
                |«λ» - (n : ℝ) * Real.pi| + |(n : ℝ) * Real.pi| ≤
                    K + |(n : ℝ) * Real.pi| := add_le_add_left hloc' _
                _ = K + Real.pi * |(n : ℝ)| := by rw [hpiabs]; ring
            _ = Real.pi * |(n : ℝ)| + K := by ring
        have hMul := mul_le_mul_of_nonneg_left hlocal (by norm_num : (0 : ℝ) ≤ 2)
        dsimp [S]
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      have hBsmall : NlsGge.Atomic.T.T024.B c (2 * «λ») ≤ L := by
        apply hLbound (2 * «λ»)
        simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hlambda
      have hJ2 := NlsGge.Weights.bracket_sq38 n
      have hJupper : japaneseBracket n ^ 2 ≤ 1 + (M : ℝ) ^ 2 := by
        rw [hJ2]
        have hprod : 0 ≤ ((M : ℝ) - |(n : ℝ)|) * ((M : ℝ) + |(n : ℝ)|) :=
          mul_nonneg (sub_nonneg.mpr hnabs.le)
            (add_nonneg (Nat.cast_nonneg M) (abs_nonneg _))
        nlinarith [hprod, sq_abs (n : ℝ)]
      have hYpos : 0 < Real.sqrt (1 + (M : ℝ) ^ 2) := by positivity
      have hJleY : japaneseBracket n ≤ Real.sqrt (1 + (M : ℝ) ^ 2) := by
        apply (Real.le_sqrt (NlsGge.Pilot.japaneseBracket_pos n).le (by positivity)).2
        nlinarith [hJupper]
      have hpow :
          (Real.sqrt (1 + (M : ℝ) ^ 2)) ^ (-2 : ℝ) ≤ japaneseBracket n ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 (by positivity)) hJleY
          (by norm_num)
      have hpowY : (Real.sqrt (1 + (M : ℝ) ^ 2)) ^ (-2 : ℝ) =
          1 / (1 + (M : ℝ) ^ 2) := by
        rw [Real.rpow_neg (Real.sqrt_pos.2 (by positivity)).le (2 : ℝ), Real.rpow_two]
        rw [Real.sq_sqrt (by positivity)]
        simp [div_eq_mul_inv]
      have hJinv : 1 / (1 + (M : ℝ) ^ 2) ≤ japaneseBracket n ^ (-2 : ℝ) := by
        rw [← hpowY]
        exact hpow
      have hrate : cMinus / (1 + (M : ℝ) ^ 2) ≤
          NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := by
        have hlowRate := NlsGge.Weights.weight_lower cMinus cPlus c hcMinus
          (fun j => (hcBounds j).1) (fun j => (hcBounds j).2)
          (2 * Real.pi * (n : ℝ))
        change cMinus ≤ NlsGge.Atomic.T.T024.a c n at hlowRate
        have hpowpos : 0 ≤ japaneseBracket n ^ (-2 : ℝ) :=
          Real.rpow_nonneg (NlsGge.Pilot.japaneseBracket_pos n).le _
        calc
          cMinus / (1 + (M : ℝ) ^ 2) ≤ cMinus * japaneseBracket n ^ (-2 : ℝ) := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hJinv) hcMinus.le
          _ ≤ NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right hlowRate hpowpos
      have hfactor : 0 ≤ NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) :=
        mul_nonneg hApos.le (Real.rpow_nonneg (NlsGge.Pilot.japaneseBracket_pos n).le _)
      have hlow : NlsGge.Atomic.T.T024.B c (2 * «λ») ≤
          C_lo * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := by
        dsimp [C_lo]
        have hmul := mul_le_mul_of_nonneg_left hrate
          (show 0 ≤ (L + 1) * (1 + (M : ℝ) ^ 2) / cMinus by positivity)
        have heq : ((L + 1) * (1 + (M : ℝ) ^ 2) / cMinus) *
            (cMinus / (1 + (M : ℝ) ^ 2)) = L + 1 := by
          field_simp [ne_of_gt hcMinus]
        rw [heq] at hmul
        nlinarith [hBsmall]
      calc
        NlsGge.Atomic.T.T024.B c (2 * «λ») ≤
            C_lo * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := hlow
        _ ≤ C * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := by
          dsimp [C]
          calc
            C_lo * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) =
                C_lo * (NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ)) := by ring
            _ ≤
                C * (NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hfactor
            _ = C * NlsGge.Atomic.T.T024.a c n * japaneseBracket n ^ (-2 : ℝ) := by ring
  exact hgridle

end NlsGge.Atomic.T.T025
end
