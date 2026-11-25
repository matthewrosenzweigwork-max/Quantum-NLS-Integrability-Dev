import Mathlib
import NlsGge.Atomic.G5.G5007
import NlsGge.Atomic.G5.G5009
import NlsGge.Atomic.G5.G5012Host
import NlsGge.Atomic.G4.G4038

/- G5-010 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5010.lean.
   Head `G5010` verbatim from STATEMENTS/G5.md (followup12; round 14 retains the head, cluster 5). No lexical edits.
   fourierRealBasisPlus/Minus are the G5012Host bodies (pending landing).
   Route (GK-17.2): l2 conjuncts = G5-009 error + (1/sqrt 8)(G5-006 errors for a = 1, -1), since
   (2/sqrt 8)(e_1 +- e_{-1}) is exactly minus the real Fourier basis vector (sqrt 8 = 2 sqrt 2, G4038Aux.sqrt8_eq).
   Vacuum conjunct (audit E6): at the zero potential Z+-_n(0) = 0 (tau = mu = n pi, antiDiscrim 0 = 0), xi_n(0) = 1
   (G2-035), beta_n(0) = 0 (G3-026 row HasSum with all spectral masses zero, as in G5-008), and grad Z+-(0) = -2 e_{+-1}
   (G5-007), so the collapsed product rule of G5-009 gives the basis vectors. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.ThirdConsultation (finiteGap)
open NlsGge.ThirdConsultation.G5005Support1 NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5010_tau_zero (n : ℤ) : tauN 0 n = (n : ℂ) * (Real.pi : ℂ) :=
  (tauGamma_free_values38 discC discR (fun φ hφ => isolating_family38 φ hφ) n).1

theorem g5010_Z_zero (n a : ℤ) : cartesianZExtended n a 0 = 0 := by
  have h1 : tauN 0 n - muSeq 0 n = 0 := by
    rw [g5010_tau_zero, g5007_muSeq_zero, sub_self]
  have h2 : terminalRoot n 0 = 0 := by
    unfold terminalRoot
    rw [antiDiscrim_zero38, zero_div]
  unfold cartesianZExtended
  split_ifs <;> simp [h1, h2]

theorem g5010_beta_zero (n : ℤ) : betaSum n 0 = 0 := by
  obtain ⟨U, hUo, hUr, hUsub, hloc⟩ := G3_026
  obtain ⟨V, C, M, hVo, h0V, hVU, hC, hM, hV⟩ := hloc (realSlice 0) (hUr ⟨0, rfl⟩)
  obtain ⟨hs, hspec, hb, hrow⟩ := hV (realSlice 0) h0V
  obtain ⟨-, hH, -, -⟩ := hrow n
  have hz : ∀ m : ℤ, offDiagonalBeta n m (realSlice 0) = 0 := by
    intro m
    have h0 : gk151BetaMass38 (realSlice 0) m = 0 := by
      rw [realSlice_zero]
      unfold gk151BetaMass38
      rw [lamPlus_zero38, lamMinus_zero38, g5010_tau_zero, muSeq_zero38]
      simp [countingCenter38]
    have h1 := hb n m
    rw [h0, norm_zero, mul_zero, zero_mul] at h1
    exact norm_le_zero_iff.mp h1
  have h2 : HasSum (fun m : ℤ => offDiagonalBeta n m (realSlice 0)) 0 := by
    simp only [hz]
    exact hasSum_zero
  have h3 := hH.unique h2
  rwa [realSlice_zero] at h3

theorem g5010_xi_zero (n : ℤ) : xiN38 n 0 = 1 := G2_035.2.2.2.1 n

theorem g5010_sqrt :
    (1 / (Real.sqrt 8 : ℂ)) * (-2) = -1 / (Real.sqrt 2 : ℂ) ∧
    (1 / ((Real.sqrt 8 : ℂ) * Complex.I)) * (-2) = -1 / (Complex.I * (Real.sqrt 2 : ℂ)) ∧
    (1 / (Real.sqrt 8 : ℂ)) * 2 = 1 / (Real.sqrt 2 : ℂ) ∧
    (1 / ((Real.sqrt 8 : ℂ) * Complex.I)) * 2 = 1 / (Complex.I * (Real.sqrt 2 : ℂ)) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [G4038Aux.sqrt8_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem g5010_vacuum (n : ℤ) :
    pairGradient (cartesianX n) 0 = fourierRealBasisPlus n ∧
    pairGradient (cartesianY n) 0 = fourierRealBasisMinus n := by
  have h0 : (0 : PotPair) ∈ sourceBetaW := g5007_zero_mem
  obtain ⟨hX, hY⟩ := g5009_grad_collapsed n 0 h0 (g5010_Z_zero n 1) (g5010_Z_zero n (-1))
  have hZp := (G5007 n 1 (Or.inl rfl)).2.2.2.2.2
  have hZm := (G5007 n (-1) (Or.inr rfl)).2.2.2.2.2
  obtain ⟨s1, s2, -, -⟩ := g5010_sqrt
  rw [hX, hY, hZp, hZm, g5010_xi_zero, g5010_beta_zero]
  unfold fourierRealBasisPlus fourierRealBasisMinus
  simp only [mul_zero, neg_zero, Complex.exp_zero, one_smul]
  constructor
  · rw [← s1]
    match_scalars <;> ring
  · rw [← s2]
    match_scalars <;> ring

theorem g5010_pgn_combo (c : ℂ) (hc : ‖c‖ ≤ 1) (a b d : PotPair) :
    pairGradientNorm (a + c • (b + d)) ^ 2 ≤
      2 * pairGradientNorm a ^ 2 + 4 * pairGradientNorm b ^ 2 + 4 * pairGradientNorm d ^ 2 ∧
    pairGradientNorm (a + c • (b - d)) ^ 2 ≤
      2 * pairGradientNorm a ^ 2 + 4 * pairGradientNorm b ^ 2 + 4 * pairGradientNorm d ^ 2 := by
  have hc2 : ‖c‖ ^ 2 ≤ 1 := by
    have := norm_nonneg c
    nlinarith
  have hs : ∀ v : PotPair, pairGradientNorm (c • v) ^ 2 ≤ pairGradientNorm v ^ 2 := by
    intro v
    rw [pgn_smul, mul_pow]
    have := sq_nonneg (pairGradientNorm v)
    nlinarith
  constructor
  · have e1 := pgn_add_sq a (c • (b + d))
    have e2 := hs (b + d)
    have e3 := pgn_add_sq b d
    nlinarith
  · have e1 := pgn_add_sq a (c • (b - d))
    have e2 := hs (b - d)
    have e3 := pgn_sub_sq b d
    nlinarith

theorem G5010 (u : PhysicalL2) (hu : finiteGap u) :
  Memℓp (fun n : ℤ => pairGradientNorm
    (pairGradient (cartesianX n) (realSlice u) - fourierRealBasisPlus n)) 2 ∧
  Memℓp (fun n : ℤ => pairGradientNorm
    (pairGradient (cartesianY n) (realSlice u) - fourierRealBasisMinus n)) 2 ∧
  (∀ n : ℤ, pairGradient (cartesianX n) 0 = fourierRealBasisPlus n ∧
    pairGradient (cartesianY n) 0 = fourierRealBasisMinus n) := by
  obtain ⟨h9X, h9Y⟩ := G5009 u hu
  have s9X := g5006_sq h9X
  have s9Y := g5006_sq h9Y
  have s6p := g5006_sq (G5006 u hu 1 (Or.inl rfl))
  have s6m := g5006_sq (G5006 u hu (-1) (Or.inr rfl))
  obtain ⟨-, -, s3, s4⟩ := g5010_sqrt
  refine ⟨?_, ?_, g5010_vacuum⟩
  · refine memlp_of_sq_summable ?_
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      (((s9X.mul_left 2).add (s6p.mul_left 4)).add (s6m.mul_left 4))
    have e : pairGradient (cartesianX n) (realSlice u) - fourierRealBasisPlus n =
        (pairGradient (cartesianX n) (realSlice u) - (1 / (Real.sqrt 8 : ℂ)) •
          (pairGradient (cartesianZExtended n 1) (realSlice u) +
            pairGradient (cartesianZExtended n (-1)) (realSlice u))) +
        (1 / (Real.sqrt 8 : ℂ)) •
          ((pairGradient (cartesianZExtended n 1) (realSlice u) + (2 : ℂ) • fourierMode 1 n) +
            (pairGradient (cartesianZExtended n (-1)) (realSlice u) + (2 : ℂ) • fourierMode (-1) n)) := by
      unfold fourierRealBasisPlus
      have hs3 : (-1 / (Real.sqrt 2 : ℂ)) = -((1 / (Real.sqrt 8 : ℂ)) * 2) := by rw [s3]; ring
      rw [hs3]
      match_scalars <;> ring
    rw [e]
    exact (g5010_pgn_combo _ g5009_norm_inv_sqrt8.1 _ _ _).1
  · refine memlp_of_sq_summable ?_
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      (((s9Y.mul_left 2).add (s6p.mul_left 4)).add (s6m.mul_left 4))
    have e : pairGradient (cartesianY n) (realSlice u) - fourierRealBasisMinus n =
        (pairGradient (cartesianY n) (realSlice u) - (1 / ((Real.sqrt 8 : ℂ) * Complex.I)) •
          (pairGradient (cartesianZExtended n 1) (realSlice u) -
            pairGradient (cartesianZExtended n (-1)) (realSlice u))) +
        (1 / ((Real.sqrt 8 : ℂ) * Complex.I)) •
          ((pairGradient (cartesianZExtended n 1) (realSlice u) + (2 : ℂ) • fourierMode 1 n) -
            (pairGradient (cartesianZExtended n (-1)) (realSlice u) + (2 : ℂ) • fourierMode (-1) n)) := by
      unfold fourierRealBasisMinus
      have hs4 : (-1 / (Complex.I * (Real.sqrt 2 : ℂ))) =
          -((1 / ((Real.sqrt 8 : ℂ) * Complex.I)) * 2) := by rw [s4]; ring
      rw [hs4]
      match_scalars <;> ring
    rw [e]
    exact (g5010_pgn_combo _ g5009_norm_inv_sqrt8.2 _ _ _).2

end
end NlsGge.GKDefinitionDesign
