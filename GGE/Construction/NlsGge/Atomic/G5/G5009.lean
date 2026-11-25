import Mathlib
import NlsGge.Atomic.G5.G5006
import NlsGge.Atomic.G5.G5008
import NlsGge.Atomic.G4.G4040
import NlsGge.Atomic.G4.G4041
import NlsGge.Atomic.G2.G2035
import NlsGge.ThirdConsultation.G5.G5005Support1
import NlsGge.ThirdConsultation.G5.G5017Support1

                                                                                                   
                                                                                                                                                              
                                                                                                         
                                                                                                                        
                                                                                                                              
                                                                                                                              
                                                                                                                          
                                                                                                         
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.ThirdConsultation (finiteGap)
open NlsGge.ThirdConsultation.G5005Support1 NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5009_X_eq (n : ℤ) (ψ : PotPair) (hψ : ψ ∈ sourceBetaW) :
    cartesianX n ψ = (xiN38 n ψ / (Real.sqrt 8 : ℂ)) *
      (cartesianZExtended n 1 ψ * Complex.exp (Complex.I * betaSum n ψ) +
        cartesianZExtended n (-1) ψ * Complex.exp (-Complex.I * betaSum n ψ)) := by
  have hgk := G4041Aux.sourceBetaW_subset_gkW hψ
  simp only [cartesianX, gk16ScalarXModel38, G4014Aux.cartZ_plus n ψ hgk,
    G4014Aux.cartZ_minus n ψ hgk]

theorem g5009_Y_eq (n : ℤ) (ψ : PotPair) (hψ : ψ ∈ sourceBetaW) :
    cartesianY n ψ = (xiN38 n ψ / ((Real.sqrt 8 : ℂ) * Complex.I)) *
      (cartesianZExtended n 1 ψ * Complex.exp (Complex.I * betaSum n ψ) -
        cartesianZExtended n (-1) ψ * Complex.exp (-Complex.I * betaSum n ψ)) := by
  have hgk := G4041Aux.sourceBetaW_subset_gkW hψ
  simp only [cartesianY, gk16ScalarYModel38, G4014Aux.cartZ_plus n ψ hgk,
    G4014Aux.cartZ_minus n ψ hgk]

/-- Product rule at a point where both Z+- vanish. -/
theorem g5009_grad_collapsed (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW)
    (hp : cartesianZExtended n 1 φ = 0) (hm : cartesianZExtended n (-1) φ = 0) :
    pairGradient (cartesianX n) φ = (xiN38 n φ / (Real.sqrt 8 : ℂ)) •
      (Complex.exp (Complex.I * betaSum n φ) • pairGradient (cartesianZExtended n 1) φ +
        Complex.exp (-Complex.I * betaSum n φ) • pairGradient (cartesianZExtended n (-1)) φ) ∧
    pairGradient (cartesianY n) φ = (xiN38 n φ / ((Real.sqrt 8 : ℂ) * Complex.I)) •
      (Complex.exp (Complex.I * betaSum n φ) • pairGradient (cartesianZExtended n 1) φ -
        Complex.exp (-Complex.I * betaSum n φ) • pairGradient (cartesianZExtended n (-1)) φ) := by
  have hxi : DifferentiableAt ℂ (xiN38 n) φ :=
    ((xiN38_analytic_commonDomain n).mono sourceFamily.V_xi φ hφ).differentiableAt
  have hb : DifferentiableAt ℂ (betaSum n) φ :=
    (betaSum_analyticOnNhd_sourceBetaW n φ hφ).differentiableAt
  have hZp : DifferentiableAt ℂ (cartesianZExtended n 1) φ :=
    (G4036 n 1 (Or.inl rfl) φ hφ).differentiableAt
  have hZm : DifferentiableAt ℂ (cartesianZExtended n (-1)) φ :=
    (G4036 n (-1) (Or.inr rfl) φ hφ).differentiableAt
  have hEp : DifferentiableAt ℂ (fun ψ : PotPair => Complex.exp (Complex.I * betaSum n ψ)) φ :=
    (hb.const_mul _).cexp
  have hEm : DifferentiableAt ℂ (fun ψ : PotPair => Complex.exp (-Complex.I * betaSum n ψ)) φ :=
    (hb.const_mul _).cexp
  have hP : DifferentiableAt ℂ (fun ψ : PotPair =>
      cartesianZExtended n 1 ψ * Complex.exp (Complex.I * betaSum n ψ)) φ := hZp.mul hEp
  have hM : DifferentiableAt ℂ (fun ψ : PotPair =>
      cartesianZExtended n (-1) ψ * Complex.exp (-Complex.I * betaSum n ψ)) φ := hZm.mul hEm
  have key : ∀ L : PotPair →L[ℂ] ℂ, pairGradientCLM L = pairGradientL L := fun L => rfl
  constructor
  · have hev : cartesianX n =ᶠ[𝓝 φ] fun ψ : PotPair => (xiN38 n ψ / (Real.sqrt 8 : ℂ)) *
        (cartesianZExtended n 1 ψ * Complex.exp (Complex.I * betaSum n ψ) +
          cartesianZExtended n (-1) ψ * Complex.exp (-Complex.I * betaSum n ψ)) := by
      filter_upwards [sourceFamily.V_open.mem_nhds hφ] with ψ hψ
      exact g5009_X_eq n ψ hψ
    have hf : DifferentiableAt ℂ (fun ψ : PotPair => xiN38 n ψ / (Real.sqrt 8 : ℂ)) φ := by
      simp only [div_eq_mul_inv]
      exact hxi.mul_const _
    have hPM : DifferentiableAt ℂ (fun ψ : PotPair =>
        cartesianZExtended n 1 ψ * Complex.exp (Complex.I * betaSum n ψ) +
          cartesianZExtended n (-1) ψ * Complex.exp (-Complex.I * betaSum n ψ)) φ := hP.add hM
    unfold pairGradient
    rw [hev.fderiv_eq, fderiv_fun_mul hf hPM, fderiv_fun_add hP hM, fderiv_fun_mul hZp hEp,
      fderiv_fun_mul hZm hEm]
    simp only [hp, hm, zero_smul, zero_mul, zero_add, add_zero, key, map_add, map_smul]
  · have hev : cartesianY n =ᶠ[𝓝 φ] fun ψ : PotPair => (xiN38 n ψ / ((Real.sqrt 8 : ℂ) * Complex.I)) *
        (cartesianZExtended n 1 ψ * Complex.exp (Complex.I * betaSum n ψ) -
          cartesianZExtended n (-1) ψ * Complex.exp (-Complex.I * betaSum n ψ)) := by
      filter_upwards [sourceFamily.V_open.mem_nhds hφ] with ψ hψ
      exact g5009_Y_eq n ψ hψ
    have hf : DifferentiableAt ℂ (fun ψ : PotPair =>
        xiN38 n ψ / ((Real.sqrt 8 : ℂ) * Complex.I)) φ := by
      simp only [div_eq_mul_inv]
      exact hxi.mul_const _
    have hPM : DifferentiableAt ℂ (fun ψ : PotPair =>
        cartesianZExtended n 1 ψ * Complex.exp (Complex.I * betaSum n ψ) -
          cartesianZExtended n (-1) ψ * Complex.exp (-Complex.I * betaSum n ψ)) φ := hP.sub hM
    unfold pairGradient
    rw [hev.fderiv_eq, fderiv_fun_mul hf hPM, fderiv_fun_sub hP hM, fderiv_fun_mul hZp hEp,
      fderiv_fun_mul hZm hEm]
    simp only [hp, hm, zero_smul, zero_mul, zero_add, sub_zero, add_zero, key, map_add, map_sub,
      map_smul]

/-- Scalar estimate for `x e^{s b} - 1` with `|s| = 1`, `|b| ≤ 1`. -/
theorem g5009_scalar (x b s : ℂ) (hs : ‖s‖ = 1) (hb : ‖b‖ ≤ 1) :
    ‖x * Complex.exp (s * b) - 1‖ ^ 2 ≤ 18 * ‖x - 1‖ ^ 2 + 8 * ‖b‖ ^ 2 := by
  have hsb : ‖s * b‖ = ‖b‖ := by rw [norm_mul, hs, one_mul]
  have hE : ‖Complex.exp (s * b) - 1‖ ≤ 2 * ‖b‖ := by
    have h := Complex.norm_exp_sub_one_le (x := s * b) (by rw [hsb]; exact hb)
    rwa [hsb] at h
  have hE1 : ‖Complex.exp (s * b)‖ ≤ 3 := by
    have h : Complex.exp (s * b) = (Complex.exp (s * b) - 1) + 1 := by ring
    calc ‖Complex.exp (s * b)‖ = ‖(Complex.exp (s * b) - 1) + 1‖ := by rw [← h]
      _ ≤ ‖Complex.exp (s * b) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 := by rw [norm_one]; linarith
  have hsplit : x * Complex.exp (s * b) - 1 =
      (x - 1) * Complex.exp (s * b) + (Complex.exp (s * b) - 1) := by ring
  have h1 : ‖x * Complex.exp (s * b) - 1‖ ≤ 3 * ‖x - 1‖ + 2 * ‖b‖ := by
    rw [hsplit]
    calc ‖(x - 1) * Complex.exp (s * b) + (Complex.exp (s * b) - 1)‖
        ≤ ‖(x - 1) * Complex.exp (s * b)‖ + ‖Complex.exp (s * b) - 1‖ := norm_add_le _ _
      _ = ‖x - 1‖ * ‖Complex.exp (s * b)‖ + ‖Complex.exp (s * b) - 1‖ := by rw [norm_mul]
      _ ≤ ‖x - 1‖ * 3 + 2 * ‖b‖ := by
          gcongr
      _ = 3 * ‖x - 1‖ + 2 * ‖b‖ := by ring
  have h0 : 0 ≤ ‖x * Complex.exp (s * b) - 1‖ := norm_nonneg _
  have hx0 : 0 ≤ ‖x - 1‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
  nlinarith [sq_nonneg (3 * ‖x - 1‖ - 2 * ‖b‖)]

/-- Squared paired-norm estimate for `c • (p • gp ± m • gm)` with `|c| ≤ 1`. -/
theorem g5009_pgn_bound (c p m : ℂ) (gp gm : PotPair) (hc : ‖c‖ ≤ 1) (Bp Bm A : ℝ)
    (hgp : pairGradientNorm gp ^ 2 ≤ Bp) (hgm : pairGradientNorm gm ^ 2 ≤ Bm)
    (hpA : ‖p‖ ^ 2 ≤ A) (hmA : ‖m‖ ^ 2 ≤ A) :
    pairGradientNorm (c • (p • gp + m • gm)) ^ 2 ≤ 2 * (Bp + Bm) * A ∧
    pairGradientNorm (c • (p • gp - m • gm)) ^ 2 ≤ 2 * (Bp + Bm) * A := by
  have hc2 : ‖c‖ ^ 2 ≤ 1 := by
    have := norm_nonneg c
    nlinarith
  have hA : 0 ≤ A := le_trans (sq_nonneg _) hpA
  have hgp0 : 0 ≤ pairGradientNorm gp ^ 2 := sq_nonneg _
  have hgm0 : 0 ≤ pairGradientNorm gm ^ 2 := sq_nonneg _
  have t1 : pairGradientNorm (p • gp) ^ 2 ≤ A * Bp := by
    rw [pgn_smul, mul_pow]
    exact mul_le_mul hpA hgp hgp0 hA
  have t2 : pairGradientNorm (m • gm) ^ 2 ≤ A * Bm := by
    rw [pgn_smul, mul_pow]
    exact mul_le_mul hmA hgm hgm0 hA
  have hs : ∀ v : PotPair, pairGradientNorm (c • v) ^ 2 ≤ pairGradientNorm v ^ 2 := by
    intro v
    rw [pgn_smul, mul_pow]
    have := sq_nonneg (pairGradientNorm v)
    nlinarith
  constructor
  · refine le_trans (hs _) (le_trans (pgn_add_sq _ _) ?_)
    nlinarith
  · refine le_trans (hs _) (le_trans (pgn_sub_sq _ _) ?_)
    nlinarith

theorem g5009_norm_fourierLp (m : ℤ) :
    ‖(fourierLp (T := (1 : ℝ)) 2 m : PhysicalL2)‖ = 1 := by
  have h := (fourierBasis (T := (1 : ℝ))).orthonormal.1 m
  rw [coe_fourierBasis] at h
  exact h

theorem g5009_pgn_fourierMode (a n : ℤ) : pairGradientNorm (fourierMode a n) = 1 := by
  unfold pairGradientNorm fourierMode
  split_ifs <;> simp [g5009_norm_fourierLp] <;> left <;>
    first
    | exact g5009_norm_fourierLp _
    | (rw [← coe_fourierBasis]; exact (fourierBasis (T := (1 : ℝ))).orthonormal.1 _)

/-- Uniform bound on the squared z-gradients over all indices (from G5-006). -/
theorem g5009_gradZ_bound (u : PhysicalL2) (hu : finiteGap u) (a : ℤ) (ha : a = 1 ∨ a = -1) :
    ∃ B : ℝ, ∀ n : ℤ, pairGradientNorm (pairGradient (cartesianZExtended n a) (realSlice u)) ^ 2 ≤ B := by
  have hs := g5006_sq (G5006 u hu a ha)
  refine ⟨2 * (∑' n : ℤ, pairGradientNorm (pairGradient (cartesianZExtended n a) (realSlice u) +
      (2 : ℂ) • fourierMode a n) ^ 2) + 8, fun n => ?_⟩
  have h1 := hs.le_tsum n (fun j _ => sq_nonneg _)
  have h2 := pgn_sub_sq (pairGradient (cartesianZExtended n a) (realSlice u) + (2 : ℂ) • fourierMode a n)
    ((2 : ℂ) • fourierMode a n)
  rw [add_sub_cancel_right] at h2
  have h3 : pairGradientNorm ((2 : ℂ) • fourierMode a n) ^ 2 = 4 := by
    rw [pgn_smul, g5009_pgn_fourierMode]; norm_num
  rw [h3] at h2
  linarith

theorem g5009_norm_inv_sqrt8 : ‖(1 / (Real.sqrt 8 : ℂ))‖ ≤ 1 ∧
    ‖(1 / ((Real.sqrt 8 : ℂ) * Complex.I))‖ ≤ 1 := by
  have h8 : 1 ≤ Real.sqrt 8 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hn : ‖((Real.sqrt 8 : ℝ) : ℂ)‖ = Real.sqrt 8 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 8)]
  constructor
  · rw [norm_div, norm_one, hn]
    exact (div_le_one (by linarith)).mpr h8
  · rw [norm_div, norm_one, norm_mul, hn, Complex.norm_I, mul_one]
    exact (div_le_one (by linarith)).mpr h8

theorem G5009 (u : PhysicalL2) (hu : finiteGap u) :
  let φ := realSlice u
  Memℓp (fun n : ℤ => pairGradientNorm
    (pairGradient (cartesianX n) φ - (1 / (Real.sqrt 8 : ℂ)) •
      (pairGradient (cartesianZExtended n 1) φ +
        pairGradient (cartesianZExtended n (-1)) φ))) 2 ∧
  Memℓp (fun n : ℤ => pairGradientNorm
    (pairGradient (cartesianY n) φ - (1 / ((Real.sqrt 8 : ℂ) * Complex.I)) •
      (pairGradient (cartesianZExtended n 1) φ -
        pairGradient (cartesianZExtended n (-1)) φ))) 2 := by
  intro φ
  have hφ : φ ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  obtain ⟨Bp, hBp⟩ := g5009_gradZ_bound u hu 1 (Or.inl rfl)
  obtain ⟨Bm, hBm⟩ := g5009_gradZ_bound u hu (-1) (Or.inr rfl)
  have hxi : Summable (fun n : ℤ => ‖xiN38 n φ - 1‖ ^ 2) := by
    obtain ⟨-, hreal, -, -, hloc⟩ := G2_035
    obtain ⟨U, hU, -, δ, C, -, -, hC⟩ := hloc φ (hreal ⟨u, rfl⟩)
    exact (hC φ (mem_of_mem_nhds hU)).2.1
  have hβ : Summable (fun n : ℤ => ‖betaSum n φ‖ ^ 2) := by
    have h := (G5008 u hu).1
    have := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mp h
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
    exact this
  have hβev : ∀ᶠ n in cofinite, ‖betaSum n φ‖ ≤ 1 := by
    have ht := hβ.tendsto_cofinite_zero
    have h1 : ∀ᶠ n in cofinite, ‖betaSum n φ‖ ^ 2 < 1 :=
      ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h1] with n hn
    have := norm_nonneg (betaSum n φ)
    nlinarith
  have hfin : {n : ℤ | NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n ≠
      NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n}.Finite := hu
  have hcol : ∀ᶠ n in cofinite, NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n =
      NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n := by
    filter_upwards [hfin.eventually_cofinite_notMem] with n hn
    by_contra hne
    exact hn hne
  have hbd : Summable (fun n : ℤ => 2 * (Bp + Bm) * (18 * ‖xiN38 n φ - 1‖ ^ 2 + 8 * ‖betaSum n φ‖ ^ 2)) :=
    ((hxi.mul_left 18).add (hβ.mul_left 8)).mul_left _
  have hmain : ∀ᶠ n in cofinite,
      pairGradientNorm (pairGradient (cartesianX n) φ - (1 / (Real.sqrt 8 : ℂ)) •
        (pairGradient (cartesianZExtended n 1) φ + pairGradient (cartesianZExtended n (-1)) φ)) ^ 2 ≤
        2 * (Bp + Bm) * (18 * ‖xiN38 n φ - 1‖ ^ 2 + 8 * ‖betaSum n φ‖ ^ 2) ∧
      pairGradientNorm (pairGradient (cartesianY n) φ - (1 / ((Real.sqrt 8 : ℂ) * Complex.I)) •
        (pairGradient (cartesianZExtended n 1) φ - pairGradient (cartesianZExtended n (-1)) φ)) ^ 2 ≤
        2 * (Bp + Bm) * (18 * ‖xiN38 n φ - 1‖ ^ 2 + 8 * ‖betaSum n φ‖ ^ 2) := by
    filter_upwards [hcol, hβev] with n hn hbn
    obtain ⟨-, -, hz⟩ := G4040 u n
    obtain ⟨hzp, hzm⟩ := hz hn
    obtain ⟨hX, hY⟩ := g5009_grad_collapsed n φ hφ hzp hzm
    set gp := pairGradient (cartesianZExtended n 1) φ
    set gm := pairGradient (cartesianZExtended n (-1)) φ
    set ξ := xiN38 n φ
    set Ep := Complex.exp (Complex.I * betaSum n φ)
    set Em := Complex.exp (-Complex.I * betaSum n φ)
    have hp2 : ‖ξ * Ep - 1‖ ^ 2 ≤ 18 * ‖ξ - 1‖ ^ 2 + 8 * ‖betaSum n φ‖ ^ 2 :=
      g5009_scalar ξ (betaSum n φ) Complex.I Complex.norm_I hbn
    have hm2 : ‖ξ * Em - 1‖ ^ 2 ≤ 18 * ‖ξ - 1‖ ^ 2 + 8 * ‖betaSum n φ‖ ^ 2 :=
      g5009_scalar ξ (betaSum n φ) (-Complex.I) (by rw [norm_neg, Complex.norm_I]) hbn
    have eX : pairGradient (cartesianX n) φ - (1 / (Real.sqrt 8 : ℂ)) • (gp + gm) =
        (1 / (Real.sqrt 8 : ℂ)) • ((ξ * Ep - 1) • gp + (ξ * Em - 1) • gm) := by
      rw [hX]
      match_scalars <;> ring
    have eY : pairGradient (cartesianY n) φ - (1 / ((Real.sqrt 8 : ℂ) * Complex.I)) • (gp - gm) =
        (1 / ((Real.sqrt 8 : ℂ) * Complex.I)) • ((ξ * Ep - 1) • gp - (ξ * Em - 1) • gm) := by
      rw [hY]
      match_scalars <;> ring
    rw [eX, eY]
    exact ⟨(g5009_pgn_bound _ _ _ gp gm g5009_norm_inv_sqrt8.1 Bp Bm _ (hBp n) (hBm n) hp2 hm2).1,
      (g5009_pgn_bound _ _ _ gp gm g5009_norm_inv_sqrt8.2 Bp Bm _ (hBp n) (hBm n) hp2 hm2).2⟩
  constructor
  · refine memlp_of_sq_summable ?_
    refine Summable.of_norm_bounded_eventually hbd ?_
    filter_upwards [hmain] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hn.1
  · refine memlp_of_sq_summable ?_
    refine Summable.of_norm_bounded_eventually hbd ?_
    filter_upwards [hmain] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hn.2

end
end NlsGge.GKDefinitionDesign
