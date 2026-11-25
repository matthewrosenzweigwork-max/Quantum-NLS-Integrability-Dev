import Mathlib
import NlsGge.Atomic.M.M027
import NlsGge.Atomic.M.M028
import NlsGge.ThirdConsultation.M.M027Analytic
import NlsGge.ThirdConsultation.M.M029Host
import NlsGge.ThirdConsultation.M.M029Analytic
import NlsGge.ThirdConsultation.M.M029Disc
import NlsGge.ThirdConsultation.M.M029Count

   
                                                                                                               

                                                                                              

                                                                                                                                   
                                                                                                                        
                                                                                                                                  
                                                                                                                              
                                                                                                                      
                                                                                                                            
                                                 
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M029R

open NlsGge.ThirdConsultation NlsGge.ThirdConsultation.MTwoModeB
open NlsGge.ThirdConsultation.MTwoMode

theorem root_loc {u a1 a2 c : ℂ} {A B : ℝ} (hB : 0 ≤ B)
    (h1 : ‖a1‖ ≤ A) (h2 : ‖a2‖ ≤ A) (hc : ‖c‖ ≤ B ^ 2) (hu : A + B < ‖u‖) :
    (u - a1) * (u - a2) - c ≠ 0 := by
  intro h
  have e : (u - a1) * (u - a2) = c := sub_eq_zero.1 h
  have n1 : B < ‖u - a1‖ := by
    have := norm_sub_norm_le u a1
    linarith
  have n2 : B < ‖u - a2‖ := by
    have := norm_sub_norm_le u a2
    linarith
  have : B * B < ‖u - a1‖ * ‖u - a2‖ := mul_lt_mul'' n1 n2 hB hB
  rw [← norm_mul, e] at this
  nlinarith

theorem weight_facts (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (k : ℤ) :
    NlsGge.Atomic.M.M054.indexWeight k ≤ w k ∧ w (-k) = w k := by
  obtain ⟨v, hv1, hve, _, hwv⟩ := hw
  have hpos : 0 < NlsGge.Atomic.M.M054.indexWeight k := by
    unfold NlsGge.Atomic.M.M054.indexWeight; have := abs_nonneg (k : ℝ); linarith
  refine ⟨?_, ?_⟩
  · rw [hwv k]
    have := hv1 k
    nlinarith
  · rw [hwv, hwv, hve]
    unfold NlsGge.Atomic.M.M054.indexWeight
    push_cast
    rw [abs_neg]

theorem fourier_term_le (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair)
    (h : potentialCoefficientEnergy w φ ≠ ⊤) (plus : Bool) (k : ℤ) :
    w k * ‖fourierPotential φ plus k‖ ≤ NlsGge.ThirdConsultation.M.componentNorm w φ plus := by
  have hS := compEnergy_summable w φ plus (compEnergy_ne_top w φ h plus)
  have hle : w k ^ 2 * ‖fourierPotential φ plus k‖ ^ 2 ≤
      ∑' j : ℤ, w j ^ 2 * ‖fourierPotential φ plus j‖ ^ 2 :=
    hS.le_tsum k (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hc2 : NlsGge.ThirdConsultation.M.componentNorm w φ plus ^ 2 =
      ∑' j : ℤ, w j ^ 2 * ‖fourierPotential φ plus j‖ ^ 2 := by
    rw [componentNorm_eq, Real.sq_sqrt ENNReal.toReal_nonneg,
      compEnergy_toReal w φ plus (compEnergy_ne_top w φ h plus)]
  have hnn : 0 ≤ NlsGge.ThirdConsultation.M.componentNorm w φ plus := Real.sqrt_nonneg _
  have := abs_le_of_sq_le_sq' (a := w k * ‖fourierPotential φ plus k‖)
    (b := NlsGge.ThirdConsultation.M.componentNorm w φ plus) (by rw [hc2, mul_pow]; exact hle) hnn
  exact this.2

theorem offdiag_norm_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold : 8 * potentialCoefficientNorm w φ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n)
    (plus : Bool) :
    w (2 * n) * ‖offDiagonal φ n lam hlam plus‖ ≤
      2 * NlsGge.ThirdConsultation.M.componentNorm w φ plus := by
  have hb := NlsGge.ThirdConsultation.M.schur_offdiagonal_bound w hw φ hφ n lam hlam hthreshold plus
  set idx : ℤ := if plus then 2 * n else -2 * n with hidx
  have hwidx : w idx = w (2 * n) := by
    rw [hidx]
    split_ifs
    · rfl
    · have : (-2 * n : ℤ) = -(2 * n) := by ring
      rw [this]; exact (weight_facts w hw (2 * n)).2
  have hF := fourier_term_le w φ hφ plus idx
  rw [hwidx] at hF
  set comp := NlsGge.ThirdConsultation.M.componentNorm w φ plus with hcomp
  have hcomp0 : 0 ≤ comp := Real.sqrt_nonneg _
  set Q := potentialCoefficientNorm w φ with hQ
  have hρ : 0 < NlsGge.Atomic.M.M054.indexWeight n := by
    unfold NlsGge.Atomic.M.M054.indexWeight; have := abs_nonneg (n : ℝ); linarith
  have hsmall : 8 * Q ^ 2 * comp / NlsGge.Atomic.M.M054.indexWeight n ≤ comp := by
    rw [div_le_iff₀ hρ]; nlinarith
  have hw0 : 0 ≤ w (2 * n) := by
    have h1 := (weight_facts w hw (2 * n)).1
    have h2 : 0 < NlsGge.Atomic.M.M054.indexWeight (2 * n) := by
      unfold NlsGge.Atomic.M.M054.indexWeight; have := abs_nonneg ((2 * n : ℤ) : ℝ); linarith
    linarith
  have hsplit : ‖offDiagonal φ n lam hlam plus‖ ≤
      ‖offDiagonal φ n lam hlam plus - fourierPotential φ plus idx‖ +
        ‖fourierPotential φ plus idx‖ := by
    have := norm_add_le (offDiagonal φ n lam hlam plus - fourierPotential φ plus idx)
      (fourierPotential φ plus idx)
    rwa [sub_add_cancel] at this
  calc w (2 * n) * ‖offDiagonal φ n lam hlam plus‖
      ≤ w (2 * n) * (‖offDiagonal φ n lam hlam plus - fourierPotential φ plus idx‖ +
        ‖fourierPotential φ plus idx‖) := mul_le_mul_of_nonneg_left hsplit hw0
    _ = w (2 * n) * ‖offDiagonal φ n lam hlam plus - fourierPotential φ plus idx‖ +
        w (2 * n) * ‖fourierPotential φ plus idx‖ := by ring
    _ ≤ 2 * comp := by linarith

theorem prod_aux (W ρ2 Q cp cm x y : ℝ) (hρ2 : 0 < ρ2) (hW : ρ2 ≤ W) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hcp : 0 ≤ cp) (hcm : 0 ≤ cm) (h1 : W * x ≤ 2 * cp) (h2 : W * y ≤ 2 * cm)
    (hsq : Q ^ 2 = cp ^ 2 + cm ^ 2) : x * y ≤ (Real.sqrt 2 * Q / ρ2) ^ 2 := by
  have hW0 : 0 ≤ W := le_trans hρ2.le hW
  have h1' : 0 ≤ W * x := mul_nonneg hW0 hx
  have h2' : 0 ≤ W * y := mul_nonneg hW0 hy
  have hprod : (W * x) * (W * y) ≤ (2 * cp) * (2 * cm) := mul_le_mul h1 h2 h2' (by linarith)
  have h4 : (2 * cp) * (2 * cm) ≤ 2 * Q ^ 2 := by rw [hsq]; nlinarith [sq_nonneg (cp - cm)]
  have hB2 : (Real.sqrt 2 * Q / ρ2) ^ 2 = 2 * Q ^ 2 / ρ2 ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  rw [hB2, le_div_iff₀ (by positivity)]
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have hρW : ρ2 ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ hρ2.le hW 2
  calc x * y * ρ2 ^ 2 ≤ x * y * W ^ 2 := mul_le_mul_of_nonneg_left hρW hxy
    _ = (W * x) * (W * y) := by ring
    _ ≤ 2 * Q ^ 2 := hprod.trans h4

theorem offdiag_prod_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (z : ℂ) (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold : 8 * potentialCoefficientNorm w φ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    ‖offDiagonal φ n z hz true * offDiagonal φ n z hz false‖ ≤
      (Real.sqrt 2 * potentialCoefficientNorm w φ /
        NlsGge.Atomic.M.M054.indexWeight (2 * n)) ^ 2 := by
  have h1 := offdiag_norm_le w hw φ hφ n z hz hthreshold true
  have h2 := offdiag_norm_le w hw φ hφ n z hz hthreshold false
  have hsq := NlsGge.ThirdConsultation.MTwoModeB.potentialNorm_sq w φ hφ
  have hρ2pos : 0 < NlsGge.Atomic.M.M054.indexWeight (2 * n) := by
    unfold NlsGge.Atomic.M.M054.indexWeight
    have := abs_nonneg ((2 * n : ℤ) : ℝ); linarith
  rw [norm_mul]
  exact prod_aux (w (2 * n)) (NlsGge.Atomic.M.M054.indexWeight (2 * n)) (potentialCoefficientNorm w φ)
    _ _ _ _ hρ2pos (weight_facts w hw (2 * n)).1 (norm_nonneg _) (norm_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) h1 h2 hsq

end NlsGge.ThirdConsultation.M029R

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem schur_has_two_roots_core
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight n) :
    ∃ D g : ℂ → ℂ, ∃ xiMinus xiPlus : ℂ,
      AnalyticOnNhd ℂ D (NlsGge.Atomic.KST004.spectralStrip n) ∧
      AnalyticOnNhd ℂ g (NlsGge.Atomic.KST004.spectralStrip n) ∧
      xiMinus ∈ MTwoMode.localSpectralDisc w φ n ∧
      xiPlus ∈ MTwoMode.localSpectralDisc w φ n ∧
      (∀ z : ℂ, ∀ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n,
        D z = MTwoMode.schurDet φ n z hz ∧
        g z ≠ 0 ∧ D z = (z - xiMinus) * (z - xiPlus) * g z) ∧
      (∀ z : ℂ, ∀ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n,
        (MTwoMode.schurDet φ n z hz = 0 ↔ z = xiMinus ∨ z = xiPlus)) := by
  classical
  obtain ⟨ap, hap, hapeq⟩ := schur_diagonal_analytic_extension w hw φ hφ n hthreshold true
  obtain ⟨am, ham, hameq⟩ := schur_diagonal_analytic_extension w hw φ hφ n hthreshold false
  obtain ⟨bp, hbp, hbpeq⟩ := schur_off_diagonal_analytic_extension w hw φ hφ n hthreshold true
  obtain ⟨bm, hbm, hbmeq⟩ := schur_off_diagonal_analytic_extension w hw φ hφ n hthreshold false
  set Q := MTwoMode.potentialCoefficientNorm w φ with hQdef
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  set ρ := NlsGge.Atomic.M.M054.indexWeight n with hρdef
  set ρ2 := NlsGge.Atomic.M.M054.indexWeight (2 * n) with hρ2def
  have hρpos : 0 < ρ := by
    rw [hρdef]; unfold NlsGge.Atomic.M.M054.indexWeight; have := abs_nonneg (n : ℝ); linarith
  have hρ2pos : 0 < ρ2 := by
    rw [hρ2def]; unfold NlsGge.Atomic.M.M054.indexWeight
    have := abs_nonneg ((2 * n : ℤ) : ℝ); linarith
  set c : ℂ := (n : ℂ) * (Real.pi : ℂ) with hc
  set S := NlsGge.Atomic.KST004.spectralStrip n with hS
  set A : ℝ := Q ^ 2 / ρ with hA
  set B : ℝ := Real.sqrt 2 * Q / ρ2 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hAB : A + B < Real.pi / 5 :=
    NlsGge.ThirdConsultation.M.disc_radius_lt Q hQ0 n hthreshold
  have hpi : 0 < Real.pi / 5 := by positivity
  -- the determinant function
  let D : ℂ → ℂ := fun z => (z - c - ap z) * (z - c - am z) - bp z * bm z
  have hDan : AnalyticOnNhd ℂ D S := fun z hz =>
    (((analyticAt_id.sub analyticAt_const).sub (hap z hz)).mul
      ((analyticAt_id.sub analyticAt_const).sub (ham z hz))).sub ((hbp z hz).mul (hbm z hz))
  have hDdet : ∀ z (hz : z ∈ S), D z = MTwoMode.schurDet φ n z hz := by
    intro z hz
    have e1 := hapeq z hz
    have e2 := hameq z hz
    have e3 := hbpeq z hz
    have e4 := hbmeq z hz
    simp only [if_true, Bool.false_eq_true, if_false] at e1 e2
    unfold MTwoMode.schurDet MTwoMode.schurMatrix
    rw [Matrix.det_fin_two_of]
    simp only [D, e1, e2, e3, e4]
    ring
  -- bounds on the strip
  have hAp : ∀ z (hz : z ∈ S), ‖ap z‖ ≤ A := by
    intro z hz
    have := schur_diagonal_bound w hw φ hφ n z hz hthreshold true
    rw [hapeq z hz]; simpa using this
  have hAm : ∀ z (hz : z ∈ S), ‖am z‖ ≤ A := by
    intro z hz
    have := schur_diagonal_bound w hw φ hφ n z hz hthreshold false
    rw [hameq z hz]; simpa using this
  have hBb : ∀ z (hz : z ∈ S), ‖bp z * bm z‖ ≤ B ^ 2 := by
    intro z hz
    rw [hbpeq z hz, hbmeq z hz]
    exact NlsGge.ThirdConsultation.M029R.offdiag_prod_le w hw φ hφ n z hz hthreshold
  -- zero-freeness off the small disc
  have hrootD : ∀ z (hz : z ∈ S), A + B < ‖z - c‖ → D z ≠ 0 := fun z hz hlt =>
    NlsGge.ThirdConsultation.M029R.root_loc hB0 (hAp z hz) (hAm z hz) (hBb z hz) hlt
  -- the disc inside the strip
  obtain ⟨-, hstrip⟩ := NlsGge.ThirdConsultation.M.local_spectral_disc_in_strip w hw φ hφ n hthreshold
  have hcb : Metric.closedBall c (Real.pi / 5) ⊆ S := hstrip
  -- Rouche count
  have hcard : Multiset.card (NlsGge.GK38.Lib.zeroMultiset D (Metric.ball c (Real.pi / 5))) = 2 := by
    refine NlsGge.ThirdConsultation.M029C.card_two hpi (a1 := ap) (a2 := am) (b := fun z => bp z * bm z)
      (hap.mono hcb) (ham.mono hcb) (fun z hz => (hbp z (hcb hz)).mul (hbm z (hcb hz))) ?_
    intro t ht0 ht1 z hz
    have hzS : z ∈ S := hcb (Metric.sphere_subset_closedBall hz)
    have hzn : ‖z - c‖ = Real.pi / 5 := by rw [← dist_eq_norm]; exact Metric.mem_sphere.1 hz
    refine NlsGge.ThirdConsultation.M029R.root_loc hB0 ?_ ?_ ?_ (by rw [hzn]; exact hAB)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      nlinarith [hAp z hzS, norm_nonneg (ap z)]
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      nlinarith [hAm z hzS, norm_nonneg (am z)]
    · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0]
      have := hBb z hzS
      have hb0 : 0 ≤ ‖bp z * bm z‖ := norm_nonneg _
      nlinarith [pow_le_one₀ ht0 ht1 (n := 2)]
  obtain ⟨ξ1, ξ2, hM⟩ := Multiset.card_eq_two.1 hcard
  have hfc : AnalyticOnNhd ℂ D (Metric.closedBall c (Real.pi / 5)) := hDan.mono hcb
  have hmemball : ∀ ξ ∈ NlsGge.GK38.Lib.zeroMultiset D (Metric.ball c (Real.pi / 5)),
      ξ ∈ Metric.ball c (Real.pi / 5) := fun ξ hξ =>
    ((NlsGge.GK38.Lib.mem_zeroMultiset_ball hfc).1 hξ).1
  have hξ1 : ξ1 ∈ Metric.ball c (Real.pi / 5) := hmemball ξ1 (by rw [hM]; simp)
  have hξ2 : ξ2 ∈ Metric.ball c (Real.pi / 5) := hmemball ξ2 (by rw [hM]; simp)
  obtain ⟨g, hgan, hgne, hfac⟩ := NlsGge.ThirdConsultation.M029C.factor_two hpi hDan hcb
    (fun z hz hzb => hrootD z hz (by
      have : Real.pi / 5 ≤ ‖z - c‖ := by
        rw [← dist_eq_norm]; exact not_lt.1 (fun h => hzb (Metric.mem_ball.2 h))
      linarith)) ξ1 ξ2 hM
  have hlocal : ∀ ξ ∈ Metric.ball c (Real.pi / 5), D ξ = 0 → ξ ∈ MTwoMode.localSpectralDisc w φ n := by
    intro ξ hξ hD0
    have hξS : ξ ∈ S := hcb (Metric.ball_subset_closedBall hξ)
    unfold MTwoMode.localSpectralDisc
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra hnot
    exact hrootD ξ hξS (not_le.1 hnot) hD0
  have hD1 : D ξ1 = 0 := by rw [hfac ξ1]; simp
  have hD2 : D ξ2 = 0 := by rw [hfac ξ2]; simp
  refine ⟨D, g, ξ1, ξ2, hDan, hgan, hlocal ξ1 hξ1 hD1, hlocal ξ2 hξ2 hD2, ?_, ?_⟩
  · intro z hz
    exact ⟨hDdet z hz, hgne z hz, hfac z⟩
  · intro z hz
    rw [← hDdet z hz, hfac z]
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (sub_eq_zero.1 h)
      · exact absurd h (hgne z hz)
    · rintro (h | h) <;> simp [h]

end NlsGge.ThirdConsultation.M

end
