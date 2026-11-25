import Mathlib
import NlsGge.Atomic.S.S042
import NlsGge.Atomic.S.S045
import NlsGge.Schur.ActualSchurBallIntegral38V1

                                                                                                          
                                                                         
                                                                                                              
                                                                                                                  
                                                                           
                                                                                                                   
                                                                                                              
                                                                                                      
                                                                                                                
                                                                                                                
                                                                                                                 
                                                                                                        
                                                                                                             
                                                                                
set_option autoImplicit false
noncomputable section
open MeasureTheory
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur NlsGge.Measure NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.S

theorem schurBall_integral_product_bound (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (c : BoundedCoefficients lo up)
      (R : ℝ), 1 ≤ R → ∀ (M N : ℕ), A * R ^ 6 ≤ (M : ℝ) →
      relativeBallIntegralV6 c N R ≤
        2 * (∏ n ∈ normalizerLow M N, R ^ 2 * fullWeightRate c.val n) *
          ∏ n ∈ normalizerHigh M N, (rhoAt C R n)⁻¹ := by
  obtain ⟨C, A₂, hC, hA₂, h42⟩ := fullEnergy_ge_highSchur lo up hl hlu
  set Aj := actualSchurJacobianMConstant38 with hAj
  have hAj1 : 1 ≤ Aj := actualSchurJacobianMConstant38_ge_one
  set T := actualSchurCenterThresholdConstant38 with hT
  refine ⟨C, A₂ + Aj + 64 * |T| + 1, hC, by positivity, ?_⟩
  intro c R hR M N hM
  obtain ⟨-, -, hb, hu⟩ := boundedCoefficients_bounds38 c
  have hR0 : 0 < R := by linarith
  have hR6 : 0 ≤ R ^ 6 := by positivity
  have hR36 : R ^ 3 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  have hapos : ∀ n : ℤ, 0 < fullWeightRate c.val n :=
    fun n => fullWeightRate_pos lo up c.val hl hb hu n
  have hrpos : ∀ n : ℤ, 0 < rhoAt C R n := fun n => Real.exp_pos _
  have hrho1 : ∀ n : ℤ, rhoAt C R n ≤ 1 := by
    intro n
    unfold rhoAt
    rw [Real.exp_le_one_iff, neg_mul]
    exact neg_nonpos.mpr (mul_nonneg hC.le (by positivity))
  have hF : 0 < freeNormalizer38 c N := by
    unfold freeNormalizer38
    exact Finset.prod_pos fun i _ => div_pos Real.pi_pos (hapos _)
  -- signed modes are the image of the Fin enumeration
  have himg : (Finset.univ : Finset (Fin (2 * N + 1))).image (modeIndex N) = normalizerModes N := by
    ext n
    unfold normalizerModes
    constructor
    · rintro hn
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Icc.mpr (modeIndex_bounds N i)
    · intro hn
      rw [Finset.mem_Icc] at hn
      obtain ⟨i, hi⟩ := modeIndex_covers N n hn.1 hn.2
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hre : ∀ (p : ℤ → Prop) [DecidablePred p] (f : ℤ → ℝ),
      ∏ n ∈ (normalizerModes N).filter p, f n =
        ∏ i ∈ Finset.univ.filter (fun i => p (modeIndex N i)), f (modeIndex N i) := by
    intro p _ f
    rw [← himg, Finset.filter_image,
      Finset.prod_image (fun i _ j _ h => modeIndex_injective N h)]
  have hlowF : ∀ f : ℤ → ℝ, ∏ n ∈ normalizerLow M N, f n =
      ∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)), f (modeIndex N i) := by
    intro f
    unfold normalizerLow
    rw [hre]
    exact Finset.prod_congr (Finset.filter_congr fun i _ => natAbs_le_iff_abs_le38 _ _)
      (fun _ _ => rfl)
  have hhighF : ∀ f : ℤ → ℝ, ∏ n ∈ normalizerHigh M N, f n =
      ∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|), f (modeIndex N i) := by
    intro f
    unfold normalizerHigh
    rw [hre]
    refine Finset.prod_congr (Finset.filter_congr fun i _ => ?_) (fun _ _ => rfl)
    rw [← not_le, ← not_le, natAbs_le_iff_abs_le38]
  have hlow0 : 0 ≤ ∏ n ∈ normalizerLow M N, R ^ 2 * fullWeightRate c.val n :=
    Finset.prod_nonneg fun n _ => by have := hapos n; positivity
  by_cases hNM : N ≤ M
  · -- low cutoff: every mode is low
    have h45 := relativeBallIntegral_lowCutoff c M N hNM R hR0.le
    have hlowAll : normalizerLow M N = normalizerModes N := by
      unfold normalizerLow
      refine Finset.filter_true_of_mem fun n hn => ?_
      have := Finset.mem_Icc.mp hn
      omega
    have hhighE : normalizerHigh M N = ∅ := by
      unfold normalizerHigh
      refine Finset.filter_false_of_mem fun n hn => ?_
      have := Finset.mem_Icc.mp hn
      omega
    rw [hhighE, Finset.prod_empty, mul_one, hlowAll]
    rw [hlowAll] at hlow0
    linarith
  · have hNM : M < N := Nat.lt_of_not_le hNM
    have hthr : ∀ X : ℝ, ∀ k : ℕ, R ^ k ≤ R ^ 6 → |X| ≤ A₂ + Aj + 64 * |T| + 1 →
        X * R ^ k ≤ (M : ℝ) := by
      intro X k hk hX
      have hk0 : (0 : ℝ) ≤ R ^ k := by positivity
      calc X * R ^ k ≤ |X| * R ^ k := mul_le_mul_of_nonneg_right (le_abs_self X) hk0
        _ ≤ (A₂ + Aj + 64 * |T| + 1) * R ^ 6 := mul_le_mul hX hk hk0 (by positivity)
        _ ≤ (M : ℝ) := hM
    have hM42 : A₂ * R ^ 6 ≤ (M : ℝ) :=
      hthr A₂ 6 le_rfl (by rw [abs_of_pos hA₂]; linarith [abs_nonneg T])
    have hAjM : Aj * R ^ 6 ≤ (M : ℝ) :=
      hthr Aj 6 le_rfl (by rw [abs_of_pos (by linarith : (0 : ℝ) < Aj)]; linarith [abs_nonneg T])
    have hK4 : T * (4 * R) ^ 3 ≤ (M : ℝ) := by
      have h := hthr (64 * T) 3 hR36 (by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 64)]; linarith)
      calc T * (4 * R) ^ 3 = 64 * T * R ^ 3 := by ring
        _ ≤ (M : ℝ) := h
    set B := {z : FourierPlane N | planeH1Norm38 N z < R} with hB
    have hBm : MeasurableSet B := (isOpen_planeH1Ball38 N R).measurableSet
    set a : Fin (2 * N + 1) → ℝ := fun i => fullWeightRate c.val (modeIndex N i) with ha
    set ρ : Fin (2 * N + 1) → ℝ := fun i => rhoAt C R (modeIndex N i) with hρ
    have hapos' : ∀ i, 0 < a i := fun i => hapos _
    have hρpos : ∀ i, 0 < ρ i := fun i => hrpos _
    have hρ1 : ∀ i, ρ i ≤ 1 := fun i => hrho1 _
    have hlowΨ : ∀ z ∈ B, ∀ i, |modeIndex N i| ≤ (M : ℤ) →
        actualSchurBallMap38 N M z i = z i ∧ ‖z i‖ < R := by
      intro z hz i hi
      exact ⟨actualSchurBallMap38_low N M z i ((natAbs_le_iff_abs_le38 _ _).mpr hi),
        lt_of_le_of_lt (plane_coord_le_H1Norm38 N z i) hz⟩
    have hE : ∀ z ∈ B, ∑ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|),
        ρ i * a i * ‖actualSchurBallMap38 N M z i‖ ^ 2 ≤ fullEnergy38 c N z := by
      intro z hz
      refine le_trans (le_of_eq ?_) (h42 c R hR M N hM42 z hz)
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : (modeIndex N i).natAbs ≤ M
      · have hi' : ¬ (M : ℤ) < |modeIndex N i| :=
          not_lt.mpr ((natAbs_le_iff_abs_le38 _ _).mp hi)
        rw [if_neg hi', if_pos hi]
      · have hi' : (M : ℤ) < |modeIndex N i| :=
          not_le.mp fun h => hi ((natAbs_le_iff_abs_le38 _ _).mpr h)
        rw [if_pos hi', if_neg hi, actualSchurBallMap38_high N M z i hi]
        rfl
    have hcv := ballChangeOfVariables38 N M hNM.le B hBm (actualSchurBallMap38 N M)
      (fun z => fderiv ℝ (actualSchurBallMap38 N M) z) a ρ hapos' hρpos hρ1
      (fun z => fullEnergy38 c N z) (continuous_fullEnergy38 c N).measurable
      (fun z => fullEnergy38_nonneg c N z) R hR0
      (actualSchurBallMap38_injOn N M R hR hAjM hK4)
      (fun z hz => actualSchurBallMap38_hasFDerivWithinAt N M R hR hK4 z hz)
      (fun z hz => actualSchurBallMap38_abs_det_ge N M R hR hAjM hK4 z hz)
      hlowΨ hE
    set X : ℝ := (∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)), Real.pi * R ^ 2) *
      ∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|), Real.pi / (ρ i * a i) with hX
    have hX0 : 0 ≤ X := mul_nonneg (Finset.prod_nonneg fun i _ => by positivity)
      (Finset.prod_nonneg fun i _ => by have := hapos' i; have := hρpos i; positivity)
    have hcv' : ∫⁻ z in B, ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂planeVolume N ≤
        ENNReal.ofReal (2 * X) := by
      refine hcv.trans_eq ?_
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
        ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by
          have := hapos' i; have := hρpos i; positivity),
        ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => by positivity),
        show (2 : ENNReal) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (by norm_num)]
    have hmeas : AEStronglyMeasurable (fun z => Real.exp (-fullEnergy38 c N z))
        ((planeVolume N).restrict B) :=
      ((continuous_fullEnergy38 c N).neg.rexp).aestronglyMeasurable
    have hnn : 0 ≤ᵐ[(planeVolume N).restrict B] (fun z => Real.exp (-fullEnergy38 c N z)) :=
      Filter.Eventually.of_forall fun z => (Real.exp_pos _).le
    have hI : ∫ z in B, Real.exp (-fullEnergy38 c N z) ∂planeVolume N ≤ 2 * X := by
      rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hcv'
    have hratio := ball_ratio_identity38 N M R a ρ hapos' hρpos
    unfold relativeBallIntegralV6
    rw [div_le_iff₀ hF]
    have hB' : schurH1Ball N R = B := rfl
    rw [hB']
    refine hI.trans (le_of_eq ?_)
    rw [hX, hratio, hlowF, hhighF]
    unfold freeNormalizer38
    ring

end NlsGge.ThirdConsultation.S
