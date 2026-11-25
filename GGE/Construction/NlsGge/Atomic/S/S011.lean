import Mathlib
import NlsGge.ThirdConsultation.S.S011Abstract
import NlsGge.ThirdConsultation.S.S006Host06
import NlsGge.Atomic.S.S010
import NlsGge.Schur.CoveredH1ParityPairPotentialNorm
import NlsGge.Schur.FreeResolventComplementaryDQTransportAfterCoordinateRange
import NlsGge.Schur.FreeResolventComplementaryQDTransportAfterCoordinateRange
import NlsGge.Schur.FreeResolventComplementarySquareBoundAfterQDTransport
import NlsGge.Schur.FreeResolventComplexHilbertSchmidtOpNormAfterL2Prerequisites
import NlsGge.Schur.FreeResolventDVDHilbertSchmidtFromEnergyAlias
import NlsGge.Schur.ResonantParityPairBasisAction

                                                                                                     
                                                                                               
                                                                                 
                                                  
                                                                                               
                                                                                               
                                                                                            
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

/-! ### Concrete norm and identity helpers (on the actual free-resolvent blocks) -/

theorem companion_freeResolventParityPair_norm_le_one (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖freeResolventParityPair n z hz‖ ≤ 1 := by
  let E := parityPairRepr n
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖E.symm (freeResolventSquare n z hz (E x))‖ ≤ 1 * ‖x‖
  calc
    ‖E.symm (freeResolventSquare n z hz (E x))‖ =
        ‖freeResolventSquare n z hz (E x)‖ := E.symm.norm_map _
    _ ≤ ‖freeResolventSquare n z hz‖ * ‖E x‖ :=
      (freeResolventSquare n z hz).le_opNorm _
    _ ≤ 1 * ‖x‖ := by
      rw [E.norm_map]
      gcongr
      exact freeResolventSquare_norm_le_one n z hz

theorem s011c_D_norm_le_one (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖schurD n z hz‖ ≤ 1 :=
  companion_freeResolventParityPair_norm_le_one n z hz

theorem s011c_X_norm (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (R : ℝ) (hR0 : 0 ≤ R)
    (h1 : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R) (h2 : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz‖ ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
  have hn0 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  have hK0 := uniformConvolutionConstant_nonneg
  have hc2 : 2 * Real.sqrt uniformConvolutionConstant ≤ freeResolventSchurUniformConstant :=
    le_max_right _ _
  have hHS := freeResolventPotentialFreeResolvent_isComplexHilbertSchmidt_from_matrix_energy
    u₁ u₂ hu₁ hu₂ n z hz
  have hsq : ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 + ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2 ≤ 2 * R ^ 2 := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, pow_le_pow_left₀ (norm_nonneg _) h2 2]
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hden : (n : ℝ) ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by linarith
  have hin : 2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) *
      (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 + ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) ≤
      (2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)|) ^ 2 := by
    have e : (2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)|) ^ 2 =
        4 * uniformConvolutionConstant * R ^ 2 / (n : ℝ) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hK0, sq_abs]; ring
    rw [e]
    calc 2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) *
          (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 + ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2)
        ≤ 2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) * (2 * R ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 2 * uniformConvolutionConstant / (n : ℝ) ^ 2 * (2 * R ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_left (by positivity) hn2 hden
      _ = 4 * uniformConvolutionConstant * R ^ 2 / (n : ℝ) ^ 2 := by ring
  have hmid : complexHilbertSchmidtNorm (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz) ≤
      2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)| := by
    refine hHS.2.trans ?_
    refine (Real.sqrt_le_sqrt hin).trans ?_
    rw [Real.sqrt_sq (by positivity)]
  refine (complexHilbertSchmidt_opNorm_le _ hHS.1).trans (hmid.trans ?_)
  apply div_le_div_of_nonneg_right _ hn0.le
  exact mul_le_mul_of_nonneg_right hc2 hR0

theorem s011c_X_eq (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz =
      schurD n z hz * (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n * schurD n z hz) := by
  ext x
  rfl

theorem s011c_A_eq (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    interaction n z hz u₁ u₂ hu₁ hu₂ =
      schurD n z hz * (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n *
        freeResolventComplementaryProjectionTransported n) := by
  ext x
  rfl

theorem s011c_B_eq (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    oppositeInteraction n z hz u₁ u₂ hu₁ hu₂ =
      freeResolventComplementaryProjectionTransported n *
        (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n * schurD n z hz) := by
  ext x
  rfl

theorem s011c_QD (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    freeResolventComplementaryProjectionTransported n * schurD n z hz = schurD n z hz :=
  freeResolventComplementaryProjectionTransported_comp_freeResolventParityPair n z hz

theorem s011c_DQ (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    schurD n z hz * freeResolventComplementaryProjectionTransported n = schurD n z hz :=
  freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n z hz

theorem s011c_Q_norm_le_one (n : ℤ) :
    ‖freeResolventComplementaryProjectionTransported n‖ ≤ 1 :=
  freeResolventComplementaryProjectionTransported_norm_le_one n

theorem s011c_parityPair_nontrivial (n : ℤ) : Nontrivial (ParityPair n) := by
  letI : Nonempty (Bool × Sector n) := ⟨(true, resonantIndex n)⟩
  letI : Nontrivial (SectorSquare n) := nontrivial_of_ne
    (lp.single 2 (true, resonantIndex n) (1 : ℂ)) 0 (by
      intro hz0
      have hval := congrArg (fun f : SectorSquare n => f (true, resonantIndex n)) hz0
      simpa using hval)
  exact (parityPairRepr n).toEquiv.nontrivial_congr.mpr inferInstance

/-! ### Real constants and scalar estimates -/

theorem s011c_const_facts :
    0 ≤ physicalH1MultiplierConstant ∧ 0 ≤ freeResolventSchurUniformConstant ∧
      2 * physicalH1MultiplierConstant ≤ complementaryInteractionConstant ∧
      4 * physicalH1MultiplierConstant * freeResolventSchurUniformConstant ≤
        complementaryInteractionConstant ∧
      0 ≤ complementaryInteractionConstant := by
  have hm : 0 ≤ physicalH1MultiplierConstant := physicalH1MultiplierConstant_pos.le
  have hc2 : 2 * Real.sqrt uniformConvolutionConstant ≤ freeResolventSchurUniformConstant :=
    le_max_right _ _
  have hc : 0 ≤ freeResolventSchurUniformConstant := le_trans (by positivity) hc2
  have hmc : 0 ≤ freeResolventSchurUniformConstant * physicalH1MultiplierConstant :=
    mul_nonneg hc hm
  unfold complementaryInteractionConstant
  refine ⟨hm, hc, ?_, ?_, ?_⟩ <;> nlinarith [hmc, hm, hc]

theorem s011c_BB_numeric (m c C R N : ℝ) (hC4 : 4 * m * c ≤ C) (hN : 0 < N)
    (hl : C * R ^ 2 ≤ N) :
    2 * m * R * (c * R / N) ≤ 1 / 2 := by
  have h1 : 4 * m * c * R ^ 2 ≤ N :=
    le_trans (mul_le_mul_of_nonneg_right hC4 (sq_nonneg R)) hl
  have e : 2 * m * R * (c * R / N) = (2 * m * c * R ^ 2) / N := by ring
  rw [e, div_le_iff₀ hN]
  linarith

/-! ### Generic algebra over a complete normed space E -/

theorem s011c_unit_facts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (hA : ‖A ^ 2‖ < 1) :
    IsUnit (1 - A) ∧ Ring.inverse (1 - A) * (1 - A) = 1 ∧
      (1 - A) * Ring.inverse (1 - A) = 1 ∧
      Ring.inverse (1 - A) = (1 + A) * Ring.inverse (1 - A ^ 2) := by
  obtain ⟨_, h1, hl, hr, heq, _⟩ := inverse_one_sub_of_square_small_twoSided A hA
  exact ⟨h1, hl, hr, heq⟩

theorem s011c_intertwine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D V Q : E →L[ℂ] E) (hQD : Q * D = D) (hDQ : D * Q = D) :
    (1 - D * (V * Q)) * D = D * (1 - Q * (V * D)) := by
  calc (1 - D * (V * Q)) * D = D - D * (V * (Q * D)) := by
        simp only [sub_mul, one_mul, mul_assoc]
    _ = D - D * (V * D) := by rw [hQD]
    _ = D - D * (Q * (V * D)) := by rw [← mul_assoc D Q, hDQ]
    _ = D * (1 - Q * (V * D)) := by rw [mul_sub, mul_one]

theorem s011c_intertwine_concrete (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) :
    (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * schurD n z hz =
      schurD n z hz * (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) := by
  rw [s011c_A_eq u₁ u₂ hu₁ hu₂ n z hz, s011c_B_eq u₁ u₂ hu₁ hu₂ n z hz]
  exact s011c_intertwine _ _ _ (s011c_QD n z hz) (s011c_DQ n z hz)

theorem s011c_Rn_identities {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B D Q S T : E →L[ℂ] E)
    (hSl : S * (1 - A) = 1) (hSr : (1 - A) * S = 1)
    (hTr : (1 - B) * T = 1)
    (hint : (1 - A) * D = D * (1 - B))
    (hQD : Q * D = D) (hDQ : D * Q = D) :
    S * D = D * T ∧ (1 - A) * (S * D) = D ∧ (S * D) * (1 - B) = D ∧
      Q * (S * D) = S * D ∧ (S * D) * Q = S * D := by
  have hDT : D * T = S * D := by
    calc D * T = (S * (1 - A)) * (D * T) := by rw [hSl, one_mul]
      _ = S * (((1 - A) * D) * T) := by simp only [mul_assoc]
      _ = S * ((D * (1 - B)) * T) := by rw [hint]
      _ = S * (D * ((1 - B) * T)) := by simp only [mul_assoc]
      _ = S * D := by rw [hTr, mul_one]
  have h11 : (1 - A) * (S * D) = D := by rw [← mul_assoc, hSr, one_mul]
  have h12 : (S * D) * (1 - B) = D := by
    calc (S * D) * (1 - B) = S * (D * (1 - B)) := by rw [mul_assoc]
      _ = S * ((1 - A) * D) := by rw [hint]
      _ = (S * (1 - A)) * D := by rw [mul_assoc]
      _ = D := by rw [hSl, one_mul]
  have h13 : Q * (S * D) = S * D := by
    rw [← hDT, ← mul_assoc, hQD]
  have h14 : (S * D) * Q = S * D := by
    rw [mul_assoc, hDQ]
  exact ⟨hDT.symm, h11, h12, h13, h14⟩

theorem s011c_BB_alg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q V D : E →L[ℂ] E) (hDQ : D * Q = D) :
    (Q * (V * D)) * (Q * (V * D)) = Q * (V * (D * (V * D))) := by
  calc (Q * (V * D)) * (Q * (V * D)) = Q * (V * ((D * Q) * (V * D))) := by
        simp only [mul_assoc]
    _ = Q * (V * (D * (V * D))) := by rw [hDQ]

theorem s011c_norm_triple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q V Y : E →L[ℂ] E) (v y : ℝ) (hQ : ‖Q‖ ≤ 1) (hV : ‖V‖ ≤ v) (hY : ‖Y‖ ≤ y)
    (hv : 0 ≤ v) : ‖Q * (V * Y)‖ ≤ v * y := by
  calc ‖Q * (V * Y)‖ ≤ ‖Q‖ * ‖V * Y‖ := norm_mul_le _ _
    _ ≤ 1 * (v * y) :=
        mul_le_mul hQ ((norm_mul_le _ _).trans (mul_le_mul hV hY (norm_nonneg _) hv))
          (norm_nonneg _) zero_le_one
    _ = v * y := one_mul _

theorem s011c_norm_Rn_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S D : E →L[ℂ] E) (C R : ℝ) (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hS : ‖S‖ ≤ 2 * (1 + C * R)) (hD : ‖D‖ ≤ 1) :
    ‖S * D‖ ≤ 2 * (1 + C) * R := by
  have hCR : 0 ≤ C * R := mul_nonneg hC (zero_le_one.trans hR)
  calc ‖S * D‖ ≤ ‖S‖ * ‖D‖ := norm_mul_le _ _
    _ ≤ (2 * (1 + C * R)) * 1 := mul_le_mul hS hD (norm_nonneg _) (by linarith)
    _ ≤ 2 * (1 + C) * R := by linarith

/-! ### Concrete A-side and B-side estimates on the threshold -/

theorem s011c_A_side (R : ℝ) (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (hpair : schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : complementaryInteractionConstant * R ^ 2 ≤ |(n : ℝ)|) :
    ‖interaction n z hz u₁ u₂ hu₁ hu₂‖ ≤ complementaryInteractionConstant * R ∧
      ‖interaction n z hz u₁ u₂ hu₁ hu₂ * interaction n z hz u₁ u₂ hu₁ hu₂‖ ≤ 1 / 2 := by
  have hpair' : ‖(physicalSobolevL2 1 u₁ hu₁, physicalSobolevL2 1 u₂ hu₂)‖ ≤ R := hpair
  have h1 : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := (norm_fst_le _).trans hpair'
  have h2 : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := (norm_snd_le _).trans hpair'
  obtain ⟨_, hS010⟩ := complementaryInteraction_square_small
  have key := hS010 R u₁ u₂ hu₁ hu₂ h1 h2 n hn z hz
  exact ⟨key.1, key.2.2 hlarge⟩

theorem s011c_B_side (R : ℝ) (hR : 1 ≤ R) (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (hpair : schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : complementaryInteractionConstant * R ^ 2 ≤ |(n : ℝ)|) :
    ‖oppositeInteraction n z hz u₁ u₂ hu₁ hu₂‖ ≤ complementaryInteractionConstant * R ∧
      ‖oppositeInteraction n z hz u₁ u₂ hu₁ hu₂ * oppositeInteraction n z hz u₁ u₂ hu₁ hu₂‖ ≤
        1 / 2 := by
  have hpair' : ‖(physicalSobolevL2 1 u₁ hu₁, physicalSobolevL2 1 u₂ hu₂)‖ ≤ R := hpair
  have h1 : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := (norm_fst_le _).trans hpair'
  have h2 : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := (norm_snd_le _).trans hpair'
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hn0 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  obtain ⟨hm, _, hC2, hC4, _⟩ := s011c_const_facts
  have hQ := s011c_Q_norm_le_one n
  have hV := coveredH1ParityPairPotential_norm_bound u₁ u₂ hu₁ hu₂ n R hR0 h1 h2
  have hX := s011c_X_norm u₁ u₂ hu₁ hu₂ R hR0 h1 h2 n hn z hz
  have hD := s011c_D_norm_le_one n z hz
  have hv : 0 ≤ 2 * physicalH1MultiplierConstant * R :=
    mul_nonneg (mul_nonneg (by norm_num) hm) hR0
  have hBeq := s011c_B_eq u₁ u₂ hu₁ hu₂ n z hz
  have hXeq := s011c_X_eq u₁ u₂ hu₁ hu₂ n z hz
  have hDQ := s011c_DQ n z hz
  have hBn : ‖oppositeInteraction n z hz u₁ u₂ hu₁ hu₂‖ ≤ complementaryInteractionConstant * R := by
    rw [hBeq]
    refine (s011c_norm_triple _ _ _ _ _ hQ hV hD hv).trans ?_
    rw [mul_one]
    exact mul_le_mul_of_nonneg_right hC2 hR0
  have hBB : oppositeInteraction n z hz u₁ u₂ hu₁ hu₂ * oppositeInteraction n z hz u₁ u₂ hu₁ hu₂ =
      freeResolventComplementaryProjectionTransported n *
        (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n *
          freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz) := by
    rw [hBeq, hXeq]
    exact s011c_BB_alg _ _ _ hDQ
  have hBBn : ‖oppositeInteraction n z hz u₁ u₂ hu₁ hu₂ * oppositeInteraction n z hz u₁ u₂ hu₁ hu₂‖ ≤
      1 / 2 := by
    rw [hBB]
    refine (s011c_norm_triple _ _ _ _ _ hQ hV hX hv).trans ?_
    exact s011c_BB_numeric _ _ _ _ _ hC4 hn0 hlarge
  exact ⟨hBn, hBBn⟩

/-! ### Concrete parts of the companion (explicit statements; each is its own declaration) -/

theorem s011c_A_inv (R : ℝ) (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (hpair : schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : complementaryInteractionConstant * R ^ 2 ≤ |(n : ℝ)|) :
    IsUnit (1 - interaction n z hz u₁ u₂ hu₁ hu₂) ∧
      Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * (1 - interaction n z hz u₁ u₂ hu₁ hu₂) = 1 ∧
      (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) = 1 ∧
      Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) =
        (1 + interaction n z hz u₁ u₂ hu₁ hu₂) *
          Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂ ^ 2) := by
  have hA := s011c_A_side R u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  have hA2 : ‖interaction n z hz u₁ u₂ hu₁ hu₂ ^ 2‖ < 1 := by
    rw [pow_two]; exact lt_of_le_of_lt hA.2 (by norm_num)
  exact s011c_unit_facts _ hA2

theorem s011c_B_inv (R : ℝ) (hR : 1 ≤ R) (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (hpair : schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : complementaryInteractionConstant * R ^ 2 ≤ |(n : ℝ)|) :
    IsUnit (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) ∧
      Ring.inverse (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) *
          (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) = 1 ∧
      (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) *
          Ring.inverse (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) = 1 ∧
      Ring.inverse (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) =
        (1 + oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) *
          Ring.inverse (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂ ^ 2) := by
  have hB := s011c_B_side R hR u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  have hB2 : ‖oppositeInteraction n z hz u₁ u₂ hu₁ hu₂ ^ 2‖ < 1 := by
    rw [pow_two]; exact lt_of_le_of_lt hB.2 (by norm_num)
  exact s011c_unit_facts _ hB2

theorem s011c_part1 (R : ℝ) (hR : 1 ≤ R) (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (hpair : schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : complementaryInteractionConstant * R ^ 2 ≤ |(n : ℝ)|) :
    IsUnit (1 - interaction n z hz u₁ u₂ hu₁ hu₂) ∧ IsUnit (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) ∧
      (Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂)).comp (1 - interaction n z hz u₁ u₂ hu₁ hu₂) = 1 ∧
      (1 - interaction n z hz u₁ u₂ hu₁ hu₂).comp (Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂)) = 1 ∧
      (Ring.inverse (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂)).comp
          (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) = 1 ∧
      (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂).comp
          (Ring.inverse (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂)) = 1 ∧
      Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) =
        (1 + interaction n z hz u₁ u₂ hu₁ hu₂) *
          Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂ ^ 2) ∧
      Ring.inverse (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) =
        (1 + oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) *
          Ring.inverse (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂ ^ 2) := by
  obtain ⟨hAu, hSl, hSr, hSeq⟩ := s011c_A_inv R u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  obtain ⟨hBu, hTl, hTr, hTeq⟩ := s011c_B_inv R hR u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  exact ⟨hAu, hBu, hSl, hSr, hTl, hTr, hSeq, hTeq⟩

theorem s011c_part2 (R : ℝ) (hR : 1 ≤ R) (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (hpair : schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : complementaryInteractionConstant * R ^ 2 ≤ |(n : ℝ)|) :
    Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * schurD n z hz =
        (schurD n z hz).comp (Ring.inverse (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂)) ∧
      (1 - interaction n z hz u₁ u₂ hu₁ hu₂).comp
          (Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * schurD n z hz) = schurD n z hz ∧
      (Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * schurD n z hz).comp
          (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂) = schurD n z hz ∧
      (freeResolventComplementaryProjectionTransported n).comp
          (Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * schurD n z hz) =
        Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * schurD n z hz ∧
      (Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * schurD n z hz).comp
          (freeResolventComplementaryProjectionTransported n) =
        Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * schurD n z hz := by
  obtain ⟨_, hSl, hSr, _⟩ := s011c_A_inv R u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  obtain ⟨_, _, hTr, _⟩ := s011c_B_inv R hR u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  obtain ⟨hDT, h11, h12, h13, h14⟩ :=
    s011c_Rn_identities _ _ _ _ _ _ hSl hSr hTr
      (s011c_intertwine_concrete n z hz u₁ u₂ hu₁ hu₂) (s011c_QD n z hz) (s011c_DQ n z hz)
  exact ⟨hDT, h11, h12, h13, h14⟩

theorem s011c_part3 (R : ℝ) (hR : 1 ≤ R) (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (hpair : schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : complementaryInteractionConstant * R ^ 2 ≤ |(n : ℝ)|) :
    ‖Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂)‖ ≤
        2 * (1 + complementaryInteractionConstant * R) ∧
      ‖Ring.inverse (1 - oppositeInteraction n z hz u₁ u₂ hu₁ hu₂)‖ ≤
        2 * (1 + complementaryInteractionConstant * R) ∧
      ‖Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂) * schurD n z hz‖ ≤
        2 * (1 + complementaryInteractionConstant) * R := by
  haveI := s011c_parityPair_nontrivial n
  obtain ⟨hAn, hAsq⟩ := s011c_A_side R u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  obtain ⟨hBn, hBsq⟩ := s011c_B_side R hR u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  obtain ⟨_, _, _, _, hC0⟩ := s011c_const_facts
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hCR : 0 ≤ complementaryInteractionConstant * R := mul_nonneg hC0 hR0
  have hSn := inverse_one_sub_of_square_le_half_norm _ _ hCR hAn hAsq
  have hTn := inverse_one_sub_of_square_le_half_norm _ _ hCR hBn hBsq
  exact ⟨hSn, hTn,
    s011c_norm_Rn_bound _ (schurD n z hz) complementaryInteractionConstant R hR hC0 hSn
      (s011c_D_norm_le_one n z hz)⟩

/-! ### Companion theorem (head verbatim from Pro round 6, section 5) -/

theorem complementaryResolvent_factorizations
    (R : ℝ) (hR : 1 ≤ R)
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (hpair : schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : complementaryInteractionConstant * R ^ 2 ≤ |(n : ℝ)|) :
    let A := interaction n z hz u₁ u₂ hu₁ hu₂
    let B := oppositeInteraction n z hz u₁ u₂ hu₁ hu₂
    let S := Ring.inverse (1 - A)
    let T := Ring.inverse (1 - B)
    let D := schurD n z hz
    let Q := freeResolventComplementaryProjectionTransported n
    let Rn := complementaryResolvent R hR u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
    IsUnit (1 - A) ∧ IsUnit (1 - B) ∧
      S.comp (1 - A) = 1 ∧ (1 - A).comp S = 1 ∧
      T.comp (1 - B) = 1 ∧ (1 - B).comp T = 1 ∧
      S = (1 + A) * Ring.inverse (1 - A ^ 2) ∧
      T = (1 + B) * Ring.inverse (1 - B ^ 2) ∧
      Rn = S.comp D ∧ Rn = D.comp T ∧
      (1 - A).comp Rn = D ∧ Rn.comp (1 - B) = D ∧
      Q.comp Rn = Rn ∧ Rn.comp Q = Rn ∧
      ‖S‖ ≤ 2 * (1 + complementaryInteractionConstant * R) ∧
      ‖T‖ ≤ 2 * (1 + complementaryInteractionConstant * R) ∧
      ‖Rn‖ ≤ 2 * (1 + complementaryInteractionConstant) * R := by
  intro A B S T D Q Rn
  have eA : A = interaction n z hz u₁ u₂ hu₁ hu₂ := rfl
  have eB : B = oppositeInteraction n z hz u₁ u₂ hu₁ hu₂ := rfl
  have eS : S = Ring.inverse (1 - A) := rfl
  have eT : T = Ring.inverse (1 - B) := rfl
  have eD : D = schurD n z hz := rfl
  have eQ : Q = freeResolventComplementaryProjectionTransported n := rfl
  have eRn : Rn = S * D := rfl
  clear_value A B S T D Q Rn
  subst eA eB eQ eD
  subst eS eT
  subst eRn
  obtain ⟨hAu, hBu, hSl, hSr, hTl, hTr, hSeq, hTeq⟩ :=
    s011c_part1 R hR u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  obtain ⟨hDT, h11, h12, h13, h14⟩ :=
    s011c_part2 R hR u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  obtain ⟨hSn, hTn, hRn⟩ :=
    s011c_part3 R hR u₁ u₂ hu₁ hu₂ hpair n hn z hz hlarge
  exact ⟨hAu, hBu, hSl, hSr, hTl, hTr, hSeq, hTeq, rfl, hDT, h11, h12, h13, h14,
    hSn, hTn, hRn⟩

end NlsGge.ThirdConsultation.S
