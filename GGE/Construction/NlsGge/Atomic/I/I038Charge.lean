import Mathlib
import NlsGge.Atomic.I.I038FiniteBlock
import NlsGge.Atomic.I.I038Smooth
import NlsGge.Birkhoff.S04Moments38e

                                                                                                                  
                                                                                                                   
                                            
                                                                                                                  
                                                                                                       
                                                                                                                      
                                                                                                            
                                                                                                                  
                                                                                                                  
                                                                                                                  
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.I
open NlsGge.Atomic.I010 (spectralEnergy)

namespace NlsGge.ThirdConsultation.I038C

/-- Same local instance as the landed G6/Round5, M053Sup3 (needed to form `ContinuousMap.toLp`). -/
local instance spatialFiniteI038C : IsFiniteMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

theorem chargeFn_eq_local (u : PhysicalL2) (hall : ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier u))
    (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) (hUu : smoothL2_38 U hU hper = u)
    (m j : ℕ) (hm : 2 ≤ m) (hjm : j ≤ m) :
    chargeFn38 m j u = localCharge38 U j := by
  have hmem : (fun n => physicalFourier u n) ∈ seqSobolev38 (((m - 1 : ℕ) : ℝ)) :=
    (mem_seqSobolev38_iff _ _).2 (hall (m - 1))
  set x : SobolevHilbert ((m - 1 : ℕ) : ℝ) := ofCarrier38 ((m - 1 : ℕ) : ℝ) (physC38 (m - 1) u)
    with hx
  have hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper)) n := by
    intro n
    have e : (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper) : PhysicalL2) = u :=
      hUu
    rw [e]
    have : x = carrierMk38 ((m - 1 : ℕ) : ℝ) _ hmem := by
      rw [hx]; exact physC38_of_mem (m - 1) u hmem
    rw [this]
    rfl
  rw [show chargeFn38 m j u = chargeSobolev38 m j x from rfl]
  exact chargeSobolev38_smooth m j hm hjm U hU hper x hsource

theorem hasSum_charge (W : ℝ → ℝ) (β : ℕ → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hW : ∀ r : ℝ, HasSum (fun j : ℕ => β j * r ^ (2 * j)) (W r))
    (u : PhysicalL2) (hall : ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier u))
    (hint : Integrable (fun t : ℝ => W (2 * t) * actualGapHeightE02_38 u t)) :
    HasSum (fun j : ℕ => β j * chargeFn38 (j + 2) j u) (spectralEnergy W u) := by
  obtain ⟨U, hU, hper, hUu⟩ := exists_smooth_rep38 u hall
  have hQ : ∀ j, chargeFn38 (j + 2) j u = localCharge38 U j := fun j =>
    chargeFn_eq_local u hall U hU hper hUu (j + 2) j (by omega) (by omega)
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := by simpa using hall 1
  have hae := smoothL2_38_cover_ae U hU hper
  rw [hUu] at hae
  have htr := fun j => actualTraceFormula_E02_38 u hu1 U hU hper hae j
  have hv0 := actualGapHeightE02_38_nonneg u
  have hloc : ∀ j, localCharge38 U j = (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t :=
    fun j => (htr j).2
  have hW0 : ∀ r, 0 ≤ W r := fun r =>
    (hW r).nonneg (fun j => mul_nonneg (hβ0 j) (by rw [pow_mul]; positivity))
  set F : ℕ → ℝ → ℝ := fun j t => β j * ((2 * t) ^ (2 * j) * actualGapHeightE02_38 u t) with hF
  have hF0 : ∀ j t, 0 ≤ F j t := fun j t =>
    mul_nonneg (hβ0 j) (mul_nonneg (by rw [pow_mul]; positivity) (hv0 t))
  have hFint : ∀ j, Integrable (F j) := fun j => (htr j).1.const_mul _
  set a : ℕ → ℝ := fun j => ∫ t, F j t with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j => integral_nonneg (hF0 j)
  have haQ : ∀ j, a j = (Real.pi / 2) * (β j * localCharge38 U j) := by
    intro j
    simp only [ha, hF]
    rw [integral_const_mul, hloc j]
    field_simp
  have hpt : ∀ t, HasSum (fun j => F j t) (W (2 * t) * actualGapHeightE02_38 u t) := by
    intro t
    have := (hW (2 * t)).mul_right (actualGapHeightE02_38 u t)
    refine this.congr_fun ?_
    intro j; simp only [hF]; ring
  have hL : ∫⁻ t, ENNReal.ofReal (W (2 * t) * actualGapHeightE02_38 u t) =
      ∑' j, ENNReal.ofReal (a j) := by
    rw [← (fun j => (ofReal_integral_eq_lintegral_ofReal (hFint j)
      (Filter.Eventually.of_forall (hF0 j))).symm) |> tsum_congr,
      ← lintegral_tsum (fun j => (hFint j).1.aemeasurable.ennreal_ofReal)]
    refine lintegral_congr (fun t => ?_)
    rw [← (hpt t).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => hF0 j t) (hpt t).summable]
  have hI0 : ∀ t, 0 ≤ W (2 * t) * actualGapHeightE02_38 u t := fun t => mul_nonneg (hW0 _) (hv0 t)
  have hlint : ∫⁻ t, ENNReal.ofReal (W (2 * t) * actualGapHeightE02_38 u t) =
      ENNReal.ofReal (∫ t, W (2 * t) * actualGapHeightE02_38 u t) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hI0)).symm
  rw [hlint] at hL
  have hne : (∑' j, ENNReal.ofReal (a j)) ≠ ⊤ := by rw [← hL]; exact ENNReal.ofReal_ne_top
  have hsum : Summable a := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (ha0 _)] using this
  have heq : ∑' j, a j = ∫ t, W (2 * t) * actualGapHeightE02_38 u t := by
    rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hsum] at hL
    exact ((ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg ha0) (integral_nonneg hI0)).1 hL.symm)
  have hA : HasSum a (∫ t, W (2 * t) * actualGapHeightE02_38 u t) := heq ▸ hsum.hasSum
  have hB := hA.mul_left (2 / Real.pi)
  have e : ∀ j, (2 / Real.pi) * a j = β j * chargeFn38 (j + 2) j u := by
    intro j; rw [haQ j, hQ j]; field_simp
  simp only [e] at hB
  exact hB

/-- The I-038 charge clause on every finite-gap field. -/
theorem finiteGap_charge (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (p : ℝ) (hp : 1 ≤ p) (c : ℕ → ℝ) (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) (S : Finset ℤ) (w : S → ℂ) :
    HasSum (fun j : ℕ => c j / ((j.factorial : ℝ) ^ p) *
      chargeFn38 (j + 2) j (finiteGapField S w))
      (spectralEnergy (NlsGge.Atomic.I037.factorialPowerWeight p c) (finiteGapField S w)) := by
  have hW2 := NlsGge.ThirdConsultation.I038S.contDiff_weight hp hc
  have hconv := NlsGge.ThirdConsultation.I038S.convexOn_weight hp hc
  have hall : ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier (finiteGapField S w)) := by
    intro m
    rw [NlsGge.ThirdConsultation.I017C.field_eq_proj Bk hB S w]
    exact Bk.sobolev_cleanΦinv38 m _ (finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 S _))
  refine hasSum_charge _ (fun j => c j / ((j.factorial : ℝ) ^ p))
    (fun j => (NlsGge.ThirdConsultation.I038S.coef_le hp hc j).1) (fun r => ?_) _ hall
    (NlsGge.ThirdConsultation.I038B.energy_split Bk hB _ hW2 hconv S w).2.2
  refine ((NlsGge.Atomic.I037.summable_term hp hc r).hasSum).congr_fun ?_
  intro j; unfold NlsGge.Atomic.I037.factorialPowerTerm; ring

end NlsGge.ThirdConsultation.I038C
