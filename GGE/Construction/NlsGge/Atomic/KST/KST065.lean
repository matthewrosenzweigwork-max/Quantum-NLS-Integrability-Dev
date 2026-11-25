import Mathlib
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST043
import NlsGge.Atomic.KST.KST059
import NlsGge.Atomic.KST.KST060
import NlsGge.Atomic.KST.KST064
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Birkhoff.BirkhoffInput38
import NlsGge.Definitions.PilotInterfaces
import NlsGge.GK38.Defs
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Hierarchy.RiccatiSmoothClassicalDerivativePhysicalL2AgreementRecovery30Fifth
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.SmoothFourier
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev38.SobolevCarrier38
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST061Host
import NlsGge.ThirdConsultation.Sobolev.Round5

                                                                                                        
                                                                                                    
                                                                                                                          
                                                                                                                           
                                                                  
                                                                                                                  
                                                    
                                                                                                                              
                                                                                                                  
                                                                                          
                                                                                                 
                                                                             
                                                                                                             
                                                                                                                     
                                                                                        
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open scoped ENNReal Real ContDiff
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KST

namespace KST065S

open NlsGge.Atomic.KST001 NlsGge.Atomic.KST064 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- Step (1): same-index gap identification. -/
theorem pairFiniteGap_of_finiteGap (u : PhysicalL2)
    (h : NlsGge.ThirdConsultation.finiteGap u) : pairFiniteGap (realSlice u) := by
  unfold pairFiniteGap
  refine h.subset fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro heq
  apply hn
  unfold NlsGge.Atomic.KST059.actualGapSequence
  rw [(lamPlus_real u n).1, (lamPlus_real u n).2, heq]
  exact sub_self _

/-- Step (2): a finitely supported gap sequence has finite weighted gap energy for every weight. -/
theorem gapEnergy_lt_top (u : PhysicalL2) (h : pairFiniteGap (realSlice u)) (W : ℤ → ℝ) :
    NlsGge.Atomic.KST059.weightedGapEnergy W
      (NlsGge.Atomic.KST059.actualGapSequence (realSlice u)) < ⊤ := by
  unfold NlsGge.Atomic.KST059.weightedGapEnergy
  rw [tsum_eq_sum (s := h.toFinset) (fun n hn => ?_)]
  · exact ENNReal.sum_lt_top.2 (fun n _ => ENNReal.ofReal_lt_top)
  · have h0 : NlsGge.Atomic.KST059.actualGapSequence (realSlice u) n = 0 := by
      by_contra hne
      exact hn (h.mem_toFinset.2 hne)
    rw [h0, norm_zero]
    simp

theorem sobolevModeWeight_eq (s : ℝ) (n : ℤ) :
    sobolevModeWeight s n = (1 + (n : ℝ) ^ 2) ^ s := by
  unfold sobolevModeWeight japaneseBracket
  rw [Real.sqrt_eq_rpow]
  change (((1 + (n : ℝ) ^ 2) ^ (1 / 2 : ℝ)) ^ (2 * s) : ℝ) = _
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem natAbs_two_mul (n : ℤ) : (((2 * n).natAbs : ℕ) : ℝ) = 2 * (n.natAbs : ℝ) := by
  have : (2 * n).natAbs = 2 * n.natAbs := by omega
  rw [this]; push_cast; ring

theorem intCast_sq_eq (n : ℤ) : (n : ℝ) ^ 2 = (n.natAbs : ℝ) ^ 2 := by
  rw [← sq_abs, ← Int.cast_abs, Int.abs_eq_natAbs]; simp

theorem polynomialWeight_two_mul_sq (s : ℝ) (n : ℤ) :
    polynomialWeight s (2 * n) ^ 2 = ((1 + 2 * (n.natAbs : ℝ)) ^ 2) ^ s := by
  unfold polynomialWeight
  rw [natAbs_two_mul, sq, ← Real.mul_rpow (by positivity) (by positivity), ← sq]

theorem sobolevModeWeight_le (s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    sobolevModeWeight s n ≤ polynomialWeight s (2 * n) ^ 2 := by
  rw [sobolevModeWeight_eq, polynomialWeight_two_mul_sq, intCast_sq_eq]
  apply Real.rpow_le_rpow (by positivity) _ hs
  nlinarith [Nat.cast_nonneg (α := ℝ) n.natAbs]

theorem polyEven (s : ℝ) (hs : 0 ≤ s) : EvenWeight (polynomialWeight s) :=
  ⟨fun k => by
    unfold polynomialWeight
    exact Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) k.natAbs]) hs,
   fun k => by simp [polynomialWeight]⟩

/-- Doubled-cover energy of the real slice of `g`, in terms of the reflected Fourier coefficients of `g`. -/
theorem energy_realSlice (W : ℤ → ℝ) (hE : EvenWeight W) (g : PhysicalL2) :
    weightedNormSq₂ W (realSlice g) =
      2 * ∑' m : ℤ, ENNReal.ofReal (W (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2) := by
  rw [periodOne_weightedPair_norm W (realSlice g) hE]
  unfold weightedEvenFourierNormSq
  have h1 : ∀ m : ℤ, weightedPairMode W (2 * m)
      (physicalFourier (realSlice g).1 m, physicalFourier (realSlice g).2 m) =
      ENNReal.ofReal (W (2 * m) ^ 2 * ‖fourierSeq38 g (-m)‖ ^ 2) +
        ENNReal.ofReal (W (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2) := by
    intro m
    have e1 : ‖physicalFourier (realSlice g).1 m‖ = ‖fourierSeq38 g (-m)‖ := by
      rw [fourierSeq38_apply, neg_neg, norm_neg]; rfl
    have e2 : ‖physicalFourier (realSlice g).2 m‖ = ‖fourierSeq38 g m‖ := by
      rw [fourierSeq38_apply, norm_neg, realSlice_snd, NlsGge.Schur.physicalFourier_star38, norm_star]
    simp only [weightedPairMode, e1, e2]
    rw [mul_add, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
  simp_rw [h1]
  rw [ENNReal.tsum_add]
  have h2 : ∑' m : ℤ, ENNReal.ofReal (W (2 * m) ^ 2 * ‖fourierSeq38 g (-m)‖ ^ 2) =
      ∑' m : ℤ, ENNReal.ofReal (W (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2) := by
    rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ => ENNReal.ofReal (W (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2))]
    refine tsum_congr fun m => ?_
    simp only [Equiv.neg_apply]
    have : W (2 * -m) = W (2 * m) := by rw [mul_neg]; exact hE.even _
    rw [this]
  rw [h2, two_mul]

/-- Finite polynomial doubled-cover energy gives membership of the reflected Fourier sequence in `h^s`. -/
theorem mem_of_energy_lt_top (s : ℝ) (hs : 0 ≤ s) (g : PhysicalL2)
    (h : weightedNormSq₂ (polynomialWeight s) (realSlice g) < ⊤) :
    fourierSeq38 g ∈ seqSobolev38 s := by
  rw [energy_realSlice _ (polyEven s hs)] at h
  rw [mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  change Summable (fun n : ℤ => sobolevModeWeight s n * ‖fourierSeq38 g n‖ ^ 2)
  have h0 : ∑' m : ℤ, ENNReal.ofReal (polynomialWeight s (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2) ≠ ⊤ := by
    intro htop
    rw [htop] at h
    simp at h
  have h1 : ∑' m : ℤ, ENNReal.ofReal (sobolevModeWeight s m * ‖fourierSeq38 g m‖ ^ 2) ≠ ⊤ := by
    refine ne_top_of_le_ne_top h0 (ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (sobolevModeWeight_le s hs m) (sq_nonneg _)
  have h2 := ENNReal.summable_toReal h1
  refine h2.congr fun m => ?_
  exact ENNReal.toReal_ofReal (mul_nonneg (by rw [sobolevModeWeight_eq]; positivity) (sq_nonneg _))

/-- Step (3): the self-adjoint inverse regularity (KST-060) at every polynomial weight. -/
theorem mem_seqSobolev_of_finiteGap (u : PhysicalL2)
    (h : pairFiniteGap (realSlice u)) (m : ℕ) :
    fourierSeq38 u ∈ seqSobolev38 (m : ℝ) := by
  have hs : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hreal : RealForm 1 (realSlice u) := ⟨Or.inl rfl, by simp [realSlice_snd]⟩
  have h60 := kst060 (realSlice u) 1 hreal (polynomialWeight (m : ℝ))
    (gapEnergy_lt_top u h _)
  exact mem_of_energy_lt_top (m : ℝ) hs u
    (h60.1 (kst_sobolev_weight_equivalence (m : ℝ) hs).1)

/-- Step (4): recovery of the Sobolev vector. -/
theorem exists_recover (m : ℕ) (g : PhysicalL2) (hg : fourierSeq38 g ∈ seqSobolev38 (m : ℝ)) :
    ∃ v : PhysicalSobolev38 (m : ℝ), NlsGge.GKDefinitionDesign.physicalSobolevEmbed m v = g := by
  refine ⟨(physicalSobolevFourierEquiv38 (m : ℝ)).symm (carrierMk38 (m : ℝ) (fourierSeq38 g) hg), ?_⟩
  apply fourierSeq38_injective
  funext n
  rw [NlsGge.GKDefinitionDesign.physicalSobolevEmbed_fourier]
  simp

/-- Step (5): a physical field whose Fourier coefficients lie in every `h^k` has an actual smooth periodic
representative of the same `L2` class. -/
theorem smooth_of_mem (u : PhysicalL2)
    (hmem : ∀ k : ℕ, fourierSeq38 u ∈ seqSobolev38 (k : ℝ)) :
    NlsGge.ThirdConsultation.KO.SmoothPhysical u := by
  have hu : ∀ k : ℕ, SobolevSquareSummable (k : ℝ) (physicalFourier u) := fun k =>
    (fourierSeq38_mem_iff (k : ℝ) u).1 (hmem k)
  have hamp : ∀ k : ℕ, Summable (fun n : ℤ => japaneseBracket n ^ k * ‖physicalFourier u n‖) :=
    fun k => summable_sobolev_amplitude k (physicalFourier u) (hu (k + 1))
  have hsumm : Summable (fun n : ℤ => physicalFourier u n • (fourier n : C(PhysicalCircle, ℂ))) := by
    apply Summable.of_norm
    simpa only [norm_smul, fourier_norm, mul_one, pow_zero, one_mul] using hamp 0
  set C : C(PhysicalCircle, ℂ) := ∑' n : ℤ, physicalFourier u n • (fourier n : C(PhysicalCircle, ℂ)) with hC
  have hCsum : HasSum (fun n : ℤ => physicalFourier u n • (fourier n : C(PhysicalCircle, ℂ))) C :=
    hsumm.hasSum
  have hser : ∀ y : ℝ, C (y : PhysicalCircle) = ∑' n : ℤ, fourierRealTerm n (physicalFourier u n) y := by
    intro y
    have h := hCsum.mapL (ContinuousMap.evalCLM ℂ (y : PhysicalCircle))
    change HasSum (fun n : ℤ => fourierRealTerm n (physicalFourier u n) y) (C (y : PhysicalCircle)) at h
    exact h.tsum_eq.symm
  have hsm : ContDiff ℝ ∞ (fun y : ℝ => C (y : PhysicalCircle)) := by
    have hfun : (fun y : ℝ => C (y : PhysicalCircle)) =
        fun y : ℝ => ∑' n : ℤ, fourierRealTerm n (physicalFourier u n) y := funext hser
    rw [hfun]
    exact contDiff_tsum (fun n => contDiff_fourierRealTerm n (physicalFourier u n))
      (fun k _ => (hamp k).mul_left ((2 * π) ^ k))
      (fun k n y _ => norm_iteratedFDeriv_fourierRealTerm_le n (physicalFourier u n) k y)
  have hper : Function.Periodic (fun y : ℝ => C (y : PhysicalCircle)) 1 := by
    intro y
    simp only [AddCircle.coe_add_period]
  refine ⟨_, hsm, hper, ?_⟩
  have hlift : NlsGge.HierarchyRiccati.Core.riccatiSmoothPeriodicLiftContinuousMapRecovery30First
      (fun y : ℝ => C (y : PhysicalCircle)) hsm.continuous hper = C := by
    ext x
    have hx := (AddCircle.equivIoc 1 0 x).2
    change AddCircle.liftIoc 1 0 (fun y : ℝ => C (y : PhysicalCircle)) x = C x
    have hc : (((AddCircle.equivIoc 1 0 x : ℝ)) : PhysicalCircle) = x := AddCircle.coe_equivIoc
    rw [← hc]
    rw [AddCircle.liftIoc_coe_apply (by simpa using hx)]
  unfold NlsGge.HierarchyRiccati.Core.smoothL2_38
  rw [hlift]
  have h := hCsum.mapL (ContinuousMap.toLp 2 spatialMeasure ℂ)
  simp only [map_smul] at h
  change HasSum (fun n : ℤ => physicalFourier u n • fourierLp (T := (1 : ℝ)) 2 n)
    (ContinuousMap.toLp 2 spatialMeasure ℂ C) at h
  exact h.unique (hasSum_fourier_series_L2 u)

end KST065S

theorem kst065 (u : PhysicalL2)
    (hfg : NlsGge.ThirdConsultation.finiteGap u) :
  pairFiniteGap (realSlice u) ∧ NlsGge.ThirdConsultation.KO.SmoothPhysical u ∧
  ∀ m : ℕ, ∃ v : NlsGge.Atomic.Common.PhysicalSobolev38 (m : ℝ),
    NlsGge.GKDefinitionDesign.physicalSobolevEmbed m v = u := by
  have hpf := KST065S.pairFiniteGap_of_finiteGap u hfg
  have hmem := KST065S.mem_seqSobolev_of_finiteGap u hpf
  exact ⟨hpf, KST065S.smooth_of_mem u hmem, fun m => KST065S.exists_recover m u (hmem m)⟩

end NlsGge.ThirdConsultation.KST
end
