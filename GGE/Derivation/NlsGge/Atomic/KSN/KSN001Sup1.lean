import Mathlib
import NlsGge.Atomic.KSN.KSN001Host
import NlsGge.Atomic.G4.G4043
import NlsGge.Atomic.G4.G4039
import NlsGge.Atomic.G6.G6013Sup1
import NlsGge.Sobolev.PeriodicBridge

/- KSN-001 SUPPORT 1 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN001Sup1.lean,
   namespace NlsGge.ThirdConsultation.KSN.KSN001Aux. Five of the eight conjuncts of the KSN001_main head (followup12
   STATEMENTS/KSN.md, verbatim, each stated as its own theorem; Pro round 14 row KSN-001 "Retain KSN001_main"):
     conjunct 2 `action_eq`     : gkActionC38 = scalarBirkhoff true * scalarBirkhoff false on sourceBetaW
                                  (landed G4043 (X^2+Y^2)/2 and (X-iY)(X+iY) = X^2+Y^2, sqrt2^2 = 2);
     conjunct 5 `pairFourier_parseval`: membership of the stored reflected Fourier sequence and the source pair norm
                                  (bracket^0 = 1; Parseval hasSum_physicalFourier_sq for both fields, the first reindexed
                                  by n -> -n; Bool x Z split by landed G4039Aux.sq_sum_prod; membership proved BEFORE the
                                  sequenceLift fallback is discarded);
     conjunct 6 `reflectedStored_isometry`: reindexing by the involution reflectPairIndex;
     conjunct 7 `evenWeighted_reflected`: literal computation, with w(-n) = w n;
     conjunct 8 `scalarBirkhoff_realSlice`: the landed G6013Sup1 bridge physicalBirkhoff_eq_cartesian (same physical map).
   Conjuncts 3/4 (complex derivative of complexBirkhoff at 0) are provable from landed G4039/G4042/G4044 and g5010_vacuum
   (route in KSN001_STOP.md) but are not done here. Conjunct 1 is BLOCKED (KSN001_STOP.md). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
namespace KSN001Aux
noncomputable section

theorem sqrt2_sq_complex : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Conjunct 2 of KSN001_main. -/
theorem action_eq : ∀ φ ∈ sourceBetaW, ∀ n : ℤ,
    gkActionC38 φ n = scalarBirkhoff true n φ * scalarBirkhoff false n φ := by
  intro φ hφ n
  rw [G4043 n φ hφ]
  unfold scalarBirkhoff
  rw [if_pos rfl, if_neg Bool.false_ne_true, div_mul_div_comm, sqrt2_sq_complex]
  linear_combination (cartesianY n φ ^ 2 / 2) * Complex.I_sq

theorem reflectPairIndex_involutive : Function.Involutive reflectPairIndex := by
  rintro ⟨b, n⟩
  cases b <;> simp [reflectPairIndex]

theorem scaleWeight_zero (n : ℤ) : scaleWeight 0 n = 1 := by
  unfold scaleWeight
  exact Real.rpow_zero _

theorem storedSequence_zero (f : Bool → ℤ → ℂ) (j : Bool × ℤ) :
    storedSequence 0 f j = f j.1 j.2 := by
  unfold storedSequence
  rw [scaleWeight_zero, Complex.ofReal_one, one_mul]

theorem memℓp_two_iff (f : Bool × ℤ → ℂ) :
    Memℓp f 2 ↔ Summable (fun j : Bool × ℤ => ‖f j‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

theorem norm_sq_eq_tsum (x : PairScale 0) : ‖x‖ ^ 2 = ∑' j : Bool × ℤ, ‖x j‖ ^ 2 := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  exact h.tsum_eq.symm

/-- Conjunct 5 of KSN001_main. -/
theorem pairFourier_parseval : ∀ φ : PotPair,
    Memℓp (storedSequence 0 (reflectedPairCoefficient φ)) 2 ∧
    ‖pairFourier φ‖^2 = ‖φ.1‖^2 + ‖φ.2‖^2 := by
  intro φ
  set f : Bool × ℤ → ℂ := storedSequence 0 (reflectedPairCoefficient φ) with hf
  have hT : ∀ n : ℤ, ‖f (true, n)‖ ^ 2 = ‖physicalFourier φ.1 (-n)‖ ^ 2 := by
    intro n
    rw [hf, storedSequence_zero]
    simp [reflectedPairCoefficient]
  have hF : ∀ n : ℤ, ‖f (false, n)‖ ^ 2 = ‖physicalFourier φ.2 n‖ ^ 2 := by
    intro n
    rw [hf, storedSequence_zero]
    simp [reflectedPairCoefficient]
  have h1 : HasSum (fun n : ℤ => ‖f (true, n)‖ ^ 2) (‖φ.1‖ ^ 2) := by
    have h := (Equiv.neg ℤ).hasSum_iff.2 (hasSum_physicalFourier_sq φ.1)
    have he : (fun n : ℤ => ‖f (true, n)‖ ^ 2) =
        (fun n : ℤ => ‖physicalFourier φ.1 n‖ ^ 2) ∘ (Equiv.neg ℤ) := by
      funext n
      rw [hT]
      rfl
    rw [he]
    exact h
  have h2 : HasSum (fun n : ℤ => ‖f (false, n)‖ ^ 2) (‖φ.2‖ ^ 2) := by
    have he : (fun n : ℤ => ‖f (false, n)‖ ^ 2) = fun n : ℤ => ‖physicalFourier φ.2 n‖ ^ 2 := by
      funext n
      exact hF n
    rw [he]
    exact hasSum_physicalFourier_sq φ.2
  obtain ⟨hs, hsum⟩ :=
    NlsGge.GKDefinitionDesign.G4039Aux.sq_sum_prod f h1.summable h2.summable
  have hmem : Memℓp f 2 := (memℓp_two_iff f).2 hs
  refine ⟨hmem, ?_⟩
  have hlift : pairFourier φ = ⟨f, hmem⟩ := by
    unfold pairFourier sequenceLift
    rw [dif_pos hmem]
  rw [hlift, norm_sq_eq_tsum]
  have hc : (∑' j : Bool × ℤ, ‖(⟨f, hmem⟩ : PairScale 0) j‖ ^ 2) =
      ∑' j : Bool × ℤ, ‖f j‖ ^ 2 := rfl
  rw [hc, hsum, h1.tsum_eq, h2.tsum_eq]

/-- Conjunct 6 of KSN001_main. -/
theorem reflectedStored_isometry : ∀ s : ℝ, Isometry (reflectedStored s) := by
  intro s
  have hnorm : ∀ z : PairScale s, ‖reflectedStored s z‖ = ‖z‖ := by
    intro z
    have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    have he : (fun j : Bool × ℤ => ‖(reflectedStored s z) j‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun j : Bool × ℤ => ‖z j‖ ^ (2 : ℝ≥0∞).toReal) ∘ reflectPairIndex_involutive.toPerm := by
      funext j
      show ‖-z (reflectPairIndex j)‖ ^ (2 : ℝ≥0∞).toReal = _
      rw [norm_neg]
      rfl
    rw [he]
    exact Equiv.tsum_eq reflectPairIndex_involutive.toPerm
      (fun j : Bool × ℤ => ‖z j‖ ^ (2 : ℝ≥0∞).toReal)
  have hsub : ∀ x y : PairScale s,
      reflectedStored s x - reflectedStored s y = reflectedStored s (x - y) := by
    intro x y
    apply lp.ext
    funext j
    rw [lp.coeFn_sub, Pi.sub_apply]
    show -x (reflectPairIndex j) - -y (reflectPairIndex j) = -(x - y) (reflectPairIndex j)
    rw [lp.coeFn_sub, Pi.sub_apply]
    ring
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, hsub, hnorm]

/-- Conjunct 7 of KSN001_main. -/
theorem evenWeighted_reflected : ∀ (w : ℤ → ℝ), (∀ n, 0 < w n) → (∀ n, w (-n) = w n) →
    ∀ (x : PairScale 0) (b : Bool) (n : ℤ),
      evenWeightedCoefficient w (reflectedStored 0 x) b n =
        -evenWeightedCoefficient w x b (if b then -n else n) := by
  intro w _hw hev x b n
  show -x (reflectPairIndex (b, n)) / (w n : ℂ) = -(x (b, if b then -n else n) / (w (if b then -n else n) : ℂ))
  cases b
  · simp [reflectPairIndex, neg_div]
  · simp [reflectPairIndex, neg_div, hev]

/-- Conjunct 8 of KSN001_main. -/
theorem scalarBirkhoff_realSlice : ∀ (u : PhysicalL2) (n : ℤ),
    scalarBirkhoff true n (realSlice u) = physicalBirkhoff u n := by
  intro u n
  unfold scalarBirkhoff
  rw [if_pos rfl]
  exact (physicalBirkhoff_eq_cartesian u n).symm

end
end KSN001Aux
end NlsGge.ThirdConsultation.KSN
