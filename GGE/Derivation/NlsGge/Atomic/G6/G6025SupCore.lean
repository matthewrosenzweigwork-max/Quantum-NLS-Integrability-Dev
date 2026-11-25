import Mathlib
import NlsGge.Atomic.G6.G6024Sup2Core
import NlsGge.Atomic.LIB.LIB008

/- G6025 SUP CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6025SupCore.lean, namespace NlsGge.ThirdConsultation.G6024S.
   SUPPORT (no packet increment) for G6-025 (Pro r15 Q6: "after Fourier conjugation it is identity plus a compact
   operator"): fromPair m factors as the LIB-008 compact inclusion h^{m+1} → h^m after the bounded same-level map
   fromPairEq (m+1) : PairScale (m+1) → h^{m+1}; the derivative of birkhoffSobolev m = F + fromPair ∘ CS ∘ T is
   F + fromPair ∘ D ∘ T (chain rule at the analytic point), so F⁻¹ ∘ d(birkhoffSobolev) − id = F⁻¹ ∘ fromPair ∘ D ∘ T
   is compact. Hypotheses = those of G6024Sup2Core.birkhoffSobolev_analytic_of (exact landed / KSN-019 types). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSN

namespace NlsGge.ThirdConsultation.G6024S
noncomputable section

theorem smw_le_sw_sq (k : ℕ) (n : ℤ) :
    sobolevModeWeight (k : ℝ) n ≤ 2 ^ k * scaleWeight (k : ℝ) n ^ 2 := by
  rw [sw_eq, smw_eq]
  calc (1 + (n : ℝ) ^ 2) ^ k ≤ (2 * bracket n ^ 2) ^ k :=
        pow_le_pow_left₀ (by positivity) (jb_sq_le_two_bracket_sq n) k
    _ = 2 ^ k * (bracket n ^ k) ^ 2 := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 k]

def fromSeqEq (k : ℕ) (y : PairScale (k : ℝ)) (n : ℤ) : ℂ :=
  y (true, n) / (scaleWeight (k : ℝ) n : ℂ)

theorem fromSeqEq_sq_le (k : ℕ) (y : PairScale (k : ℝ)) (n : ℤ) :
    sobolevModeWeight (k : ℝ) n * ‖fromSeqEq k y n‖ ^ 2 ≤ 2 ^ k * ‖y (true, n)‖ ^ 2 := by
  unfold fromSeqEq
  have hp : 0 < scaleWeight (k : ℝ) n := by
    rw [sw_eq]; exact pow_pos (lt_of_lt_of_le one_pos (bracket_one_le _)) _
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le, div_pow]
  have h := smw_le_sw_sq k n
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right h (sq_nonneg ‖y (true, n)‖)
  nlinarith

theorem fibre_true (k : ℕ) (y : PairScale (k : ℝ)) :
    Summable (fun n : ℤ => ‖y (true, n)‖ ^ 2) ∧ ∑' n : ℤ, ‖y (true, n)‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have hy := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) y
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hy
  have hinj : Function.Injective (fun n : ℤ => ((true, n) : Bool × ℤ)) := fun a b h => by simpa using h
  have hs := hy.summable.comp_injective hinj
  refine ⟨hs, ?_⟩
  rw [← hy.tsum_eq]
  exact hs.tsum_le_tsum_of_inj _ hinj (fun c _ => sq_nonneg _) (fun n => le_rfl) hy.summable

theorem fromSeqEq_mem (k : ℕ) (y : PairScale (k : ℝ)) : fromSeqEq k y ∈ seqSobolev38 (k : ℝ) := by
  show Memℓp (weightedCoordinates (sobolevModeWeight (k : ℝ)) (fromSeqEq k y)) 2
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) (((fibre_true k y).1).mul_left (2 ^ k))
  rw [weightedCoordinates, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (sobolevModeWeight_pos _ _).le]
  exact fromSeqEq_sq_le k y n

def fromPairEq (k : ℕ) : PairScale (k : ℝ) →L[ℝ] SobolevCarrier38 (k : ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun y => carrierMk38 (k : ℝ) (fromSeqEq k y) (fromSeqEq_mem k y)
      map_add' := fun x y => by
        apply carrierExt38
        funext n
        rw [carrierCoe38_add]
        simp only [carrierCoe38_mk, fromSeqEq, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := fun c x => by
        apply carrierExt38
        funext n
        rw [RingHom.id_apply, carrierCoe38_smul]
        simp only [carrierCoe38_mk, fromSeqEq, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
        ring }
    (Real.sqrt (2 ^ k)) (fun y => by
      have h0 := carrier_hasSum k (carrierMk38 (k : ℝ) (fromSeqEq k y) (fromSeqEq_mem k y))
      simp only [carrierCoe38_mk] at h0
      have h2 : ‖carrierMk38 (k : ℝ) (fromSeqEq k y) (fromSeqEq_mem k y)‖ ^ 2 ≤ (Real.sqrt (2 ^ k) * ‖y‖) ^ 2 := by
        rw [← h0.tsum_eq, mul_pow, Real.sq_sqrt (by positivity)]
        obtain ⟨hs, hle⟩ := fibre_true k y
        refine (h0.summable.tsum_le_tsum (fun n => fromSeqEq_sq_le k y n) (hs.mul_left _)).trans ?_
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hle (by positivity)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2)

theorem fromPair_factor (m : ℕ) :
    fromPair m = (NlsGge.Atomic.LIB008.sobolevSequenceInclusion ((m + 1 : ℕ) : ℝ) (m : ℝ)
      (by push_cast; linarith)).comp (fromPairEq (m + 1)) := by
  ext y
  apply carrierExt38
  funext n
  rw [ContinuousLinearMap.comp_apply, NlsGge.Atomic.LIB008.sobolevSequenceInclusion_apply, fromPair_coe]
  rfl

theorem fromPair_compact (m : ℕ) : IsCompactOperator (fromPair m) := by
  rw [fromPair_factor]
  exact (NlsGge.Atomic.LIB008.sobolevSequenceInclusion_compact
    (show (m : ℝ) < ((m + 1 : ℕ) : ℝ) by push_cast; linarith)).comp_clm (fromPairEq (m + 1))

/-- G6-025 conclusion from the G6-024 inputs. -/
theorem jacobian_compact_of (m : ℕ)
    (hmemB : ∀ u : PhysicalSobolev38 (m : ℝ),
      (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hA : AnalyticOnNhd ℂ (complexSmoothing m) (complexDomain (m : ℝ) (Nat.cast_nonneg m)))
    (hmem : ∀ x ∈ complexDomain (m : ℝ) (Nat.cast_nonneg m),
      Memℓp (storedSequence ((m : ℝ) + 1) (smoothingCoefficient m x)) 2)
    (u : PhysicalSobolev38 (m : ℝ)) :
    IsCompactOperator (sobolevJacobianConjugate m u -
      ContinuousLinearMap.id ℝ (PhysicalSobolev38 (m : ℝ))) := by
  set F : PhysicalSobolev38 (m : ℝ) →L[ℝ] SobolevCarrier38 (m : ℝ) :=
    (physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap with hF
  set T : PhysicalSobolev38 (m : ℝ) →L[ℝ] PairScale (m : ℝ) := (toPair m).comp F with hT
  have hC : AnalyticAt ℝ (complexSmoothing m) (T u) :=
    (hA _ (toPair_mem_complexDomain m u)).restrictScalars
  set D : PairScale (m : ℝ) →L[ℝ] PairScale ((m : ℝ) + 1) := fderiv ℝ (complexSmoothing m) (T u) with hD
  have heq : birkhoffSobolev m = fun v => F v + fromPair m (complexSmoothing m (T v)) :=
    funext (birkhoffSobolev_eq m hmemB hSR hmem)
  have hder : HasFDerivAt (birkhoffSobolev m) (F + (fromPair m).comp (D.comp T)) u := by
    rw [heq]
    have h1 : HasFDerivAt (fun v => complexSmoothing m (T v)) (D.comp T) u :=
      hC.differentiableAt.hasFDerivAt.comp u T.hasFDerivAt
    exact F.hasFDerivAt.add ((fromPair m).hasFDerivAt.comp u h1)
  have hJ : sobolevJacobianConjugate m u - ContinuousLinearMap.id ℝ (PhysicalSobolev38 (m : ℝ)) =
      (physicalSobolevFourierEquiv38 (m : ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fromPair m).comp (D.comp T)) := by
    unfold sobolevJacobianConjugate
    rw [hder.fderiv]
    ext v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply, map_add]
    simp [hF]
  rw [hJ]
  change IsCompactOperator
    (⇑((physicalSobolevFourierEquiv38 (m : ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘
      (⇑(fromPair m) ∘ ⇑(D.comp T)))
  exact ((fromPair_compact m).comp_clm (D.comp T)).clm_comp
    (physicalSobolevFourierEquiv38 (m : ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap

end
end NlsGge.ThirdConsultation.G6024S
