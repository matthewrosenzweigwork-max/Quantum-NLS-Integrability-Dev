import Mathlib
import NlsGge.Atomic.KSN.KSN012Host
import NlsGge.Atomic.KSN.KSN012Sup4
import NlsGge.ThirdConsultation.G6.Energy031A
import NlsGge.Birkhoff.BirkhoffAPI38

                                                                                       
                                                                                         
                                                                                                                  
                                                                                                                
                        
                                                                                                                 
                                                                                               
                                                                                                          
                                                                                                                  
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSN

namespace NlsGge.ThirdConsultation.G6024S
noncomputable section

theorem bracket_sq_le_jb_sq (k : ℤ) : bracket k ^ 2 ≤ 1 + (k : ℝ) ^ 2 := by
  unfold bracket
  have hm : ((k.natAbs : ℕ) : ℝ) ^ 2 = (k : ℝ) ^ 2 := by rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rcases max_cases 1 ((k.natAbs : ℕ) : ℝ) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; nlinarith [sq_nonneg (k : ℝ)]
  · rw [h, hm]; linarith

theorem jb_sq_le_two_bracket_sq (k : ℤ) : 1 + (k : ℝ) ^ 2 ≤ 2 * bracket k ^ 2 := by
  unfold bracket
  have hm : ((k.natAbs : ℕ) : ℝ) ^ 2 = (k : ℝ) ^ 2 := by rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rcases max_cases 1 ((k.natAbs : ℕ) : ℝ) with ⟨h, h1⟩ | ⟨h, h1⟩
  · rw [h]
    have : (k : ℝ) ^ 2 ≤ 1 := by rw [← hm]; nlinarith [Nat.cast_nonneg (α := ℝ) k.natAbs]
    linarith
  · rw [h, hm]
    have : 1 ≤ (k : ℝ) ^ 2 := by rw [← hm]; nlinarith
    linarith

theorem smw_eq (m : ℕ) (k : ℤ) : sobolevModeWeight (m : ℝ) k = (1 + (k : ℝ) ^ 2) ^ m := by
  unfold sobolevModeWeight japaneseBracket
  rw [show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring]
  show (Real.sqrt (1 + (k : ℝ) ^ 2)) ^ (((2 * m : ℕ) : ℝ)) = _
  rw [Real.rpow_natCast, pow_mul, Real.sq_sqrt (by positivity)]

theorem sw_eq (s : ℕ) (k : ℤ) : scaleWeight (s : ℝ) k = bracket k ^ s := by
  unfold scaleWeight; exact Real.rpow_natCast _ _

theorem bracket_one_le (k : ℤ) : 1 ≤ bracket k := le_max_left _ _

theorem sw_sq_le_smw (m : ℕ) (k : ℤ) : scaleWeight (m : ℝ) k ^ 2 ≤ sobolevModeWeight (m : ℝ) k := by
  rw [sw_eq, smw_eq, ← pow_mul, mul_comm, pow_mul]
  exact pow_le_pow_left₀ (by positivity) (bracket_sq_le_jb_sq k) m

theorem smw_le_sw_succ_sq (m : ℕ) (k : ℤ) :
    sobolevModeWeight (m : ℝ) k ≤ 2 ^ m * scaleWeight ((m + 1 : ℕ) : ℝ) k ^ 2 := by
  rw [sw_eq, smw_eq]
  have h1 : (1 + (k : ℝ) ^ 2) ^ m ≤ (2 * bracket k ^ 2) ^ m :=
    pow_le_pow_left₀ (by positivity) (jb_sq_le_two_bracket_sq k) m
  have hb := bracket_one_le k
  have h2 : (bracket k ^ 2) ^ m ≤ (bracket k ^ (m + 1)) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    exact pow_le_pow_right₀ hb (by ring_nf; omega)
  calc (1 + (k : ℝ) ^ 2) ^ m ≤ (2 * bracket k ^ 2) ^ m := h1
    _ = 2 ^ m * (bracket k ^ 2) ^ m := by rw [mul_pow]
    _ ≤ 2 ^ m * (bracket k ^ (m + 1)) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem smw_neg (m : ℕ) (k : ℤ) : sobolevModeWeight (m : ℝ) (-k) = sobolevModeWeight (m : ℝ) k := by
  rw [smw_eq, smw_eq]; push_cast; ring

theorem sw_neg (s : ℕ) (k : ℤ) : scaleWeight (s : ℝ) (-k) = scaleWeight (s : ℝ) k := by
  rw [sw_eq, sw_eq]; unfold bracket; rw [Int.natAbs_neg]

theorem carrier_hasSum (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) :
    HasSum (fun k : ℤ => sobolevModeWeight (m : ℝ) k * ‖carrierCoe38 (m : ℝ) z k‖ ^ 2) (‖z‖ ^ 2) :=
  weightedHilbert_hasSum (sobolevModeWeight (m : ℝ)) (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from z)

/-! ### toPair -/

def pairFun (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) (j : Bool × ℤ) : ℂ :=
  (scaleWeight (m : ℝ) j.2 : ℂ) *
    (if j.1 then -carrierCoe38 (m : ℝ) z (-j.2) else -star (carrierCoe38 (m : ℝ) z j.2))

theorem pairFun_sq_le (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) (j : Bool × ℤ) :
    ‖pairFun m z j‖ ^ 2 ≤ (if j.1 then sobolevModeWeight (m : ℝ) (-j.2) * ‖carrierCoe38 (m : ℝ) z (-j.2)‖ ^ 2
      else sobolevModeWeight (m : ℝ) j.2 * ‖carrierCoe38 (m : ℝ) z j.2‖ ^ 2) := by
  unfold pairFun
  have hs := (show (0 : ℝ) ≤ scaleWeight (m : ℝ) j.2 by rw [sw_eq]; exact pow_nonneg (le_trans zero_le_one (bracket_one_le _)) _)
  rcases j with ⟨b, k⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs, norm_neg,
      norm_star, mul_pow]
    exact mul_le_mul_of_nonneg_right (sw_sq_le_smw m k) (sq_nonneg _)
  · simp only [↓reduceIte, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs, norm_neg, mul_pow]
    rw [← sw_neg] at *
    have := sw_sq_le_smw m (-k)
    rw [sw_neg] at this ⊢
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

theorem pairFun_summable (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) :
    Summable (fun j : Bool × ℤ => ‖pairFun m z j‖ ^ 2) ∧
      ∑' j : Bool × ℤ, ‖pairFun m z j‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
  have hz := carrier_hasSum m z
  have hneg : HasSum (fun k : ℤ => sobolevModeWeight (m : ℝ) (-k) * ‖carrierCoe38 (m : ℝ) z (-k)‖ ^ 2)
      (‖z‖ ^ 2) := by
    have := (Equiv.neg ℤ).hasSum_iff.2 hz
    simpa [Function.comp_def] using this
  set f : Bool × ℤ → ℝ := fun j => ‖pairFun m z j‖ ^ 2 with hf
  have hf0 : 0 ≤ f := fun j => sq_nonneg _
  have hT : ∀ k, f (true, k) ≤ sobolevModeWeight (m : ℝ) (-k) * ‖carrierCoe38 (m : ℝ) z (-k)‖ ^ 2 :=
    fun k => by simpa using pairFun_sq_le m z (true, k)
  have hF : ∀ k, f (false, k) ≤ sobolevModeWeight (m : ℝ) k * ‖carrierCoe38 (m : ℝ) z k‖ ^ 2 :=
    fun k => by simpa using pairFun_sq_le m z (false, k)
  have hsb : ∀ b : Bool, Summable (fun k : ℤ => f (b, k)) := by
    intro b
    cases b
    · exact Summable.of_nonneg_of_le (fun k => hf0 _) hF hz.summable
    · exact Summable.of_nonneg_of_le (fun k => hf0 _) hT hneg.summable
  have hs : Summable f := (summable_prod_of_nonneg hf0).2 ⟨hsb, (hasSum_fintype _).summable⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod' hsb, tsum_fintype, Fintype.sum_bool]
  have h1 : ∑' k : ℤ, f (true, k) ≤ ‖z‖ ^ 2 := by
    rw [← hneg.tsum_eq]; exact (hsb true).tsum_le_tsum hT hneg.summable
  have h2 : ∑' k : ℤ, f (false, k) ≤ ‖z‖ ^ 2 := by
    rw [← hz.tsum_eq]; exact (hsb false).tsum_le_tsum hF hz.summable
  linarith

theorem pairFun_mem (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) : Memℓp (pairFun m z) 2 := by
  refine memℓp_gen ?_
  refine (pairFun_summable m z).1.congr (fun j => ?_)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

def toPair (m : ℕ) : SobolevCarrier38 (m : ℝ) →L[ℝ] PairScale (m : ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun z => ⟨pairFun m z, pairFun_mem m z⟩
      map_add' := fun x y => by
        ext j
        simp only [pairFun, lp.coeFn_add, Pi.add_apply, carrierCoe38_add, star_add]
        split_ifs <;> ring
      map_smul' := fun c x => by
        ext j
        simp only [pairFun, lp.coeFn_smul, Pi.smul_apply, carrierCoe38_smul, RingHom.id_apply]
        rw [Complex.real_smul]
        split_ifs
        · ring
        · simp only [star_mul', Complex.star_def, Complex.conj_ofReal]; ring }
    (Real.sqrt 2) (fun z => by
      have h0 := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num)
        (⟨pairFun m z, pairFun_mem m z⟩ : PairScale (m : ℝ))
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h0
      have h2 : ‖(⟨pairFun m z, pairFun_mem m z⟩ : PairScale (m : ℝ))‖ ^ 2 ≤ (Real.sqrt 2 * ‖z‖) ^ 2 := by
        rw [h0, mul_pow, Real.sq_sqrt (by norm_num)]
        exact (pairFun_summable m z).2
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2)

theorem toPair_apply (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) (j : Bool × ℤ) :
    toPair m z j = pairFun m z j := rfl

/-! ### fromPair -/

def fromSeq (m : ℕ) (y : PairScale ((m + 1 : ℕ) : ℝ)) (n : ℤ) : ℂ :=
  y (true, n) / (scaleWeight ((m + 1 : ℕ) : ℝ) n : ℂ)

theorem fromSeq_sq_le (m : ℕ) (y : PairScale ((m + 1 : ℕ) : ℝ)) (n : ℤ) :
    sobolevModeWeight (m : ℝ) n * ‖fromSeq m y n‖ ^ 2 ≤ 2 ^ m * ‖y (true, n)‖ ^ 2 := by
  unfold fromSeq
  have hp : 0 < scaleWeight ((m + 1 : ℕ) : ℝ) n := by
    rw [sw_eq]; exact pow_pos (lt_of_lt_of_le one_pos (bracket_one_le _)) _
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le, div_pow]
  have h := smw_le_sw_succ_sq m n
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right h (sq_nonneg ‖y (true, n)‖)
  nlinarith

theorem fromSeq_fibre (m : ℕ) (y : PairScale ((m + 1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ => ‖y (true, n)‖ ^ 2) ∧ ∑' n : ℤ, ‖y (true, n)‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have hy := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) y
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hy
  have hinj : Function.Injective (fun n : ℤ => ((true, n) : Bool × ℤ)) := fun a b h => by simpa using h
  have hs := hy.summable.comp_injective hinj
  refine ⟨hs, ?_⟩
  rw [← hy.tsum_eq]
  exact hs.tsum_le_tsum_of_inj _ hinj (fun c _ => sq_nonneg _) (fun n => le_rfl) hy.summable

theorem fromSeq_mem (m : ℕ) (y : PairScale ((m + 1 : ℕ) : ℝ)) : fromSeq m y ∈ seqSobolev38 (m : ℝ) := by
  show Memℓp (weightedCoordinates (sobolevModeWeight (m : ℝ)) (fromSeq m y)) 2
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) (((fromSeq_fibre m y).1).mul_left (2 ^ m))
  rw [weightedCoordinates, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (sobolevModeWeight_pos _ _).le]
  exact fromSeq_sq_le m y n

def fromPair (m : ℕ) : PairScale ((m + 1 : ℕ) : ℝ) →L[ℝ] SobolevCarrier38 (m : ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun y => carrierMk38 (m : ℝ) (fromSeq m y) (fromSeq_mem m y)
      map_add' := fun x y => by
        apply carrierExt38
        funext n
        rw [carrierCoe38_add]
        simp only [carrierCoe38_mk, fromSeq, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := fun c x => by
        apply carrierExt38
        funext n
        rw [RingHom.id_apply, carrierCoe38_smul]
        simp only [carrierCoe38_mk, fromSeq, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
        ring }
    (Real.sqrt (2 ^ m)) (fun y => by
      have h0 := carrier_hasSum m (carrierMk38 (m : ℝ) (fromSeq m y) (fromSeq_mem m y))
      simp only [carrierCoe38_mk] at h0
      have h2 : ‖carrierMk38 (m : ℝ) (fromSeq m y) (fromSeq_mem m y)‖ ^ 2 ≤ (Real.sqrt (2 ^ m) * ‖y‖) ^ 2 := by
        rw [← h0.tsum_eq, mul_pow, Real.sq_sqrt (by positivity)]
        obtain ⟨hs, hle⟩ := fromSeq_fibre m y
        refine (h0.summable.tsum_le_tsum (fun n => fromSeq_sq_le m y n) (hs.mul_left _)).trans ?_
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hle (by positivity)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2)

theorem fromPair_coe (m : ℕ) (y : PairScale ((m + 1 : ℕ) : ℝ)) (n : ℤ) :
    carrierCoe38 (m : ℝ) (fromPair m y) n = y (true, n) / (scaleWeight ((m + 1 : ℕ) : ℝ) n : ℂ) := rfl

end
end NlsGge.ThirdConsultation.G6024S
