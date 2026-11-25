import QuantumNLS.RB7Commute
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Finite Sobolev moments give finite differentiability of the rotation in all its times. -/

set_option autoImplicit false
noncomputable section

open scoped ContDiff NNReal
open Set

namespace QuantumNLS.Def024LossR32m

open QuantumNLS.Fourier Sobolev Sobolev.PosWeight RB7

private abbrev base (L : ℝ) (n : ℤ) : ℝ := 1 + |2 * Real.pi * (n : ℝ) / L|

private lemma base_pos (L : ℝ) (n : ℤ) : 0 < base L n :=
  zero_lt_one.trans_le (one_le_x L n)

private lemma sqrt_weight (L s : ℝ) (n : ℤ) :
    Real.sqrt (sobolevWeight L s n) = base L n ^ s := by
  rw [sobolevWeight_eq, Real.sqrt_eq_rpow, ← Real.rpow_mul (base_pos L n).le]
  congr 1
  ring

private lemma phase_smooth : ContDiff ℝ ∞ (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

private lemma phase_derivative_norm (j : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ))) x‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [show (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ))) =
    (fun y : ℝ => 1 * Complex.exp (Complex.I * (y : ℂ))) from by simp,
    iteratedDeriv_expterm, one_mul, norm_mul, norm_pow, Complex.norm_I, one_pow]
  rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]

variable {ι : Type} [Fintype ι]

private def timeAngle {V : PosWeight} (D : FreqData V ι) (z : WSeq V) (n : ℤ) :
    (ι → ℝ) →L[ℝ] ℝ :=
  -(∑ r : ι, (D.Ω r z n) • ContinuousLinearMap.proj r)

private lemma timeAngle_apply {V : PosWeight} (D : FreqData V ι) (z : WSeq V) (n : ℤ)
    (t : ι → ℝ) : timeAngle D z n t = angle D t z n := by
  simp [timeAngle, angle, mul_comm]

private lemma timeAngle_norm {V : PosWeight} (D : FreqData V ι) (z : WSeq V) (n : ℤ) :
    ‖timeAngle D z n‖ ≤ ∑ r, |D.Ω r z n| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun r _ => abs_nonneg _)
  intro t
  rw [timeAngle_apply, angle, norm_neg, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm t r) (abs_nonneg _)

private abbrev Seq2 := lp (fun _ : ℤ => ℂ) 2

private def singleMul (n : ℤ) (c : ℂ) : ℂ →L[ℝ] Seq2 :=
  ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).comp
    (c • ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ

private def phaseTerm (n : ℤ) (c : ℂ) (A : (ι → ℝ) →L[ℝ] ℝ) : (ι → ℝ) → Seq2 :=
  fun t => lp.single 2 n (c * Complex.exp (Complex.I * (A t : ℂ)))

private lemma phaseTerm_norm (n : ℤ) (c : ℂ) (A : (ι → ℝ) →L[ℝ] ℝ) (j : ℕ) (t : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (phaseTerm n c A) t‖ ≤ ‖c‖ * ‖A‖ ^ j := by
  let M := singleMul n c
  have hM : ‖M‖ ≤ ‖c‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    change ‖lp.single (E := fun _ : ℤ => ℂ) 2 n (c * u)‖ ≤ ‖c‖ * ‖u‖
    rw [lp.norm_single (by norm_num), norm_mul]
  let f : ℝ → ℂ := fun x => Complex.exp (Complex.I * (x : ℂ))
  have hf : ContDiff ℝ ∞ f := phase_smooth
  change ‖iteratedFDeriv ℝ j (fun s => M ((f ∘ A) s)) t‖ ≤ _
  calc
    _ ≤ ‖M‖ * ‖iteratedFDeriv ℝ j (f ∘ A) t‖ :=
      M.norm_iteratedFDeriv_comp_left (hf.comp A.contDiff).contDiffAt (by simp)
    _ ≤ ‖c‖ * ‖A‖ ^ j := by
      rw [A.iteratedFDeriv_comp_right hf t (by simp)]
      refine mul_le_mul hM ?_ (norm_nonneg _) (norm_nonneg _)
      simpa [f, phase_derivative_norm] using
        (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
          (iteratedFDeriv ℝ j f (A t)) (fun _ => A))

variable {L : ℝ} [Fact (0 < L)]

/-- A fixed datum can be rotated in all time coordinates with `m` derivatives at level `a`
when the finitely many frequency moments at `a+2` are finite. -/
theorem finite_rotation_smooth {a : ℝ} (D : FreqData (def002 L a) ι) (z : h02 L a)
    (P : ℤ → ℝ) (hP : ∀ n, 0 ≤ P n)
    {K : ℝ} (hK : 0 ≤ K) (hΩ : ∀ n, (∑ r, |D.Ω r z n|) ≤ K * P n) (m : ℕ)
    (hz : ∀ j ≤ m, Summable fun n => sobolevWeight L (a + 2) n * P n ^ (2 * j) * ‖z.val n‖ ^ 2) :
    ContDiff ℝ (m : ℕ∞) (fun t => flow D t z) := by
  let J := toL2ᵢ (def002 L a)
  let c : ℤ → ℂ := fun n => (Real.sqrt (sobolevWeight L a n) : ℂ) * z.val n
  let A := timeAngle D z
  let v : ℕ → ℤ → ℝ := fun j n => ‖c n‖ * (K * P n) ^ j
  have hv : ∀ j ≤ m, Summable (v j) := by
    intro j hj
    let W : ℝ := ∑' n, sobolevWeight L (a + 2) n * P n ^ (2 * j) * ‖z.val n‖ ^ 2
    have hnon (n : ℤ) : 0 ≤ sobolevWeight L (a + 2) n * P n ^ (2 * j) * ‖z.val n‖ ^ 2 := by
      have := (sobolevWeight_pos L (a + 2) n).le
      have := hP n
      positivity
    refine Summable.of_nonneg_of_le (fun n => by have := hP n; dsimp [v]; positivity) ?_
      ((RB7H.summable_base_rpow (L := L) (p := 2) one_lt_two).mul_left (K ^ j * Real.sqrt W))
    intro n
    have hpoint : (base L n ^ (a + 2) * P n ^ j * ‖z.val n‖) ^ 2 ≤ W := by
      have ht := (hz j hj).le_tsum n (fun i _ => hnon i)
      convert ht using 1
      rw [mul_pow, mul_pow, ← pow_mul, mul_comm j 2, ← sqrt_weight, Real.sq_sqrt (sobolevWeight_pos L _ _).le]
    have hroot : base L n ^ (a + 2) * P n ^ j * ‖z.val n‖ ≤ Real.sqrt W := by
      have hW : 0 ≤ W := tsum_nonneg hnon
      have hs : 0 ≤ base L n ^ (a + 2) * P n ^ j * ‖z.val n‖ := by
        have := hP n
        have := (base_pos L n).le
        positivity
      exact (pow_le_pow_iff_left₀ hs (Real.sqrt_nonneg W) two_ne_zero).mp
        (by simpa only [Real.sq_sqrt hW] using hpoint)
    have hb := base_pos L n
    have hadd : base L n ^ a = base L n ^ (a + 2) * base L n ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hb]
      congr 1
      ring
    dsimp [v, c]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), sqrt_weight,
      mul_pow, hadd]
    change _ ≤ (K ^ j * Real.sqrt W) * base L n ^ (-(2 : ℝ))
    calc
      _ = (base L n ^ (a + 2) * P n ^ j * ‖z.val n‖) *
          (K ^ j * base L n ^ (-(2 : ℝ))) := by ring
      _ ≤ _ := by
        simpa only [mul_left_comm, mul_comm, mul_assoc] using
          mul_le_mul_of_nonneg_right hroot (show 0 ≤ K ^ j * base L n ^ (-(2 : ℝ)) by positivity)
  have hsum : ContDiff ℝ (m : ℕ∞) (fun t => ∑' n, phaseTerm n (c n) (A n) t) := by
    apply contDiff_tsum (v := v)
    · intro n
      exact (singleMul n (c n)).contDiff.comp
        (phase_smooth.of_le (by simp) |>.comp (A n).contDiff)
    · intro j hj
      exact hv j (by exact_mod_cast hj)
    · intro j n t _
      refine (phaseTerm_norm n (c n) (A n) j t).trans ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) ((timeAngle_norm D z n).trans (hΩ n)) j) (norm_nonneg _)
  have hval (t : ι → ℝ) (n : ℤ) :
      (J (flow D t z) : Seq2) n = c n * Complex.exp (Complex.I * (A n t : ℂ)) := by
    change (toL2 (def002 L a) (flow D t z) : Seq2) n = _
    rw [toL2_apply, flow_val]
    change (Real.sqrt (sobolevWeight L a n) : ℂ) * _ = _
    rw [show A n t = angle D t z n from timeAngle_apply D z n t, mul_comm Complex.I]
    dsimp [c]
    ring
  have heq (t : ι → ℝ) : (∑' n, phaseTerm n (c n) (A n) t) = J (flow D t z) := by
    have hs := lp.hasSum_single (p := 2) (by norm_num) (J (flow D t z))
    have hterms : (fun n => lp.single 2 n ((J (flow D t z) : Seq2) n)) =
        fun n => phaseTerm n (c n) (A n) t := by
      funext n
      rw [hval, phaseTerm]
    rw [← hterms]
    exact hs.tsum_eq
  have h : (fun t => flow D t z) = fun t => J.symm (∑' n, phaseTerm n (c n) (A n) t) := by
    funext t
    rw [heq, J.symm_apply_apply]
  rw [h]
  exact (J.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hsum

omit [Fact (0 < L)] in
/-- Finite-level version of the moment estimate in `RB7.hzP_of_Hinf`. -/
theorem finite_moment (S : ι → ℝ) (hS : ∀ r, 0 ≤ S r) (a : ℝ)
    (z : ℤ → ℂ) (j : ℕ) (hz : MemHs L (a + (2 * j) * (∑ r, S r)) z) :
    Summable fun n => sobolevWeight L a n * (∑ r, sobolevWeight L (S r) n) ^ (2 * j) * ‖z n‖ ^ 2 := by
  let B := ∑ r, S r
  let c : ℝ := Fintype.card ι
  have hB (r : ι) : S r ≤ B := Finset.single_le_sum (f := S) (fun r _ => hS r) (Finset.mem_univ r)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hz.mul_left (c ^ (2 * j)))
  · have := (sobolevWeight_pos L a n).le
    have : 0 ≤ ∑ r, sobolevWeight L (S r) n := Finset.sum_nonneg fun r _ => (sobolevWeight_pos L _ _).le
    positivity
  · have hP : (∑ r, sobolevWeight L (S r) n) ≤ c * sobolevWeight L B n := by
      calc
        _ ≤ ∑ _r : ι, sobolevWeight L B n := Finset.sum_le_sum fun r _ => sobolevWeight_le L (hB r) n
        _ = _ := by simp [c]
    have hP0 : 0 ≤ ∑ r, sobolevWeight L (S r) n := Finset.sum_nonneg fun r _ => (sobolevWeight_pos L _ _).le
    have hw := (sobolevWeight_pos L a n).le
    calc
      _ ≤ sobolevWeight L a n * (c * sobolevWeight L B n) ^ (2 * j) * ‖z n‖ ^ 2 := by
        gcongr
      _ = _ := by
        change _ = c ^ (2 * j) * (sobolevWeight L (a + (2 * (j : ℝ)) * B) n * ‖z n‖ ^ 2)
        rw [mul_pow, sobolevWeight_pow, Nat.cast_mul, Nat.cast_ofNat, ← sobolevWeight_add]
        ring

end QuantumNLS.Def024LossR32m

#print axioms QuantumNLS.Def024LossR32m.finite_rotation_smooth
#print axioms QuantumNLS.Def024LossR32m.finite_moment
