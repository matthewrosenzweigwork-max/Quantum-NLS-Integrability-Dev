import Mathlib
import NlsGge.GK38.GradFundamentalL2
import NlsGge.ThirdConsultation.G1.G1098PairCLM
import NlsGge.Atomic.G5.G5005Host

                                                                                 
                                                                                                    
                                       
                                                                                       
                                            
                                                                                                             
                                                                                                          
                                                                                               
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G5005Support1
noncomputable section

theorem pgn_nonneg (v : PotPair) : 0 ≤ pairGradientNorm v := Real.sqrt_nonneg _

theorem pgn_sq (v : PotPair) : pairGradientNorm v ^ 2 = ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem pgn_smul (c : ℂ) (v : PotPair) : pairGradientNorm (c • v) = ‖c‖ * pairGradientNorm v := by
  unfold pairGradientNorm
  have h : ‖(c • v).1‖ ^ 2 + ‖(c • v).2‖ ^ 2 = ‖c‖ ^ 2 * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) := by
    simp only [Prod.smul_fst, Prod.smul_snd, norm_smul]; ring
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem sq_norm_sub_le (a b : PhysicalL2) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem sq_norm_add_le (a b : PhysicalL2) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem pgn_sub_sq (v w : PotPair) :
    pairGradientNorm (v - w) ^ 2 ≤ 2 * pairGradientNorm v ^ 2 + 2 * pairGradientNorm w ^ 2 := by
  rw [pgn_sq, pgn_sq, pgn_sq]
  simp only [Prod.fst_sub, Prod.snd_sub]
  nlinarith [sq_norm_sub_le v.1 w.1, sq_norm_sub_le v.2 w.2]

theorem pgn_add_sq (v w : PotPair) :
    pairGradientNorm (v + w) ^ 2 ≤ 2 * pairGradientNorm v ^ 2 + 2 * pairGradientNorm w ^ 2 := by
  rw [pgn_sq, pgn_sq, pgn_sq]
  simp only [Prod.fst_add, Prod.snd_add]
  nlinarith [sq_norm_add_le v.1 w.1, sq_norm_add_le v.2 w.2]

theorem memlp_of_sq_summable {f : ℤ → ℝ} (h : Summable (fun n => f n ^ 2)) : Memℓp f 2 := by
  refine (memℓp_gen_iff (by simp)).mpr ?_
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- Finite sums of squared L2 norms of kernel classes are bounded by the integrated fixed-time bound. -/
theorem sum_pgn_sq_le (g : ℤ → PairKernelCont38) {B : ℝ} (S : Finset ℤ)
    (h : ∀ t : Set.Icc (0 : ℝ) 1, ∑ n ∈ S, (‖g n t 0‖ ^ 2 + ‖g n t 1‖ ^ 2) ≤ B) :
    ∑ n ∈ S, pairGradientNorm (pairKernelL2Class38 (g n)) ^ 2 ≤ B := by
  have hc : ∀ n, Continuous (fun s : ℝ =>
      ‖pairKernelExt38 (g n) s 0‖ ^ 2 + ‖pairKernelExt38 (g n) s 1‖ ^ 2) := fun n =>
    ((((continuous_apply 0).comp (continuous_pairKernelExt38 (g n))).norm.pow 2).add
      (((continuous_apply 1).comp (continuous_pairKernelExt38 (g n))).norm.pow 2))
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∑ n ∈ S,
      (‖pairKernelExt38 (g n) s 0‖ ^ 2 + ‖pairKernelExt38 (g n) s 1‖ ^ 2) ≤ B := by
    intro s hs
    have hev : ∀ n, pairKernelExt38 (g n) s = g n ⟨s, hs⟩ := fun n => pairKernelExt38_of_mem _ hs
    simp only [hev]
    exact h ⟨s, hs⟩
  calc ∑ n ∈ S, pairGradientNorm (pairKernelL2Class38 (g n)) ^ 2
      = ∑ n ∈ S, ∫ s in (0 : ℝ)..1,
          (‖pairKernelExt38 (g n) s 0‖ ^ 2 + ‖pairKernelExt38 (g n) s 1‖ ^ 2) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [pgn_sq]
        exact potNormSq_pairKernelL2Class38 (g n)
    _ = ∫ s in (0 : ℝ)..1, ∑ n ∈ S,
          (‖pairKernelExt38 (g n) s 0‖ ^ 2 + ‖pairKernelExt38 (g n) s 1‖ ^ 2) :=
        (intervalIntegral.integral_finsetSum (fun n _ => (hc n).intervalIntegrable 0 1)).symm
    _ ≤ ∫ _ in (0 : ℝ)..1, B :=
        intervalIntegral.integral_mono_on zero_le_one
          (continuous_finsetSum S (fun n _ => hc n) |>.intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1) hpt
    _ = B := by simp

/-- Outside a finite exceptional set the fixed-time finite-sum bound gives a square-summable sequence of norms. -/
theorem summable_pgn_sq (g : ℤ → PairKernelCont38) {B : ℝ} (F : Finset ℤ)
    (h : ∀ t : Set.Icc (0 : ℝ) 1, ∀ S : Finset ℤ, (∀ n ∈ S, n ∉ F) →
      ∑ n ∈ S, (‖g n t 0‖ ^ 2 + ‖g n t 1‖ ^ 2) ≤ B) :
    Summable (fun n => pairGradientNorm (pairKernelL2Class38 (g n)) ^ 2) := by
  refine summable_of_sum_le (c := B + ∑ n ∈ F, pairGradientNorm (pairKernelL2Class38 (g n)) ^ 2)
    (fun n => sq_nonneg _) (fun T => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not T (fun n => n ∉ F)]
  have h1 : ∑ n ∈ T.filter (fun n => n ∉ F), pairGradientNorm (pairKernelL2Class38 (g n)) ^ 2 ≤ B :=
    sum_pgn_sq_le g _ (fun t => h t _ (fun n hn => (Finset.mem_filter.mp hn).2))
  have h2 : ∑ n ∈ T.filter (fun n => ¬ n ∉ F), pairGradientNorm (pairKernelL2Class38 (g n)) ^ 2 ≤
      ∑ n ∈ F, pairGradientNorm (pairKernelL2Class38 (g n)) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => sq_nonneg _)
    intro n hn
    have := (Finset.mem_filter.mp hn).2
    simpa using this
  linarith

/-! ### Fourier kernels -/

def fkE (n : ℤ) : PairKernelCont38 :=
  ⟨fun t => ![Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I),
              Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I))], by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop⟩

def fkD (n : ℤ) : PairKernelCont38 :=
  ⟨fun t => ![-Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I),
              Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I))], by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop⟩

theorem fourier_liftIoc_apply (m : ℤ) (c : ℂ) (x : AddCircle (1 : ℝ)) :
    AddCircle.liftIoc 1 0 (fun s : ℝ => c * Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * (s : ℂ) * Complex.I)) x =
      c * fourier (T := (1 : ℝ)) m x := by
  obtain ⟨y, hmem, rfl⟩ : ∃ y : ℝ, y ∈ Ioc (0 : ℝ) (0 + 1) ∧ (y : AddCircle (1 : ℝ)) = x :=
    ⟨_, (AddCircle.equivIoc (1 : ℝ) 0 x).2, AddCircle.coe_equivIoc⟩
  rw [AddCircle.liftIoc_coe_apply hmem, fourier_coe_apply]
  congr 2
  push_cast
  ring_nf

/-- The period-one Fourier monomial as an honest `PhysicalL2` element. -/
def FL (m : ℤ) : PhysicalL2 := fourierLp (T := (1 : ℝ)) 2 m

/-- A kernel agreeing everywhere on `(0,1]` with `c * e^{2 pi i m s}` has L2 class `c • FL m`. -/
theorem intervalKernel_eq_fourier (m : ℤ) (c : ℂ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hk : ∀ s ∈ Ioc (0 : ℝ) 1,
      f s = c * Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * (s : ℂ) * Complex.I)) :
    intervalKernelL2Class38 f hf = c • FL m := by
  apply MeasureTheory.Lp.ext
  have h1 : ∀ᵐ x ∂spatialMeasure,
      intervalKernelL2Class38 f hf x = AddCircle.liftIoc 1 0 f x :=
    (memLp_intervalKernelLift38 f hf).coeFn_toLp
  have h2 : ∀ᵐ x ∂spatialMeasure, (FL m : PhysicalCircle → ℂ) x = fourier (T := (1 : ℝ)) m x :=
    coeFn_fourierLp (T := (1 : ℝ)) 2 m
  have h3 : ∀ᵐ x ∂spatialMeasure,
      (c • FL m : PhysicalL2) x = c * (FL m : PhysicalCircle → ℂ) x :=
    MeasureTheory.Lp.coeFn_smul c (FL m)
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  have key : AddCircle.liftIoc 1 0 f x = c * fourier (T := (1 : ℝ)) m x := by
    have : AddCircle.liftIoc 1 0 f x =
        AddCircle.liftIoc 1 0 (fun s : ℝ =>
          c * Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * (s : ℂ) * Complex.I)) x := by
      obtain ⟨y, hmem, rfl⟩ : ∃ y : ℝ, y ∈ Ioc (0 : ℝ) (0 + 1) ∧ (y : AddCircle (1 : ℝ)) = x :=
        ⟨_, (AddCircle.equivIoc (1 : ℝ) 0 x).2, AddCircle.coe_equivIoc⟩
      rw [AddCircle.liftIoc_coe_apply hmem, AddCircle.liftIoc_coe_apply hmem]
      exact hk y (by simpa using hmem)
    exact this.trans (fourier_liftIoc_apply m c x)
  exact e1.trans (key.trans ((congrArg (fun y => c * y) e2.symm).trans e3.symm))

theorem fkE_apply0 (n : ℤ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    pairKernelExt38 (fkE n) s 0 =
      Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (s : ℂ) * Complex.I) := by
  rw [pairKernelExt38_of_mem _ hs]; rfl

theorem fkE_apply1 (n : ℤ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    pairKernelExt38 (fkE n) s 1 =
      Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (s : ℂ) * Complex.I)) := by
  rw [pairKernelExt38_of_mem _ hs]; rfl

theorem fkD_apply0 (n : ℤ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    pairKernelExt38 (fkD n) s 0 =
      -Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (s : ℂ) * Complex.I) := by
  rw [pairKernelExt38_of_mem _ hs]; rfl

theorem fkD_apply1 (n : ℤ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    pairKernelExt38 (fkD n) s 1 =
      Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (s : ℂ) * Complex.I)) := by
  rw [pairKernelExt38_of_mem _ hs]; rfl

theorem fourierMode_one (n : ℤ) : fourierMode 1 n = (0, FL (-n)) := by
  simp [fourierMode, FL]

theorem fourierMode_neg_one (n : ℤ) : fourierMode (-1) n = (FL n, 0) := by
  simp [fourierMode, FL]

theorem interval_neg_mode (n : ℤ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hk : ∀ s ∈ Ioc (0 : ℝ) 1, f s = Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (s : ℂ) * Complex.I))) :
    intervalKernelL2Class38 f hf = FL (-n) := by
  have h := intervalKernel_eq_fourier (-n) 1 f hf (fun s hs => by
    rw [hk s hs, one_mul]
    congr 1
    push_cast
    ring)
  rw [h, one_smul]

theorem class_fkE (n : ℤ) : pairKernelL2Class38 (fkE n) = fourierMode 1 n + fourierMode (-1) n := by
  rw [fourierMode_one, fourierMode_neg_one, Prod.mk_add_mk, zero_add, add_zero]
  unfold pairKernelL2Class38
  congr 1
  · have h := intervalKernel_eq_fourier n 1 (fun s => pairKernelExt38 (fkE n) s 0)
      (memLp_pairKernelExt38 (fkE n) 0) (fun s hs => by
        rw [fkE_apply0 n ⟨hs.1.le, hs.2⟩, one_mul])
    rw [h, one_smul]
  · exact interval_neg_mode n _ (memLp_pairKernelExt38 (fkE n) 1) (fun s hs => fkE_apply1 n ⟨hs.1.le, hs.2⟩)

theorem class_fkD (n : ℤ) : pairKernelL2Class38 (fkD n) = fourierMode 1 n - fourierMode (-1) n := by
  rw [fourierMode_one, fourierMode_neg_one, Prod.mk_sub_mk, zero_sub, sub_zero]
  unfold pairKernelL2Class38
  congr 1
  · have h := intervalKernel_eq_fourier n (-1) (fun s => pairKernelExt38 (fkD n) s 0)
      (memLp_pairKernelExt38 (fkD n) 0) (fun s hs => by
        rw [fkD_apply0 n ⟨hs.1.le, hs.2⟩]; ring)
    rw [h, neg_one_smul]
  · exact interval_neg_mode n _ (memLp_pairKernelExt38 (fkD n) 1) (fun s hs => fkD_apply1 n ⟨hs.1.le, hs.2⟩)

end
end NlsGge.ThirdConsultation.G5005Support1
