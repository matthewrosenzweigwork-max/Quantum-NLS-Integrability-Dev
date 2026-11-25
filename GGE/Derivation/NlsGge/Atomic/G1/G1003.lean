import NlsGge.Atomic.Volterra
import NlsGge.Atomic.G1.G1001
import NlsGge.Atomic.G1.G1002
import Mathlib.Tactic

/-! A local-L² factorial bound for the literal free-kernel homogeneous Volterra
terms. The matrix coefficient and the recursion are imported from the shared
source-aligned interface. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.L2Operator Interval

namespace NlsGge.Atomic.G1

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.Pilot

private def pairSqDensity38 (a b : ℝ → ℂ) (s : ℝ) : ℝ :=
  ‖a s‖ ^ 2 + ‖b s‖ ^ 2

private def pairDensity38 (a b : ℝ → ℂ) (s : ℝ) : ℝ :=
  Real.sqrt (pairSqDensity38 a b s)

private theorem pairSqDensity38_nonneg (a b : ℝ → ℂ) (s : ℝ) :
    0 ≤ pairSqDensity38 a b s := by
  simp only [pairSqDensity38]
  positivity

private theorem pairDensity38_nonneg (a b : ℝ → ℂ) (s : ℝ) :
    0 ≤ pairDensity38 a b s := Real.sqrt_nonneg _

private theorem pairDensity38_sq (a b : ℝ → ℂ) (s : ℝ) :
    pairDensity38 a b s ^ 2 = pairSqDensity38 a b s := by
  rw [pairDensity38, Real.sq_sqrt (pairSqDensity38_nonneg a b s)]

private theorem pairDensity38_aestronglyMeasurable (a b : ℝ → ℂ)
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (pairDensity38 a b) volume := by
  have hq : AEStronglyMeasurable (pairSqDensity38 a b) volume := by
    unfold pairSqDensity38
    exact (ha.norm.pow 2).add (hb.norm.pow 2)
  exact Real.continuous_sqrt.comp_aestronglyMeasurable hq

private theorem intervalIntegrable_pairDensity38 (a b : ℝ → ℂ) {t : ℝ}
    (ht : 0 ≤ t) (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hsq : IntervalIntegrable (pairSqDensity38 a b) volume 0 t) :
    IntervalIntegrable (pairDensity38 a b) volume 0 t := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t)
  have hqInt : Integrable (pairSqDensity38 a b) μ := by
    change Integrable (pairSqDensity38 a b) (volume.restrict (Set.Ioc (0 : ℝ) t))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hsq
  have hμfinite : μ Set.univ < ⊤ := by
    change (volume.restrict (Set.Ioc (0 : ℝ) t)) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    rw [Real.volume_Ioc]
    simp only [sub_zero]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure μ := ⟨hμfinite⟩
  have hfmeas : AEStronglyMeasurable (pairDensity38 a b) μ :=
    (pairDensity38_aestronglyMeasurable a b ha hb).restrict
  have hfSqInt : Integrable (fun s => ‖pairDensity38 a b s‖ ^ 2) μ := by
    convert hqInt using 1
    funext s
    rw [Real.norm_eq_abs, abs_of_nonneg (pairDensity38_nonneg a b s),
      pairDensity38_sq]
  have hfMem : MemLp (pairDensity38 a b) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hfmeas).2 hfSqInt
  have hfMemOne : MemLp (pairDensity38 a b) 1 μ :=
    hfMem.mono_exponent (by norm_num)
  have hfInt : Integrable (pairDensity38 a b) μ :=
    memLp_one_iff_integrable.mp hfMemOne
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hfInt

private theorem integral_pairDensity38_le (a b : ℝ → ℂ) {t : ℝ}
    (ht : 0 ≤ t) (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hsq : IntervalIntegrable (pairSqDensity38 a b) volume 0 t) :
    (∫ s in (0 : ℝ)..t, pairDensity38 a b s) ≤
      Real.sqrt t * pairL2NormOn38 a b t := by
  let g : ℝ → ℂ := fun s => (pairDensity38 a b s : ℂ)
  have hgmeas : AEStronglyMeasurable g volume := by
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (pairDensity38_aestronglyMeasurable a b ha hb)
  have hgsq : IntervalIntegrable (fun s => ‖g s‖ ^ 2) volume 0 t := by
    convert hsq using 1
    funext s
    simp [g, Complex.norm_real, abs_of_nonneg (pairDensity38_nonneg a b s),
      pairDensity38_sq, pairSqDensity38]
  have hcs := NlsGge.GK38.integral_norm_le_sqrt_mul ht hgmeas hgsq
  have hIntegralSq : (∫ s in (0 : ℝ)..t, ‖g s‖ ^ 2) =
      ∫ s in (0 : ℝ)..t, pairSqDensity38 a b s := by
    apply intervalIntegral.integral_congr
    intro s hs
    simp [g, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pairDensity38_nonneg a b s), pairDensity38_sq]
  have hNormInt : (∫ s in (0 : ℝ)..t, pairDensity38 a b s) =
      ∫ s in (0 : ℝ)..t, ‖g s‖ := by
    apply intervalIntegral.integral_congr
    intro s hs
    simp [g, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pairDensity38_nonneg a b s)]
  rw [← hNormInt, hIntegralSq] at hcs
  simpa [pairL2NormOn38, pairSqDensity38] using hcs

private theorem freeDiagonalEntry_norm_le (z : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (i : Fin 2) :
    ‖freeZsFundamentalComplex z r i i‖ ≤ Real.exp (|z.im| * r) := by
  have hord : OrderedSimplex r [] := ⟨hr, trivial⟩
  have h := freeSimplexPropagator_norm_le (z := z) (t := r) (ts := []) hord
  have h' : ‖freeZsFundamentalComplex z r‖ ≤ Real.exp (|z.im| * r) := by
    simpa [freeSimplexPropagator, alternatingPhase, alternatingTail] using h
  rw [freeZsFundamentalComplex, freeDiagonalCandidate, Matrix.l2_opNorm_diagonal] at h'
  have hcoord := (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mp h' i
  change ‖freeDiagonalCandidate z r i i‖ ≤ _
  simpa [freeDiagonalCandidate, Matrix.diagonal] using hcoord

private theorem norm_potential_entry_le_density (a b : ℝ → ℂ) (s : ℝ)
    (i j : Fin 2) :
    ‖rawPotCoeff38 a b s i j‖ ≤ pairDensity38 a b s := by
  have hA := Real.sqrt_le_sqrt (show ‖a s‖ ^ 2 ≤ pairSqDensity38 a b s by
    dsimp [pairSqDensity38]
    exact le_add_of_nonneg_right (sq_nonneg ‖b s‖))
  have hB := Real.sqrt_le_sqrt (show ‖b s‖ ^ 2 ≤ pairSqDensity38 a b s by
    dsimp [pairSqDensity38]
    exact le_add_of_nonneg_left (sq_nonneg ‖a s‖))
  have hAnorm : ‖a s‖ ≤ pairDensity38 a b s := by
    calc
      ‖a s‖ = Real.sqrt (‖a s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := hA
  have hBnorm : ‖b s‖ ≤ pairDensity38 a b s := by
    calc
      ‖b s‖ = Real.sqrt (‖b s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := hB
  fin_cases i <;> fin_cases j <;>
    simp [rawPotCoeff38, Complex.norm_mul, hAnorm, hBnorm,
      pairDensity38_nonneg]

private def otherFin2 (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

private theorem otherFin2_ne (i : Fin 2) : otherFin2 i ≠ i := by
  fin_cases i <;> simp [otherFin2]

private theorem otherFin2_otherFin2 (i : Fin 2) : otherFin2 (otherFin2 i) = i := by
  fin_cases i <;> simp [otherFin2]

private theorem otherFin2_eq_of_ne {i j : Fin 2} (hij : i ≠ j) : otherFin2 i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [otherFin2]

private theorem volterra_integrand_entry (a b : ℝ → ℂ) (z : ℂ) (n : ℕ)
    (t s : ℝ) (i j : Fin 2) :
    (freeZsFundamentalComplex z (t - s) * rawPotCoeff38 a b s *
      freeKernelVolterraTerm38 a b z n s) i j =
      freeZsFundamentalComplex z (t - s) i i *
        rawPotCoeff38 a b s i (otherFin2 i) *
          freeKernelVolterraTerm38 a b z n s (otherFin2 i) j := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, otherFin2, rawPotCoeff38,
      freeZsFundamentalComplex, freeDiagonalCandidate]

private theorem freeE_mul_apply_local (z : ℂ) (t : ℝ) (X : PairMat38)
    (i j : Fin 2) :
    (freeE z t * X) i j = freeE z t i i * X i j := by
  fin_cases i <;> fin_cases j <;>
    simp [freeE, Matrix.mul_apply, Fin.sum_univ_two]

private theorem norm_first_component_le_density (a b : ℝ → ℂ) (s : ℝ) :
    ‖a s‖ ≤ pairDensity38 a b s := by
  have hq : ‖a s‖ ^ 2 ≤ pairSqDensity38 a b s := by
    dsimp [pairSqDensity38]
    exact le_add_of_nonneg_right (sq_nonneg ‖b s‖)
  calc
    ‖a s‖ = Real.sqrt (‖a s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (pairSqDensity38 a b s) := Real.sqrt_le_sqrt hq
    _ = pairDensity38 a b s := rfl

private theorem norm_second_component_le_density (a b : ℝ → ℂ) (s : ℝ) :
    ‖b s‖ ≤ pairDensity38 a b s := by
  have hq : ‖b s‖ ^ 2 ≤ pairSqDensity38 a b s := by
    dsimp [pairSqDensity38]
    exact le_add_of_nonneg_left (sq_nonneg ‖a s‖)
  calc
    ‖b s‖ = Real.sqrt (‖b s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (pairSqDensity38 a b s) := Real.sqrt_le_sqrt hq
    _ = pairDensity38 a b s := rfl

private theorem intervalIntegrable_rawPotCoeff38 (a b : ℝ → ℂ) {t : ℝ}
    (ht : 0 ≤ t) (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hsq : IntervalIntegrable (pairSqDensity38 a b) volume 0 t) (i j : Fin 2) :
    IntervalIntegrable (fun s => rawPotCoeff38 a b s i j) volume 0 t := by
  have hf : IntervalIntegrable (pairDensity38 a b) volume 0 t :=
    intervalIntegrable_pairDensity38 a b ht ha hb hsq
  have haInt : IntervalIntegrable a volume 0 t := by
    apply hf.mono_fun' ha.restrict
    exact Filter.Eventually.of_forall fun s => norm_first_component_le_density a b s
  have hbInt : IntervalIntegrable b volume 0 t := by
    apply hf.mono_fun' hb.restrict
    exact Filter.Eventually.of_forall fun s => norm_second_component_le_density a b s
  fin_cases i <;> fin_cases j
  · simpa [rawPotCoeff38] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 t)
  · simpa [rawPotCoeff38] using haInt.const_mul Complex.I
  · simpa [rawPotCoeff38, neg_mul] using hbInt.const_mul (-Complex.I)
  · simpa [rawPotCoeff38] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 t)

private def freeKernelVolterraIntegrand38 (a b : ℝ → ℂ) (z : ℂ) (n : ℕ)
    (u s : ℝ) : PairMat38 :=
  freeZsFundamentalComplex z (u - s) * rawPotCoeff38 a b s *
    freeKernelVolterraTerm38 a b z n s

private theorem continuous_freeZs_entry38 (z : ℂ) (f : ℝ → ℝ)
    (hf : Continuous f) (i j : Fin 2) :
    Continuous (fun x => freeZsFundamentalComplex z (f x) i j) := by
  have heq : (fun x => freeZsFundamentalComplex z (f x) i j) =
      fun x => freeE z (f x) i j := by
    funext x
    rw [← freeE_eq]
  rw [heq]
  exact (continuous_apply j).comp
    ((continuous_apply i).comp ((continuous_freeE z).comp hf))

private theorem intervalIntegrable_freeKernelVolterraIntegrand38
    (a b : ℝ → ℂ) (z : ℂ) (n : ℕ) {T v : ℝ} (hT : 0 ≤ T)
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hsq : IntervalIntegrable (pairSqDensity38 a b) volume 0 T)
    (hterm : ∀ i j : Fin 2,
      ContinuousOn (fun s => freeKernelVolterraTerm38 a b z n s i j)
        (Set.Icc (0 : ℝ) T))
    (hv : v ∈ Set.Icc (0 : ℝ) T) (u : ℝ) (i j : Fin 2) :
    IntervalIntegrable
      (fun s => freeKernelVolterraIntegrand38 a b z n u s i j) volume 0 v := by
  have hpot := intervalIntegrable_rawPotCoeff38 a b hT ha hb hsq
  have hsub : Set.uIcc (0 : ℝ) v ⊆ Set.uIcc (0 : ℝ) T := by
    rw [Set.uIcc_of_le hv.1, Set.uIcc_of_le hT]
    exact Set.Icc_subset_Icc le_rfl hv.2
  have hpotV := (hpot i (otherFin2 i)).mono_set hsub
  have hE : ContinuousOn
      (fun s => freeZsFundamentalComplex z (u - s) i i) (Set.Icc (0 : ℝ) v) := by
    have hglobal : Continuous (fun s : ℝ => freeZsFundamentalComplex z (u - s) i i) :=
      continuous_freeZs_entry38 z (fun s => u - s)
        (continuous_const.sub continuous_id) i i
    exact hglobal.continuousOn
  have hTentry : ContinuousOn
      (fun s => freeKernelVolterraTerm38 a b z n s (otherFin2 i) j)
      (Set.Icc (0 : ℝ) v) :=
    (hterm (otherFin2 i) j).mono (Set.Icc_subset_Icc_right hv.2)
  have hfactor : ContinuousOn
      (fun s => freeZsFundamentalComplex z (u - s) i i *
        freeKernelVolterraTerm38 a b z n s (otherFin2 i) j)
      (Set.Icc (0 : ℝ) v) := hE.mul hTentry
  have hfactorU : ContinuousOn
      (fun s => freeZsFundamentalComplex z (u - s) i i *
        freeKernelVolterraTerm38 a b z n s (otherFin2 i) j)
      (Set.uIcc (0 : ℝ) v) := by
    simpa [Set.uIcc_of_le hv.1] using hfactor
  have hprod : IntervalIntegrable
      (fun s => rawPotCoeff38 a b s i (otherFin2 i) *
        (freeZsFundamentalComplex z (u - s) i i *
          freeKernelVolterraTerm38 a b z n s (otherFin2 i) j)) volume 0 v :=
    hpotV.mul_continuousOn hfactorU
  apply hprod.congr
  intro s hs
  change rawPotCoeff38 a b s i (otherFin2 i) *
      (freeZsFundamentalComplex z (u - s) i i *
        freeKernelVolterraTerm38 a b z n s (otherFin2 i) j) =
    (freeZsFundamentalComplex z (u - s) * rawPotCoeff38 a b s *
      freeKernelVolterraTerm38 a b z n s) i j
  rw [volterra_integrand_entry]
  ring

private theorem freeKernelVolterraTerm38_succ_entry_factor
    (a b : ℝ → ℂ) (z : ℂ) (n : ℕ) (t : ℝ) (i j : Fin 2) :
    freeKernelVolterraTerm38 a b z (n + 1) t i j =
      freeZsFundamentalComplex z t i i *
        (∫ s in (0 : ℝ)..t,
          (freeZsFundamentalComplex z (-s) * rawPotCoeff38 a b s *
            freeKernelVolterraTerm38 a b z n s) i j) := by
  change (∫ s in (0 : ℝ)..t,
      (freeZsFundamentalComplex z (t - s) * rawPotCoeff38 a b s *
        freeKernelVolterraTerm38 a b z n s) i j) = _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  change (freeZsFundamentalComplex z (t - s) * rawPotCoeff38 a b s *
      freeKernelVolterraTerm38 a b z n s) i j =
    freeZsFundamentalComplex z t i i *
      (freeZsFundamentalComplex z (-s) * rawPotCoeff38 a b s *
        freeKernelVolterraTerm38 a b z n s) i j
  have hleft :
      (freeZsFundamentalComplex z (t - s) * rawPotCoeff38 a b s *
        freeKernelVolterraTerm38 a b z n s) i j =
      freeZsFundamentalComplex z (t - s) i i *
        rawPotCoeff38 a b s i (otherFin2 i) *
          freeKernelVolterraTerm38 a b z n s (otherFin2 i) j :=
    volterra_integrand_entry a b z n t s i j
  have hright :
      (freeZsFundamentalComplex z (-s) * rawPotCoeff38 a b s *
        freeKernelVolterraTerm38 a b z n s) i j =
      freeZsFundamentalComplex z (-s) i i *
        rawPotCoeff38 a b s i (otherFin2 i) *
          freeKernelVolterraTerm38 a b z n s (otherFin2 i) j := by
    simpa only [zero_sub] using volterra_integrand_entry a b z n 0 s i j
  have hexp : freeZsFundamentalComplex z (t - s) i i =
      freeZsFundamentalComplex z t i i * freeZsFundamentalComplex z (-s) i i := by
    rw [← freeE_eq z (t - s), ← freeE_eq z t, ← freeE_eq z (-s)]
    have hmat : freeE z (t - s) = freeE z t * freeE z (-s) := by
      calc
        freeE z (t - s) = freeE z (t + -s) := by congr 1 <;> ring
        _ = freeE z t * freeE z (-s) := freeE_add z t (-s)
    rw [hmat, freeE_mul_apply_local]
  rw [hleft, hright, hexp]
  ring

private theorem freeKernelVolterraTerm38_regular
    (a b : ℝ → ℂ) (z : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hsq : IntervalIntegrable (pairSqDensity38 a b) volume 0 T) :
    ∀ n,
      (∀ i j : Fin 2, ContinuousOn
        (fun s => freeKernelVolterraTerm38 a b z n s i j) (Set.Icc (0 : ℝ) T)) ∧
      (∀ v ∈ Set.Icc (0 : ℝ) T, ∀ i j : Fin 2,
        IntervalIntegrable
          (fun s => freeKernelVolterraIntegrand38 a b z n v s i j) volume 0 v) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro i j
        have hmat : Continuous (fun s : ℝ => freeZsFundamentalComplex z s) := by
          simpa only [Function.comp_apply, ← freeE_eq] using continuous_freeE z
        exact ((continuous_apply j).comp ((continuous_apply i).comp hmat)).continuousOn
      · intro v hv i j
        apply intervalIntegrable_freeKernelVolterraIntegrand38
          a b z 0 hT ha hb hsq ?_ hv v i j
        intro k l
        have hmat : Continuous (fun s : ℝ => freeZsFundamentalComplex z s) := by
          simpa only [Function.comp_apply, ← freeE_eq] using continuous_freeE z
        exact ((continuous_apply l).comp ((continuous_apply k).comp hmat)).continuousOn
  | succ n ih =>
      have hcontSucc : ∀ i j : Fin 2, ContinuousOn
          (fun s => freeKernelVolterraTerm38 a b z (n + 1) s i j)
          (Set.Icc (0 : ℝ) T) := by
        intro i j
        let F : ℝ → ℂ := fun s =>
          (freeZsFundamentalComplex z (-s) * rawPotCoeff38 a b s *
            freeKernelVolterraTerm38 a b z n s) i j
        have hF : IntervalIntegrable F volume 0 T := by
          have h := intervalIntegrable_freeKernelVolterraIntegrand38
            a b z n hT ha hb hsq ih.1 ⟨hT, le_rfl⟩ 0 i j
          simpa [F, freeKernelVolterraIntegrand38, zero_sub] using h
        have hFU : IntegrableOn F (Set.uIcc (0 : ℝ) T) := by
          simpa [Set.uIcc_of_le hT] using
            (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hF
        have hprimitive : ContinuousOn
            (fun u => ∫ s in (0 : ℝ)..u, F s) (Set.Icc (0 : ℝ) T) := by
          have h := intervalIntegral.continuousOn_primitive_interval hFU
          simpa [Set.uIcc_of_le hT] using h
        have hE : ContinuousOn
            (fun u => freeZsFundamentalComplex z u i i) (Set.Icc (0 : ℝ) T) := by
          have hglobal : Continuous (fun u : ℝ => freeZsFundamentalComplex z u i i) :=
            continuous_freeZs_entry38 z id continuous_id i i
          exact hglobal.continuousOn
        have hmul := hE.mul hprimitive
        apply hmul.congr
        intro u hu
        exact freeKernelVolterraTerm38_succ_entry_factor a b z n u i j
      constructor
      · exact hcontSucc
      · intro v hv i j
        exact intervalIntegrable_freeKernelVolterraIntegrand38
          a b z (n + 1) hT ha hb hsq hcontSucc hv v i j

/-- Each recursively defined term is continuous entrywise on the local interval,
and each of its source-recursion integrands is genuinely interval integrable. -/
theorem freeKernelVolterraTerm38_locally_regular
    (a b : ℝ → ℂ) (z : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hsq : IntervalIntegrable (fun s => ‖a s‖ ^ 2 + ‖b s‖ ^ 2) volume 0 T) :
    ∀ n,
      (∀ i j : Fin 2, ContinuousOn
        (fun s => freeKernelVolterraTerm38 a b z n s i j) (Set.Icc (0 : ℝ) T)) ∧
      (∀ v ∈ Set.Icc (0 : ℝ) T, ∀ i j : Fin 2,
        IntervalIntegrable
          (fun s => (freeZsFundamentalComplex z (v - s) * rawPotCoeff38 a b s *
            freeKernelVolterraTerm38 a b z n s) i j) volume 0 v) := by
  have hsq' : IntervalIntegrable (pairSqDensity38 a b) volume 0 T := by
    change IntervalIntegrable (pairSqDensity38 a b) volume 0 T
    exact hsq
  simpa [freeKernelVolterraIntegrand38] using
    freeKernelVolterraTerm38_regular a b z hT ha hb hsq'

private def evenVolterraIndex : ℕ → Prop
  | 0 => True
  | n + 1 => ¬ evenVolterraIndex n

private theorem freeKernelVolterraTerm38_sparse (a b : ℝ → ℂ) (z : ℂ) :
    ∀ n t,
      (evenVolterraIndex n → ∀ i j : Fin 2, i ≠ j →
        freeKernelVolterraTerm38 a b z n t i j = 0) ∧
      (¬ evenVolterraIndex n → ∀ i j : Fin 2, i = j →
        freeKernelVolterraTerm38 a b z n t i j = 0) := by
  intro n
  induction n with
  | zero =>
      intro t
      constructor
      · intro _ i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [freeKernelVolterraTerm38, freeZsFundamentalComplex,
            freeDiagonalCandidate]
      · intro h
        exact (h trivial).elim
  | succ n ih =>
      intro t
      constructor
      · intro hEven i j hij
        have hPrevOdd : ¬ evenVolterraIndex n := by
          simpa [evenVolterraIndex] using hEven
        simp only [freeKernelVolterraTerm38]
        rw [intervalIntegral.integral_zero_ae]
        filter_upwards with s
        rw [volterra_integrand_entry]
        have hFlip : otherFin2 i = j := otherFin2_eq_of_ne hij
        rw [(ih s).2 hPrevOdd (otherFin2 i) j hFlip]
        simp
      · intro hOdd i j hij
        have hPrevEven : evenVolterraIndex n := by
          by_contra hPrevOdd
          exact hOdd (by simpa [evenVolterraIndex] using hPrevOdd)
        simp only [freeKernelVolterraTerm38]
        rw [intervalIntegral.integral_zero_ae]
        filter_upwards with s
        rw [volterra_integrand_entry]
        have hFlip : otherFin2 i ≠ j := by
          rw [hij]
          exact otherFin2_ne j
        rw [(ih s).1 hPrevEven (otherFin2 i) j hFlip]
        simp

private theorem intervalIntegrable_density_power (a b : ℝ → ℂ) (z : ℂ)
    {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hf : IntervalIntegrable (pairDensity38 a b) volume 0 t)
    (hnonneg : ∀ s, 0 ≤ pairDensity38 a b s) :
    IntervalIntegrable
      (fun s => pairDensity38 a b s *
        (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
          (n.factorial : ℝ)) volume 0 t := by
  let F : ℝ → ℝ := fun x => ∫ x' in (0 : ℝ)..x, pairDensity38 a b x'
  have hfU : IntegrableOn (pairDensity38 a b) (Set.uIcc (0 : ℝ) t) := by
    simpa [Set.uIcc_of_le ht] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht).mp hf
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) t) := by
    have h := intervalIntegral.continuousOn_primitive_interval hfU
    simpa [F, Set.uIcc_of_le ht] using h
  have hScont : ContinuousOn
      (fun s => (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
        (n.factorial : ℝ)) (Set.Icc (0 : ℝ) t) := by
    simpa [F] using (hFcont.pow n).div_const (n.factorial : ℝ)
  have hScontU : ContinuousOn
      (fun s => (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
        (n.factorial : ℝ)) (Set.uIcc (0 : ℝ) t) := by
    simpa [Set.uIcc_of_le ht] using hScont
  apply (hf.mul_continuousOn hScontU).congr
  intro s hs
  simp only [F]
  ring

private theorem freeKernelVolterraTerm38_entry_bound
    (a b : ℝ → ℂ) (z : ℂ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hsq : IntervalIntegrable (pairSqDensity38 a b) volume 0 t) (i j : Fin 2) :
    ‖freeKernelVolterraTerm38 a b z n t i j‖ ≤
      Real.exp (|z.im| * t) *
        (∫ s in (0 : ℝ)..t, pairDensity38 a b s) ^ n /
          (n.factorial : ℝ) := by
  have hf0 : ∀ s, 0 ≤ pairDensity38 a b s := pairDensity38_nonneg a b
  induction n generalizing t i j with
  | zero =>
      simp only [freeKernelVolterraTerm38, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, mul_one]
      by_cases hij : i = j
      · subst j
        exact freeDiagonalEntry_norm_le z ht i
      · simp [freeZsFundamentalComplex, freeDiagonalCandidate, hij]
        positivity
  | succ n ih =>
      have hsqPublic : IntervalIntegrable
          (fun s => ‖a s‖ ^ 2 + ‖b s‖ ^ 2) volume 0 t := by
        change IntervalIntegrable (fun s => ‖a s‖ ^ 2 + ‖b s‖ ^ 2) volume 0 t
        exact hsq
      have hregular := freeKernelVolterraTerm38_locally_regular
        a b z ht ha hb hsqPublic
      have hf : IntervalIntegrable (pairDensity38 a b) volume 0 t :=
        intervalIntegrable_pairDensity38 a b ht ha hb hsq
      have hSc := intervalIntegrable_density_power (n := n) a b z ht hf hf0
      have hactual : IntervalIntegrable
          (fun s => freeKernelVolterraIntegrand38 a b z n t s i j) volume 0 t :=
        (hregular n).2 t ⟨ht, le_rfl⟩ i j
      have hmajor : IntervalIntegrable
          (fun s => Real.exp (|z.im| * t) *
            (pairDensity38 a b s *
              (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                (n.factorial : ℝ))) volume 0 t := by
        simpa [mul_div_assoc] using hSc.const_mul (Real.exp (|z.im| * t))
      have hFnonneg : ∀ s ∈ Set.Icc (0 : ℝ) t,
          0 ≤ ∫ x in (0 : ℝ)..s, pairDensity38 a b x := by
        intro s hs
        exact intervalIntegral.integral_nonneg_of_forall hs.1 (hf0)
      have hpoint : ∀ s, s ∈ Set.Icc (0 : ℝ) t →
          ‖freeKernelVolterraIntegrand38 a b z n t s i j‖ ≤
            Real.exp (|z.im| * t) *
              (pairDensity38 a b s *
                (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                  (n.factorial : ℝ)) := by
        intro s hs
        change ‖(freeZsFundamentalComplex z (t - s) * rawPotCoeff38 a b s *
          freeKernelVolterraTerm38 a b z n s) i j‖ ≤ _
        have hfree := freeDiagonalEntry_norm_le z (sub_nonneg.mpr hs.2) i
        have hpot := norm_potential_entry_le_density a b s i (otherFin2 i)
        have hsub : Set.uIcc (0 : ℝ) s ⊆ Set.uIcc (0 : ℝ) t := by
          rw [Set.uIcc_of_le hs.1, Set.uIcc_of_le ht]
          exact Set.Icc_subset_Icc le_rfl hs.2
        have hprev := ih (t := s) hs.1 (hsq.mono_set hsub) (otherFin2 i) j
        have hprev' :
            ‖freeKernelVolterraTerm38 a b z n s (otherFin2 i) j‖ ≤
              Real.exp (|z.im| * s) *
                ((∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                  (n.factorial : ℝ)) := by
          calc
            _ ≤ Real.exp (|z.im| * s) *
                (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                  (n.factorial : ℝ) := hprev
            _ = _ := by ring
        have hFpos := hFnonneg s hs
        have hEpos : 0 ≤ Real.exp (|z.im| * (t - s)) := Real.exp_nonneg _
        have hPpos : 0 ≤ pairDensity38 a b s := hf0 s
        have hRpos : 0 ≤ Real.exp (|z.im| * s) := Real.exp_nonneg _
        have hPowpos : 0 ≤ (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n :=
          pow_nonneg hFpos _
        have hmul :
            ‖freeZsFundamentalComplex z (t - s) i i *
                rawPotCoeff38 a b s i (otherFin2 i) *
                freeKernelVolterraTerm38 a b z n s (otherFin2 i) j‖ ≤
              (Real.exp (|z.im| * (t - s)) * pairDensity38 a b s) *
                (Real.exp (|z.im| * s) *
                  ((∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                    (n.factorial : ℝ))) := by
          calc
            _ ≤ ‖freeZsFundamentalComplex z (t - s) i i‖ *
                ‖rawPotCoeff38 a b s i (otherFin2 i)‖ *
                ‖freeKernelVolterraTerm38 a b z n s (otherFin2 i) j‖ := by
                  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
                    (norm_mul_le _ _) (norm_nonneg _))
            _ ≤ (Real.exp (|z.im| * (t - s)) * pairDensity38 a b s) *
                (Real.exp (|z.im| * s) *
                  ((∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                    (n.factorial : ℝ))) := by
                  gcongr
        rw [volterra_integrand_entry]
        calc
          _ ≤ (Real.exp (|z.im| * (t - s)) * pairDensity38 a b s) *
              (Real.exp (|z.im| * s) *
                ((∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                  (n.factorial : ℝ))) := hmul
          _ = (Real.exp (|z.im| * (t - s)) * Real.exp (|z.im| * s)) *
                (pairDensity38 a b s *
                  ((∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                    (n.factorial : ℝ))) := by ring
          _ = Real.exp (|z.im| * t) *
                (pairDensity38 a b s *
                  ((∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                    (n.factorial : ℝ))) := by
                congr 1
                rw [← Real.exp_add]
                congr 1 <;> ring
          _ = Real.exp (|z.im| * t) *
                (pairDensity38 a b s *
                  (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                    (n.factorial : ℝ)) := by ring
      have hstep :
          ‖∫ s in (0 : ℝ)..t,
            freeKernelVolterraIntegrand38 a b z n t s i j‖ ≤
            ∫ s in (0 : ℝ)..t, Real.exp (|z.im| * t) *
              (pairDensity38 a b s *
                (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                  (n.factorial : ℝ)) := by
        calc
          _ ≤ ∫ s in (0 : ℝ)..t,
              ‖freeKernelVolterraIntegrand38 a b z n t s i j‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht
          _ ≤ _ := intervalIntegral.integral_mono_on ht hactual.norm hmajor hpoint
      change ‖∫ s in (0 : ℝ)..t,
          freeKernelVolterraIntegrand38 a b z n t s i j‖ ≤ _
      calc
        _ ≤ ∫ s in (0 : ℝ)..t, Real.exp (|z.im| * t) *
            (pairDensity38 a b s *
              (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n /
                (n.factorial : ℝ)) := hstep
        _ = Real.exp (|z.im| * t) *
            ((∫ s in (0 : ℝ)..t, pairDensity38 a b s *
              (∫ x in (0 : ℝ)..s, pairDensity38 a b x) ^ n) /
                (n.factorial : ℝ)) := by
          rw [intervalIntegral.integral_const_mul]
          rw [intervalIntegral.integral_div]
        _ = Real.exp (|z.im| * t) *
            ((∫ s in (0 : ℝ)..t, pairDensity38 a b s) ^ (n + 1) /
              ((n + 1 : ℕ) : ℝ) /
                (n.factorial : ℝ)) := by
          rw [intervalIntegral_mul_primitive_pow (pairDensity38 a b) ht
            ((intervalIntegrable_iff_integrableOn_Icc_of_le ht).mp hf) n]
          rw [Nat.cast_add_one]
        _ = Real.exp (|z.im| * t) *
            (∫ s in (0 : ℝ)..t, pairDensity38 a b s) ^ (n + 1) /
              ((n + 1).factorial : ℝ) := by
          have hfac : ((n + 1).factorial : ℝ) =
              ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul]
          rw [hfac]
          rw [Nat.cast_add_one]
          field_simp
          <;> ring
private theorem even_sparse_matrix_opNorm_le (M : PairMat38) (C : ℝ)
    (hC : 0 ≤ C) (hdiag : ∀ i j : Fin 2, i ≠ j → M i j = 0)
    (hb : ∀ i : Fin 2, ‖M i i‖ ≤ C) : ‖M‖ ≤ C := by
  have hM : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hdiag i j hij
  rw [hM, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).2 hb

private theorem odd_sparse_matrix_opNorm_le (M : PairMat38) (C : ℝ)
    (hC : 0 ≤ C) (hdiag : ∀ i : Fin 2, M i i = 0)
    (hb : ∀ i : Fin 2, ‖M i (otherFin2 i)‖ ≤ C) : ‖M‖ ≤ C := by
  let P : PairMat38 := !![0, 1; 1, 0]
  let D : PairMat38 := Matrix.diagonal (fun i => M i (otherFin2 i))
  have hPmul : Matrix.conjTranspose P * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, Matrix.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]
  have hPnorm : ‖P‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self P
    rw [hPmul] at h
    norm_num at h ⊢
    nlinarith [norm_nonneg P]
  have hM : M = D * P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, P, otherFin2, Matrix.diagonal, Matrix.mul_apply,
        Fin.sum_univ_two, hdiag]
  calc
    ‖M‖ = ‖D * P‖ := by rw [hM]
    _ ≤ ‖D‖ * ‖P‖ := Matrix.l2_opNorm_mul D P
    _ = ‖D‖ := by rw [hPnorm, mul_one]
    _ ≤ C := by
      rw [Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg hC).2 hb

private theorem freeKernelVolterraTerm38_norm_le_scalar
    (a b : ℝ → ℂ) (z : ℂ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hsq : IntervalIntegrable (pairSqDensity38 a b) volume 0 t) :
    ‖freeKernelVolterraTerm38 a b z n t‖ ≤
      Real.exp (|z.im| * t) *
        (∫ s in (0 : ℝ)..t, pairDensity38 a b s) ^ n /
          (n.factorial : ℝ) := by
  let C : ℝ := Real.exp (|z.im| * t) *
    (∫ s in (0 : ℝ)..t, pairDensity38 a b s) ^ n /
      (n.factorial : ℝ)
  have hQ : 0 ≤ ∫ s in (0 : ℝ)..t, pairDensity38 a b s :=
    intervalIntegral.integral_nonneg_of_forall ht (pairDensity38_nonneg a b)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbEntry : ∀ i j : Fin 2,
      ‖freeKernelVolterraTerm38 a b z n t i j‖ ≤ C := by
    intro i j
    dsimp [C]
    exact freeKernelVolterraTerm38_entry_bound a b z n ht ha hb hsq i j
  rcases freeKernelVolterraTerm38_sparse a b z n t with ⟨hEven, hOdd⟩
  by_cases he : evenVolterraIndex n
  · apply even_sparse_matrix_opNorm_le _ C hC
    · exact hEven he
    · intro i
      exact hbEntry i i
  · apply odd_sparse_matrix_opNorm_le _ C hC
    · intro i
      exact hOdd he i i rfl
    · intro i
      exact hbEntry i (otherFin2 i)

theorem freeKernelVolterraTerm38_norm_le
    (a b : ℝ → ℂ) (z : ℂ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hsq : IntervalIntegrable (fun s => ‖a s‖ ^ 2 + ‖b s‖ ^ 2) volume 0 t) :
    ‖freeKernelVolterraTerm38 a b z n t‖ ≤
      Real.exp (|z.im| * t) *
        (Real.sqrt t * pairL2NormOn38 a b t) ^ n /
          (n.factorial : ℝ) := by
  have hsq' : IntervalIntegrable (pairSqDensity38 a b) volume 0 t := by
    change IntervalIntegrable (pairSqDensity38 a b) volume 0 t
    exact hsq
  have hscalar := freeKernelVolterraTerm38_norm_le_scalar a b z n ht ha hb hsq'
  have hcs := integral_pairDensity38_le a b ht ha hb hsq'
  have hIpos : 0 ≤ ∫ s in (0 : ℝ)..t, pairDensity38 a b s :=
    intervalIntegral.integral_nonneg_of_forall ht (pairDensity38_nonneg a b)
  have hRpos : 0 ≤ Real.sqrt t * pairL2NormOn38 a b t := by
    dsimp [pairL2NormOn38]
    positivity
  have hp := pow_le_pow_left₀ hIpos hcs n
  have hexp : 0 ≤ Real.exp (|z.im| * t) := Real.exp_nonneg _
  calc
    _ ≤ Real.exp (|z.im| * t) *
        (∫ s in (0 : ℝ)..t, pairDensity38 a b s) ^ n /
          (n.factorial : ℝ) := hscalar
    _ ≤ Real.exp (|z.im| * t) *
        (Real.sqrt t * pairL2NormOn38 a b t) ^ n /
          (n.factorial : ℝ) := by
      have hfac : 0 < (n.factorial : ℝ) := by positivity
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp hexp) hfac.le

private theorem coverRep38_periodic_two (f : PhysicalL2) :
    Function.Periodic (coverRep38 f) 2 := by
  intro t
  simp only [coverRep38, AddCircle.coe_add, AddCircle.coe_period, add_zero]

private theorem coverRep38_sq_periodic_two (f : PhysicalL2) :
    Function.Periodic (fun t => ‖coverRep38 f t‖ ^ 2) 2 := by
  intro t
  change ‖coverRep38 f (t + 2)‖ ^ 2 = ‖coverRep38 f t‖ ^ 2
  rw [coverRep38_periodic_two f t]

private theorem intervalIntegrable_coverRep38_sq_any (f : PhysicalL2) (a b : ℝ) :
    IntervalIntegrable (fun t => ‖coverRep38 f t‖ ^ 2) volume a b :=
  (coverRep38_sq_periodic_two f).intervalIntegrable₀ (by norm_num)
    (intervalIntegrable_coverRep38_sq_two f) a b

theorem potentialVolterraTerm38_norm_le (φ : PotPair) (z : ℂ) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖potentialVolterraTerm38 φ z n t‖ ≤
      Real.exp (|z.im| * t) *
        (Real.sqrt t * potentialL2NormOn38 φ t) ^ n /
          (n.factorial : ℝ) := by
  have ha : AEStronglyMeasurable (potRepFst38 φ) volume :=
    (stronglyMeasurable_coverRep38 φ.1).aestronglyMeasurable
  have hb : AEStronglyMeasurable (potRepSnd38 φ) volume :=
    (stronglyMeasurable_coverRep38 φ.2).aestronglyMeasurable
  have hsq : IntervalIntegrable
      (fun s => ‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2) volume 0 t := by
    exact (intervalIntegrable_coverRep38_sq_any φ.1 0 t).add
      (intervalIntegrable_coverRep38_sq_any φ.2 0 t)
  simpa [potentialVolterraTerm38, potentialL2NormOn38] using
    freeKernelVolterraTerm38_norm_le
      (potRepFst38 φ) (potRepSnd38 φ) z n ht ha hb hsq

end NlsGge.Atomic.G1

end
