import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS014Host
import NlsGge.ThirdConsultation.KSPS.KSPS014Support2
import NlsGge.ThirdConsultation.KSPS.KSPS014Support3

                                                                                                                    
                                                                                                            
                                      
                                                                                           
                                                                                       
                                                                                         
                                                                                                               
                                                                                                               
                                                  
set_option autoImplicit false
open MeasureTheory Matrix
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS014W
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS

/-! ### Absolutely continuous primitives -/

theorem ac_mul {f g : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun y => f y * g y) a b :=
  hf.smul hg

theorem ac_cmul (c : ℂ) {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun y => c * f y) a b :=
  hf.const_smul c

theorem prim_facts {F g : ℝ → ℂ} (C : ℂ) (hg : IntervalIntegrable g volume 0 1)
    (hF : ∀ y ∈ Set.Icc (0 : ℝ) 1, F y = C + ∫ t in (0 : ℝ)..y, g t) :
    AbsolutelyContinuousOnInterval F 0 1 ∧
      ∀ᵐ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → HasDerivAt F (g x) x := by
  refine ⟨?_, ?_⟩
  · have hp := NlsGge.SpectralFoundations.complex_intervalIntegral_primitive_absolutelyContinuousV2
      hg (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1)
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => C) 0 1 :=
      (contDiffOn_const (c := C) (n := 1) (s := Set.uIcc (0 : ℝ) 1)).absolutelyContinuousOnInterval
    refine (hc.add hp).congr (fun y hy => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hy
    exact (hF y hy).symm
  · filter_upwards [hg.ae_hasDerivAt_integral] with x hx hmem
    have hmem' : x ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le zero_le_one]
      exact ⟨hmem.1.le, hmem.2.le⟩
    have hd := (hx hmem' 0 (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1)).const_add C
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with z hz
    exact hF z ⟨hz.1.le, hz.2.le⟩

theorem ii_sub {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : IntervalIntegrable f volume 0 y :=
  hf.mono_set (Set.uIcc_subset_uIcc (Set.left_mem_uIcc) (by rw [Set.uIcc_of_le zero_le_one]; exact hy))

theorem ii_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun t => ∑ i ∈ s, f i t) volume a b := by
  have h2 := IntervalIntegrable.sum s h
  convert h2 using 1
  funext t
  simp [Finset.sum_apply]

/-! ### The finite Riccati sums -/

/-- `sum_k (2 i lam)^-k T_k(x)`, T_k the continuous H^1 trace of the k-th Riccati coefficient. -/
def gsum {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (y : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ * KSPSWKB.coefficientTrace φ b k y

def gder {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (y : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ *
    coverRep38 (weakDerivative (KSPSRiccati.coefficient φ b k)) y

def gcov {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (y : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ *
    coverRep38 (KSPSRiccati.coefficient φ b k) y

def psum {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (y : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ * KSPSRiccati.«prefix» φ b k y

def pder {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (y : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ *
    (coverRep38 (KSPSRiccati.sidePotential φ b) y * coverRep38 (KSPSRiccati.coefficient φ b k) y)

theorem pder_eq {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (y : ℝ) :
    pder φ b lam y = coverRep38 (KSPSRiccati.sidePotential φ b) y * gcov φ b lam y := by
  unfold pder gcov
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem gder_ii {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    IntervalIntegrable (gder φ b lam) volume 0 1 := by
  unfold gder
  exact ii_finset_sum _ (fun k _ => (intervalIntegrable_coverRep38_one _).const_mul _)

theorem prod_ii (f g : PhysicalL2) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => coverRep38 f t * coverRep38 g t) volume 0 y := by
  have h := NlsGge.ThirdConsultation.KSPSSupport.h150_prod_integrableOn f g
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hy.1).2
    (h.mono_set (Set.Icc_subset_Icc le_rfl hy.2))

theorem pder_ii {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    IntervalIntegrable (pder φ b lam) volume 0 1 := by
  unfold pder
  exact ii_finset_sum _ (fun k _ => (prod_ii _ _ ⟨zero_le_one, le_rfl⟩).const_mul _)

theorem gsum_eq {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (y : ℝ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    gsum φ b lam y = gsum φ b lam 0 + ∫ t in (0 : ℝ)..y, gder φ b lam t := by
  have hint : ∀ k ∈ Finset.Icc 1 N, IntervalIntegrable
      (fun t => ((2 * Complex.I * lam) ^ k)⁻¹ *
        coverRep38 (weakDerivative (KSPSRiccati.coefficient φ b k)) t) volume 0 y :=
    fun k _ => (ii_sub (intervalIntegrable_coverRep38_one _) hy).const_mul _
  unfold gsum gder
  rw [intervalIntegral.integral_finset_sum hint, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_const_mul]
  simp only [KSPSWKB.coefficientTrace, intervalIntegral.integral_same, add_zero]
  ring

theorem psum_eq {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (y : ℝ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    psum φ b lam y = 0 + ∫ t in (0 : ℝ)..y, pder φ b lam t := by
  have hint : ∀ k ∈ Finset.Icc 1 N, IntervalIntegrable
      (fun t => ((2 * Complex.I * lam) ^ k)⁻¹ *
        (coverRep38 (KSPSRiccati.sidePotential φ b) t *
          coverRep38 (KSPSRiccati.coefficient φ b k) t)) volume 0 y :=
    fun k _ => (prod_ii _ _ hy).const_mul _
  unfold psum pder
  rw [intervalIntegral.integral_finset_sum hint, zero_add]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem gsum_facts {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    AbsolutelyContinuousOnInterval (gsum φ b lam) 0 1 ∧
      ∀ᵐ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → HasDerivAt (gsum φ b lam) (gder φ b lam x) x :=
  prim_facts _ (gder_ii φ b lam) (gsum_eq φ b lam)

theorem psum_facts {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    AbsolutelyContinuousOnInterval (psum φ b lam) 0 1 ∧
      ∀ᵐ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → HasDerivAt (psum φ b lam) (pder φ b lam x) x :=
  prim_facts _ (pder_ii φ b lam) (psum_eq φ b lam)

theorem trace_ae {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → gcov φ b lam x = gsum φ b lam x := by
  have h : ∀ k ∈ Finset.Icc 1 N, ∀ᵐ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 →
      coverRep38 (KSPSRiccati.coefficient φ b k) x = KSPSWKB.coefficientTrace φ b k x := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact KSPSWKB.coefficientTrace_ae (le_trans hk'.1 hk'.2) φ b k hk'.1 hk'.2
  have h2 := (Filter.eventually_all_finset (Finset.Icc 1 N)).2 h
  filter_upwards [h2] with x hx hmem
  unfold gcov gsum
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [hx k hk ⟨hmem.1, hmem.2.le⟩]

theorem phase_facts {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    AbsolutelyContinuousOnInterval (KSPSRiccati.phaseFactor φ b lam) 0 1 ∧
      ∀ᵐ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
        HasDerivAt (KSPSRiccati.phaseFactor φ b lam)
          (KSPSRiccati.phaseFactor φ b lam x * ((if b then (-1 : ℂ) else 1) * pder φ b lam x)) x := by
  obtain ⟨hac, hder⟩ := psum_facts φ b lam
  refine ⟨ac_complex_exp38 (ac_cmul (if b then (-1 : ℂ) else 1) hac), ?_⟩
  filter_upwards [hder] with x hx hmem
  exact ((hx hmem).const_mul (if b then (-1 : ℂ) else 1)).cexp

theorem expo_hasDerivAt (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (w * (y : ℂ))) (Complex.exp (w * (x : ℂ)) * w) x := by
  have h : HasDerivAt (fun v : ℂ => w * v) w (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul w
  exact h.cexp.comp_ofReal

theorem expo_neg_hasDerivAt (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (-(w * (y : ℂ)))) (Complex.exp (-(w * (x : ℂ))) * (-w)) x := by
  have h0 : HasDerivAt (fun v : ℂ => -w * v) (-w) (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul (-w)
  have h : HasDerivAt (fun v : ℂ => -(w * v)) (-w) (x : ℂ) := by
    convert h0 using 1
    funext v
    ring
  exact h.cexp.comp_ofReal

theorem expo_ac (w : ℂ) : AbsolutelyContinuousOnInterval (fun y : ℝ => Complex.exp (w * (y : ℂ))) 0 1 := by
  have h : ContDiff ℝ 1 (fun y : ℝ => w * Complex.ofRealCLM y) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  exact ac_complex_exp38 h.contDiffOn.absolutelyContinuousOnInterval

theorem expo_neg_ac (w : ℂ) :
    AbsolutelyContinuousOnInterval (fun y : ℝ => Complex.exp (-(w * (y : ℂ)))) 0 1 := by
  have h : ContDiff ℝ 1 (fun y : ℝ => -(w * Complex.ofRealCLM y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
  exact ac_complex_exp38 h.contDiffOn.absolutelyContinuousOnInterval

/-! ### The explicit column and the forced system -/

/-- The explicit (non-remainder) part of `KSPSWKB.wkbColumn`. -/
def explicitColumn {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : {z : ℂ // z ≠ 0}) (x : ℝ) : Fin 2 → ℂ :=
  if b then
    (Complex.exp (Complex.I * lam.1 * (x : ℂ)) *
      KSPSRiccati.phaseFactor φ true lam.1 x) • ![KSPSWKB.beta φ lam.1 x, 1]
  else
    (Complex.exp (-(Complex.I * lam.1 * (x : ℂ))) *
      KSPSRiccati.phaseFactor φ false lam.1 x) • ![1, KSPSWKB.alpha φ lam.1 x]

theorem wkbColumn_eq {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : {z : ℂ // z ≠ 0}) (x : ℝ) :
    KSPSWKB.wkbColumn φ b lam x =
      explicitColumn φ b lam x + ((2 * Complex.I * lam.1) ^ N)⁻¹ • KSPSWKB.sourceRemainderVector φ b lam x :=
  rfl

/-- The forcing term `(2 i lam)^-N R s(t)`. -/
def forcingTerm {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : {z : ℂ // z ≠ 0}) (t : ℝ) : Fin 2 → ℂ :=
  ((2 * Complex.I * lam.1) ^ N)⁻¹ •
    (NlsGge.ThirdConsultation.KSPSVolterra.R *ᵥ KSPSWKB.sourceForcingVector φ b lam t)

theorem explicitColumn_false_apply {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0}) (y : ℝ) :
    explicitColumn φ false lam y 0 =
        Complex.exp (-(Complex.I * lam.1 * (y : ℂ))) * KSPSRiccati.phaseFactor φ false lam.1 y ∧
    explicitColumn φ false lam y 1 =
        Complex.exp (-(Complex.I * lam.1 * (y : ℂ))) * KSPSRiccati.phaseFactor φ false lam.1 y *
          (-Complex.I * gsum φ false lam.1 y) := by
  have h : explicitColumn φ false lam y =
      (Complex.exp (-(Complex.I * lam.1 * (y : ℂ))) * KSPSRiccati.phaseFactor φ false lam.1 y) •
        ![1, KSPSWKB.alpha φ lam.1 y] := rfl
  rw [h]
  refine ⟨?_, ?_⟩
  · simp
  · simp only [Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
    rfl

theorem explicitColumn_true_apply {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0}) (y : ℝ) :
    explicitColumn φ true lam y 0 =
        Complex.exp (Complex.I * lam.1 * (y : ℂ)) * KSPSRiccati.phaseFactor φ true lam.1 y *
          (-Complex.I * gsum φ true lam.1 y) ∧
    explicitColumn φ true lam y 1 =
        Complex.exp (Complex.I * lam.1 * (y : ℂ)) * KSPSRiccati.phaseFactor φ true lam.1 y := by
  have h : explicitColumn φ true lam y =
      (Complex.exp (Complex.I * lam.1 * (y : ℂ)) * KSPSRiccati.phaseFactor φ true lam.1 y) •
        ![KSPSWKB.beta φ lam.1 y, 1] := rfl
  rw [h]
  refine ⟨?_, ?_⟩
  · simp only [Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
    rfl
  · simp

theorem forcingTerm_apply {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : {z : ℂ // z ≠ 0}) (t : ℝ) :
    forcingTerm φ b lam t 0 = (if b then ((2 * Complex.I * lam.1) ^ N)⁻¹ * (Complex.I *
        (Complex.exp (Complex.I * lam.1 * (t : ℂ)) *
          ((2 * Complex.I * lam.1) ^ N * KSPSRiccati.phaseFactor φ true lam.1 t *
            coverRep38 (KSPSRiccati.rho φ true lam.1) t))) else 0) ∧
    forcingTerm φ b lam t 1 = (if b then 0 else ((2 * Complex.I * lam.1) ^ N)⁻¹ * (-Complex.I *
        (Complex.exp (-(Complex.I * lam.1 * (t : ℂ))) *
          ((2 * Complex.I * lam.1) ^ N * KSPSRiccati.phaseFactor φ false lam.1 t *
            coverRep38 (KSPSRiccati.rho φ false lam.1) t)))) := by
  cases b <;> refine ⟨?_, ?_⟩ <;>
    simp only [forcingTerm, KSPSWKB.sourceForcingVector, KSPSRiccati.forcing, Bool.false_eq_true,
      ↓reduceIte, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      NlsGge.ThirdConsultation.KSPSVolterra.R, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;> ring

theorem forcing_ii {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (g : ℝ → ℂ) (hg : Continuous g) :
    IntervalIntegrable (fun t : ℝ => g t *
      ((2 * Complex.I * lam) ^ N * KSPSRiccati.phaseFactor φ b lam t *
        coverRep38 (KSPSRiccati.rho φ b lam) t)) volume 0 1 := by
  have hph := NlsGge.ThirdConsultation.KSPSSupport.h150_phase_continuousOn φ b lam
  rw [← Set.uIcc_of_le zero_le_one] at hph
  have h1 := (intervalIntegrable_coverRep38_one (KSPSRiccati.rho φ b lam)).continuousOn_mul hph
  have h2 := (h1.const_mul ((2 * Complex.I * lam) ^ N)).continuousOn_mul hg.continuousOn
  convert h2 using 1
  funext t
  ring

theorem forcingTerm_ii {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : {z : ℂ // z ≠ 0}) (i : Fin 2) :
    IntervalIntegrable (fun t => forcingTerm φ b lam t i) volume 0 1 := by
  have hp : Continuous (fun t : ℝ => Complex.exp (Complex.I * lam.1 * (t : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hn : Continuous (fun t : ℝ => Complex.exp (-(Complex.I * lam.1 * (t : ℂ)))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg
  have h0 : (fun t => forcingTerm φ b lam t 0) = fun t : ℝ => (if b then ((2 * Complex.I * lam.1) ^ N)⁻¹ *
      (Complex.I * (Complex.exp (Complex.I * lam.1 * (t : ℂ)) *
        ((2 * Complex.I * lam.1) ^ N * KSPSRiccati.phaseFactor φ true lam.1 t *
          coverRep38 (KSPSRiccati.rho φ true lam.1) t))) else 0) :=
    funext fun t => (forcingTerm_apply φ b lam t).1
  have h1 : (fun t => forcingTerm φ b lam t 1) = fun t : ℝ => (if b then 0 else
      ((2 * Complex.I * lam.1) ^ N)⁻¹ * (-Complex.I *
      (Complex.exp (-(Complex.I * lam.1 * (t : ℂ))) *
        ((2 * Complex.I * lam.1) ^ N * KSPSRiccati.phaseFactor φ false lam.1 t *
          coverRep38 (KSPSRiccati.rho φ false lam.1) t)))) :=
    funext fun t => (forcingTerm_apply φ b lam t).2
  fin_cases i
  · try simp only [Fin.zero_eta, Fin.isValue]
    rw [h0]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact intervalIntegrable_const
    · simp only [↓reduceIte]
      exact ((forcing_ii φ true lam.1 _ hp).const_mul _).const_mul _
  · try simp only [Fin.mk_one, Fin.isValue]
    rw [h1]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ((forcing_ii φ false lam.1 _ hn).const_mul _).const_mul _
    · simp only [↓reduceIte]
      exact intervalIntegrable_const

/-! ### The explicit column: absolute continuity and the forced system a.e. -/

theorem explicitColumn_ac {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : {z : ℂ // z ≠ 0}) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (fun y => explicitColumn φ b lam y i) 0 1 := by
  have hph := (phase_facts φ b lam.1).1
  have hG := ac_cmul (-Complex.I) (gsum_facts φ b lam.1).1
  cases b
  · have hE := ac_mul (expo_neg_ac (Complex.I * lam.1)) hph
    fin_cases i
    · exact hE.congr (fun y _ => ((explicitColumn_false_apply φ lam y).1).symm)
    · exact (ac_mul hE hG).congr (fun y _ => ((explicitColumn_false_apply φ lam y).2).symm)
  · have hE := ac_mul (expo_ac (Complex.I * lam.1)) hph
    fin_cases i
    · exact (ac_mul hE hG).congr (fun y _ => ((explicitColumn_true_apply φ lam y).1).symm)
    · exact hE.congr (fun y _ => ((explicitColumn_true_apply φ lam y).2).symm)

theorem zs_mulVec (p : PotPair) (z : ℂ) (s : ℝ) (v : Fin 2 → ℂ) :
    (zsCoeffPot38 p z s *ᵥ v) 0 = -(Complex.I * z) * v 0 + Complex.I * coverRep38 p.1 s * v 1 ∧
    (zsCoeffPot38 p z s *ᵥ v) 1 = -(Complex.I * coverRep38 p.2 s) * v 0 + Complex.I * z * v 1 := by
  obtain ⟨a00, a01, a10, a11⟩ := zsCoeffPot38_apply p z s
  refine ⟨?_, ?_⟩ <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, a00, a01, a10, a11]

theorem explicitColumn_deriv {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : {z : ℂ // z ≠ 0}) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → ∀ i : Fin 2,
      HasDerivAt (fun y => explicitColumn φ b lam y i)
        ((zsCoeffPot38 (toPotPair φ) lam.1 x *ᵥ explicitColumn φ b lam x) i +
          forcingTerm φ b lam x i) x := by
  have hc0 : (2 * Complex.I * lam.1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) lam.2
  have hc : ((2 * Complex.I * lam.1) ^ N)⁻¹ * (2 * Complex.I * lam.1) ^ N = 1 :=
    inv_mul_cancel₀ (pow_ne_zero N hc0)
  filter_upwards [(gsum_facts φ b lam.1).2, (phase_facts φ b lam.1).2, trace_ae φ b lam.1,
    k14_rho_ae φ b lam.1] with x hG hP htr hrho hmem
  have hG := hG hmem
  have hP := hP hmem
  have htr := htr hmem
  have hpd := pder_eq φ b lam.1 x
  have hrho' : coverRep38 (KSPSRiccati.rho φ b lam.1) x =
      (if b then (-1 : ℂ) else 1) * gder φ b lam.1 x - (2 * Complex.I * lam.1) * gcov φ b lam.1 x +
        coverRep38 (KSPSRiccati.sidePotential φ b) x * gcov φ b lam.1 x ^ 2 -
        coverRep38 (KSPSRiccati.sideInput φ b) x := hrho
  rw [htr] at hrho' hpd
  have hm := zs_mulVec (toPotPair φ) lam.1 x (explicitColumn φ b lam x)
  have hf := forcingTerm_apply φ b lam x
  cases b
  · have hs : KSPSRiccati.sidePotential φ false = (toPotPair φ).1 := rfl
    have hi : KSPSRiccati.sideInput φ false = (toPotPair φ).2 := rfl
    rw [hs, hi] at hrho'
    rw [hs] at hpd
    obtain ⟨e0, e1⟩ := explicitColumn_false_apply φ lam x
    have hE := (expo_neg_hasDerivAt (Complex.I * lam.1) x).mul hP
    simp only [Bool.false_eq_true, ↓reduceIte] at hrho' hf hE
    intro i
    fin_cases i
    · have hfun : (fun y => explicitColumn φ false lam y 0) = fun y : ℝ =>
          Complex.exp (-(Complex.I * lam.1 * (y : ℂ))) * KSPSRiccati.phaseFactor φ false lam.1 y :=
        funext fun y => (explicitColumn_false_apply φ lam y).1
      try simp only [Fin.zero_eta, Fin.isValue]
      rw [hfun]
      refine hE.congr_deriv ?_
      rw [hm.1, e0, e1, hf.1, hpd]
      linear_combination (Complex.exp (-(Complex.I * lam.1 * (x : ℂ))) * KSPSRiccati.phaseFactor φ false lam.1 x *
        coverRep38 (toPotPair φ).1 x * gsum φ false lam.1 x) * Complex.I_sq
    · have hfun : (fun y => explicitColumn φ false lam y 1) = fun y : ℝ =>
          Complex.exp (-(Complex.I * lam.1 * (y : ℂ))) * KSPSRiccati.phaseFactor φ false lam.1 y *
            (-Complex.I * gsum φ false lam.1 y) :=
        funext fun y => (explicitColumn_false_apply φ lam y).2
      try simp only [Fin.mk_one, Fin.isValue]
      rw [hfun]
      refine (hE.mul (hG.const_mul (-Complex.I))).congr_deriv ?_
      rw [hm.2, e0, e1, hf.2, hpd]
      simp only [Pi.mul_apply]
      linear_combination
        (Complex.I * Complex.exp (-(Complex.I * lam.1 * (x : ℂ))) *
          KSPSRiccati.phaseFactor φ false lam.1 x) * hrho' +
        (Complex.I * Complex.exp (-(Complex.I * lam.1 * (x : ℂ))) *
          KSPSRiccati.phaseFactor φ false lam.1 x *
            coverRep38 (KSPSRiccati.rho φ false lam.1) x) * hc
  · have hs : KSPSRiccati.sidePotential φ true = (toPotPair φ).2 := rfl
    have hi : KSPSRiccati.sideInput φ true = (toPotPair φ).1 := rfl
    rw [hs, hi] at hrho'
    rw [hs] at hpd
    obtain ⟨e0, e1⟩ := explicitColumn_true_apply φ lam x
    have hE := (expo_hasDerivAt (Complex.I * lam.1) x).mul hP
    simp only [↓reduceIte] at hrho' hf hE
    intro i
    fin_cases i
    · have hfun : (fun y => explicitColumn φ true lam y 0) = fun y : ℝ =>
          Complex.exp (Complex.I * lam.1 * (y : ℂ)) * KSPSRiccati.phaseFactor φ true lam.1 y *
            (-Complex.I * gsum φ true lam.1 y) :=
        funext fun y => (explicitColumn_true_apply φ lam y).1
      try simp only [Fin.zero_eta, Fin.isValue]
      rw [hfun]
      refine (hE.mul (hG.const_mul (-Complex.I))).congr_deriv ?_
      rw [hm.1, e0, e1, hf.1, hpd]
      simp only [Pi.mul_apply]
      linear_combination
        (-Complex.I * Complex.exp (Complex.I * lam.1 * (x : ℂ)) *
          KSPSRiccati.phaseFactor φ true lam.1 x) * hrho' +
        (-Complex.I * Complex.exp (Complex.I * lam.1 * (x : ℂ)) *
          KSPSRiccati.phaseFactor φ true lam.1 x *
            coverRep38 (KSPSRiccati.rho φ true lam.1) x) * hc
    · have hfun : (fun y => explicitColumn φ true lam y 1) = fun y : ℝ =>
          Complex.exp (Complex.I * lam.1 * (y : ℂ)) * KSPSRiccati.phaseFactor φ true lam.1 y :=
        funext fun y => (explicitColumn_true_apply φ lam y).2
      try simp only [Fin.mk_one, Fin.isValue]
      rw [hfun]
      refine hE.congr_deriv ?_
      rw [hm.2, e0, e1, hf.2, hpd]
      linear_combination (-(Complex.exp (Complex.I * lam.1 * (x : ℂ)) * KSPSRiccati.phaseFactor φ true lam.1 x *
        coverRep38 (toPotPair φ).2 x * gsum φ true lam.1 x)) * Complex.I_sq

/-! ### Adjugate variation of constants -/

theorem adjugate2_mulVec (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 A *ᵥ v) 0 = A 1 1 * v 0 + -A 0 1 * v 1 ∧
    (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 A *ᵥ v) 1 = -A 1 0 * v 0 + A 0 0 * v 1 := by
  simp [NlsGge.ThirdConsultation.KSPSVolterra.adjugate2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem adj_ii (p : PotPair) (z : ℂ) (r : ℝ → Fin 2 → ℂ)
    (hr : ∀ i, IntervalIntegrable (fun t => r t i) volume 0 1) (i : Fin 2) :
    IntervalIntegrable
      (fun t => (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z t) *ᵥ r t) i) volume 0 1 := by
  have hcont : ∀ k l : Fin 2, ContinuousOn (fun t => fundExt p z t k l) (Set.uIcc (0 : ℝ) 1) := by
    intro k l
    rw [Set.uIcc_of_le zero_le_one]
    exact fundExt_continuousOn p z k l
  fin_cases i
  · have h := ((hr 0).continuousOn_mul (hcont 1 1)).add ((hr 1).continuousOn_mul (hcont 0 1).neg)
    convert h using 1
    funext t
    try simp only [Fin.zero_eta, Fin.isValue]
    exact (adjugate2_mulVec _ _).1
  · have h := ((hr 0).continuousOn_mul (hcont 1 0).neg).add ((hr 1).continuousOn_mul (hcont 0 0))
    convert h using 1
    funext t
    try simp only [Fin.mk_one, Fin.isValue]
    exact (adjugate2_mulVec _ _).2

theorem voc (p : PotPair) (z : ℂ) (e r : ℝ → Fin 2 → ℂ)
    (hac : ∀ i, AbsolutelyContinuousOnInterval (fun y => e y i) 0 1)
    (hr : ∀ i, IntervalIntegrable (fun t => r t i) volume 0 1)
    (hder : ∀ᵐ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → ∀ i : Fin 2,
      HasDerivAt (fun y => e y i) ((zsCoeffPot38 p z x *ᵥ e x) i + r x i) x)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (i : Fin 2) :
    (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z x) *ᵥ e x) i =
      e 0 i + ∫ t in (0 : ℝ)..x,
        (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z t) *ᵥ r t) i := by
  have hm : ∀ k l : Fin 2, AbsolutelyContinuousOnInterval (fun y => -fundExt p z y k l) 0 1 :=
    fun k l => (fundExt_ac p z k l).neg
  have hne : ∀ᵐ y : ℝ, y ∈ Set.uIcc (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 := by
    have h0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by simp [ae_iff, measure_singleton]
    have h1 : ∀ᵐ y : ℝ ∂volume, y ≠ 1 := by simp [ae_iff, measure_singleton]
    filter_upwards [h0, h1] with y hy0 hy1 hmem
    rw [Set.uIcc_of_le zero_le_one] at hmem
    exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hy0), lt_of_le_of_ne hmem.2 hy1⟩
  have hxu : x ∈ Set.uIcc (0 : ℝ) 1 := by rw [Set.uIcc_of_le zero_le_one]; exact hx
  have hIcc : ∀ y : ℝ, y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 := fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hz := fundExt_zero p z
  fin_cases i
  · try simp only [Fin.zero_eta, Fin.isValue]
    have hfun : (fun y => (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z y) *ᵥ e y) 0) =
        fun y => fundExt p z y 1 1 * e y 0 + -fundExt p z y 0 1 * e y 1 :=
      funext fun y => (adjugate2_mulVec _ _).1
    have hF : AbsolutelyContinuousOnInterval
        (fun y => (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z y) *ᵥ e y) 0) 0 1 := by
      rw [hfun]
      exact (ac_mul (fundExt_ac p z 1 1) (hac 0)).add (ac_mul (hm 0 1) (hac 1))
    have hd : ∀ᵐ y : ℝ, y ∈ Set.uIcc (0 : ℝ) 1 →
        HasDerivAt (fun y => (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z y) *ᵥ e y) 0)
          ((NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z y) *ᵥ r y) 0) y := by
      filter_upwards [hne, hder, fundExt_ae_hasDerivAt p z 0 1, fundExt_ae_hasDerivAt p z 1 1,
        fundExt_ae_hasDerivAt p z 0 0, fundExt_ae_hasDerivAt p z 1 0] with y hy hy1 h01 h11 h00 h10 hmem
      have hyo := hy hmem
      have he := hy1 hyo
      rw [hfun]
      refine (((h11 (hIcc y hyo)).mul (he 0)).add (((h01 (hIcc y hyo)).neg).mul (he 1))).congr_deriv ?_
      obtain ⟨a00, a01, a10, a11⟩ := zsCoeffPot38_apply p z y
      rw [(adjugate2_mulVec _ _).1, (zs_mulVec p z y (e y)).1, (zs_mulVec p z y (e y)).2]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Pi.neg_apply, a00, a01, a10, a11]
      ring
    have h := NlsGge.SpectralFoundations.complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
      hF (adj_ii p z r hr 0) hd x hxu
    rw [h, (adjugate2_mulVec _ _).1, hz]
    simp
  · try simp only [Fin.mk_one, Fin.isValue]
    have hfun : (fun y => (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z y) *ᵥ e y) 1) =
        fun y => -fundExt p z y 1 0 * e y 0 + fundExt p z y 0 0 * e y 1 :=
      funext fun y => (adjugate2_mulVec _ _).2
    have hF : AbsolutelyContinuousOnInterval
        (fun y => (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z y) *ᵥ e y) 1) 0 1 := by
      rw [hfun]
      exact (ac_mul (hm 1 0) (hac 0)).add (ac_mul (fundExt_ac p z 0 0) (hac 1))
    have hd : ∀ᵐ y : ℝ, y ∈ Set.uIcc (0 : ℝ) 1 →
        HasDerivAt (fun y => (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z y) *ᵥ e y) 1)
          ((NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt p z y) *ᵥ r y) 1) y := by
      filter_upwards [hne, hder, fundExt_ae_hasDerivAt p z 0 1, fundExt_ae_hasDerivAt p z 1 1,
        fundExt_ae_hasDerivAt p z 0 0, fundExt_ae_hasDerivAt p z 1 0] with y hy hy1 h01 h11 h00 h10 hmem
      have hyo := hy hmem
      have he := hy1 hyo
      rw [hfun]
      refine ((((h10 (hIcc y hyo)).neg).mul (he 0)).add ((h00 (hIcc y hyo)).mul (he 1))).congr_deriv ?_
      obtain ⟨a00, a01, a10, a11⟩ := zsCoeffPot38_apply p z y
      rw [(adjugate2_mulVec _ _).2, (zs_mulVec p z y (e y)).1, (zs_mulVec p z y (e y)).2]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Pi.neg_apply, a00, a01, a10, a11]
      ring
    have h := NlsGge.SpectralFoundations.complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
      hF (adj_ii p z r hr 1) hd x hxu
    rw [h, (adjugate2_mulVec _ _).2, hz]
    simp

end
end NlsGge.ThirdConsultation.KSPS014W
