import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.G1.G1015
import NlsGge.Atomic.G1.G1040
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairVolterraProbe
import NlsGge.Atomic.G2.G2005
import NlsGge.Atomic.G2.G2006
import NlsGge.GK38.Lib.InterpolationHilbertOp
import NlsGge.GK38.Lib.EntireProductsGrowth
import NlsGge.GK38.Lib.EntireProductsCircle
import NlsGge.GK38.ProductReprRatio
import NlsGge.GK38.PeriodicAsymptotics

                                                                                                                     

section
                                                                                                                            
                                                                                                                             
                                                                                                                                  
                                                                                                                            
                                                                                                                             
                                                                                                                          
                                              

                                                                                                                           
                                                                                                                            
                                                                                                                                   
                                                                                                                     
                                                                                                                            
                                                                                                                              
                                                                                                             

                                                                                                         
                                                                                     
                                                                                              
                                                                                             
                                                                                                         

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1050S2.K47.K17.K16

noncomputable section


theorem lipschitzOnWith_exp_Iic : LipschitzOnWith 1 Real.exp (Set.Iic (0 : ℝ)) := by
  refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℝ) (f := Real.exp) (s := Set.Iic (0 : ℝ))
    (fun x _ => Real.differentiableAt_exp) (fun x hx => ?_) (convex_Iic 0)
  rw [Real.deriv_exp]
  have : Real.exp x ≤ 1 := Real.exp_le_one_iff.2 hx
  rw [← NNReal.coe_le_coe]
  simpa using this

/-- Gronwall's inequality in integral form with an integrable weight. -/
theorem gronwall_integral {t : ℝ} (ht : 0 ≤ t) {ω n : ℝ → ℝ}
    (hω0 : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ ω s)
    (hω : IntervalIntegrable ω volume 0 t) (hn : ContinuousOn n (Set.Icc (0 : ℝ) t)) (c : ℝ)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) t, n s ≤ c + ∫ r in (0 : ℝ)..s, ω r * n r) :
    n t ≤ c * Real.exp (∫ r in (0 : ℝ)..t, ω r) := by
  have hu : Set.uIcc (0 : ℝ) t = Set.Icc 0 t := Set.uIcc_of_le ht
  have hωn : IntervalIntegrable (fun r => ω r * n r) volume 0 t :=
    hω.mul_continuousOn (by rw [hu]; exact hn)
  set W : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, ω r with hW
  set Q : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, ω r * n r with hQ
  have hWac : AbsolutelyContinuousOnInterval W 0 t :=
    hω.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have hQac : AbsolutelyContinuousOnInterval Q 0 t :=
    hωn.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have hW0 : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ W s := fun s hs =>
    intervalIntegral.integral_nonneg hs.1 fun r hr => hω0 r ⟨hr.1, hr.2.trans hs.2⟩
  have hnegac : AbsolutelyContinuousOnInterval (fun s => -W s) 0 t := hWac.neg
  have hexpac : AbsolutelyContinuousOnInterval (fun s => Real.exp (-W s)) 0 t := by
    have := lipschitzOnWith_exp_Iic.comp_absolutelyContinuousOnInterval
      (g := fun s => -W s) (a := 0) (b := t)
      (fun s hs => by
        rw [hu] at hs
        exact neg_nonpos.2 (hW0 s hs)) hnegac
    exact this
  have hcac : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 t :=
    (contDiff_const.contDiffOn (s := Set.uIcc (0 : ℝ) t) (n := 1)).absolutelyContinuousOnInterval
  set P : ℝ → ℝ := fun s => Real.exp (-W s) * (Q s + c) with hP
  have hPac : AbsolutelyContinuousOnInterval P 0 t := by
    have := hexpac.fun_mul (hQac.add hcac)
    exact this
  have hint := hPac.intervalIntegrable_deriv
  have hae : ∀ᵐ s : ℝ, s ∈ Set.uIcc (0 : ℝ) t → deriv P s ≤ 0 := by
    filter_upwards [hω.ae_hasDerivAt_integral, hωn.ae_hasDerivAt_integral] with s h1 h2 hs
    have hs' : s ∈ Set.Icc (0 : ℝ) t := by rwa [hu] at hs
    have d1 : HasDerivAt W (ω s) s := h1 hs 0 left_mem_uIcc
    have d2 : HasDerivAt Q (ω s * n s) s := h2 hs 0 left_mem_uIcc
    have d3 : HasDerivAt (fun x => Real.exp (-W x)) (Real.exp (-W s) * (-ω s)) s :=
      (d1.neg).exp
    have d4 : HasDerivAt P (Real.exp (-W s) * (-ω s) * (Q s + c) +
        Real.exp (-W s) * (ω s * n s)) s := d3.mul (d2.add_const c)
    rw [d4.deriv]
    have hn' := h s hs'
    have e1 : Real.exp (-W s) * (-ω s) * (Q s + c) + Real.exp (-W s) * (ω s * n s) =
        Real.exp (-W s) * ω s * (n s - (c + Q s)) := by ring
    rw [e1]
    have : n s - (c + Q s) ≤ 0 := by
      have := hn'
      simp only [hQ] at *
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le (hω0 s hs')) this
  have hI : ∫ s in (0 : ℝ)..t, deriv P s ≤ 0 := by
    have := intervalIntegral.integral_mono_ae_restrict (μ := volume) (a := 0) (b := t) ht hint
      (intervalIntegrable_const (c := (0 : ℝ)))
      ((ae_restrict_iff' measurableSet_Icc).2 (hae.mono fun s hs hs1 => hs (by rwa [hu])))
    simpa using this
  rw [hPac.integral_deriv_eq_sub] at hI
  have hP0 : P 0 = c := by simp [hP, hW, hQ]
  have hPt : P t ≤ c := by linarith
  have h1 : Q t + c ≤ c * Real.exp (W t) := by
    have := mul_le_mul_of_nonneg_right hPt (Real.exp_pos (W t)).le
    have e : P t * Real.exp (W t) = Q t + c := by
      simp only [hP, mul_assoc]
      rw [mul_comm (Q t + c), ← mul_assoc, ← Real.exp_add]
      simp
    rw [e] at this
    linarith
  have := h t ⟨ht, le_rfl⟩
  have e2 : (∫ r in (0 : ℝ)..t, ω r * n r) = Q t := rfl
  have e3 : (∫ r in (0 : ℝ)..t, ω r) = W t := rfl
  rw [e3]
  linarith



theorem norm_matrix_integral_le {F : ℝ → PairMat38} {t : ℝ} (ht : 0 ≤ t) {h : ℝ → ℝ}
    (hent : ∀ i j : Fin 2, IntervalIntegrable (fun s => F s i j) volume 0 t)
    (hh : IntervalIntegrable h volume 0 t)
    (hb : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖F s‖ ≤ h s) :
    ‖(Matrix.of fun i j => ∫ s in (0 : ℝ)..t, F s i j : PairMat38)‖ ≤ ∫ s in (0 : ℝ)..t, h s := by
  have hmeas : AEStronglyMeasurable F (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    have e : F = fun s => ∑ i : Fin 2, ∑ j : Fin 2, Matrix.single i j (F s i j) := by
      funext s
      exact Matrix.matrix_eq_sum_single (F s)
    rw [e]
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    have hc : Continuous (fun c : ℂ => (Matrix.single i j c : PairMat38)) := by
      refine continuous_matrix fun a b => ?_
      by_cases hab : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := hab
        have e : (fun c : ℂ => (Matrix.single i j c : PairMat38) i j) = fun c => c := by
          funext c
          simp
        rw [e]
        exact continuous_id
      · have : (fun c : ℂ => (Matrix.single i j c : PairMat38) a b) = fun _ => 0 := by
          funext c
          simp [Matrix.single_apply, hab]
        rw [this]
        exact continuous_const
    exact hc.comp_aestronglyMeasurable (hent i j).1.aestronglyMeasurable
  have hhi : IntegrableOn h (Set.Ioc (0 : ℝ) t) := hh.1
  have hF : IntervalIntegrable F volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    refine Integrable.mono' hhi hmeas ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hb)
  have hG : ‖∫ s in (0 : ℝ)..t, F s‖ ≤ ∫ s in (0 : ℝ)..t, h s :=
    intervalIntegral.norm_integral_le_of_norm_le ht
      (Eventually.of_forall fun s hs => hb s hs) hh
  have hEq : (Matrix.of fun i j => ∫ s in (0 : ℝ)..t, F s i j : PairMat38) =
      ∫ s in (0 : ℝ)..t, F s := by
    ext i j
    let L : PairMat38 →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
    have := L.intervalIntegral_comp_comm hF
    exact this
  rw [hEq]
  exact hG


/-! ### Norm bounds for the free solution and the potential coefficient -/

/-- The pointwise `ℓ²` size of the potential. -/
def omegaW (φ : PotPair) (s : ℝ) : ℝ :=
  Real.sqrt (‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2)

theorem omegaW_nonneg (φ : PotPair) (s : ℝ) : 0 ≤ omegaW φ s := Real.sqrt_nonneg _

def otherFin2 (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem even_sparse_matrix_opNorm_le (M : PairMat38) (C : ℝ)
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

theorem odd_sparse_matrix_opNorm_le (M : PairMat38) (C : ℝ)
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

theorem norm_potCoeff38_le_omega (φ : PotPair) (s : ℝ) : ‖potCoeff38 φ s‖ ≤ omegaW φ s := by
  have h1 : ‖potRepFst38 φ s‖ ≤ omegaW φ s :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖potRepSnd38 φ s‖])
  have h2 : ‖potRepSnd38 φ s‖ ≤ omegaW φ s :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖potRepFst38 φ s‖])
  refine odd_sparse_matrix_opNorm_le _ _ (omegaW_nonneg φ s)
    (fun i => by fin_cases i <;> simp [potCoeff38]) (fun i => ?_)
  fin_cases i <;> simp [potCoeff38, otherFin2, h1, h2]

theorem norm_freeE_le (z : ℂ) {r : ℝ} (hr : 0 ≤ r) : ‖freeE z r‖ ≤ Real.exp (|z.im| * r) := by
  refine even_sparse_matrix_opNorm_le _ _ (Real.exp_pos _).le (fun i j hij => ?_) (fun i => ?_)
  · fin_cases i <;> fin_cases j <;> simp [freeE] at hij ⊢
  · have := norm_freeE_entry_le z r i i
    rwa [abs_of_nonneg hr] at this

/-! ### The functions on `[0,1]` -/

theorem hT1 : (0 : ℝ) ≤ 1 := zero_le_one

/-- `M(s) = ∑ M_n(s)` as a function on `ℝ` (constant extension of the fundamental solution). -/
def Mfun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 := ext38T hT1 (fundContT φ z hT1) s

/-- `M_1(s)` as a function on `ℝ`. -/
def M1fun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 :=
  ext38T hT1 (volterraPT φ z hT1 (freeFundT 1 z)) s

def Xfun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 := Mfun φ z s - freeE z s

def Nfun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 := Xfun φ z s - M1fun φ z s

def kerT (φ : PotPair) (z : ℂ) (t s : ℝ) : PairMat38 :=
  freeE z (t - s) * potCoeff38 φ s * Xfun φ z s

theorem cont_Mfun (φ : PotPair) (z : ℂ) : Continuous (Mfun φ z) := continuous_ext38T hT1 _

theorem cont_M1fun (φ : PotPair) (z : ℂ) : Continuous (M1fun φ z) := continuous_ext38T hT1 _

theorem cont_Xfun (φ : PotPair) (z : ℂ) : Continuous (Xfun φ z) :=
  (cont_Mfun φ z).sub (continuous_freeE z)

theorem cont_Nfun (φ : PotPair) (z : ℂ) : Continuous (Nfun φ z) :=
  (cont_Xfun φ z).sub (cont_M1fun φ z)


theorem fundContT_entry_eq' (φ : PotPair) (z : ℂ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    fundContT φ z hT1 ⟨t, ht⟩ i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s *
        ext38T hT1 (fundContT φ z hT1) s) i j := by
  have h := congrArg (fun G : PairContT 1 => G ⟨t, ht⟩ i j) (fundContT_eq_add φ z hT1)
  simp only [ContinuousMap.add_apply, Pi.add_apply] at h
  rw [h]
  rfl

theorem tsum_entry (φ : PotPair) (z : ℂ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    (∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j = fundContT φ z hT1 ⟨t, ht⟩ i j := by
  have hent : ∀ i j : Fin 2, HasSum (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)
      (fundContT φ z hT1 ⟨t, ht⟩ i j) := by
    intro i j
    have e : (fun n : ℕ => potentialVolterraTerm38 φ z n t i j) =
        fun n : ℕ => ((volterraPT φ z hT1 ^ n) (freeFundT 1 z)) ⟨t, ht⟩ i j :=
      funext fun n => by rw [term_eq_powT φ z hT1 n t ht]
    rw [e]
    exact hasSum_entryT φ z hT1 ⟨t, ht⟩ i j
  have hS : Summable (fun n : ℕ => potentialVolterraTerm38 φ z n t) :=
    Pi.summable.2 fun i => Pi.summable.2 fun j => (hent i j).summable
  have hcont : Continuous (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) :=
    (continuous_id.matrix_elem i j)
  have h1 : HasSum (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)
      ((∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j) :=
    hS.hasSum.map (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) hcont
  exact h1.unique (hent i j)

theorem tsum_eq_Mfun (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∑' n : ℕ, potentialVolterraTerm38 φ z n t) = Mfun φ z t := by
  ext i j
  rw [tsum_entry φ z ht i j, Mfun, ext38T_of_mem hT1 _ ht]

theorem term1_eq (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    potentialVolterraTerm38 φ z 1 t = M1fun φ z t := by
  have h := term_eq_powT φ z hT1 1 t ht
  rw [pow_one] at h
  rw [h, M1fun, ext38T_of_mem hT1 _ ht]

theorem ker_integrable (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    IntervalIntegrable (fun s => kerT φ z t s i j) volume 0 t := by
  have hK : Continuous fun s : ℝ => freeE z (t - s) :=
    (continuous_freeE z).comp (continuous_const.sub continuous_id)
  have h1 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (cont_Mfun φ z) ht i j
  have h2 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (continuous_freeE z) ht i j
  refine (h1.sub h2).congr ?_
  intro s _
  simp [kerT, Xfun, Matrix.mul_sub, Matrix.sub_apply]

theorem stepB (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Nfun φ z t = Matrix.of fun i j => ∫ s in (0 : ℝ)..t, kerT φ z t s i j := by
  ext i j
  have hK : Continuous fun s : ℝ => freeE z (t - s) :=
    (continuous_freeE z).comp (continuous_const.sub continuous_id)
  have h1 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (cont_Mfun φ z) ht i j
  have h2 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (continuous_freeE z) ht i j
  have hM : Mfun φ z t i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * Mfun φ z s) i j := by
    rw [Mfun, ext38T_of_mem hT1 _ ht]
    exact fundContT_entry_eq' φ z ht i j
  have hM1 : M1fun φ z t i j =
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * freeE z s) i j := by
    rw [M1fun, ext38T_of_mem hT1 _ ht, volterraPT_apply, volterraFunT_apply]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
      have := Set.uIcc_subset_Icc (Set.left_mem_Icc.2 hT1) ht hs
      exact this
    rw [ext38T_of_mem hT1 _ hs']
    rfl
  have hker : (∫ s in (0 : ℝ)..t, kerT φ z t s i j) =
      (∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * Mfun φ z s) i j) -
        ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * freeE z s) i j := by
    rw [← intervalIntegral.integral_sub h1 h2]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [kerT, Xfun, Matrix.mul_sub, Matrix.sub_apply]
  rw [Matrix.of_apply, hker]
  simp only [Nfun, Xfun, Matrix.sub_apply]
  rw [hM, hM1]
  ring

/-! ### The weight `ω` and weighted norms -/

theorem omegaW_sq (φ : PotPair) (s : ℝ) :
    omegaW φ s ^ 2 = ‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem intervalIntegrable_omegaW_sq (φ : PotPair) :
    IntervalIntegrable (fun s => omegaW φ s ^ 2) volume 0 1 := by
  have h := (intervalIntegrable_coverRep38_sq_one φ.1).add (intervalIntegrable_coverRep38_sq_one φ.2)
  refine h.congr ?_
  intro s _
  simp only [omegaW_sq, potRepFst38, potRepSnd38]

theorem integral_omegaW_sq (φ : PotPair) :
    ∫ s in (0 : ℝ)..1, omegaW φ s ^ 2 = ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
  have e : ∀ s, omegaW φ s ^ 2 = ‖coverRep38 φ.1 s‖ ^ 2 + ‖coverRep38 φ.2 s‖ ^ 2 := fun s => by
    rw [omegaW_sq]; rfl
  simp_rw [e]
  rw [intervalIntegral.integral_add (intervalIntegrable_coverRep38_sq_one φ.1)
    (intervalIntegrable_coverRep38_sq_one φ.2), integral_sq_coverRep38_one, integral_sq_coverRep38_one]

theorem omegaW_le_potW (φ : PotPair) (s : ℝ) : omegaW φ s ≤ potW38 φ s := by
  unfold omegaW potW38
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg (potRepFst38 φ s), norm_nonneg (potRepSnd38 φ s)]

theorem intervalIntegrable_omegaW (φ : PotPair) : IntervalIntegrable (omegaW φ) volume 0 1 := by
  have hsq : IntervalIntegrable (fun s => ‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_coverRep38_sq_one φ.1).add (intervalIntegrable_coverRep38_sq_one φ.2)
  have hm : AEStronglyMeasurable (omegaW φ) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hsq.1.aestronglyMeasurable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Integrable.mono' (intervalIntegrable_potW38 φ).1 hm ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s _ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (omegaW_nonneg φ s)]
  exact omegaW_le_potW φ s

/-- The weighted norms. -/
def aW (φ : PotPair) (z : ℂ) (s : ℝ) : ℝ := Real.exp (-|z.im| * s) * ‖M1fun φ z s‖
def nW (φ : PotPair) (z : ℂ) (s : ℝ) : ℝ := Real.exp (-|z.im| * s) * ‖Nfun φ z s‖
def YW (φ : PotPair) (z : ℂ) (s : ℝ) : ℝ := Real.exp (-|z.im| * s) * ‖Xfun φ z s‖

theorem continuous_expW (z : ℂ) : Continuous fun s : ℝ => Real.exp (-|z.im| * s) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_id)

theorem continuous_aW (φ : PotPair) (z : ℂ) : Continuous (aW φ z) :=
  (continuous_expW z).mul (cont_M1fun φ z).norm

theorem continuous_nW (φ : PotPair) (z : ℂ) : Continuous (nW φ z) :=
  (continuous_expW z).mul (cont_Nfun φ z).norm

theorem continuous_YW (φ : PotPair) (z : ℂ) : Continuous (YW φ z) :=
  (continuous_expW z).mul (cont_Xfun φ z).norm

theorem aW_nonneg (φ : PotPair) (z : ℂ) (s : ℝ) : 0 ≤ aW φ z s :=
  mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem nW_nonneg (φ : PotPair) (z : ℂ) (s : ℝ) : 0 ≤ nW φ z s :=
  mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem YW_le (φ : PotPair) (z : ℂ) (s : ℝ) : YW φ z s ≤ aW φ z s + nW φ z s := by
  have h : ‖Xfun φ z s‖ ≤ ‖M1fun φ z s‖ + ‖Nfun φ z s‖ := by
    have : Xfun φ z s = M1fun φ z s + Nfun φ z s := by simp [Nfun]
    rw [this]
    exact norm_add_le _ _
  unfold YW aW nW
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-! ### The integral inequality -/

theorem n_le_integral (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    nW φ z t ≤ ∫ s in (0 : ℝ)..t, YW φ z s * omegaW φ s := by
  have hωt : IntervalIntegrable (omegaW φ) volume 0 t :=
    (intervalIntegrable_omegaW φ).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc le_rfl ht.2)
  have hcont : Continuous fun s : ℝ => Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖ :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (cont_Xfun φ z).norm
  have hh : IntervalIntegrable (fun s => (Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖) *
      omegaW φ s) volume 0 t := hωt.continuousOn_mul hcont.continuousOn
  have hb : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖kerT φ z t s‖ ≤
      (Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖) * omegaW φ s := by
    intro s hs
    have hts : 0 ≤ t - s := sub_nonneg.2 hs.2
    unfold kerT
    calc ‖freeE z (t - s) * potCoeff38 φ s * Xfun φ z s‖
        ≤ ‖freeE z (t - s) * potCoeff38 φ s‖ * ‖Xfun φ z s‖ := norm_mul_le _ _
      _ ≤ (‖freeE z (t - s)‖ * ‖potCoeff38 φ s‖) * ‖Xfun φ z s‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (Real.exp (|z.im| * (t - s)) * omegaW φ s) * ‖Xfun φ z s‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact mul_le_mul (norm_freeE_le z hts) (norm_potCoeff38_le_omega φ s)
            (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  have hN := norm_matrix_integral_le ht.1 (ker_integrable φ z ht) hh hb
  rw [← stepB φ z ht] at hN
  unfold nW
  calc Real.exp (-|z.im| * t) * ‖Nfun φ z t‖
      ≤ Real.exp (-|z.im| * t) * ∫ s in (0 : ℝ)..t,
          (Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖) * omegaW φ s :=
        mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le
    _ = ∫ s in (0 : ℝ)..t, YW φ z s * omegaW φ s := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        simp only [YW]
        rw [← mul_assoc, ← mul_assoc, ← Real.exp_add]
        have e : -|z.im| * t + |z.im| * (t - s) = -|z.im| * s := by ring
        rw [e]

/-! ### Gronwall step -/

theorem Icc_sub_Icc_one {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩

theorem intervalIntegrable_omegaW_on (φ : PotPair) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (omegaW φ) volume 0 t :=
  (intervalIntegrable_omegaW φ).mono_set (by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc le_rfl ht.2)

/-- `∫₀ᵗ ω a`. -/
def bW (φ : PotPair) (z : ℂ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, omegaW φ s * aW φ z s

theorem intervalIntegrable_omega_mul {φ : PotPair} {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => omegaW φ s * g s) volume 0 t :=
  (intervalIntegrable_omegaW_on φ ht).mul_continuousOn hg.continuousOn

theorem n_le_b_add_Q (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    nW φ z t ≤ bW φ z t + ∫ s in (0 : ℝ)..t, omegaW φ s * nW φ z s := by
  refine (n_le_integral φ z ht).trans ?_
  have hia := intervalIntegrable_omega_mul (φ := φ) (continuous_aW φ z) ht
  have hin := intervalIntegrable_omega_mul (φ := φ) (continuous_nW φ z) ht
  unfold bW
  rw [← intervalIntegral.integral_add hia hin]
  have hY : IntervalIntegrable (fun s => YW φ z s * omegaW φ s) volume 0 t :=
    (intervalIntegrable_omegaW_on φ ht).continuousOn_mul (continuous_YW φ z).continuousOn
  refine intervalIntegral.integral_mono_on ht.1 hY (hia.add hin) fun s hs => ?_
  have := YW_le φ z s
  have hω := omegaW_nonneg φ s
  nlinarith

theorem bW_mono (φ : PotPair) (z : ℂ) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : bW φ z s ≤ bW φ z t := by
  unfold bW
  refine intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2 ?_
    (intervalIntegrable_omega_mul (φ := φ) (continuous_aW φ z) ht)
  exact Eventually.of_forall fun r => mul_nonneg (omegaW_nonneg φ r) (aW_nonneg φ z r)

theorem n_le_gronwall (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    nW φ z t ≤ bW φ z t * Real.exp (∫ r in (0 : ℝ)..t, omegaW φ r) := by
  refine gronwall_integral ht.1 (ω := omegaW φ) (n := nW φ z)
    (fun s _ => omegaW_nonneg φ s) (intervalIntegrable_omegaW_on φ ht)
    (continuous_nW φ z).continuousOn (bW φ z t) fun s hs => ?_
  have h1 := n_le_b_add_Q φ z (Icc_sub_Icc_one hs ht)
  have h2 := bW_mono φ z hs ht
  linarith

/-! ### Cauchy-Schwarz -/

theorem cs_integral {t : ℝ} (ht : 0 ≤ t) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable (fun s => f s ^ 2) volume 0 t)
    (hg : IntervalIntegrable (fun s => g s ^ 2) volume 0 t)
    (hfg : IntervalIntegrable (fun s => f s * g s) volume 0 t) :
    (∫ s in (0 : ℝ)..t, f s * g s) ^ 2 ≤
      (∫ s in (0 : ℝ)..t, f s ^ 2) * ∫ s in (0 : ℝ)..t, g s ^ 2 := by
  have key : ∀ x : ℝ, 0 ≤ (∫ s in (0 : ℝ)..t, f s ^ 2) * (x * x) +
      (-2 * ∫ s in (0 : ℝ)..t, f s * g s) * x + ∫ s in (0 : ℝ)..t, g s ^ 2 := by
    intro x
    have h0 : 0 ≤ ∫ s in (0 : ℝ)..t, (x * f s - g s) ^ 2 :=
      intervalIntegral.integral_nonneg ht fun s _ => sq_nonneg _
    have e : ∫ s in (0 : ℝ)..t, (x * f s - g s) ^ 2 =
        (∫ s in (0 : ℝ)..t, f s ^ 2) * (x * x) +
          (-2 * ∫ s in (0 : ℝ)..t, f s * g s) * x + ∫ s in (0 : ℝ)..t, g s ^ 2 := by
      have e1 : ∀ s, (x * f s - g s) ^ 2 =
          (x * x) * f s ^ 2 + (-2 * x) * (f s * g s) + g s ^ 2 := fun s => by ring
      simp_rw [e1]
      rw [intervalIntegral.integral_add ((hf.const_mul (x * x)).add (hfg.const_mul (-2 * x))) hg,
        intervalIntegral.integral_add (hf.const_mul (x * x)) (hfg.const_mul (-2 * x)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    linarith
  have := discrim_le_zero key
  unfold _root_.discrim at this
  nlinarith

theorem W_le (φ : PotPair) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ r in (0 : ℝ)..t, omegaW φ r ≤ Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) := by
  have hf : IntervalIntegrable (fun s => omegaW φ s ^ 2) volume 0 t :=
    (intervalIntegrable_omegaW_sq φ).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc le_rfl ht.2)
  have hg : IntervalIntegrable (fun s : ℝ => (1 : ℝ) ^ 2) volume 0 t := intervalIntegrable_const
  have hfg : IntervalIntegrable (fun s => omegaW φ s * 1) volume 0 t := by
    simpa using intervalIntegrable_omegaW_on φ ht
  have h := cs_integral ht.1 hf hg hfg
  simp only [mul_one, one_pow, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  have hsq : ∫ s in (0 : ℝ)..t, omegaW φ s ^ 2 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    rw [← integral_omegaW_sq φ]
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_ (intervalIntegrable_omegaW_sq φ)
    exact Eventually.of_forall fun r => sq_nonneg _
  have hP : 0 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by positivity
  have h3 : (∫ r in (0 : ℝ)..t, omegaW φ r) ^ 2 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    have hI : 0 ≤ ∫ s in (0 : ℝ)..t, omegaW φ s ^ 2 :=
      intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _
    nlinarith [ht.2, ht.1]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h3)

theorem b_le (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    bW φ z t ≤ Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) *
      Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2) := by
  have hf : IntervalIntegrable (fun s => omegaW φ s ^ 2) volume 0 t :=
    (intervalIntegrable_omegaW_sq φ).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc le_rfl ht.2)
  have hg : IntervalIntegrable (fun s => aW φ z s ^ 2) volume 0 t :=
    ((continuous_aW φ z).pow 2).intervalIntegrable 0 t
  have hfg := intervalIntegrable_omega_mul (φ := φ) (continuous_aW φ z) ht
  have h := cs_integral ht.1 hf hg hfg
  have hsq : ∫ s in (0 : ℝ)..t, omegaW φ s ^ 2 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    rw [← integral_omegaW_sq φ]
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_ (intervalIntegrable_omegaW_sq φ)
    exact Eventually.of_forall fun r => sq_nonneg _
  have hJ : 0 ≤ ∫ s in (0 : ℝ)..t, aW φ z s ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _
  have hP : 0 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by positivity
  have h3 : (bW φ z t) ^ 2 ≤ (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * ∫ s in (0 : ℝ)..t, aW φ z s ^ 2 :=
    h.trans (mul_le_mul_of_nonneg_right hsq hJ)
  rw [← Real.sqrt_mul hP]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h3)

/-! ### Assembly -/

theorem aW_eq_term (φ : PotPair) (z : ℂ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖ = aW φ z s := by
  rw [term1_eq φ z hs]; rfl

theorem G1016_whole :
    ((∀ (φ : PotPair) (z : ℂ) (t : ℝ), 0 ≤ t → t ≤ 1 →
    IntervalIntegrable
      (fun s : ℝ => (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2)
      MeasureTheory.volume 0 t ∧
    Real.exp (-|z.im| * t) *
        ‖(∑' n : ℕ, potentialVolterraTerm38 φ z n t) - freeZsFundamentalComplex z t‖ ≤
      Real.exp (-|z.im| * t) * ‖potentialVolterraTerm38 φ z 1 t‖ +
        (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2))) *
          Real.sqrt (∫ s in (0 : ℝ)..t,
            (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2)
  : Prop)) := by
  intro φ z t ht0 ht1
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hcongr : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2 = aW φ z s ^ 2 := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    rw [aW_eq_term φ z (Icc_sub_Icc_one hs ht)]
  refine ⟨?_, ?_⟩
  · refine (((continuous_aW φ z).pow 2).intervalIntegrable 0 t).congr ?_
    intro s hs
    exact (hcongr s (Set.uIoc_subset_uIcc hs)).symm
  · have hI : (∫ s in (0 : ℝ)..t,
        (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2) =
        ∫ s in (0 : ℝ)..t, aW φ z s ^ 2 :=
      intervalIntegral.integral_congr hcongr
    rw [hI, aW_eq_term φ z ht, tsum_eq_Mfun φ z ht, ← freeE_eq]
    have hY : Real.exp (-|z.im| * t) * ‖Mfun φ z t - freeE z t‖ = YW φ z t := rfl
    rw [hY]
    have h1 := YW_le φ z t
    have h2 := n_le_gronwall φ z ht
    have h3 := b_le φ z ht
    have h4 := W_le φ ht
    have hb0 : 0 ≤ bW φ z t := intervalIntegral.integral_nonneg ht0 fun s _ =>
      mul_nonneg (omegaW_nonneg φ s) (aW_nonneg φ z s)
    have h5 : bW φ z t * Real.exp (∫ r in (0 : ℝ)..t, omegaW φ r) ≤
        (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2)) *
          Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2)) :=
      mul_le_mul h3 (Real.exp_le_exp.2 h4) (Real.exp_pos _).le
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have h6 : (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2)) *
          Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2)) =
        (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2))) *
          Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2) := by ring
    rw [h6] at h5
    linarith

end

end NlsGge.Atomic.G1050S2.K47.K17.K16



/-! ### G1-017: high-frequency local uniform asymptotics -/

open NlsGge.Atomic.G1050S2.K47.K17.K16

namespace NlsGge.Atomic.G1050S2.K47.K17

noncomputable section

theorem norm_exp_mul_le {c : ℂ} {A : ℝ} (hc : |c.re| ≤ A) (u : ℝ) :
    ‖Complex.exp (c * (u : ℂ))‖ ≤ Real.exp (A * |u|) := by
  rw [Complex.norm_exp]
  have e : (c * (u : ℂ)).re = c.re * u := by simp
  rw [e]
  apply Real.exp_le_exp.2
  calc c.re * u ≤ |c.re * u| := le_abs_self _
    _ = |c.re| * |u| := abs_mul _ _
    _ ≤ A * |u| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)

theorem norm_exp_kernel_le {c : ℂ} {A : ℝ} (hc : |c.re| ≤ A) {t r : ℝ} (hr : r ∈ Icc (0 : ℝ) t) :
    ‖Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))‖ ≤ Real.exp (A * t) := by
  have hA : 0 ≤ A := le_trans (abs_nonneg _) hc
  have e : ((t : ℂ) - 2 * (r : ℂ)) = (((t - 2 * r : ℝ)) : ℂ) := by push_cast; ring
  rw [e]
  refine (norm_exp_mul_le hc _).trans (Real.exp_le_exp.2 ?_)
  refine mul_le_mul_of_nonneg_left ?_ hA
  rw [abs_le]
  constructor <;> linarith [hr.1, hr.2]

theorem rl_smooth {h h' : ℝ → ℂ} (hh : ∀ r, HasDerivAt h (h' r) r) (hh' : Continuous h')
    {c : ℂ} (hc0 : c ≠ 0) {A : ℝ} (hc : |c.re| ≤ A) {t : ℝ} (ht : 0 ≤ t) :
    ‖∫ r in (0 : ℝ)..t, h r * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))‖ ≤
      Real.exp (A * t) * (‖h t‖ + ‖h 0‖ + ∫ r in (0 : ℝ)..t, ‖h' r‖) / (2 * ‖c‖) := by
  set k : ℝ → ℂ := fun r => Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ))) with hkdef
  have hk : ∀ r : ℝ, HasDerivAt k (k r * (c * (-2))) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
    have h2 : HasDerivAt (fun r : ℝ => c * ((t : ℂ) - 2 * (r : ℂ))) (c * (-2)) r := by
      have := ((h1.const_mul (2 : ℂ)).const_sub (t : ℂ)).const_mul c
      convert this using 1
      ring
    exact h2.cexp
  have hc2 : (-2 * c) ≠ 0 := mul_ne_zero (by norm_num) hc0
  have hv : ∀ r : ℝ, HasDerivAt (fun r => k r / (-2 * c)) (k r) r := by
    intro r
    have := (hk r).div_const (-2 * c)
    convert this using 1
    field_simp
  have hkc : Continuous k := by
    simp only [hkdef]
    fun_prop
  have hvc : Continuous (fun r => k r / (-2 * c)) := hkc.div_const _
  have hint1 : IntervalIntegrable h' volume 0 t := hh'.intervalIntegrable 0 t
  have hint2 : IntervalIntegrable k volume 0 t := hkc.intervalIntegrable 0 t
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := h) (u' := h') (v := fun r => k r / (-2 * c)) (v' := k) (a := 0) (b := t)
    (fun x _ => hh x) (fun x _ => hv x) hint1 hint2
  have hkb : ∀ r ∈ Icc (0 : ℝ) t, ‖k r‖ ≤ Real.exp (A * t) := fun r hr =>
    norm_exp_kernel_le hc hr
  have hnc : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hn2 : ‖(-2 * c)‖ = 2 * ‖c‖ := by simp [norm_mul]
  have hkt : ‖k t‖ ≤ Real.exp (A * t) := hkb t ⟨ht, le_rfl⟩
  have hk0 : ‖k 0‖ ≤ Real.exp (A * t) := hkb 0 ⟨le_rfl, ht⟩
  have hI : ‖∫ r in (0 : ℝ)..t, h' r * (k r / (-2 * c))‖ ≤
      ∫ r in (0 : ℝ)..t, ‖h' r‖ * (Real.exp (A * t) / (2 * ‖c‖)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le ht ?_ ?_
    · refine Filter.Eventually.of_forall fun r hr => ?_
      rw [norm_mul, norm_div, hn2]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hkb r ⟨hr.1.le, hr.2⟩) (by positivity)) (norm_nonneg _)
    · exact (hh'.norm.intervalIntegrable 0 t).mul_const _
  rw [intervalIntegral.integral_mul_const] at hI
  have hmain : ∫ r in (0 : ℝ)..t, h r * k r =
      h t * (k t / (-2 * c)) - h 0 * (k 0 / (-2 * c)) -
        ∫ r in (0 : ℝ)..t, h' r * (k r / (-2 * c)) := by
    have := hibp
    simpa using this
  have hbt : ‖h t * (k t / (-2 * c))‖ ≤ ‖h t‖ * (Real.exp (A * t) / (2 * ‖c‖)) := by
    rw [norm_mul, norm_div, hn2]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hkt (by positivity)) (norm_nonneg _)
  have hb0 : ‖h 0 * (k 0 / (-2 * c))‖ ≤ ‖h 0‖ * (Real.exp (A * t) / (2 * ‖c‖)) := by
    rw [norm_mul, norm_div, hn2]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hk0 (by positivity)) (norm_nonneg _)
  show ‖∫ r in (0 : ℝ)..t, h r * k r‖ ≤ _
  rw [hmain]
  calc ‖h t * (k t / (-2 * c)) - h 0 * (k 0 / (-2 * c)) -
        ∫ r in (0 : ℝ)..t, h' r * (k r / (-2 * c))‖
      ≤ ‖h t * (k t / (-2 * c))‖ + ‖h 0 * (k 0 / (-2 * c))‖ +
        ‖∫ r in (0 : ℝ)..t, h' r * (k r / (-2 * c))‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖h t‖ * (Real.exp (A * t) / (2 * ‖c‖)) + ‖h 0‖ * (Real.exp (A * t) / (2 * ‖c‖)) +
        (∫ r in (0 : ℝ)..t, ‖h' r‖) * (Real.exp (A * t) / (2 * ‖c‖)) := by
        gcongr
    _ = Real.exp (A * t) * (‖h t‖ + ‖h 0‖ + ∫ r in (0 : ℝ)..t, ‖h' r‖) / (2 * ‖c‖) := by
        ring

theorem sq_sub_integrable {u f : ℝ → ℂ} (hu : AEStronglyMeasurable u volume)
    (hf : AEStronglyMeasurable f volume)
    (hu2 : IntervalIntegrable (fun s => ‖u s‖ ^ 2) volume 0 1)
    (hf2 : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1) :
    IntervalIntegrable (fun s => ‖u s - f s‖ ^ 2) volume 0 1 := by
  have hg : IntervalIntegrable (fun s => 2 * ‖u s‖ ^ 2 + 2 * ‖f s‖ ^ 2) volume 0 1 :=
    (hu2.const_mul 2).add (hf2.const_mul 2)
  refine hg.mono_fun' ((hu.sub hf).norm.pow 2).restrict (Filter.Eventually.of_forall fun s => ?_)
  show ‖‖u s - f s‖ ^ 2‖ ≤ _
  rw [norm_pow, norm_norm]
  have h := norm_sub_le (u s) (f s)
  nlinarith [sq_nonneg (‖u s‖ - ‖f s‖), norm_nonneg (u s - f s), norm_nonneg (u s), norm_nonneg (f s)]

theorem exists_smooth_approx {f : ℝ → ℂ} (hm : AEStronglyMeasurable f volume)
    (hsq : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h h' : ℝ → ℂ, (∀ r, HasDerivAt h (h' r) r) ∧ Continuous h' ∧ Continuous h ∧
      IntervalIntegrable (fun s => ‖f s - h s‖ ^ 2) volume 0 1 ∧
      ∫ s in (0 : ℝ)..1, ‖f s - h s‖ ^ 2 ≤ δ := by
  set F : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator f with hF
  have hFm : AEStronglyMeasurable F volume := hm.indicator measurableSet_Ioc
  have hFint : Integrable (fun s => ‖F s‖ ^ 2) volume := by
    have e : (fun s => ‖F s‖ ^ 2) = (Ioc (0 : ℝ) 1).indicator (fun s => ‖f s‖ ^ 2) := by
      funext s
      by_cases hs : s ∈ Ioc (0 : ℝ) 1 <;> simp [hF, hs]
    rw [e, integrable_indicator_iff measurableSet_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hsq
  have hF2 : MemLp F 2 volume := (memLp_two_iff_integrable_sq_norm hFm).2 hFint
  have hF2' : MemLp F (ENNReal.ofReal 2) volume := by simpa using hF2
  obtain ⟨g, hgc, hgint, hgcont, hg2⟩ :=
    hF2'.exists_hasCompactSupport_integral_rpow_sub_le (p := 2) (by norm_num) (ε := δ / 4)
      (by positivity)
  have hg2' : MemLp g 2 volume := by simpa using hg2
  have hgu : UniformContinuous g := hgc.uniformContinuous_of_continuous hgcont
  obtain ⟨h, hcd, hdist⟩ := hgu.exists_contDiff_dist_le (ε := Real.sqrt δ / 2)
    (by positivity)
  have hdiff : Differentiable ℝ h := hcd.differentiable (by simp)
  have hcont : Continuous h := hcd.continuous
  have hρint : Integrable (fun s => ‖F s - g s‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (hFm.sub hgcont.aestronglyMeasurable)).1 (hF2.sub hg2')
  have hρ : ∫ s, ‖F s - g s‖ ^ 2 ≤ δ / 4 := by
    simpa [Real.rpow_two] using hgint
  have hη2 : (Real.sqrt δ / 2) ^ 2 = δ / 4 := by
    rw [div_pow, Real.sq_sqrt hδ.le]; norm_num
  have hdom : IntegrableOn (fun s => 2 * ‖F s - g s‖ ^ 2 + 2 * (δ / 4)) (Ioc (0 : ℝ) 1) volume :=
    (hρint.integrableOn.const_mul 2).add (integrableOn_const (by simp))
  have hmeas : AEStronglyMeasurable (fun s => ‖f s - h s‖ ^ 2) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((hm.sub hcont.aestronglyMeasurable).norm.pow 2).restrict
  have hpt : ∀ s ∈ Ioc (0 : ℝ) 1, ‖f s - h s‖ ^ 2 ≤ 2 * ‖F s - g s‖ ^ 2 + 2 * (δ / 4) := by
    intro s hs
    have hFs : F s = f s := by simp [hF, hs]
    have h1 : ‖g s - h s‖ ≤ Real.sqrt δ / 2 := by
      have := hdist s
      rw [dist_eq_norm] at this
      rw [norm_sub_rev]; exact this.le
    have h2 : ‖f s - h s‖ ≤ ‖F s - g s‖ + ‖g s - h s‖ := by
      rw [← hFs]
      calc ‖F s - h s‖ = ‖(F s - g s) + (g s - h s)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h3 : ‖g s - h s‖ ^ 2 ≤ δ / 4 := by
      rw [← hη2]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖F s - g s‖ - ‖g s - h s‖), norm_nonneg (F s - g s),
      norm_nonneg (g s - h s), norm_nonneg (f s - h s)]
  have hIoc : IntegrableOn (fun s => ‖f s - h s‖ ^ 2) (Ioc (0 : ℝ) 1) volume := by
    refine hdom.mono' hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    rw [norm_pow, norm_norm]
    exact hpt s hs
  refine ⟨h, deriv h, fun r => (hdiff r).hasDerivAt, hcd.continuous_deriv (by simp), hcont,
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hIoc, ?_⟩
  rw [intervalIntegral.integral_of_le zero_le_one]
  calc ∫ s in Ioc (0 : ℝ) 1, ‖f s - h s‖ ^ 2
      ≤ ∫ s in Ioc (0 : ℝ) 1, (2 * ‖F s - g s‖ ^ 2 + 2 * (δ / 4)) :=
        setIntegral_mono_on hIoc hdom measurableSet_Ioc hpt
    _ = 2 * (∫ s in Ioc (0 : ℝ) 1, ‖F s - g s‖ ^ 2) + 2 * (δ / 4) := by
        rw [integral_add (hρint.integrableOn.const_mul 2) (integrableOn_const (by simp)),
          integral_const_mul]
        simp
    _ ≤ 2 * (δ / 4) + 2 * (δ / 4) := by
        have := setIntegral_le_integral (s := Ioc (0 : ℝ) 1) hρint
          (Filter.Eventually.of_forall fun s => by positivity)
        linarith
    _ = δ := by ring

theorem rl_uniform {f : ℝ → ℂ} (hm : AEStronglyMeasurable f volume)
    (hsq : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1) {η : ℝ} (hη : 0 < η) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ u : ℝ → ℂ, AEStronglyMeasurable u volume →
      IntervalIntegrable (fun s => ‖u s‖ ^ 2) volume 0 1 →
      (∫ s in (0 : ℝ)..1, ‖u s - f s‖ ^ 2) ≤ η ^ 2 →
      ∀ c : ℂ, Λ < ‖c‖ → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        Real.exp (-|c.re| * t) *
          ‖∫ r in (0 : ℝ)..t, u r * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))‖ ≤ 3 * η := by
  obtain ⟨h, h', hh, hh', hhc, hhint, hhI⟩ := exists_smooth_approx hm hsq (δ := η ^ 2) (by positivity)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hhc.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, zero_le_one⟩)
  set I' : ℝ := ∫ r in (0 : ℝ)..1, ‖h' r‖ with hI'
  have hI'0 : 0 ≤ I' := intervalIntegral.integral_nonneg zero_le_one fun r _ => norm_nonneg _
  refine ⟨max 1 ((2 * M + I') / (2 * η)), le_max_left _ _, ?_⟩
  intro u hum hu2 hufI c hc t ht0 ht1
  have hc1 : 1 < ‖c‖ := lt_of_le_of_lt (le_max_left _ _) hc
  have hc0 : c ≠ 0 := norm_pos_iff.1 (by linarith)
  set A : ℝ := |c.re| with hA
  have hcA : |c.re| ≤ A := le_rfl
  have hku : ∀ r ∈ Icc (0 : ℝ) t, ‖Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))‖ ≤ Real.exp (A * t) :=
    fun r hr => norm_exp_kernel_le hcA hr
  have hkc : Continuous (fun r : ℝ => Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))) := by fun_prop
  -- L² bound for u - h
  have hfI := sq_sub_integrable hum hm hu2 hsq
  have huhI : IntervalIntegrable (fun s => ‖u s - h s‖ ^ 2) volume 0 1 := by
    have hg : IntervalIntegrable (fun s => 2 * ‖u s - f s‖ ^ 2 + 2 * ‖f s - h s‖ ^ 2) volume 0 1 :=
      (hfI.const_mul 2).add (hhint.const_mul 2)
    refine hg.mono_fun' ((hum.sub hhc.aestronglyMeasurable).norm.pow 2).restrict
      (Filter.Eventually.of_forall fun s => ?_)
    show ‖‖u s - h s‖ ^ 2‖ ≤ _
    rw [norm_pow, norm_norm]
    have h1 := norm_sub_le (u s - f s) (h s - f s)
    have e : u s - h s = (u s - f s) + (f s - h s) := by ring
    have h2 : ‖u s - h s‖ ≤ ‖u s - f s‖ + ‖f s - h s‖ := by
      rw [e]; exact norm_add_le _ _
    nlinarith [sq_nonneg (‖u s - f s‖ - ‖f s - h s‖), norm_nonneg (u s - h s),
      norm_nonneg (u s - f s), norm_nonneg (f s - h s)]
  have huh4 : ∫ s in (0 : ℝ)..1, ‖u s - h s‖ ^ 2 ≤ 4 * η ^ 2 := by
    have hg : IntervalIntegrable (fun s => 2 * ‖u s - f s‖ ^ 2 + 2 * ‖f s - h s‖ ^ 2) volume 0 1 :=
      (hfI.const_mul 2).add (hhint.const_mul 2)
    calc ∫ s in (0 : ℝ)..1, ‖u s - h s‖ ^ 2
        ≤ ∫ s in (0 : ℝ)..1, (2 * ‖u s - f s‖ ^ 2 + 2 * ‖f s - h s‖ ^ 2) := by
          refine intervalIntegral.integral_mono_on zero_le_one huhI hg fun s _ => ?_
          have e : u s - h s = (u s - f s) + (f s - h s) := by ring
          have h2 : ‖u s - h s‖ ≤ ‖u s - f s‖ + ‖f s - h s‖ := by
            rw [e]; exact norm_add_le _ _
          nlinarith [sq_nonneg (‖u s - f s‖ - ‖f s - h s‖), norm_nonneg (u s - h s),
            norm_nonneg (u s - f s), norm_nonneg (f s - h s)]
      _ = 2 * (∫ s in (0 : ℝ)..1, ‖u s - f s‖ ^ 2) + 2 * ∫ s in (0 : ℝ)..1, ‖f s - h s‖ ^ 2 := by
          rw [intervalIntegral.integral_add (hfI.const_mul 2) (hhint.const_mul 2),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ 4 * η ^ 2 := by linarith
  have huht : ∫ s in (0 : ℝ)..t, ‖u s - h s‖ ^ 2 ≤ 4 * η ^ 2 := by
    refine le_trans ?_ huh4
    refine intervalIntegral.integral_mono_interval le_rfl ht0 ht1
      (Filter.Eventually.of_forall fun s => ?_) huhI
    exact (sq_nonneg ‖u s - h s‖ : (0 : ℝ) ≤ ‖u s - h s‖ ^ 2)
  -- split
  have huint : IntervalIntegrable u volume 0 t := by
    have hg : IntervalIntegrable (fun s : ℝ => 1 + ‖u s‖ ^ 2) volume 0 1 :=
      intervalIntegrable_const.add hu2
    have h1 : IntervalIntegrable u volume 0 1 := by
      refine hg.mono_fun' hum.restrict (Filter.Eventually.of_forall fun s => ?_)
      show ‖u s‖ ≤ 1 + ‖u s‖ ^ 2
      nlinarith [sq_nonneg (‖u s‖ - 1), norm_nonneg (u s)]
    exact h1.mono_set (by
      rw [Set.uIcc_of_le ht0, Set.uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl ht1)
  have hkcon : ContinuousOn (fun r : ℝ => Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))) (uIcc 0 t) :=
    hkc.continuousOn
  have hu_k : IntervalIntegrable (fun r => u r * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ))))
      volume 0 t := huint.mul_continuousOn hkcon
  have hh_k : IntervalIntegrable (fun r => h r * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ))))
      volume 0 t := (hhc.intervalIntegrable 0 t).mul_continuousOn hkcon
  have hsplit : (∫ r in (0 : ℝ)..t, u r * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))) =
      (∫ r in (0 : ℝ)..t, (u r - h r) * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))) +
        ∫ r in (0 : ℝ)..t, h r * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ))) := by
    rw [← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun r _ => ?_
      ring
    · have := hu_k.sub hh_k
      refine this.congr ?_
      intro r _
      simp only [Pi.sub_apply]
      ring
    · exact hh_k
  -- first term
  have hq1 : ‖∫ r in (0 : ℝ)..t, (u r - h r) * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))‖ ≤
      Real.exp (A * t) * (2 * η) := by
    have hsub : IntervalIntegrable (fun r => ‖u r - h r‖) volume 0 t :=
      ((huint.sub (hhc.intervalIntegrable 0 t)).norm)
    have hb : ‖∫ r in (0 : ℝ)..t, (u r - h r) * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))‖ ≤
        ∫ r in (0 : ℝ)..t, ‖u r - h r‖ * Real.exp (A * t) := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht0 ?_ (hsub.mul_const _)
      refine Filter.Eventually.of_forall fun r hr => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hku r ⟨hr.1.le, hr.2⟩) (norm_nonneg _)
    rw [intervalIntegral.integral_mul_const] at hb
    have hcs := NlsGge.GK38.integral_norm_le_sqrt_mul (g := fun r => u r - h r) ht0
      (hum.sub hhc.aestronglyMeasurable)
      (huhI.mono_set (by
        rw [Set.uIcc_of_le ht0, Set.uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl ht1))
    have hsq2 : Real.sqrt (∫ r in (0 : ℝ)..t, ‖u r - h r‖ ^ 2) ≤ 2 * η := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      nlinarith [huht]
    have hst : Real.sqrt (t - 0) ≤ 1 := by
      rw [sub_zero]; exact Real.sqrt_le_one.2 ht1
    have hI2 : ∫ r in (0 : ℝ)..t, ‖u r - h r‖ ≤ 2 * η := by
      refine hcs.trans ?_
      calc Real.sqrt (t - 0) * Real.sqrt (∫ r in (0 : ℝ)..t, ‖u r - h r‖ ^ 2)
          ≤ 1 * (2 * η) := mul_le_mul hst hsq2 (Real.sqrt_nonneg _) zero_le_one
        _ = 2 * η := one_mul _
    calc _ ≤ (∫ r in (0 : ℝ)..t, ‖u r - h r‖) * Real.exp (A * t) := hb
      _ ≤ (2 * η) * Real.exp (A * t) :=
          mul_le_mul_of_nonneg_right hI2 (Real.exp_pos _).le
      _ = Real.exp (A * t) * (2 * η) := mul_comm _ _
  -- second term
  have hq2 : ‖∫ r in (0 : ℝ)..t, h r * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))‖ ≤
      Real.exp (A * t) * η := by
    have hb := rl_smooth hh hh' hc0 hcA ht0
    have hCb : ‖h t‖ + ‖h 0‖ + ∫ r in (0 : ℝ)..t, ‖h' r‖ ≤ 2 * M + I' := by
      have h1 : ‖h t‖ ≤ M := hM t ⟨ht0, ht1⟩
      have h2 : ‖h 0‖ ≤ M := hM 0 ⟨le_rfl, zero_le_one⟩
      have h3 : ∫ r in (0 : ℝ)..t, ‖h' r‖ ≤ I' := by
        refine intervalIntegral.integral_mono_interval le_rfl ht0 ht1
          (Filter.Eventually.of_forall fun r => norm_nonneg _) (hh'.norm.intervalIntegrable 0 1)
      linarith
    have hden : (2 * M + I') / (2 * ‖c‖) ≤ η := by
      have : (2 * M + I') / (2 * η) < ‖c‖ := lt_of_le_of_lt (le_max_right _ _) hc
      rw [div_lt_iff₀ (by positivity)] at this
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc _ ≤ Real.exp (A * t) * (‖h t‖ + ‖h 0‖ + ∫ r in (0 : ℝ)..t, ‖h' r‖) / (2 * ‖c‖) := hb
      _ ≤ Real.exp (A * t) * (2 * M + I') / (2 * ‖c‖) := by
          gcongr
      _ = Real.exp (A * t) * ((2 * M + I') / (2 * ‖c‖)) := by ring
      _ ≤ Real.exp (A * t) * η := mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
  rw [hsplit]
  have hw : Real.exp (-A * t) * Real.exp (A * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-|c.re| * t) * ‖(∫ r in (0 : ℝ)..t, (u r - h r) * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))) +
          ∫ r in (0 : ℝ)..t, h r * Complex.exp (c * ((t : ℂ) - 2 * (r : ℂ)))‖
      ≤ Real.exp (-A * t) * (Real.exp (A * t) * (2 * η) + Real.exp (A * t) * η) := by
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hq1 hq2))
          (Real.exp_pos _).le
    _ = 3 * η := by
        have : Real.exp (-A * t) * (Real.exp (A * t) * (2 * η) + Real.exp (A * t) * η) =
            (Real.exp (-A * t) * Real.exp (A * t)) * (3 * η) := by ring
        rw [this, hw, one_mul]

end

end NlsGge.Atomic.G1050S2.K47.K17

open NlsGge.Pilot

namespace NlsGge.Atomic.G1050S2.K47.K17

noncomputable section

theorem freeE_mul_apply' (z : ℂ) (a : ℝ) (X : PairMat38) (i j : Fin 2) :
    (freeE z a * X) i j = freeE z a i i * X i j := by
  fin_cases i <;> fin_cases j <;> simp [freeE, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_freeE_apply' (z : ℂ) (a : ℝ) (X : PairMat38) (i j : Fin 2) :
    (X * freeE z a) i j = X i j * freeE z a j j := by
  fin_cases i <;> fin_cases j <;> simp [freeE, Matrix.mul_apply, Fin.sum_univ_two]

theorem M1_entry (ψ : PotPair) (z : ℂ) (t : ℝ) (i j : Fin 2) :
    potentialVolterraTerm38 ψ z 1 t i j =
      ∫ r in (0 : ℝ)..t, freeE z (t - r) i i * rawPotCoeff38 (potRepFst38 ψ) (potRepSnd38 ψ) r i j *
        freeE z r j j := by
  have h : potentialVolterraTerm38 ψ z 1 t i j = ∫ r in (0 : ℝ)..t,
      (freeZsFundamentalComplex z (t - r) * rawPotCoeff38 (potRepFst38 ψ) (potRepSnd38 ψ) r *
        freeZsFundamentalComplex z r) i j := rfl
  rw [h]
  refine intervalIntegral.integral_congr fun r _ => ?_
  rw [← freeE_eq, ← freeE_eq, mul_freeE_apply', freeE_mul_apply']

theorem M1_diag (ψ : PotPair) (z : ℂ) (t : ℝ) (i : Fin 2) :
    potentialVolterraTerm38 ψ z 1 t i i = 0 := by
  rw [M1_entry]
  have : ∀ r : ℝ, freeE z (t - r) i i * rawPotCoeff38 (potRepFst38 ψ) (potRepSnd38 ψ) r i i *
      freeE z r i i = 0 := by
    intro r
    fin_cases i <;> simp [rawPotCoeff38]
  simp [this]

theorem M1_01 (ψ : PotPair) (z : ℂ) (t : ℝ) :
    potentialVolterraTerm38 ψ z 1 t 0 1 = Complex.I *
      ∫ r in (0 : ℝ)..t, potRepFst38 ψ r *
        Complex.exp (-(Complex.I * z) * ((t : ℂ) - 2 * (r : ℂ))) := by
  rw [M1_entry, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have e : Complex.exp (-(Complex.I * z * (((t - r : ℝ)) : ℂ))) * Complex.exp (Complex.I * z * (r : ℂ)) =
      Complex.exp (-(Complex.I * z) * ((t : ℂ) - 2 * (r : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [freeE, rawPotCoeff38, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  calc _ = Complex.I * potRepFst38 ψ r *
        (Complex.exp (-(Complex.I * z * (((t - r : ℝ)) : ℂ))) * Complex.exp (Complex.I * z * (r : ℂ))) := by
        ring
    _ = _ := by rw [e]; ring

theorem M1_10 (ψ : PotPair) (z : ℂ) (t : ℝ) :
    potentialVolterraTerm38 ψ z 1 t 1 0 = -(Complex.I *
      ∫ r in (0 : ℝ)..t, potRepSnd38 ψ r *
        Complex.exp ((Complex.I * z) * ((t : ℂ) - 2 * (r : ℂ)))) := by
  rw [M1_entry, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have e : Complex.exp (Complex.I * z * (((t - r : ℝ)) : ℂ)) * Complex.exp (-(Complex.I * z * (r : ℂ))) =
      Complex.exp ((Complex.I * z) * ((t : ℂ) - 2 * (r : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [freeE, rawPotCoeff38, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  calc _ = -(Complex.I * potRepSnd38 ψ r) *
        (Complex.exp (Complex.I * z * (((t - r : ℝ)) : ℂ)) * Complex.exp (-(Complex.I * z * (r : ℂ)))) := by
        ring
    _ = _ := by rw [e]; ring

theorem repr_aem (f : PhysicalL2) : AEStronglyMeasurable (coverRep38 f) volume :=
  (stronglyMeasurable_coverRep38 f).aestronglyMeasurable

theorem repr_diff_int (ψ φ : PotPair) (η : ℝ) (hψ : ‖ψ - φ‖ < η) :
    (∫ s in (0 : ℝ)..1, ‖potRepFst38 ψ s - potRepFst38 φ s‖ ^ 2) ≤ η ^ 2 ∧
    (∫ s in (0 : ℝ)..1, ‖potRepSnd38 ψ s - potRepSnd38 φ s‖ ^ 2) ≤ η ^ 2 := by
  have key : ∀ f g : PhysicalL2, ‖f - g‖ < η →
      (∫ s in (0 : ℝ)..1, ‖coverRep38 f s - coverRep38 g s‖ ^ 2) ≤ η ^ 2 := by
    intro f g hfg
    have hae : ∀ᵐ s : ℝ, coverRep38 (f - g) s = coverRep38 f s - coverRep38 g s :=
      coverRep38_sub_ae f g
    have e : (∫ s in (0 : ℝ)..1, ‖coverRep38 f s - coverRep38 g s‖ ^ 2) =
        ∫ s in (0 : ℝ)..1, ‖coverRep38 (f - g) s‖ ^ 2 := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with s hs _
      rw [hs]
    rw [e, integral_sq_coverRep38_one]
    exact pow_le_pow_left₀ (norm_nonneg _) hfg.le 2
  have h1 : ‖(ψ - φ).1‖ ≤ ‖ψ - φ‖ := norm_fst_le _
  have h2 : ‖(ψ - φ).2‖ ≤ ‖ψ - φ‖ := norm_snd_le _
  exact ⟨key ψ.1 φ.1 (lt_of_le_of_lt h1 hψ), key ψ.2 φ.2 (lt_of_le_of_lt h2 hψ)⟩

theorem M1_weighted_small (φ : PotPair) {η : ℝ} (hη : 0 < η) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ ψ : PotPair, ‖ψ - φ‖ < η → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, Λ < ‖z‖ →
      Real.exp (-|z.im| * t) * ‖potentialVolterraTerm38 ψ z 1 t‖ ≤ 3 * η := by
  obtain ⟨Λ₁, h1, hΛ₁⟩ := rl_uniform (repr_aem φ.1) (intervalIntegrable_coverRep38_sq_one φ.1) hη
  obtain ⟨Λ₂, h2, hΛ₂⟩ := rl_uniform (repr_aem φ.2) (intervalIntegrable_coverRep38_sq_one φ.2) hη
  refine ⟨max Λ₁ Λ₂, le_trans h1 (le_max_left _ _), ?_⟩
  intro ψ hψ t ht0 ht1 z hz
  obtain ⟨hd1, hd2⟩ := repr_diff_int ψ φ η hψ
  have hz1 : Λ₁ < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hz2 : Λ₂ < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
  have b1 := hΛ₁ (potRepFst38 ψ) (repr_aem ψ.1) (intervalIntegrable_coverRep38_sq_one ψ.1) hd1
    (-(Complex.I * z)) (by simpa [norm_mul] using hz1) t ht0 ht1
  have b2 := hΛ₂ (potRepSnd38 ψ) (repr_aem ψ.2) (intervalIntegrable_coverRep38_sq_one ψ.2) hd2
    (Complex.I * z) (by simpa [norm_mul] using hz2) t ht0 ht1
  have re1 : |(-(Complex.I * z)).re| = |z.im| := by simp
  have re2 : |(Complex.I * z).re| = |z.im| := by simp
  rw [re1] at b1
  rw [re2] at b2
  have hC : 0 ≤ 3 * η * Real.exp (|z.im| * t) := by positivity
  have hmat : ‖potentialVolterraTerm38 ψ z 1 t‖ ≤ 3 * η * Real.exp (|z.im| * t) := by
    refine K16.odd_sparse_matrix_opNorm_le _ _ hC (fun i => M1_diag ψ z t i) (fun i => ?_)
    have hw : ∀ x : ℝ, Real.exp (-|z.im| * t) * x ≤ 3 * η → x ≤ 3 * η * Real.exp (|z.im| * t) := by
      intro x hx
      have e : x = Real.exp (|z.im| * t) * (Real.exp (-|z.im| * t) * x) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
      rw [e]
      calc Real.exp (|z.im| * t) * (Real.exp (-|z.im| * t) * x)
          ≤ Real.exp (|z.im| * t) * (3 * η) := mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
        _ = 3 * η * Real.exp (|z.im| * t) := mul_comm _ _
    rcases (by fin_cases i <;> simp : i = 0 ∨ i = 1) with rfl | rfl
    · have ho : K16.otherFin2 0 = 1 := by simp [K16.otherFin2]
      rw [ho, M1_01, norm_mul, Complex.norm_I, one_mul]
      exact hw _ b1
    · have ho : K16.otherFin2 1 = 0 := by simp [K16.otherFin2]
      rw [ho, M1_10, norm_neg, norm_mul, Complex.norm_I, one_mul]
      exact hw _ b2
  have hexp : Real.exp (-|z.im| * t) * Real.exp (|z.im| * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-|z.im| * t) * ‖potentialVolterraTerm38 ψ z 1 t‖
      ≤ Real.exp (-|z.im| * t) * (3 * η * Real.exp (|z.im| * t)) :=
        mul_le_mul_of_nonneg_left hmat (Real.exp_pos _).le
    _ = (Real.exp (-|z.im| * t) * Real.exp (|z.im| * t)) * (3 * η) := by ring
    _ = 3 * η := by rw [hexp, one_mul]

theorem differentiableAt_M (ψ : PotPair) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => ∑' n : ℕ, potentialVolterraTerm38 ψ w n t) z := by
  have h := NlsGge.Atomic.G1004GenT.analytic_all t ht (z, ψ) (Set.mem_univ _)
  have hc : AnalyticAt ℂ (fun w : ℂ => (w, ψ)) z :=
    analyticAt_id.prod analyticAt_const
  have h2 := AnalyticAt.comp (g := fun p : ℂ × PotPair => ∑' n : ℕ, potentialVolterraTerm38 p.2 p.1 n t)
    (f := fun w : ℂ => (w, ψ)) (x := z) h hc
  exact h2.differentiableAt

theorem differentiable_E (t : ℝ) : Differentiable ℂ (fun w : ℂ => freeZsFundamentalComplex w t) := by
  intro z
  have h : AnalyticAt ℂ (fun w : ℂ => freeE w t) z := by
    refine NlsGge.Atomic.G1004GenT.analyticAt_of_entries fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [freeE] <;> fun_prop
  have e : (fun w : ℂ => freeZsFundamentalComplex w t) = fun w => freeE w t := by
    funext w; exact (freeE_eq w t).symm
  rw [e]
  exact h.differentiableAt

end

end NlsGge.Atomic.G1050S2.K47.K17

/-! ### The final statement -/

namespace NlsGge.Atomic.G1050S2.K47.K17

noncomputable section

theorem G1017_whole : ((
  ∀ (φ : PotPair) (ε : ℝ), 0 < ε →
  ∃ U : Set PotPair, U ∈ nhds φ ∧ ∃ Λ : ℝ,
    ∀ ψ ∈ U, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, Λ < ‖z‖ →
      DifferentiableAt ℂ (fun w : ℂ => ∑' n : ℕ, potentialVolterraTerm38 ψ w n t) z ∧
      Real.exp (-|z.im| * t) *
          ‖(∑' n : ℕ, potentialVolterraTerm38 ψ z n t) - freeZsFundamentalComplex z t‖ ≤ ε ∧
      Real.exp (-|z.im| * t) *
          ‖deriv (fun w : ℂ => ∑' n : ℕ, potentialVolterraTerm38 ψ w n t) z -
            deriv (fun w : ℂ => freeZsFundamentalComplex w t) z‖ ≤ ε
  : Prop)) := by
  intro φ ε hε
  set B : ℝ := ‖φ.1‖ + ‖φ.2‖ + 2 with hB
  have hB0 : 0 ≤ B := by positivity
  set K : ℝ := 1 + B * Real.exp B with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ B * Real.exp B := by positivity
    linarith
  set η : ℝ := min 1 (ε / (9 * K)) with hη
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ ε / (9 * K) := min_le_right _ _
  obtain ⟨Λ, hΛ1, hsmall⟩ := M1_weighted_small φ hηpos
  refine ⟨Metric.ball φ η, Metric.ball_mem_nhds φ hηpos, Λ + 1, ?_⟩
  intro ψ hψ t ht0 ht1 z hz
  have hψd : ‖ψ - φ‖ < η := by simpa [dist_eq_norm] using hψ
  -- the first estimate at every w beyond Λ
  have key : ∀ w : ℂ, Λ < ‖w‖ →
      Real.exp (-|w.im| * t) *
        ‖(∑' n : ℕ, potentialVolterraTerm38 ψ w n t) - freeZsFundamentalComplex w t‖ ≤ ε / 3 := by
    intro w hw
    obtain ⟨hint, hb⟩ := K16.G1016_whole ψ w t ht0 ht1
    have ha : ∀ s ∈ Icc (0 : ℝ) 1, Real.exp (-|w.im| * s) * ‖potentialVolterraTerm38 ψ w 1 s‖ ≤ 3 * η :=
      fun s hs => hsmall ψ hψd s hs.1 hs.2 w hw
    have hI : ∫ s in (0 : ℝ)..t, (Real.exp (-|w.im| * s) * ‖potentialVolterraTerm38 ψ w 1 s‖) ^ 2 ≤
        (3 * η) ^ 2 := by
      have h1 : ∫ s in (0 : ℝ)..t, (Real.exp (-|w.im| * s) * ‖potentialVolterraTerm38 ψ w 1 s‖) ^ 2 ≤
          ∫ s in (0 : ℝ)..t, (3 * η) ^ 2 := by
        refine intervalIntegral.integral_mono_on ht0 hint intervalIntegrable_const fun s hs => ?_
        have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht1⟩
        exact pow_le_pow_left₀ (by positivity) (ha s hs') 2
      refine h1.trans ?_
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      have : 0 ≤ (3 * η) ^ 2 := sq_nonneg _
      nlinarith
    have hsq : Real.sqrt (∫ s in (0 : ℝ)..t,
        (Real.exp (-|w.im| * s) * ‖potentialVolterraTerm38 ψ w 1 s‖) ^ 2) ≤ 3 * η :=
      Real.sqrt_le_iff.2 ⟨by positivity, hI⟩
    have hN : Real.sqrt (‖ψ.1‖ ^ 2 + ‖ψ.2‖ ^ 2) ≤ B := by
      have h1 : ‖ψ.1‖ ≤ ‖φ.1‖ + 1 := by
        have : ‖ψ.1‖ ≤ ‖φ.1‖ + ‖(ψ - φ).1‖ := by
          calc ‖ψ.1‖ = ‖φ.1 + (ψ - φ).1‖ := by simp
            _ ≤ _ := norm_add_le _ _
        have := norm_fst_le (ψ - φ)
        linarith
      have h2 : ‖ψ.2‖ ≤ ‖φ.2‖ + 1 := by
        have : ‖ψ.2‖ ≤ ‖φ.2‖ + ‖(ψ - φ).2‖ := by
          calc ‖ψ.2‖ = ‖φ.2 + (ψ - φ).2‖ := by simp
            _ ≤ _ := norm_add_le _ _
        have := norm_snd_le (ψ - φ)
        linarith
      refine Real.sqrt_le_iff.2 ⟨hB0, ?_⟩
      nlinarith [norm_nonneg ψ.1, norm_nonneg ψ.2, norm_nonneg φ.1, norm_nonneg φ.2]
    have hc : Real.sqrt (‖ψ.1‖ ^ 2 + ‖ψ.2‖ ^ 2) * Real.exp (Real.sqrt (‖ψ.1‖ ^ 2 + ‖ψ.2‖ ^ 2)) ≤
        B * Real.exp B :=
      mul_le_mul hN (Real.exp_le_exp.2 hN) (Real.exp_pos _).le hB0
    have hfirst : Real.exp (-|w.im| * t) * ‖potentialVolterraTerm38 ψ w 1 t‖ ≤ 3 * η :=
      ha t ⟨ht0, ht1⟩
    calc _ ≤ _ := hb
      _ ≤ 3 * η + (B * Real.exp B) * (3 * η) := by
          refine add_le_add hfirst ?_
          calc (Real.sqrt (‖ψ.1‖ ^ 2 + ‖ψ.2‖ ^ 2) * Real.exp (Real.sqrt (‖ψ.1‖ ^ 2 + ‖ψ.2‖ ^ 2))) *
                Real.sqrt (∫ s in (0 : ℝ)..t,
                  (Real.exp (-|w.im| * s) * ‖potentialVolterraTerm38 ψ w 1 s‖) ^ 2)
              ≤ (B * Real.exp B) * (3 * η) :=
                mul_le_mul hc hsq (Real.sqrt_nonneg _) (by positivity)
            _ = _ := rfl
      _ = 3 * η * K := by rw [hK]; ring
      _ ≤ ε / 3 := by
          have h9 : 3 * η * K ≤ 3 * (ε / (9 * K)) * K :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
          have h10 : 3 * (ε / (9 * K)) * K = ε / 3 := by
            field_simp
            ring
          linarith
  have hdiffM := differentiableAt_M ψ ht0
  have hdiffE := differentiable_E t
  refine ⟨hdiffM z, ?_, ?_⟩
  · have := key z (by linarith)
    linarith
  · set G : ℂ → PairMat38 := fun w => (∑' n : ℕ, potentialVolterraTerm38 ψ w n t) -
      freeZsFundamentalComplex w t with hG
    have hGd : Differentiable ℂ G := fun w => (hdiffM w).sub (hdiffE w)
    have hderiv : deriv (fun w : ℂ => ∑' n : ℕ, potentialVolterraTerm38 ψ w n t) z -
        deriv (fun w : ℂ => freeZsFundamentalComplex w t) z = deriv G z :=
      (deriv_sub (hdiffM z) (hdiffE z)).symm
    rw [hderiv]
    have hC : ∀ w ∈ Metric.sphere z 1, ‖G w‖ ≤ (ε / 3) * Real.exp ((|z.im| + 1) * t) := by
      intro w hw
      have hwz : ‖w - z‖ = 1 := by simpa [dist_eq_norm] using hw
      have hwn : Λ < ‖w‖ := by
        have : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
          calc ‖z‖ = ‖w - (w - z)‖ := by simp
            _ ≤ _ := norm_sub_le _ _
        linarith
      have hk := key w hwn
      have him : |w.im| ≤ |z.im| + 1 := by
        have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
        have h2 : w.im = z.im + (w - z).im := by simp
        calc |w.im| = |z.im + (w - z).im| := by rw [← h2]
          _ ≤ |z.im| + |(w - z).im| := abs_add_le _ _
          _ ≤ |z.im| + 1 := by linarith
      have hGw : ‖G w‖ ≤ (ε / 3) * Real.exp (|w.im| * t) := by
        have hpos : 0 < Real.exp (-|w.im| * t) := Real.exp_pos _
        have h3 : Real.exp (-|w.im| * t) * ‖G w‖ ≤ ε / 3 := hk
        have e : ‖G w‖ = Real.exp (|w.im| * t) * (Real.exp (-|w.im| * t) * ‖G w‖) := by
          rw [← mul_assoc, ← Real.exp_add]; simp
        rw [e]
        calc Real.exp (|w.im| * t) * (Real.exp (-|w.im| * t) * ‖G w‖)
            ≤ Real.exp (|w.im| * t) * (ε / 3) :=
              mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
          _ = (ε / 3) * Real.exp (|w.im| * t) := mul_comm _ _
      refine hGw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
      exact mul_le_mul_of_nonneg_right him ht0
    have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hGd.diffContOnCl hC
    rw [div_one] at hcau
    have hexp : Real.exp (-|z.im| * t) * Real.exp ((|z.im| + 1) * t) = Real.exp t := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp1 : Real.exp t ≤ 3 := by
      have : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.2 ht1
      have := Real.exp_one_lt_d9
      linarith
    calc Real.exp (-|z.im| * t) * ‖deriv G z‖
        ≤ Real.exp (-|z.im| * t) * ((ε / 3) * Real.exp ((|z.im| + 1) * t)) :=
          mul_le_mul_of_nonneg_left hcau (Real.exp_pos _).le
      _ = (ε / 3) * Real.exp t := by rw [← hexp]; ring
      _ ≤ (ε / 3) * 3 := mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = ε := by ring

end

end NlsGge.Atomic.G1050S2.K47.K17



/-! ### G1-047: characteristic comparison outside the discs -/

namespace NlsGge.Atomic.G1050S2.K47

noncomputable section

theorem series_eq_fundPair (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    ∑' n : ℕ, potentialVolterraTerm38 φ z n t.1 = fundPair φ z t := by
  have ht : t.1 ∈ Set.Icc (0 : ℝ) 1 := t.2
  rw [NlsGge.Atomic.G1004GenT.tsum_terms_eq_fundContT φ z zero_le_one ht]
  rfl

theorem series_one_eq_monodromyPair (φ : PotPair) (z : ℂ) :
    ∑' n : ℕ, potentialVolterraTerm38 φ z n 1 = monodromyPair φ z := by
  rw [monodromyPair_eq_fundPair]
  exact series_eq_fundPair φ z ⟨1, zero_le_one, le_rfl⟩

theorem entry_le_l2 (A : PairMat38) (i k : Fin 2) : ‖A i k‖ ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single k (1 : ℂ))
  have h1 : ‖(EuclideanSpace.single k (1 : ℂ))‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le
    ((EuclideanSpace.equiv (Fin 2) ℂ).symm (A.mulVec (EuclideanSpace.single k (1 : ℂ)))) i
  simpa [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply] using h2

theorem norm_trace_le (A : PairMat38) : ‖Matrix.trace A‖ ≤ 2 * ‖A‖ := by
  rw [Matrix.trace_fin_two]
  have h0 := entry_le_l2 A 0 0
  have h1 := entry_le_l2 A 1 1
  calc ‖A 0 0 + A 1 1‖ ≤ ‖A 0 0‖ + ‖A 1 1‖ := norm_add_le _ _
    _ ≤ 2 * ‖A‖ := by linarith

theorem hasDerivAt_trace {f : ℂ → PairMat38} {f' : PairMat38} {z : ℂ} (h : HasDerivAt f f' z) :
    HasDerivAt (fun w => Matrix.trace (f w)) (Matrix.trace f') z := by
  let T : PairMat38 →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  have h2 := T.hasFDerivAt.comp_hasDerivAt z h
  have e : (T ∘ f) = fun w => Matrix.trace (f w) := rfl
  have e' : T f' = Matrix.trace f' := rfl
  rw [e, e'] at h2
  exact h2

theorem unweight {a X A : ℝ} (h : Real.exp (-a * 1) * X ≤ A) : X ≤ A * Real.exp a := by
  have hw : Real.exp (-a * 1) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  have h1 := mul_le_mul_of_nonneg_left h (Real.exp_pos a).le
  have key : Real.exp a * (Real.exp (-a * 1) * X) = X := by
    rw [← mul_assoc, mul_comm (Real.exp a), hw, one_mul]
  rw [key] at h1
  linarith [mul_comm (Real.exp a) A]

theorem trace_freeZs (z : ℂ) : Matrix.trace (freeZsFundamentalComplex z 1) = 2 * Complex.cos z := by
  rw [← freeE_eq, ← monodromyPair_zero_potential]
  exact trace_monodromyPair_zero z

theorem norm_cos_le (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h1 : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_I_re]
    exact Real.exp_le_exp.2 (neg_le_abs _)
  have h2 : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_I_re, Complex.neg_im]
    exact Real.exp_le_exp.2 (by simpa using le_abs_self z.im)
  rw [Complex.cos, norm_div]
  have h3 : ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖ ≤ 2 * Real.exp |z.im| :=
    (norm_add_le _ _).trans (by linarith)
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h4, div_le_iff₀ (by norm_num)]
  linarith

theorem G1047_whole : ((
  ∀ (φ : PotPair) (ε : ℝ), 0 < ε →
  ∃ U : Set PotPair, U ∈ nhds φ ∧ ∃ Λ : ℝ,
    ∀ ψ ∈ U, ∀ z : ℂ, Λ < ‖z‖ → (∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖) →
      DifferentiableAt ℂ (fun w : ℂ => Matrix.trace (monodromyPair ψ w)) z ∧
      ‖((Matrix.trace (monodromyPair ψ z)) ^ 2 - 4) / (-4 * Complex.sin z ^ 2) - 1‖ ≤ ε ∧
      ‖deriv (fun w : ℂ => Matrix.trace (monodromyPair ψ w)) z / (-2 * Complex.sin z) - 1‖ ≤ ε
  : Prop)) := by
  intro φ ε hε
  set A : ℝ := min 1 (ε / 48) with hA
  have hApos : 0 < A := lt_min one_pos (by positivity)
  have hA1 : A ≤ 1 := min_le_left _ _
  have hA48 : A ≤ ε / 48 := min_le_right _ _
  obtain ⟨U, hU, Λ, hΛ⟩ := K17.G1017_whole φ A hApos
  refine ⟨U, hU, Λ, ?_⟩
  intro ψ hψ z hz hdisc
  have hs := NlsGge.Atomic.G1.sin_lower_outside_discs z hdisc
  obtain ⟨hdiff, hb1, hb2⟩ := hΛ ψ hψ 1 zero_le_one le_rfl z hz
  have e : ∀ w : ℂ, ∑' n : ℕ, potentialVolterraTerm38 ψ w n 1 = monodromyPair ψ w :=
    fun w => series_one_eq_monodromyPair ψ w
  simp only [e] at hdiff hb1 hb2
  set R : ℝ := Real.exp |z.im| with hR
  have hRpos : 0 < R := Real.exp_pos _
  have hs0 : 0 < ‖Complex.sin z‖ := by
    have : 0 < 4 * ‖Complex.sin z‖ := lt_trans hRpos hs
    linarith
  have hs0' : Complex.sin z ≠ 0 := norm_pos_iff.1 hs0
  have hsR : R / 4 < ‖Complex.sin z‖ := by linarith
  have hcos : ‖Complex.cos z‖ ≤ R := norm_cos_le z
  -- unweighted bounds
  have hMb : ‖monodromyPair ψ z - freeZsFundamentalComplex z 1‖ ≤ A * R := unweight hb1
  have hdiffE := K17.differentiable_E 1
  have hMd : DifferentiableAt ℂ (fun w : ℂ => monodromyPair ψ w) z := hdiff
  have hdM := hMd.hasDerivAt
  have hdE := (hdiffE z).hasDerivAt
  have hDb : ‖deriv (fun w : ℂ => monodromyPair ψ w) z -
      deriv (fun w : ℂ => freeZsFundamentalComplex w 1) z‖ ≤ A * R := unweight hb2
  have hTd := hasDerivAt_trace hdM
  refine ⟨hTd.differentiableAt, ?_, ?_⟩
  · -- the discriminant ratio
    set D : ℂ := Matrix.trace (monodromyPair ψ z) with hD
    set δ : ℂ := D - 2 * Complex.cos z with hδ
    have hδb : ‖δ‖ ≤ 2 * (A * R) := by
      have : δ = Matrix.trace (monodromyPair ψ z - freeZsFundamentalComplex z 1) := by
        rw [Matrix.trace_sub, trace_freeZs]
      rw [this]
      exact (norm_trace_le _).trans (by linarith)
    have hcs : Complex.cos z ^ 2 + Complex.sin z ^ 2 = 1 := Complex.cos_sq_add_sin_sq z
    have hs2 : (-4 * Complex.sin z ^ 2) ≠ 0 := by
      have : Complex.sin z ^ 2 ≠ 0 := pow_ne_zero 2 hs0'
      intro h
      apply this
      have h' : (-4 : ℂ) * Complex.sin z ^ 2 = 0 := h
      rcases mul_eq_zero.1 h' with h1 | h1
      · norm_num at h1
      · exact h1
    have hnum : D ^ 2 - 4 - (-4 * Complex.sin z ^ 2) = 4 * Complex.cos z * δ + δ ^ 2 := by
      have hDe : D = 2 * Complex.cos z + δ := by rw [hδ]; ring
      rw [hDe]
      linear_combination (4 : ℂ) * hcs
    have hratio : (D ^ 2 - 4) / (-4 * Complex.sin z ^ 2) - 1 =
        (4 * Complex.cos z * δ + δ ^ 2) / (-4 * Complex.sin z ^ 2) := by
      rw [← hnum]; field_simp; ring
    rw [hratio, norm_div]
    have hden : 0 < ‖(-4 * Complex.sin z ^ 2 : ℂ)‖ := norm_pos_iff.2 hs2
    rw [div_le_iff₀ hden]
    have hden_eq : ‖(-4 * Complex.sin z ^ 2 : ℂ)‖ = 4 * ‖Complex.sin z‖ ^ 2 := by
      simp [norm_mul, norm_pow]
    rw [hden_eq]
    have hN : ‖4 * Complex.cos z * δ + δ ^ 2‖ ≤ 12 * (A * R ^ 2) := by
      have h1 : ‖4 * Complex.cos z * δ‖ ≤ 4 * R * (2 * (A * R)) := by
        rw [norm_mul, norm_mul]
        have h4 : ‖(4 : ℂ)‖ = 4 := by simp
        rw [h4]
        gcongr
      have h2 : ‖δ ^ 2‖ ≤ (2 * (A * R)) ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hδb 2
      have h3 : (2 * (A * R)) ^ 2 ≤ 4 * (A * R ^ 2) := by
        nlinarith [mul_pos hApos hRpos, hA1, sq_nonneg R]
      calc _ ≤ ‖4 * Complex.cos z * δ‖ + ‖δ ^ 2‖ := norm_add_le _ _
        _ ≤ 4 * R * (2 * (A * R)) + 4 * (A * R ^ 2) := add_le_add h1 (h2.trans h3)
        _ = 12 * (A * R ^ 2) := by ring
    have hs2' : R ^ 2 / 16 ≤ ‖Complex.sin z‖ ^ 2 := by
      nlinarith [hsR, hRpos]
    calc ‖4 * Complex.cos z * δ + δ ^ 2‖ ≤ 12 * (A * R ^ 2) := hN
      _ ≤ ε * (4 * ‖Complex.sin z‖ ^ 2) := by
          have : 12 * (A * R ^ 2) ≤ 48 * A * (R ^ 2 / 4) := by nlinarith
          have h5 : 48 * A ≤ ε := by linarith
          have h6 : R ^ 2 / 4 ≤ 4 * ‖Complex.sin z‖ ^ 2 := by nlinarith
          calc 12 * (A * R ^ 2) ≤ 48 * A * (R ^ 2 / 4) := this
            _ ≤ ε * (4 * ‖Complex.sin z‖ ^ 2) :=
                mul_le_mul h5 h6 (by positivity) hε.le
  · -- the derivative ratio
    have hTdE := hasDerivAt_trace hdE
    have hderivE : Matrix.trace (deriv (fun w : ℂ => freeZsFundamentalComplex w 1) z) =
        -2 * Complex.sin z := by
      have hfun : (fun w : ℂ => Matrix.trace (freeZsFundamentalComplex w 1)) =
          fun w => 2 * Complex.cos w := funext trace_freeZs
      rw [hfun] at hTdE
      have hc : HasDerivAt (fun w : ℂ => 2 * Complex.cos w) (2 * (-Complex.sin z)) z :=
        (Complex.hasDerivAt_cos z).const_mul 2
      have := hTdE.unique hc
      rw [this]; ring
    have hderivM : deriv (fun w : ℂ => Matrix.trace (monodromyPair ψ w)) z =
        Matrix.trace (deriv (fun w : ℂ => monodromyPair ψ w) z) := hTd.deriv
    set δ' : ℂ := Matrix.trace (deriv (fun w : ℂ => monodromyPair ψ w) z -
      deriv (fun w : ℂ => freeZsFundamentalComplex w 1) z) with hδ'
    have hδb : ‖δ'‖ ≤ 2 * (A * R) := (norm_trace_le _).trans (by linarith)
    have hs1 : (-2 * Complex.sin z) ≠ 0 := by
      intro h
      rcases mul_eq_zero.1 h with h1 | h1
      · norm_num at h1
      · exact hs0' h1
    have hratio : deriv (fun w : ℂ => Matrix.trace (monodromyPair ψ w)) z / (-2 * Complex.sin z) - 1 =
        δ' / (-2 * Complex.sin z) := by
      have : deriv (fun w : ℂ => Matrix.trace (monodromyPair ψ w)) z =
          -2 * Complex.sin z + δ' := by
        rw [hderivM, hδ', Matrix.trace_sub, hderivE]; ring
      rw [this]; field_simp; ring
    rw [hratio, norm_div]
    have hden : 0 < ‖(-2 * Complex.sin z : ℂ)‖ := norm_pos_iff.2 hs1
    rw [div_le_iff₀ hden]
    have hden_eq : ‖(-2 * Complex.sin z : ℂ)‖ = 2 * ‖Complex.sin z‖ := by
      simp [norm_mul]
    rw [hden_eq]
    calc ‖δ'‖ ≤ 2 * (A * R) := hδb
      _ ≤ ε * (2 * ‖Complex.sin z‖) := by
          have h5 : 4 * A ≤ ε := by linarith
          have h6 : 2 * (A * R) ≤ (4 * A) * (2 * ‖Complex.sin z‖) := by
            nlinarith [mul_pos hApos hRpos]
          exact h6.trans (mul_le_mul_of_nonneg_right h5 (by positivity))

end

end NlsGge.Atomic.G1050S2.K47
end

section
set_option autoImplicit false

                                                                             
section
                                                                                                                   
                                                                                                                       
                                                                                                                                    
                                                                                                                          
                                                                                                            
                                                                                                   

set_option autoImplicit false

                                                                             
section
                                                                                                         
                                                                                     
                                                                                              
                                                                                             
                                                                                                         

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1050S2.K20.K19.K16

noncomputable section


theorem lipschitzOnWith_exp_Iic : LipschitzOnWith 1 Real.exp (Set.Iic (0 : ℝ)) := by
  refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℝ) (f := Real.exp) (s := Set.Iic (0 : ℝ))
    (fun x _ => Real.differentiableAt_exp) (fun x hx => ?_) (convex_Iic 0)
  rw [Real.deriv_exp]
  have : Real.exp x ≤ 1 := Real.exp_le_one_iff.2 hx
  rw [← NNReal.coe_le_coe]
  simpa using this

/-- Gronwall's inequality in integral form with an integrable weight. -/
theorem gronwall_integral {t : ℝ} (ht : 0 ≤ t) {ω n : ℝ → ℝ}
    (hω0 : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ ω s)
    (hω : IntervalIntegrable ω volume 0 t) (hn : ContinuousOn n (Set.Icc (0 : ℝ) t)) (c : ℝ)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) t, n s ≤ c + ∫ r in (0 : ℝ)..s, ω r * n r) :
    n t ≤ c * Real.exp (∫ r in (0 : ℝ)..t, ω r) := by
  have hu : Set.uIcc (0 : ℝ) t = Set.Icc 0 t := Set.uIcc_of_le ht
  have hωn : IntervalIntegrable (fun r => ω r * n r) volume 0 t :=
    hω.mul_continuousOn (by rw [hu]; exact hn)
  set W : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, ω r with hW
  set Q : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, ω r * n r with hQ
  have hWac : AbsolutelyContinuousOnInterval W 0 t :=
    hω.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have hQac : AbsolutelyContinuousOnInterval Q 0 t :=
    hωn.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have hW0 : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ W s := fun s hs =>
    intervalIntegral.integral_nonneg hs.1 fun r hr => hω0 r ⟨hr.1, hr.2.trans hs.2⟩
  have hnegac : AbsolutelyContinuousOnInterval (fun s => -W s) 0 t := hWac.neg
  have hexpac : AbsolutelyContinuousOnInterval (fun s => Real.exp (-W s)) 0 t := by
    have := lipschitzOnWith_exp_Iic.comp_absolutelyContinuousOnInterval
      (g := fun s => -W s) (a := 0) (b := t)
      (fun s hs => by
        rw [hu] at hs
        exact neg_nonpos.2 (hW0 s hs)) hnegac
    exact this
  have hcac : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 t :=
    (contDiff_const.contDiffOn (s := Set.uIcc (0 : ℝ) t) (n := 1)).absolutelyContinuousOnInterval
  set P : ℝ → ℝ := fun s => Real.exp (-W s) * (Q s + c) with hP
  have hPac : AbsolutelyContinuousOnInterval P 0 t := by
    have := hexpac.fun_mul (hQac.add hcac)
    exact this
  have hint := hPac.intervalIntegrable_deriv
  have hae : ∀ᵐ s : ℝ, s ∈ Set.uIcc (0 : ℝ) t → deriv P s ≤ 0 := by
    filter_upwards [hω.ae_hasDerivAt_integral, hωn.ae_hasDerivAt_integral] with s h1 h2 hs
    have hs' : s ∈ Set.Icc (0 : ℝ) t := by rwa [hu] at hs
    have d1 : HasDerivAt W (ω s) s := h1 hs 0 left_mem_uIcc
    have d2 : HasDerivAt Q (ω s * n s) s := h2 hs 0 left_mem_uIcc
    have d3 : HasDerivAt (fun x => Real.exp (-W x)) (Real.exp (-W s) * (-ω s)) s :=
      (d1.neg).exp
    have d4 : HasDerivAt P (Real.exp (-W s) * (-ω s) * (Q s + c) +
        Real.exp (-W s) * (ω s * n s)) s := d3.mul (d2.add_const c)
    rw [d4.deriv]
    have hn' := h s hs'
    have e1 : Real.exp (-W s) * (-ω s) * (Q s + c) + Real.exp (-W s) * (ω s * n s) =
        Real.exp (-W s) * ω s * (n s - (c + Q s)) := by ring
    rw [e1]
    have : n s - (c + Q s) ≤ 0 := by
      have := hn'
      simp only [hQ] at *
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le (hω0 s hs')) this
  have hI : ∫ s in (0 : ℝ)..t, deriv P s ≤ 0 := by
    have := intervalIntegral.integral_mono_ae_restrict (μ := volume) (a := 0) (b := t) ht hint
      (intervalIntegrable_const (c := (0 : ℝ)))
      ((ae_restrict_iff' measurableSet_Icc).2 (hae.mono fun s hs hs1 => hs (by rwa [hu])))
    simpa using this
  rw [hPac.integral_deriv_eq_sub] at hI
  have hP0 : P 0 = c := by simp [hP, hW, hQ]
  have hPt : P t ≤ c := by linarith
  have h1 : Q t + c ≤ c * Real.exp (W t) := by
    have := mul_le_mul_of_nonneg_right hPt (Real.exp_pos (W t)).le
    have e : P t * Real.exp (W t) = Q t + c := by
      simp only [hP, mul_assoc]
      rw [mul_comm (Q t + c), ← mul_assoc, ← Real.exp_add]
      simp
    rw [e] at this
    linarith
  have := h t ⟨ht, le_rfl⟩
  have e2 : (∫ r in (0 : ℝ)..t, ω r * n r) = Q t := rfl
  have e3 : (∫ r in (0 : ℝ)..t, ω r) = W t := rfl
  rw [e3]
  linarith



theorem norm_matrix_integral_le {F : ℝ → PairMat38} {t : ℝ} (ht : 0 ≤ t) {h : ℝ → ℝ}
    (hent : ∀ i j : Fin 2, IntervalIntegrable (fun s => F s i j) volume 0 t)
    (hh : IntervalIntegrable h volume 0 t)
    (hb : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖F s‖ ≤ h s) :
    ‖(Matrix.of fun i j => ∫ s in (0 : ℝ)..t, F s i j : PairMat38)‖ ≤ ∫ s in (0 : ℝ)..t, h s := by
  have hmeas : AEStronglyMeasurable F (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    have e : F = fun s => ∑ i : Fin 2, ∑ j : Fin 2, Matrix.single i j (F s i j) := by
      funext s
      exact Matrix.matrix_eq_sum_single (F s)
    rw [e]
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    have hc : Continuous (fun c : ℂ => (Matrix.single i j c : PairMat38)) := by
      refine continuous_matrix fun a b => ?_
      by_cases hab : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := hab
        have e : (fun c : ℂ => (Matrix.single i j c : PairMat38) i j) = fun c => c := by
          funext c
          simp
        rw [e]
        exact continuous_id
      · have : (fun c : ℂ => (Matrix.single i j c : PairMat38) a b) = fun _ => 0 := by
          funext c
          simp [Matrix.single_apply, hab]
        rw [this]
        exact continuous_const
    exact hc.comp_aestronglyMeasurable (hent i j).1.aestronglyMeasurable
  have hhi : IntegrableOn h (Set.Ioc (0 : ℝ) t) := hh.1
  have hF : IntervalIntegrable F volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    refine Integrable.mono' hhi hmeas ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hb)
  have hG : ‖∫ s in (0 : ℝ)..t, F s‖ ≤ ∫ s in (0 : ℝ)..t, h s :=
    intervalIntegral.norm_integral_le_of_norm_le ht
      (Eventually.of_forall fun s hs => hb s hs) hh
  have hEq : (Matrix.of fun i j => ∫ s in (0 : ℝ)..t, F s i j : PairMat38) =
      ∫ s in (0 : ℝ)..t, F s := by
    ext i j
    let L : PairMat38 →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
    have := L.intervalIntegral_comp_comm hF
    exact this
  rw [hEq]
  exact hG


/-! ### Norm bounds for the free solution and the potential coefficient -/

/-- The pointwise `ℓ²` size of the potential. -/
def omegaW (φ : PotPair) (s : ℝ) : ℝ :=
  Real.sqrt (‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2)

theorem omegaW_nonneg (φ : PotPair) (s : ℝ) : 0 ≤ omegaW φ s := Real.sqrt_nonneg _

def otherFin2 (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem even_sparse_matrix_opNorm_le (M : PairMat38) (C : ℝ)
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

theorem odd_sparse_matrix_opNorm_le (M : PairMat38) (C : ℝ)
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

theorem norm_potCoeff38_le_omega (φ : PotPair) (s : ℝ) : ‖potCoeff38 φ s‖ ≤ omegaW φ s := by
  have h1 : ‖potRepFst38 φ s‖ ≤ omegaW φ s :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖potRepSnd38 φ s‖])
  have h2 : ‖potRepSnd38 φ s‖ ≤ omegaW φ s :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖potRepFst38 φ s‖])
  refine odd_sparse_matrix_opNorm_le _ _ (omegaW_nonneg φ s)
    (fun i => by fin_cases i <;> simp [potCoeff38]) (fun i => ?_)
  fin_cases i <;> simp [potCoeff38, otherFin2, h1, h2]

theorem norm_freeE_le (z : ℂ) {r : ℝ} (hr : 0 ≤ r) : ‖freeE z r‖ ≤ Real.exp (|z.im| * r) := by
  refine even_sparse_matrix_opNorm_le _ _ (Real.exp_pos _).le (fun i j hij => ?_) (fun i => ?_)
  · fin_cases i <;> fin_cases j <;> simp [freeE] at hij ⊢
  · have := norm_freeE_entry_le z r i i
    rwa [abs_of_nonneg hr] at this

/-! ### The functions on `[0,1]` -/

theorem hT1 : (0 : ℝ) ≤ 1 := zero_le_one

/-- `M(s) = ∑ M_n(s)` as a function on `ℝ` (constant extension of the fundamental solution). -/
def Mfun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 := ext38T hT1 (fundContT φ z hT1) s

/-- `M_1(s)` as a function on `ℝ`. -/
def M1fun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 :=
  ext38T hT1 (volterraPT φ z hT1 (freeFundT 1 z)) s

def Xfun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 := Mfun φ z s - freeE z s

def Nfun (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 := Xfun φ z s - M1fun φ z s

def kerT (φ : PotPair) (z : ℂ) (t s : ℝ) : PairMat38 :=
  freeE z (t - s) * potCoeff38 φ s * Xfun φ z s

theorem cont_Mfun (φ : PotPair) (z : ℂ) : Continuous (Mfun φ z) := continuous_ext38T hT1 _

theorem cont_M1fun (φ : PotPair) (z : ℂ) : Continuous (M1fun φ z) := continuous_ext38T hT1 _

theorem cont_Xfun (φ : PotPair) (z : ℂ) : Continuous (Xfun φ z) :=
  (cont_Mfun φ z).sub (continuous_freeE z)

theorem cont_Nfun (φ : PotPair) (z : ℂ) : Continuous (Nfun φ z) :=
  (cont_Xfun φ z).sub (cont_M1fun φ z)


theorem fundContT_entry_eq' (φ : PotPair) (z : ℂ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    fundContT φ z hT1 ⟨t, ht⟩ i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s *
        ext38T hT1 (fundContT φ z hT1) s) i j := by
  have h := congrArg (fun G : PairContT 1 => G ⟨t, ht⟩ i j) (fundContT_eq_add φ z hT1)
  simp only [ContinuousMap.add_apply, Pi.add_apply] at h
  rw [h]
  rfl

theorem tsum_entry (φ : PotPair) (z : ℂ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    (∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j = fundContT φ z hT1 ⟨t, ht⟩ i j := by
  have hent : ∀ i j : Fin 2, HasSum (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)
      (fundContT φ z hT1 ⟨t, ht⟩ i j) := by
    intro i j
    have e : (fun n : ℕ => potentialVolterraTerm38 φ z n t i j) =
        fun n : ℕ => ((volterraPT φ z hT1 ^ n) (freeFundT 1 z)) ⟨t, ht⟩ i j :=
      funext fun n => by rw [term_eq_powT φ z hT1 n t ht]
    rw [e]
    exact hasSum_entryT φ z hT1 ⟨t, ht⟩ i j
  have hS : Summable (fun n : ℕ => potentialVolterraTerm38 φ z n t) :=
    Pi.summable.2 fun i => Pi.summable.2 fun j => (hent i j).summable
  have hcont : Continuous (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) :=
    (continuous_id.matrix_elem i j)
  have h1 : HasSum (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)
      ((∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j) :=
    hS.hasSum.map (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) hcont
  exact h1.unique (hent i j)

theorem tsum_eq_Mfun (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∑' n : ℕ, potentialVolterraTerm38 φ z n t) = Mfun φ z t := by
  ext i j
  rw [tsum_entry φ z ht i j, Mfun, ext38T_of_mem hT1 _ ht]

theorem term1_eq (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    potentialVolterraTerm38 φ z 1 t = M1fun φ z t := by
  have h := term_eq_powT φ z hT1 1 t ht
  rw [pow_one] at h
  rw [h, M1fun, ext38T_of_mem hT1 _ ht]

theorem ker_integrable (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    IntervalIntegrable (fun s => kerT φ z t s i j) volume 0 t := by
  have hK : Continuous fun s : ℝ => freeE z (t - s) :=
    (continuous_freeE z).comp (continuous_const.sub continuous_id)
  have h1 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (cont_Mfun φ z) ht i j
  have h2 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (continuous_freeE z) ht i j
  refine (h1.sub h2).congr ?_
  intro s _
  simp [kerT, Xfun, Matrix.mul_sub, Matrix.sub_apply]

theorem stepB (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Nfun φ z t = Matrix.of fun i j => ∫ s in (0 : ℝ)..t, kerT φ z t s i j := by
  ext i j
  have hK : Continuous fun s : ℝ => freeE z (t - s) :=
    (continuous_freeE z).comp (continuous_const.sub continuous_id)
  have h1 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (cont_Mfun φ z) ht i j
  have h2 := intervalIntegrable_triple_entryT_of_mem φ hT1 hK (continuous_freeE z) ht i j
  have hM : Mfun φ z t i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * Mfun φ z s) i j := by
    rw [Mfun, ext38T_of_mem hT1 _ ht]
    exact fundContT_entry_eq' φ z ht i j
  have hM1 : M1fun φ z t i j =
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * freeE z s) i j := by
    rw [M1fun, ext38T_of_mem hT1 _ ht, volterraPT_apply, volterraFunT_apply]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
      have := Set.uIcc_subset_Icc (Set.left_mem_Icc.2 hT1) ht hs
      exact this
    rw [ext38T_of_mem hT1 _ hs']
    rfl
  have hker : (∫ s in (0 : ℝ)..t, kerT φ z t s i j) =
      (∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * Mfun φ z s) i j) -
        ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * freeE z s) i j := by
    rw [← intervalIntegral.integral_sub h1 h2]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [kerT, Xfun, Matrix.mul_sub, Matrix.sub_apply]
  rw [Matrix.of_apply, hker]
  simp only [Nfun, Xfun, Matrix.sub_apply]
  rw [hM, hM1]
  ring

/-! ### The weight `ω` and weighted norms -/

theorem omegaW_sq (φ : PotPair) (s : ℝ) :
    omegaW φ s ^ 2 = ‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem intervalIntegrable_omegaW_sq (φ : PotPair) :
    IntervalIntegrable (fun s => omegaW φ s ^ 2) volume 0 1 := by
  have h := (intervalIntegrable_coverRep38_sq_one φ.1).add (intervalIntegrable_coverRep38_sq_one φ.2)
  refine h.congr ?_
  intro s _
  simp only [omegaW_sq, potRepFst38, potRepSnd38]

theorem integral_omegaW_sq (φ : PotPair) :
    ∫ s in (0 : ℝ)..1, omegaW φ s ^ 2 = ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
  have e : ∀ s, omegaW φ s ^ 2 = ‖coverRep38 φ.1 s‖ ^ 2 + ‖coverRep38 φ.2 s‖ ^ 2 := fun s => by
    rw [omegaW_sq]; rfl
  simp_rw [e]
  rw [intervalIntegral.integral_add (intervalIntegrable_coverRep38_sq_one φ.1)
    (intervalIntegrable_coverRep38_sq_one φ.2), integral_sq_coverRep38_one, integral_sq_coverRep38_one]

theorem omegaW_le_potW (φ : PotPair) (s : ℝ) : omegaW φ s ≤ potW38 φ s := by
  unfold omegaW potW38
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg (potRepFst38 φ s), norm_nonneg (potRepSnd38 φ s)]

theorem intervalIntegrable_omegaW (φ : PotPair) : IntervalIntegrable (omegaW φ) volume 0 1 := by
  have hsq : IntervalIntegrable (fun s => ‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_coverRep38_sq_one φ.1).add (intervalIntegrable_coverRep38_sq_one φ.2)
  have hm : AEStronglyMeasurable (omegaW φ) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hsq.1.aestronglyMeasurable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Integrable.mono' (intervalIntegrable_potW38 φ).1 hm ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s _ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (omegaW_nonneg φ s)]
  exact omegaW_le_potW φ s

/-- The weighted norms. -/
def aW (φ : PotPair) (z : ℂ) (s : ℝ) : ℝ := Real.exp (-|z.im| * s) * ‖M1fun φ z s‖
def nW (φ : PotPair) (z : ℂ) (s : ℝ) : ℝ := Real.exp (-|z.im| * s) * ‖Nfun φ z s‖
def YW (φ : PotPair) (z : ℂ) (s : ℝ) : ℝ := Real.exp (-|z.im| * s) * ‖Xfun φ z s‖

theorem continuous_expW (z : ℂ) : Continuous fun s : ℝ => Real.exp (-|z.im| * s) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_id)

theorem continuous_aW (φ : PotPair) (z : ℂ) : Continuous (aW φ z) :=
  (continuous_expW z).mul (cont_M1fun φ z).norm

theorem continuous_nW (φ : PotPair) (z : ℂ) : Continuous (nW φ z) :=
  (continuous_expW z).mul (cont_Nfun φ z).norm

theorem continuous_YW (φ : PotPair) (z : ℂ) : Continuous (YW φ z) :=
  (continuous_expW z).mul (cont_Xfun φ z).norm

theorem aW_nonneg (φ : PotPair) (z : ℂ) (s : ℝ) : 0 ≤ aW φ z s :=
  mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem nW_nonneg (φ : PotPair) (z : ℂ) (s : ℝ) : 0 ≤ nW φ z s :=
  mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem YW_le (φ : PotPair) (z : ℂ) (s : ℝ) : YW φ z s ≤ aW φ z s + nW φ z s := by
  have h : ‖Xfun φ z s‖ ≤ ‖M1fun φ z s‖ + ‖Nfun φ z s‖ := by
    have : Xfun φ z s = M1fun φ z s + Nfun φ z s := by simp [Nfun]
    rw [this]
    exact norm_add_le _ _
  unfold YW aW nW
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-! ### The integral inequality -/

theorem n_le_integral (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    nW φ z t ≤ ∫ s in (0 : ℝ)..t, YW φ z s * omegaW φ s := by
  have hωt : IntervalIntegrable (omegaW φ) volume 0 t :=
    (intervalIntegrable_omegaW φ).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc le_rfl ht.2)
  have hcont : Continuous fun s : ℝ => Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖ :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (cont_Xfun φ z).norm
  have hh : IntervalIntegrable (fun s => (Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖) *
      omegaW φ s) volume 0 t := hωt.continuousOn_mul hcont.continuousOn
  have hb : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖kerT φ z t s‖ ≤
      (Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖) * omegaW φ s := by
    intro s hs
    have hts : 0 ≤ t - s := sub_nonneg.2 hs.2
    unfold kerT
    calc ‖freeE z (t - s) * potCoeff38 φ s * Xfun φ z s‖
        ≤ ‖freeE z (t - s) * potCoeff38 φ s‖ * ‖Xfun φ z s‖ := norm_mul_le _ _
      _ ≤ (‖freeE z (t - s)‖ * ‖potCoeff38 φ s‖) * ‖Xfun φ z s‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (Real.exp (|z.im| * (t - s)) * omegaW φ s) * ‖Xfun φ z s‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact mul_le_mul (norm_freeE_le z hts) (norm_potCoeff38_le_omega φ s)
            (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  have hN := norm_matrix_integral_le ht.1 (ker_integrable φ z ht) hh hb
  rw [← stepB φ z ht] at hN
  unfold nW
  calc Real.exp (-|z.im| * t) * ‖Nfun φ z t‖
      ≤ Real.exp (-|z.im| * t) * ∫ s in (0 : ℝ)..t,
          (Real.exp (|z.im| * (t - s)) * ‖Xfun φ z s‖) * omegaW φ s :=
        mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le
    _ = ∫ s in (0 : ℝ)..t, YW φ z s * omegaW φ s := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        simp only [YW]
        rw [← mul_assoc, ← mul_assoc, ← Real.exp_add]
        have e : -|z.im| * t + |z.im| * (t - s) = -|z.im| * s := by ring
        rw [e]

/-! ### Gronwall step -/

theorem Icc_sub_Icc_one {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩

theorem intervalIntegrable_omegaW_on (φ : PotPair) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (omegaW φ) volume 0 t :=
  (intervalIntegrable_omegaW φ).mono_set (by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc le_rfl ht.2)

/-- `∫₀ᵗ ω a`. -/
def bW (φ : PotPair) (z : ℂ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, omegaW φ s * aW φ z s

theorem intervalIntegrable_omega_mul {φ : PotPair} {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => omegaW φ s * g s) volume 0 t :=
  (intervalIntegrable_omegaW_on φ ht).mul_continuousOn hg.continuousOn

theorem n_le_b_add_Q (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    nW φ z t ≤ bW φ z t + ∫ s in (0 : ℝ)..t, omegaW φ s * nW φ z s := by
  refine (n_le_integral φ z ht).trans ?_
  have hia := intervalIntegrable_omega_mul (φ := φ) (continuous_aW φ z) ht
  have hin := intervalIntegrable_omega_mul (φ := φ) (continuous_nW φ z) ht
  unfold bW
  rw [← intervalIntegral.integral_add hia hin]
  have hY : IntervalIntegrable (fun s => YW φ z s * omegaW φ s) volume 0 t :=
    (intervalIntegrable_omegaW_on φ ht).continuousOn_mul (continuous_YW φ z).continuousOn
  refine intervalIntegral.integral_mono_on ht.1 hY (hia.add hin) fun s hs => ?_
  have := YW_le φ z s
  have hω := omegaW_nonneg φ s
  nlinarith

theorem bW_mono (φ : PotPair) (z : ℂ) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : bW φ z s ≤ bW φ z t := by
  unfold bW
  refine intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2 ?_
    (intervalIntegrable_omega_mul (φ := φ) (continuous_aW φ z) ht)
  exact Eventually.of_forall fun r => mul_nonneg (omegaW_nonneg φ r) (aW_nonneg φ z r)

theorem n_le_gronwall (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    nW φ z t ≤ bW φ z t * Real.exp (∫ r in (0 : ℝ)..t, omegaW φ r) := by
  refine gronwall_integral ht.1 (ω := omegaW φ) (n := nW φ z)
    (fun s _ => omegaW_nonneg φ s) (intervalIntegrable_omegaW_on φ ht)
    (continuous_nW φ z).continuousOn (bW φ z t) fun s hs => ?_
  have h1 := n_le_b_add_Q φ z (Icc_sub_Icc_one hs ht)
  have h2 := bW_mono φ z hs ht
  linarith

/-! ### Cauchy-Schwarz -/

theorem cs_integral {t : ℝ} (ht : 0 ≤ t) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable (fun s => f s ^ 2) volume 0 t)
    (hg : IntervalIntegrable (fun s => g s ^ 2) volume 0 t)
    (hfg : IntervalIntegrable (fun s => f s * g s) volume 0 t) :
    (∫ s in (0 : ℝ)..t, f s * g s) ^ 2 ≤
      (∫ s in (0 : ℝ)..t, f s ^ 2) * ∫ s in (0 : ℝ)..t, g s ^ 2 := by
  have key : ∀ x : ℝ, 0 ≤ (∫ s in (0 : ℝ)..t, f s ^ 2) * (x * x) +
      (-2 * ∫ s in (0 : ℝ)..t, f s * g s) * x + ∫ s in (0 : ℝ)..t, g s ^ 2 := by
    intro x
    have h0 : 0 ≤ ∫ s in (0 : ℝ)..t, (x * f s - g s) ^ 2 :=
      intervalIntegral.integral_nonneg ht fun s _ => sq_nonneg _
    have e : ∫ s in (0 : ℝ)..t, (x * f s - g s) ^ 2 =
        (∫ s in (0 : ℝ)..t, f s ^ 2) * (x * x) +
          (-2 * ∫ s in (0 : ℝ)..t, f s * g s) * x + ∫ s in (0 : ℝ)..t, g s ^ 2 := by
      have e1 : ∀ s, (x * f s - g s) ^ 2 =
          (x * x) * f s ^ 2 + (-2 * x) * (f s * g s) + g s ^ 2 := fun s => by ring
      simp_rw [e1]
      rw [intervalIntegral.integral_add ((hf.const_mul (x * x)).add (hfg.const_mul (-2 * x))) hg,
        intervalIntegral.integral_add (hf.const_mul (x * x)) (hfg.const_mul (-2 * x)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    linarith
  have := discrim_le_zero key
  unfold _root_.discrim at this
  nlinarith

theorem W_le (φ : PotPair) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ r in (0 : ℝ)..t, omegaW φ r ≤ Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) := by
  have hf : IntervalIntegrable (fun s => omegaW φ s ^ 2) volume 0 t :=
    (intervalIntegrable_omegaW_sq φ).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc le_rfl ht.2)
  have hg : IntervalIntegrable (fun s : ℝ => (1 : ℝ) ^ 2) volume 0 t := intervalIntegrable_const
  have hfg : IntervalIntegrable (fun s => omegaW φ s * 1) volume 0 t := by
    simpa using intervalIntegrable_omegaW_on φ ht
  have h := cs_integral ht.1 hf hg hfg
  simp only [mul_one, one_pow, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  have hsq : ∫ s in (0 : ℝ)..t, omegaW φ s ^ 2 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    rw [← integral_omegaW_sq φ]
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_ (intervalIntegrable_omegaW_sq φ)
    exact Eventually.of_forall fun r => sq_nonneg _
  have hP : 0 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by positivity
  have h3 : (∫ r in (0 : ℝ)..t, omegaW φ r) ^ 2 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    have hI : 0 ≤ ∫ s in (0 : ℝ)..t, omegaW φ s ^ 2 :=
      intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _
    nlinarith [ht.2, ht.1]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h3)

theorem b_le (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    bW φ z t ≤ Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) *
      Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2) := by
  have hf : IntervalIntegrable (fun s => omegaW φ s ^ 2) volume 0 t :=
    (intervalIntegrable_omegaW_sq φ).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc le_rfl ht.2)
  have hg : IntervalIntegrable (fun s => aW φ z s ^ 2) volume 0 t :=
    ((continuous_aW φ z).pow 2).intervalIntegrable 0 t
  have hfg := intervalIntegrable_omega_mul (φ := φ) (continuous_aW φ z) ht
  have h := cs_integral ht.1 hf hg hfg
  have hsq : ∫ s in (0 : ℝ)..t, omegaW φ s ^ 2 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    rw [← integral_omegaW_sq φ]
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_ (intervalIntegrable_omegaW_sq φ)
    exact Eventually.of_forall fun r => sq_nonneg _
  have hJ : 0 ≤ ∫ s in (0 : ℝ)..t, aW φ z s ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _
  have hP : 0 ≤ ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by positivity
  have h3 : (bW φ z t) ^ 2 ≤ (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * ∫ s in (0 : ℝ)..t, aW φ z s ^ 2 :=
    h.trans (mul_le_mul_of_nonneg_right hsq hJ)
  rw [← Real.sqrt_mul hP]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h3)

/-! ### Assembly -/

theorem aW_eq_term (φ : PotPair) (z : ℂ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖ = aW φ z s := by
  rw [term1_eq φ z hs]; rfl

theorem G1016_whole :
    ((∀ (φ : PotPair) (z : ℂ) (t : ℝ), 0 ≤ t → t ≤ 1 →
    IntervalIntegrable
      (fun s : ℝ => (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2)
      MeasureTheory.volume 0 t ∧
    Real.exp (-|z.im| * t) *
        ‖(∑' n : ℕ, potentialVolterraTerm38 φ z n t) - freeZsFundamentalComplex z t‖ ≤
      Real.exp (-|z.im| * t) * ‖potentialVolterraTerm38 φ z 1 t‖ +
        (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2))) *
          Real.sqrt (∫ s in (0 : ℝ)..t,
            (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2)
  : Prop)) := by
  intro φ z t ht0 ht1
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hcongr : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2 = aW φ z s ^ 2 := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    rw [aW_eq_term φ z (Icc_sub_Icc_one hs ht)]
  refine ⟨?_, ?_⟩
  · refine (((continuous_aW φ z).pow 2).intervalIntegrable 0 t).congr ?_
    intro s hs
    exact (hcongr s (Set.uIoc_subset_uIcc hs)).symm
  · have hI : (∫ s in (0 : ℝ)..t,
        (Real.exp (-|z.im| * s) * ‖potentialVolterraTerm38 φ z 1 s‖) ^ 2) =
        ∫ s in (0 : ℝ)..t, aW φ z s ^ 2 :=
      intervalIntegral.integral_congr hcongr
    rw [hI, aW_eq_term φ z ht, tsum_eq_Mfun φ z ht, ← freeE_eq]
    have hY : Real.exp (-|z.im| * t) * ‖Mfun φ z t - freeE z t‖ = YW φ z t := rfl
    rw [hY]
    have h1 := YW_le φ z t
    have h2 := n_le_gronwall φ z ht
    have h3 := b_le φ z ht
    have h4 := W_le φ ht
    have hb0 : 0 ≤ bW φ z t := intervalIntegral.integral_nonneg ht0 fun s _ =>
      mul_nonneg (omegaW_nonneg φ s) (aW_nonneg φ z s)
    have h5 : bW φ z t * Real.exp (∫ r in (0 : ℝ)..t, omegaW φ r) ≤
        (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2)) *
          Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2)) :=
      mul_le_mul h3 (Real.exp_le_exp.2 h4) (Real.exp_pos _).le
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have h6 : (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2)) *
          Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2)) =
        (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) * Real.exp (Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2))) *
          Real.sqrt (∫ s in (0 : ℝ)..t, aW φ z s ^ 2) := by ring
    rw [h6] at h5
    linarith

end

end NlsGge.Atomic.G1050S2.K20.K19.K16

end

open MeasureTheory Filter Topology Set
open NlsGge.GK38
/-! ### The first Volterra term -/

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1050S2.K20.K19.Aux

noncomputable section

theorem term1_apply (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) (i j : Fin 2) :
    freeKernelVolterraTerm38 a b z 1 t i j =
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * rawPotCoeff38 a b s * freeE z s) i j := by
  simp only [freeKernelVolterraTerm38, freeE_eq]

theorem term1_entry01 (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 0 1 =
      Complex.I * Complex.exp (-(Complex.I * z * (t : ℂ))) *
        ∫ s in (0 : ℝ)..t, a s * Complex.exp (2 * Complex.I * z * (s : ℂ)) := by
  rw [term1_apply,
    ← intervalIntegral.integral_const_mul (Complex.I * Complex.exp (-(Complex.I * z * (t : ℂ))))]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : Complex.exp (-(Complex.I * z * ((t - s : ℝ) : ℂ))) * Complex.exp (Complex.I * z * (s : ℂ)) =
      Complex.exp (-(Complex.I * z * (t : ℂ))) * Complex.exp (2 * Complex.I * z * (s : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [freeE, rawPotCoeff38, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  linear_combination (Complex.I * a s) * e

theorem term1_entry10 (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 1 0 =
      -Complex.I * Complex.exp (Complex.I * z * (t : ℂ)) *
        ∫ s in (0 : ℝ)..t, b s * Complex.exp (2 * Complex.I * (-z) * (s : ℂ)) := by
  rw [term1_apply,
    ← intervalIntegral.integral_const_mul (-Complex.I * Complex.exp (Complex.I * z * (t : ℂ)))]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : Complex.exp (Complex.I * z * ((t - s : ℝ) : ℂ)) * Complex.exp (-(Complex.I * z * (s : ℂ))) =
      Complex.exp (Complex.I * z * (t : ℂ)) * Complex.exp (2 * Complex.I * (-z) * (s : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [freeE, rawPotCoeff38, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  linear_combination (-(Complex.I * b s)) * e

theorem term1_entry00 (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 0 0 = 0 := by
  rw [term1_apply]
  simp [freeE, rawPotCoeff38, Matrix.mul_apply, Fin.sum_univ_two]

theorem term1_entry11 (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 1 1 = 0 := by
  rw [term1_apply]
  simp [freeE, rawPotCoeff38, Matrix.mul_apply, Fin.sum_univ_two]

theorem norm_term1_le (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    ‖freeKernelVolterraTerm38 a b z 1 t‖ ≤
      max (‖freeKernelVolterraTerm38 a b z 1 t 0 1‖) (‖freeKernelVolterraTerm38 a b z 1 t 1 0‖) := by
  refine NlsGge.Atomic.G1050S2.K20.K19.K16.odd_sparse_matrix_opNorm_le _ _ (le_max_of_le_left (norm_nonneg _))
    (fun i => ?_) (fun i => ?_)
  · fin_cases i
    · exact term1_entry00 a b z t
    · exact term1_entry11 a b z t
  · fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _


end

end NlsGge.Atomic.G1050S2.K20.K19.Aux

namespace NlsGge.Atomic.G1050S2.K20.K19.Aux

noncomputable section

theorem entry01_osc (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 0 1 = Complex.I * seqOsc38 a (-z) t := by
  rw [term1_entry01, seqOsc38, mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : Complex.exp (Complex.I * (-z) * ((t - 2 * s : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * z * (t : ℂ))) * Complex.exp (2 * Complex.I * z * (s : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [e]
  ring

theorem entry10_osc (a b : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    freeKernelVolterraTerm38 a b z 1 t 1 0 = -Complex.I * seqOsc38 b z t := by
  rw [term1_entry10, seqOsc38, mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : Complex.exp (Complex.I * z * ((t - 2 * s : ℝ) : ℂ)) =
      Complex.exp (Complex.I * z * (t : ℂ)) * Complex.exp (2 * Complex.I * (-z) * (s : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [e]
  ring

theorem W_sq_le (a b : ℝ → ℂ) (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    (Real.exp (-|z.im| * s) * ‖freeKernelVolterraTerm38 a b z 1 s‖) ^ 2 ≤
      ‖seqOsc38 a (-z) s‖ ^ 2 + ‖seqOsc38 b z s‖ ^ 2 := by
  have hexp : Real.exp (-|z.im| * s) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    nlinarith [abs_nonneg z.im]
  have hN := norm_term1_le a b z s
  rw [entry01_osc, entry10_osc, norm_mul, norm_mul, Complex.norm_I, one_mul] at hN
  simp only [norm_neg, Complex.norm_I, one_mul] at hN
  set x := ‖freeKernelVolterraTerm38 a b z 1 s‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have h1 : (Real.exp (-|z.im| * s) * x) ^ 2 ≤ x ^ 2 := by
    have : Real.exp (-|z.im| * s) * x ≤ x := by nlinarith
    exact pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le hx0) this 2
  have h2 : x ^ 2 ≤ ‖seqOsc38 a (-z) s‖ ^ 2 + ‖seqOsc38 b z s‖ ^ 2 := by
    rcases max_cases ‖seqOsc38 a (-z) s‖ ‖seqOsc38 b z s‖ with ⟨hm, _⟩ | ⟨hm, _⟩
    · have : x ≤ ‖seqOsc38 a (-z) s‖ := hm ▸ hN
      nlinarith [norm_nonneg (seqOsc38 b z s)]
    · have : x ≤ ‖seqOsc38 b z s‖ := hm ▸ hN
      nlinarith [norm_nonneg (seqOsc38 a (-z) s)]
  exact h1.trans h2

end

end NlsGge.Atomic.G1050S2.K20.K19.Aux

namespace NlsGge.Atomic.G1050S2.K20.K19.Aux

noncomputable section

open NlsGge.Pilot

theorem bessel_fin_b (f : PhysicalL2) (ξ : ℤ → ℂ) {R1 : ℝ}
    (hR : ∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset ℤ) :
    ∑ n ∈ S, ‖seqOsc38 (coverRep38 f) (ξ n) s‖ ^ 2 ≤ Real.exp (2 * R1) * ‖f‖ ^ 2 := by
  have h := NlsGge.Atomic.G1015.perturbed_fourier_bessel_physical f
    (fun n : ℤ => ξ n - (n : ℂ) * (Real.pi : ℂ)) hR hs
  simp only [add_sub_cancel] at h
  exact (Summable.sum_le_tsum S (fun n _ => sq_nonneg _) h.1).trans h.2

theorem bessel_fin_a (f : PhysicalL2) (ξ : ℤ → ℂ) {R1 : ℝ}
    (hR : ∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset ℤ) :
    ∑ n ∈ S, ‖seqOsc38 (coverRep38 f) (-ξ n) s‖ ^ 2 ≤ Real.exp (2 * R1) * ‖f‖ ^ 2 := by
  have hα : ∀ m : ℤ, ‖(-ξ (-m) - (m : ℂ) * (Real.pi : ℂ))‖ ≤ R1 := by
    intro m
    have := hR (-m)
    have e : -ξ (-m) - (m : ℂ) * (Real.pi : ℂ) = -(ξ (-m) - ((-m : ℤ) : ℂ) * (Real.pi : ℂ)) := by
      push_cast; ring
    rw [e, norm_neg]
    exact this
  have h := NlsGge.Atomic.G1015.perturbed_fourier_bessel_physical f
    (fun m : ℤ => -ξ (-m) - (m : ℂ) * (Real.pi : ℂ)) hα hs
  simp only [add_sub_cancel] at h
  have hle : ∑ m ∈ S.image (fun n : ℤ => -n), ‖seqOsc38 (coverRep38 f) (-ξ (-m)) s‖ ^ 2 ≤
      ∑' m : ℤ, ‖seqOsc38 (coverRep38 f) (-ξ (-m)) s‖ ^ 2 :=
    Summable.sum_le_tsum _ (fun m _ => sq_nonneg _) h.1
  rw [Finset.sum_image (fun x _ y _ hxy => neg_injective hxy)] at hle
  simp only [neg_neg] at hle
  exact hle.trans h.2

end

end NlsGge.Atomic.G1050S2.K20.K19.Aux

namespace NlsGge.Atomic.G1050S2.K20.K19

noncomputable section

open NlsGge.Atomic.G1050S2.K20.K19.Aux
open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot
open scoped Matrix.Norms.L2Operator

theorem G1019_whole : ((
  ∀ R0 R1 : ℝ, ∃ C : ℝ, ∀ (φ : PotPair) (ξ : ℤ → ℂ),
    Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ R0 →
    (∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Summable (fun n : ℤ =>
        ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖ ^ 2) ∧
      (∑' n : ℤ,
        ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖ ^ 2) ≤ C
  : Prop)) := by
  intro R0 R1
  set R0' : ℝ := max R0 0 with hR0'
  set R1' : ℝ := max R1 0 with hR1'
  have hR1p : 0 ≤ R1' := le_max_right _ _
  have hR0p : 0 ≤ R0' := le_max_right _ _
  refine ⟨2 * Real.exp (2 * R1') * (Real.exp (2 * R1') * R0' ^ 2 +
    R0' ^ 2 * Real.exp (2 * R0') * (Real.exp (2 * R1') * R0' ^ 2)), ?_⟩
  intro φ ξ hφ hξ t ht0 ht1
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  set c : ℝ := Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcR : c ≤ R0' := hφ.trans (le_max_left _ _)
  have hc2 : c ^ 2 = ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hξ' : ∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1' :=
    fun n => (hξ n).trans (le_max_left _ _)
  have himR : ∀ n : ℤ, |(ξ n).im| ≤ R1' := by
    intro n
    refine le_trans ?_ (hξ' n)
    have := Complex.abs_im_le_norm (ξ n - (n : ℂ) * (Real.pi : ℂ))
    simpa using this
  set Wf : ℤ → ℝ → ℝ := fun n s =>
    Real.exp (-|(ξ n).im| * s) * ‖potentialVolterraTerm38 φ (ξ n) 1 s‖ with hWf
  set X : ℤ → ℝ := fun n =>
    ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖ with hX
  have hK : ∀ n : ℤ, IntervalIntegrable (fun s => Wf n s ^ 2) MeasureTheory.volume 0 t ∧
      Real.exp (-|(ξ n).im| * t) * X n ≤ Wf n t + (c * Real.exp c) *
        Real.sqrt (∫ s in (0 : ℝ)..t, Wf n s ^ 2) :=
    fun n => K16.G1016_whole φ (ξ n) t ht0 ht1
  set Ib : ℤ → ℝ := fun n => ∫ s in (0 : ℝ)..t, Wf n s ^ 2 with hIb
  have hIb0 : ∀ n, 0 ≤ Ib n := fun n =>
    intervalIntegral.integral_nonneg ht0 fun s _ => sq_nonneg _
  have hWf0 : ∀ n s, 0 ≤ Wf n s := fun n s => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  -- pointwise bound for one index
  have hXn : ∀ n : ℤ, X n ^ 2 ≤ 2 * Real.exp (2 * R1') * (Wf n t ^ 2 + c ^ 2 * Real.exp (2 * c) * Ib n) := by
    intro n
    have h1 := (hK n).2
    have hexp : Real.exp (|(ξ n).im| * t) ≤ Real.exp R1' := by
      apply Real.exp_le_exp.2
      calc |(ξ n).im| * t ≤ |(ξ n).im| * 1 :=
            mul_le_mul_of_nonneg_left ht1 (abs_nonneg _)
        _ ≤ R1' := by simpa using himR n
    have hXle : X n ≤ Real.exp R1' * (Wf n t + (c * Real.exp c) * Real.sqrt (Ib n)) := by
      have hw : Real.exp (|(ξ n).im| * t) * Real.exp (-|(ξ n).im| * t) = 1 := by
        rw [← Real.exp_add]; simp
      have h2 : X n = Real.exp (|(ξ n).im| * t) * (Real.exp (-|(ξ n).im| * t) * X n) := by
        rw [← mul_assoc, hw, one_mul]
      have hnn : 0 ≤ Wf n t + (c * Real.exp c) * Real.sqrt (Ib n) := by
        have := hWf0 n t
        positivity
      calc X n = Real.exp (|(ξ n).im| * t) * (Real.exp (-|(ξ n).im| * t) * X n) := h2
        _ ≤ Real.exp (|(ξ n).im| * t) * (Wf n t + (c * Real.exp c) * Real.sqrt (Ib n)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ ≤ Real.exp R1' * (Wf n t + (c * Real.exp c) * Real.sqrt (Ib n)) :=
            mul_le_mul_of_nonneg_right hexp hnn
    have hX0 : 0 ≤ X n := norm_nonneg _
    have hsq : X n ^ 2 ≤ (Real.exp R1' * (Wf n t + (c * Real.exp c) * Real.sqrt (Ib n))) ^ 2 :=
      pow_le_pow_left₀ hX0 hXle 2
    have hsqrt : Real.sqrt (Ib n) ^ 2 = Ib n := Real.sq_sqrt (hIb0 n)
    have he2 : Real.exp R1' ^ 2 = Real.exp (2 * R1') := by rw [← Real.exp_nat_mul]; norm_num
    have he2c : Real.exp c ^ 2 = Real.exp (2 * c) := by rw [← Real.exp_nat_mul]; norm_num
    have hu := hWf0 n t
    set u := Wf n t
    set v := (c * Real.exp c) * Real.sqrt (Ib n) with hv
    have hv2 : v ^ 2 = c ^ 2 * Real.exp (2 * c) * Ib n := by
      rw [hv, mul_pow, mul_pow, hsqrt, he2c]
    calc X n ^ 2 ≤ (Real.exp R1' * (u + v)) ^ 2 := hsq
      _ = Real.exp (2 * R1') * (u + v) ^ 2 := by rw [mul_pow, he2]
      _ ≤ Real.exp (2 * R1') * (2 * (u ^ 2 + v ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          nlinarith [sq_nonneg (u - v)]
      _ = 2 * Real.exp (2 * R1') * (u ^ 2 + c ^ 2 * Real.exp (2 * c) * Ib n) := by
          rw [hv2]; ring
  -- sums over finite sets
  have hpt : ∀ (S : Finset ℤ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) t →
      ∑ n ∈ S, Wf n s ^ 2 ≤ Real.exp (2 * R1') * c ^ 2 := by
    intro S s hs
    have hs1 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht1⟩
    have h1 : ∑ n ∈ S, Wf n s ^ 2 ≤
        ∑ n ∈ S, (‖seqOsc38 (coverRep38 φ.1) (-ξ n) s‖ ^ 2 + ‖seqOsc38 (coverRep38 φ.2) (ξ n) s‖ ^ 2) :=
      Finset.sum_le_sum fun n _ => W_sq_le (potRepFst38 φ) (potRepSnd38 φ) (ξ n) hs.1
    rw [Finset.sum_add_distrib] at h1
    have ha := bessel_fin_a φ.1 ξ hξ' hs1 S
    have hb := bessel_fin_b φ.2 ξ hξ' hs1 S
    rw [hc2]
    nlinarith
  have hint : ∀ S : Finset ℤ, ∑ n ∈ S, Ib n ≤ Real.exp (2 * R1') * c ^ 2 := by
    intro S
    have hI : ∑ n ∈ S, Ib n = ∫ s in (0 : ℝ)..t, ∑ n ∈ S, Wf n s ^ 2 := by
      rw [intervalIntegral.integral_finset_sum]
      intro n _
      exact (hK n).1
    rw [hI]
    have hsumint : IntervalIntegrable (fun s => ∑ n ∈ S, Wf n s ^ 2) MeasureTheory.volume 0 t := by
      have := IntervalIntegrable.sum S fun n _ => (hK n).1
      simpa only [Finset.sum_fn] using this
    have := intervalIntegral.integral_mono_on ht0 hsumint
      (intervalIntegrable_const (c := Real.exp (2 * R1') * c ^ 2)) (fun s hs => hpt S s hs)
    refine this.trans ?_
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have hp : 0 ≤ Real.exp (2 * R1') * c ^ 2 := by positivity
    nlinarith
  have hsum : ∀ S : Finset ℤ, ∑ n ∈ S, X n ^ 2 ≤
      2 * Real.exp (2 * R1') * (Real.exp (2 * R1') * R0' ^ 2 +
        R0' ^ 2 * Real.exp (2 * R0') * (Real.exp (2 * R1') * R0' ^ 2)) := by
    intro S
    have h1 : ∑ n ∈ S, X n ^ 2 ≤
        ∑ n ∈ S, 2 * Real.exp (2 * R1') * (Wf n t ^ 2 + c ^ 2 * Real.exp (2 * c) * Ib n) :=
      Finset.sum_le_sum fun n _ => hXn n
    have h2 : ∑ n ∈ S, 2 * Real.exp (2 * R1') * (Wf n t ^ 2 + c ^ 2 * Real.exp (2 * c) * Ib n) =
        2 * Real.exp (2 * R1') * (∑ n ∈ S, Wf n t ^ 2 +
          c ^ 2 * Real.exp (2 * c) * ∑ n ∈ S, Ib n) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h3 := hpt S t ⟨ht0, le_rfl⟩
    have h4 := hint S
    have hE : 0 < Real.exp (2 * R1') := Real.exp_pos _
    have hmono : 2 * Real.exp (2 * R1') * (∑ n ∈ S, Wf n t ^ 2 +
          c ^ 2 * Real.exp (2 * c) * ∑ n ∈ S, Ib n) ≤
        2 * Real.exp (2 * R1') * (Real.exp (2 * R1') * c ^ 2 +
          c ^ 2 * Real.exp (2 * c) * (Real.exp (2 * R1') * c ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh : c ^ 2 * Real.exp (2 * c) * ∑ n ∈ S, Ib n ≤
          c ^ 2 * Real.exp (2 * c) * (Real.exp (2 * R1') * c ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      linarith
    have hcc : 2 * Real.exp (2 * R1') * (Real.exp (2 * R1') * c ^ 2 +
          c ^ 2 * Real.exp (2 * c) * (Real.exp (2 * R1') * c ^ 2)) ≤
        2 * Real.exp (2 * R1') * (Real.exp (2 * R1') * R0' ^ 2 +
          R0' ^ 2 * Real.exp (2 * R0') * (Real.exp (2 * R1') * R0' ^ 2)) := by
      have hc2' : c ^ 2 ≤ R0' ^ 2 := pow_le_pow_left₀ hc0 hcR 2
      have hec : Real.exp (2 * c) ≤ Real.exp (2 * R0') := Real.exp_le_exp.2 (by linarith)
      gcongr
    exact h1.trans (h2 ▸ (hmono.trans hcc))
  have hsumm : Summable (fun n : ℤ => X n ^ 2) :=
    summable_of_sum_le (fun n => sq_nonneg _) hsum
  exact ⟨hsumm, hsumm.tsum_le_of_sum_le hsum⟩

end

end NlsGge.Atomic.G1050S2.K20.K19

end

namespace NlsGge.Atomic.G1050S2.K20

noncomputable section

open MeasureTheory Filter Topology Set
open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot
open scoped Matrix.Norms.L2Operator

theorem differentiableAt_M (ψ : PotPair) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => ∑' n : ℕ, potentialVolterraTerm38 ψ w n t) z := by
  have h := NlsGge.Atomic.G1004GenT.analytic_all t ht (z, ψ) (Set.mem_univ _)
  have hc : AnalyticAt ℂ (fun w : ℂ => (w, ψ)) z :=
    analyticAt_id.prod analyticAt_const
  have h2 := AnalyticAt.comp (g := fun p : ℂ × PotPair => ∑' n : ℕ, potentialVolterraTerm38 p.2 p.1 n t)
    (f := fun w : ℂ => (w, ψ)) (x := z) h hc
  exact h2.differentiableAt

theorem differentiable_E (t : ℝ) : Differentiable ℂ (fun w : ℂ => freeZsFundamentalComplex w t) := by
  intro z
  have h : AnalyticAt ℂ (fun w : ℂ => freeE w t) z := by
    refine NlsGge.Atomic.G1004GenT.analyticAt_of_entries fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [freeE] <;> fun_prop
  have e : (fun w : ℂ => freeZsFundamentalComplex w t) = fun w => freeE w t := by
    funext w; exact (freeE_eq w t).symm
  rw [e]
  exact h.differentiableAt

/-- Cauchy's estimate in mean-square form on the unit circle. -/
theorem cauchy_sq_bound {f : ℂ → Matrix (Fin 2) (Fin 2) ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    ‖deriv f c‖ ^ 2 ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap c 1 θ)‖ ^ 2 := by
  have hI := (hf.diffContOnCl (s := Metric.ball c 1)).deriv_eq_smul_circleIntegral (c := c)
    (R := 1) one_pos
  have hpi : 0 < 2 * Real.pi := by positivity
  have hcont : Continuous fun θ : ℝ => ‖f (circleMap c 1 θ)‖ :=
    (hf.continuous.comp (continuous_circleMap c 1)).norm
  have hnorm : ‖(2 * Real.pi * Complex.I) • deriv f c‖ = 2 * Real.pi * ‖deriv f c‖ := by
    rw [norm_smul]
    congr 1
    simp [Complex.norm_mul, abs_of_pos Real.pi_pos]
  have hle : ‖∮ z in C(c, 1), (1 / (z - c) ^ 2) • f z‖ ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap c 1 θ)‖ := by
    rw [circleIntegral]
    refine (intervalIntegral.norm_integral_le_integral_norm hpi.le).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [norm_smul, deriv_circleMap, norm_mul, Complex.norm_I, mul_one]
    have h1 : ‖circleMap 0 1 θ‖ = 1 := by simp
    have h2 : ‖1 / (circleMap c 1 θ - c) ^ 2‖ = 1 := by
      rw [norm_div, norm_pow, norm_one]
      have : circleMap c 1 θ - c = circleMap 0 1 θ := by simp [circleMap]
      rw [this, h1]; simp
    simp only [h1, h2, one_mul]
  have hB : 2 * Real.pi * ‖deriv f c‖ ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap c 1 θ)‖ := by
    rw [← hnorm, ← hI]; exact hle
  have hcs := NlsGge.Atomic.G1050S2.K20.K19.K16.cs_integral (t := 2 * Real.pi) hpi.le
    (f := fun θ => ‖f (circleMap c 1 θ)‖) (g := fun _ => (1 : ℝ))
    ((hcont.pow 2).intervalIntegrable 0 _) (by simpa using intervalIntegrable_const)
    (by simpa using hcont.intervalIntegrable 0 (2 * Real.pi))
  simp only [mul_one, one_pow, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hcs
  have hd0 : 0 ≤ 2 * Real.pi * ‖deriv f c‖ := by positivity
  have h3 : (2 * Real.pi * ‖deriv f c‖) ^ 2 ≤ (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap c 1 θ)‖ ^ 2) * (2 * Real.pi) :=
    (pow_le_pow_left₀ hd0 hB 2).trans hcs
  rw [inv_mul_eq_div, le_div_iff₀ hpi]
  nlinarith [h3]

theorem G1020_whole : ((
  ∀ R0 R1 : ℝ, ∃ C : ℝ, ∀ (φ : PotPair) (ξ : ℤ → ℂ),
    Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ R0 →
    (∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∀ n : ℤ, DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) (ξ n)) ∧
      Summable (fun n : ℤ =>
        ‖deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) (ξ n) -
            deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n)‖ ^ 2) ∧
      (∑' n : ℤ,
        ‖deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) (ξ n) -
            deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n)‖ ^ 2) ≤ C
  : Prop)) := by
  intro R0 R1
  obtain ⟨C, hC⟩ := K19.G1019_whole R0 (R1 + 1)
  refine ⟨C, ?_⟩
  intro φ ξ hφ hξ t ht0 ht1
  have hMd : ∀ w : ℂ, DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) w :=
    fun w => differentiableAt_M φ ht0 w
  refine ⟨fun n => hMd (ξ n), ?_⟩
  set f : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun w =>
    (∑' m : ℕ, potentialVolterraTerm38 φ w m t) - freeZsFundamentalComplex w t with hf
  have hfd : Differentiable ℂ f := fun w => (hMd w).sub (differentiable_E t w)
  have hderiv : ∀ n : ℤ, deriv f (ξ n) =
      deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) (ξ n) -
        deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n) := fun n =>
    deriv_sub (hMd (ξ n)) (differentiable_E t (ξ n))
  have hcirc : ∀ θ : ℝ, ∀ S : Finset ℤ,
      ∑ n ∈ S, ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 ≤ C := by
    intro θ S
    have hξθ : ∀ n : ℤ, ‖(fun n => circleMap (ξ n) 1 θ) n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1 + 1 := by
      intro n
      have e : circleMap (ξ n) 1 θ - (n : ℂ) * (Real.pi : ℂ) =
          (ξ n - (n : ℂ) * (Real.pi : ℂ)) + circleMap 0 1 θ := by
        simp [circleMap]; ring
      show ‖circleMap (ξ n) 1 θ - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1 + 1
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖circleMap 0 1 θ‖ = 1 := by simp
      linarith [hξ n]
    obtain ⟨hs, hb⟩ := hC φ (fun n => circleMap (ξ n) 1 θ) hφ hξθ t ht0 ht1
    exact (Summable.sum_le_tsum S (fun n _ => sq_nonneg _) hs).trans hb
  have hpi : 0 < 2 * Real.pi := by positivity
  have hgc : ∀ n : ℤ, Continuous fun θ : ℝ => ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 := fun n =>
    ((hfd.continuous.comp (continuous_circleMap (ξ n) 1)).norm).pow 2
  have hsum : ∀ S : Finset ℤ, ∑ n ∈ S, ‖deriv f (ξ n)‖ ^ 2 ≤ C := by
    intro S
    have h1 : ∑ n ∈ S, ‖deriv f (ξ n)‖ ^ 2 ≤
        ∑ n ∈ S, (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 :=
      Finset.sum_le_sum fun n _ => cauchy_sq_bound hfd (ξ n)
    have h2 : ∑ n ∈ S, (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 =
        (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ n ∈ S, ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 := by
      rw [← Finset.mul_sum, intervalIntegral.integral_finset_sum]
      intro n _
      exact (hgc n).intervalIntegrable 0 _
    have hint : ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ n ∈ S, ‖f (circleMap (ξ n) 1 θ)‖ ^ 2 ≤
        ∫ θ in (0 : ℝ)..(2 * Real.pi), C := by
      refine intervalIntegral.integral_mono_on hpi.le ?_ intervalIntegrable_const fun θ _ => hcirc θ S
      exact (continuous_finset_sum _ fun n _ => hgc n).intervalIntegrable 0 _
    have h3 : (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), C = C := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      field_simp
    calc ∑ n ∈ S, ‖deriv f (ξ n)‖ ^ 2 ≤ _ := h1
      _ = _ := h2
      _ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), C :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = C := h3
  have hsumm : Summable (fun n : ℤ => ‖deriv f (ξ n)‖ ^ 2) :=
    summable_of_sum_le (fun n => sq_nonneg _) hsum
  have hrw : (fun n : ℤ => ‖deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m t) (ξ n) -
      deriv (fun w : ℂ => freeZsFundamentalComplex w t) (ξ n)‖ ^ 2) =
      fun n : ℤ => ‖deriv f (ξ n)‖ ^ 2 := by
    funext n; rw [hderiv n]
  rw [hrw]
  exact ⟨hsumm, hsumm.tsum_le_of_sum_le hsum⟩

end

end NlsGge.Atomic.G1050S2.K20
end

section
set_option autoImplicit false

open Filter Topology Finset NlsGge.GK38.Lib NlsGge.Atomic.G2

namespace NlsGge.Atomic.G1050S2.K10

noncomputable section

/-- Uniform pointwise smallness on the large circles (the content of G2-009 with the sup replaced
by the pointwise statement and summability made explicit). -/
theorem circle_pointwise_small (s : L2Z) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z : ℂ, ‖z‖ = (N : ℝ) * Real.pi + Real.pi / 2 →
      Summable (fun m : ℤ => ‖s m‖ / ‖(m : ℂ) * (Real.pi : ℂ) - z‖) ∧
        ∑' m : ℤ, ‖s m‖ / ‖(m : ℂ) * (Real.pi : ℂ) - z‖ ≤ ε := by
  let σ : ℤ → ℂ := fun m => (m : ℂ) * (Real.pi : ℂ) + s m
  have hσ : Summable (fun m : ℤ => ‖prodDev σ m‖ ^ 2) := by
    simpa [σ, prodDev] using summable_sq_lp s
  obtain ⟨N₀, hN₀⟩ := circle_sum_bound hσ (mul_pos Real.pi_pos hε)
  refine ⟨N₀, fun N hN z hz => ?_⟩
  have hπ : 0 < Real.pi := Real.pi_pos
  have hgeom (m : ℤ) :
      ‖s m‖ / ‖(m : ℂ) * (Real.pi : ℂ) - z‖ ≤ (1 / Real.pi) * (‖s m‖ / circDist N m) := by
    have hd := circDist_pos N m
    calc ‖s m‖ / ‖(m : ℂ) * (Real.pi : ℂ) - z‖ ≤ ‖s m‖ / (Real.pi * circDist N m) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hπ hd) (pi_mul_dd_le hz m)
      _ = (1 / Real.pi) * (‖s m‖ / circDist N m) := by field_simp
  have hnonneg : ∀ m : ℤ, 0 ≤ ‖s m‖ / ‖(m : ℂ) * (Real.pi : ℂ) - z‖ :=
    fun m => div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hfin (S : Finset ℤ) :
      ∑ m ∈ S, ‖s m‖ / ‖(m : ℂ) * (Real.pi : ℂ) - z‖ ≤ ε := by
    calc ∑ m ∈ S, ‖s m‖ / ‖(m : ℂ) * (Real.pi : ℂ) - z‖
        ≤ ∑ m ∈ S, (1 / Real.pi) * (‖s m‖ / circDist N m) :=
          Finset.sum_le_sum fun m _ => hgeom m
      _ = (1 / Real.pi) * ∑ m ∈ S, ‖s m‖ / circDist N m := by rw [Finset.mul_sum]
      _ ≤ (1 / Real.pi) * (Real.pi * ε) := by
          have hsource : ∑ m ∈ S, ‖s m‖ / circDist N m ≤ Real.pi * ε := by
            simpa [σ, prodDev] using hN₀ N hN S
          exact mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = ε := by field_simp
  have hsum : Summable (fun m : ℤ => ‖s m‖ / ‖(m : ℂ) * (Real.pi : ℂ) - z‖) :=
    summable_of_sum_le hnonneg hfin
  exact ⟨hsum, Real.tsum_le_of_sum_le hnonneg hfin⟩

theorem mpi_sub_ne_zero {N : ℕ} {z : ℂ} (hz : ‖z‖ = (N : ℝ) * Real.pi + Real.pi / 2) (m : ℤ) :
    (m : ℂ) * (Real.pi : ℂ) - z ≠ 0 := by
  intro h
  have h1 := pi_mul_dd_le hz m
  have h2 : ‖(m : ℂ) * (Real.pi : ℂ) - z‖ = 0 := by rw [h]; simp
  have h3 := circDist_pos N m
  have := Real.pi_pos
  nlinarith

/-- `sin` does not vanish on the large circles. -/
theorem sin_ne_zero_of_norm {N : ℕ} {z : ℂ} (hz : ‖z‖ = (N : ℝ) * Real.pi + Real.pi / 2) :
    Complex.sin z ≠ 0 := by
  intro h
  rw [Complex.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have h1 : ‖z‖ = |(k : ℝ)| * Real.pi := by
    rw [hk, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    simp
  have hπ := Real.pi_pos
  have h2 : |(k : ℝ)| = (N : ℝ) + 1 / 2 := by
    have : |(k : ℝ)| * Real.pi = ((N : ℝ) + 1 / 2) * Real.pi := by rw [← h1, hz]; ring
    exact mul_right_cancel₀ hπ.ne' this
  have h3 : (2 * |k| : ℤ) = 2 * N + 1 := by
    have : ((2 * |k| : ℤ) : ℝ) = ((2 * N + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  omega

/-- The symmetric finite product of the unperturbed factors is `-λ ∏_{j<K}(1 - λ²/(π j)²)`. -/
theorem prod_unperturbed (lam : ℂ) (K : ℕ) :
    ∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (((m : ℂ) * (Real.pi : ℂ) - lam) / (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ))) =
      -lam * ∏ j ∈ Finset.range K, ((1 : ℂ) - (lam / (Real.pi : ℂ)) ^ 2 / ((j : ℂ) + 1) ^ 2) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  induction K with
  | zero => simp
  | succ K ih =>
    have hcast : (((K + 1 : ℕ)) : ℤ) = (K : ℤ) + 1 := by push_cast; ring
    rw [hcast, Finset.prod_range_succ, ← mul_assoc, ← ih]
    have hA : Finset.Icc (-((K : ℤ) + 1)) ((K : ℤ) + 1) =
        insert ((K : ℤ) + 1) (insert (-((K : ℤ) + 1)) (Finset.Icc (-(K : ℤ)) (K : ℤ))) := by
      ext m
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hn1 : (K : ℤ) + 1 ∉ insert (-((K : ℤ) + 1)) (Finset.Icc (-(K : ℤ)) (K : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hn2 : -((K : ℤ) + 1) ∉ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hA, Finset.prod_insert hn1, Finset.prod_insert hn2]
    have h1 : ((K : ℤ) + 1) ≠ 0 := by omega
    have h2 : -((K : ℤ) + 1) ≠ 0 := by omega
    have hk : ((K : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero K
    rw [if_neg h1, if_neg h2]
    push_cast
    field_simp
    ring


theorem g2010_ratio_one : (
  ∀ s : L2Z,
  ∃ F : ℂ → ℂ,
    (∀ lam : ℂ,
        Filter.Tendsto
          (fun K : ℕ =>
            -(∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              (((m : ℂ) * (Real.pi : ℂ) + s m) - lam) /
                (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ))))
          Filter.atTop (nhds (F lam))) ∧
    (∀ (N : ℕ) (lam : ℂ), lam ∈ Metric.sphere (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 2) →
        Complex.sin lam ≠ 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ lam ∈ Metric.sphere (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 2),
          ‖F lam / Complex.sin lam - 1‖ ≤ ε)
  : Prop) := by
  intro s
  obtain ⟨P0, hP0, _⟩ := g2006_part2 0
  set F : ℂ → ℂ := fun lam => -(gFac s lam 0 * P0 (lam, s)) with hF
  have hF1 : ∀ lam : ℂ, Filter.Tendsto
      (fun K : ℕ => -(∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (((m : ℂ) * (Real.pi : ℂ) + s m) - lam) /
          (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ))))
      Filter.atTop (nhds (F lam)) := by
    intro lam
    have h := hP0 (lam, s)
    have h' := ((tendsto_const_nhds (x := gFac s lam 0)).mul h).neg
    refine h'.congr (fun K => ?_)
    have h0 : (0 : ℤ) ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    have hmul := Finset.mul_prod_erase (Finset.Icc (-(K : ℤ)) (K : ℤ))
      (fun m : ℤ => (((m : ℂ) * (Real.pi : ℂ) + s m) - lam) /
        (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ))) h0
    show -(gFac s lam 0 * Fp 0 K (lam, s)) = _
    rw [← hmul]
    simp [Fp, gFac]
  refine ⟨F, hF1, ?_, ?_⟩
  · intro N lam hlam
    exact sin_ne_zero_of_norm (by simpa [mem_sphere_zero_iff_norm] using hlam)
  · intro ε hε
    set ε' : ℝ := min (1 / 2) (ε / 2) with hε'
    have hε'pos : 0 < ε' := lt_min (by norm_num) (by linarith)
    obtain ⟨N0, hN0⟩ := circle_pointwise_small s hε'pos
    refine ⟨N0, fun N hN lam hlam => ?_⟩
    have hz : ‖lam‖ = (N : ℝ) * Real.pi + Real.pi / 2 := by
      simpa [mem_sphere_zero_iff_norm] using hlam
    obtain ⟨hsum, hS⟩ := hN0 N hN lam hz
    have hsin := sin_ne_zero_of_norm hz
    set a : ℤ → ℂ := fun m => s m / ((m : ℂ) * (Real.pi : ℂ) - lam) with ha
    have hsa : Summable (fun m : ℤ => ‖a m‖) :=
      hsum.congr (fun m => (norm_div _ _).symm)
    have hSa : ∑' m : ℤ, ‖a m‖ ≤ ε' := by
      refine le_trans (le_of_eq (tsum_congr (fun m => norm_div _ _))) hS
    have hfac : ∀ m : ℤ, gFac s lam m =
        ((((m : ℂ) * (Real.pi : ℂ) - lam) /
          (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ))) * (1 + a m)) := by
      intro m
      have hne := mpi_sub_ne_zero hz m
      unfold gFac
      simp only [ha]
      field_simp
      ring
    set R : ℕ → ℂ := fun K => ∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (1 + a m) with hR
    set A : ℕ → ℂ := fun K => ∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (((m : ℂ) * (Real.pi : ℂ) - lam) /
        (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ))) with hA
    have hBA : ∀ K : ℕ, ∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (((m : ℂ) * (Real.pi : ℂ) + s m) - lam) /
          (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)) = A K * R K := by
      intro K
      rw [hA, hR, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun m _ => hfac m)
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hEuler : Tendsto (fun K : ℕ => -A K) atTop (𝓝 (Complex.sin lam)) := by
      have h := Complex.tendsto_euler_sin_prod (lam / (Real.pi : ℂ))
      rw [show (Real.pi : ℂ) * (lam / (Real.pi : ℂ)) = lam by field_simp] at h
      refine h.congr (fun K => ?_)
      rw [hA]
      simp only [prod_unperturbed lam K]
      field_simp
    have h1 := hF1 lam
    have h2 : Tendsto R atTop (𝓝 (F lam / Complex.sin lam)) := by
      have := h1.div hEuler hsin
      refine this.congr' ?_
      filter_upwards [hEuler.eventually_ne hsin] with K hK
      simp only [Pi.div_apply]
      rw [hBA K]
      have hK' : A K ≠ 0 := fun h => hK (by simp [h])
      field_simp
    have hb : ∀ K : ℕ, ‖R K - 1‖ ≤ Real.exp (∑' m : ℤ, ‖a m‖) - 1 := by
      intro K
      refine (Finset.norm_prod_one_add_sub_one_le _ a).trans ?_
      have := hsa.sum_le_tsum (Finset.Icc (-(K : ℤ)) (K : ℤ)) (fun _ _ => norm_nonneg _)
      have := Real.exp_le_exp.mpr this
      linarith
    have h3 : ‖F lam / Complex.sin lam - 1‖ ≤ Real.exp (∑' m : ℤ, ‖a m‖) - 1 :=
      le_of_tendsto' ((h2.sub_const 1).norm) hb
    refine h3.trans ?_
    have hε'lt : ε' < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hexp : Real.exp (∑' m : ℤ, ‖a m‖) ≤ Real.exp ε' := Real.exp_le_exp.mpr hSa
    have hb2 := Real.exp_bound_div_one_sub_of_interval' hε'pos hε'lt
    have hε'half : ε' ≤ 1 / 2 := min_le_left _ _
    have hε'eps : ε' ≤ ε / 2 := min_le_right _ _
    have hdiv : 1 / (1 - ε') ≤ 1 + 2 * ε' := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith

end

end NlsGge.Atomic.G1050S2.K10
end

                                                                                
                                                                          
                                                                                                                                         
                                                                                                                                         
                                                       
                                                                                                                                 
                                                                                                                                     
                                                                                                                                        
                                                                                                                             
                                                                                                                                    
                                                                                        
                                                                               

namespace NlsGge.Atomic.G1050S2

open Filter Topology SummationFilter Set Metric NlsGge.GK38 NlsGge.Atomic.Volterra NlsGge.SpectralFoundations NlsGge.Pilot
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ### The critical asymptotics from G1-047 -/

theorem deriv_err_of_ratio {D s : ℂ} {ε : ℝ} (hs : s ≠ 0) (h : ‖D / (-2 * s) - 1‖ ≤ ε) :
    ‖D - (-2 * s)‖ ≤ ε * ‖(-2 : ℂ) * s‖ := by
  have hne : (-2 : ℂ) * s ≠ 0 := mul_ne_zero (by norm_num) hs
  have e : D - (-2 * s) = (D / (-2 * s) - 1) * (-2 * s) := by field_simp; ring
  rw [e, norm_mul]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

theorem critical_asymp (φ₀ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ R : ℝ, ∀ φ ∈ U, ∀ z : ℂ, R < ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖deriv (discrim φ) z - (-2 * Complex.sin z)‖ ≤ ε * ‖(-2 : ℂ) * Complex.sin z‖ := by
  obtain ⟨U, hU, Λ, h⟩ := K47.G1047_whole φ₀ ε hε
  refine ⟨U, hU, Λ, fun φ hφ z hz hsep => ?_⟩
  have hsep' : ∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := hsep
  obtain ⟨-, -, h3⟩ := h φ hφ z hz hsep'
  have h3' : ‖deriv (discrim φ) z / (-2 * Complex.sin z) - 1‖ ≤ ε := h3
  exact deriv_err_of_ratio (counting_sin_ne_zero38 hsep) h3'

/-! ### The critical counting cutoff and the labelling -/

theorem critical_counting_lemmaG (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, 0 < N ∧
      ∀ φ : PotPair, φ ∈ U → RootCountingAt38 (deriv (discrim φ)) 1 N := by
  obtain ⟨U, hU, R, herr⟩ := critical_asymp φ₀ (1 / 4) (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N : ℕ := K + 1
  have hN : 0 < N := Nat.succ_pos K
  have hRN : R < countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  refine ⟨U, hU, N, hN, fun φ hφ => ?_⟩
  have hcmp : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖deriv (discrim φ) z - deriv (NlsGge.GK38.discrim 0) z‖ < ‖deriv (NlsGge.GK38.discrim 0) z‖ := by
    intro z hz hsep
    have hs : Complex.sin z ≠ 0 := counting_sin_ne_zero38 hsep
    have h := herr φ hφ z (lt_of_lt_of_le hRN hz) hsep
    have hpos : 0 < ‖(-2 : ℂ) * Complex.sin z‖ :=
      norm_pos_iff.mpr (mul_ne_zero (by norm_num) hs)
    rw [discrimDeriv_zero38]
    calc ‖deriv (discrim φ) z - (-2 * Complex.sin z)‖ ≤ (1 / 4) * ‖(-2 : ℂ) * Complex.sin z‖ := h
      _ < ‖(-2 : ℂ) * Complex.sin z‖ := by linarith
  have hsphere := counting_radius_mem_sphere38 N
  have hnorm : countingRadius38 N ≤ ‖(countingRadius38 N : ℂ)‖ := by
    simp [Complex.norm_real, abs_of_pos (countingRadius_pos38 N)]
  have hsep := counting_central_sphere_separated38 N hsphere
  obtain ⟨hs₂, hc₂, he₂⟩ := critical_counting_at38 φ N hcmp
  refine ⟨hN, analyticOnNhd_discrimDeriv38 φ,
    ⟨_, critical_ne_zero_of_comparison38 (hcmp _ hnorm hsep)⟩,
    critical_zeroMult_support_finite38 φ, hs₂, ?_, he₂⟩
  simpa only [one_mul] using hc₂

theorem exists_cutoffG (φ : PotPair) : ∃ N : ℕ, RootCountingAt38 (deriv (discrim φ)) 1 N := by
  obtain ⟨U, hU, N, -, h⟩ := critical_counting_lemmaG φ
  exact ⟨N, h φ (mem_of_mem_nhds hU)⟩

open Classical in
def cutoffG (φ : PotPair) : ℕ := Nat.find (exists_cutoffG φ)

theorem cutoffG_spec (φ : PotPair) : RootCountingAt38 (deriv (discrim φ)) 1 (cutoffG φ) := by
  classical
  exact Nat.find_spec (exists_cutoffG φ)

def lamG (φ : PotPair) : ℤ → ℂ := criticalCandidate38 (deriv (discrim φ)) (cutoffG φ)

theorem lamG_eq {φ : PotPair} {N : ℕ} (h : RootCountingAt38 (deriv (discrim φ)) 1 N) :
    lamG φ = criticalCandidate38 (deriv (discrim φ)) N :=
  criticalCandidate_cutoff_invariant38 (cutoffG_spec φ) h

theorem lamG_enumeration (φ : PotPair) : RootEnumeration38 (deriv (discrim φ)) (lamG φ) :=
  criticalCandidate_enumeration38 (cutoffG_spec φ)

/-! ### The critical square sums from G1-020 -/

theorem trace_deriv_freeZs (z : ℂ) :
    Matrix.trace (deriv (fun w : ℂ => freeZsFundamentalComplex w 1) z) = -2 * Complex.sin z := by
  have hdE := (K47.K17.differentiable_E 1 z).hasDerivAt
  have hTdE := K47.hasDerivAt_trace hdE
  have hfun : (fun w : ℂ => Matrix.trace (freeZsFundamentalComplex w 1)) =
      fun w => 2 * Complex.cos w := funext K47.trace_freeZs
  rw [hfun] at hTdE
  have hc : HasDerivAt (fun w : ℂ => 2 * Complex.cos w) (2 * (-Complex.sin z)) z :=
    (Complex.hasDerivAt_cos z).const_mul 2
  have := hTdE.unique hc
  rw [this]; ring

theorem deriv_discrim_add_two_sin (φ : PotPair) (z : ℂ)
    (hd : DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1) z) :
    deriv (discrim φ) z + 2 * Complex.sin z =
      Matrix.trace (deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1) z -
        deriv (fun w : ℂ => freeZsFundamentalComplex w 1) z) := by
  have hfun : (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1) =
      fun w : ℂ => monodromyPair φ w := funext (K47.series_one_eq_monodromyPair φ)
  rw [hfun] at hd ⊢
  have hTd := K47.hasDerivAt_trace hd.hasDerivAt
  have h1 : deriv (discrim φ) z =
      Matrix.trace (deriv (fun w : ℂ => monodromyPair φ w) z) := hTd.deriv
  rw [h1, Matrix.trace_sub, trace_deriv_freeZs]
  ring

theorem critical_roots_sine_l2G (R c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
      (∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      (∀ n : ℤ, deriv (discrim φ) (υ n) = 0) →
      Summable (fun n : ℤ => ‖Complex.sin (υ n)‖ ^ 2) ∧
        (∑' n : ℤ, ‖Complex.sin (υ n)‖ ^ 2) ≤ C := by
  obtain ⟨C0, hC⟩ := K20.G1020_whole (2 * |R|) c
  refine ⟨max C0 0, le_max_right _ _, fun φ hφ υ hshift hroot => ?_⟩
  have hR : Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ 2 * |R| := by
    have h1 : ‖φ.1‖ ≤ |R| := (norm_fst_le φ).trans (hφ.trans (le_abs_self _))
    have h2 : ‖φ.2‖ ≤ |R| := (norm_snd_le φ).trans (hφ.trans (le_abs_self _))
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [norm_nonneg φ.1, norm_nonneg φ.2, abs_nonneg R]
  obtain ⟨hd, hs, ht⟩ := hC φ υ hR hshift 1 zero_le_one le_rfl
  set D : ℤ → PairMat38 := fun n =>
    deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1) (υ n) -
      deriv (fun w : ℂ => freeZsFundamentalComplex w 1) (υ n) with hD
  have hpt : ∀ n : ℤ, ‖Complex.sin (υ n)‖ ^ 2 ≤ ‖D n‖ ^ 2 := by
    intro n
    have h := deriv_discrim_add_two_sin φ (υ n) (hd n)
    rw [hroot n, zero_add] at h
    have hb : ‖(2 : ℂ) * Complex.sin (υ n)‖ ≤ 2 * ‖D n‖ := by
      rw [h]; exact K47.norm_trace_le _
    rw [norm_mul, Complex.norm_ofNat] at hb
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have hsm : Summable (fun n : ℤ => ‖Complex.sin (υ n)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpt hs
  refine ⟨hsm, ?_⟩
  exact ((hsm.tsum_le_tsum hpt hs).trans ht).trans (le_max_left _ _)

theorem critical_l2G (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : PotPair, φ ∈ U →
      Summable (fun n : ℤ => ‖lamG φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      (∑' n : ℤ, ‖lamG φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ C := by
  obtain ⟨U, hU, N, _hN, hloc⟩ := critical_counting_lemmaG φ₀
  let b : ℝ := 2 * (N : ℝ) * Real.pi + Real.pi / 4
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let R : ℝ := ‖φ₀‖ + 1
  obtain ⟨Cd, hCd, hd⟩ := critical_roots_sine_l2G R b
  let T : ℝ := ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) * b ^ 2
  let K : ℝ := Real.pi / 2 + 1
  let Bd : ℝ := T + K ^ 2 * Cd
  have hBd : 0 ≤ Bd := by dsimp [Bd, T]; positivity
  refine ⟨U ∩ ball φ₀ 1, inter_mem hU (ball_mem_nhds φ₀ zero_lt_one), Bd, hBd, fun φ hφ => ?_⟩
  have hR : ‖φ‖ ≤ R := by
    have hdist : ‖φ - φ₀‖ < 1 := mem_ball_iff_norm.mp hφ.2
    have hn : ‖φ‖ ≤ ‖φ - φ₀‖ + ‖φ₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (φ - φ₀) φ₀
    dsimp [R]
    linarith
  have hcount := hloc φ hφ.1
  have heD := lamG_eq hcount
  have hsh (n : ℤ) := criticalCandidate_shift_bound38 hcount n
  have hshift : ∀ n : ℤ, ‖lamG φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ b := by
    intro n
    have := (hsh n).1
    simpa only [heD, countingCenter38] using this
  have hfar : ∀ n : ℤ, (N : ℤ) < |n| →
      ‖lamG φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Real.pi / 4 := by
    intro n hn
    have := (hsh n).2 hn
    simpa only [heD, countingCenter38] using this.le
  have hdRoot (n : ℤ) : deriv (discrim φ) (lamG φ n) = 0 := (lamG_enumeration φ).1 n
  obtain ⟨hsD, htD⟩ := hd φ hR (lamG φ) hshift hdRoot
  have hd' := localized_sine_l2_38 (lamG φ) N b Cd hb hCd hshift hfar hsD htD
  refine ⟨hd'.1, ?_⟩
  have hh := hd'.2
  change _ ≤ Bd at hh
  exact hh

/-! ### The circle growth of the product from G2-010 -/

theorem piN_cast (m : ℤ) : ((πn m : ℝ) : ℂ) = if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ) := by
  unfold πn NlsGge.GK38.Lib.piN
  split_ifs <;> push_cast <;> rfl

theorem partial_prod_tendsto (σ : ℤ → ℂ)
    (hσ : Summable fun n : ℤ => ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) (z : ℂ) :
    Tendsto (fun K : ℕ => ∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (σ m - z) / (πn m : ℂ)) atTop
      (𝓝 (singleProduct38 σ z)) := by
  have hP := ((Lib.product_entire σ hσ).1 z).hasProd
  unfold HasProd at hP
  rw [symmetricIcc_eq_map_Icc_nat, tendsto_map'_iff] at hP
  exact hP

theorem product_growthG (σ : ℤ → ℂ)
    (hσ : Summable fun n : ℤ => ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = n * Real.pi + Real.pi / 2 →
      ‖singleProduct38 σ z + Complex.sin z‖ ≤ ε * ‖Complex.sin z‖ := by
  intro ε hε
  let s : Lib.L2Z := ⟨fun m => σ m - (m : ℂ) * (Real.pi : ℂ),
    (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr (by simpa using hσ)⟩
  obtain ⟨F, hF1, -, hF3⟩ := K10.g2010_ratio_one s
  obtain ⟨N0, hN0⟩ := hF3 ε hε
  refine ⟨N0, fun n hn z hz => ?_⟩
  have hzs : z ∈ Metric.sphere (0 : ℂ) ((n : ℝ) * Real.pi + Real.pi / 2) := by
    simpa [mem_sphere_zero_iff_norm] using hz
  have hsin : Complex.sin z ≠ 0 := by
    have hd := Lib.pi_mul_dd_le hz
    exact (K10.sin_ne_zero_of_norm hz)
  have hr := hN0 n hn z hzs
  have hlim := partial_prod_tendsto σ hσ z
  have hlim2 : Tendsto (fun K : ℕ => -(∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (σ m - z) / (πn m : ℂ))) atTop (𝓝 (-(singleProduct38 σ z))) := hlim.neg
  have hF := hF1 z
  have heq : (fun K : ℕ => -(∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (((m : ℂ) * (Real.pi : ℂ) + (s : ℤ → ℂ) m) - z) /
        (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)))) =
      fun K : ℕ => -(∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (σ m - z) / (πn m : ℂ)) := by
    funext K
    congr 1
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [piN_cast]
    congr 1
    show (m : ℂ) * (Real.pi : ℂ) + (σ m - (m : ℂ) * (Real.pi : ℂ)) - z = σ m - z
    ring
  rw [heq] at hF
  have hFeq : F z = -(singleProduct38 σ z) := tendsto_nhds_unique hF hlim2
  rw [hFeq] at hr
  have hne : ‖Complex.sin z‖ ≠ 0 := norm_ne_zero_iff.mpr hsin
  have he : singleProduct38 σ z + Complex.sin z = -((-(singleProduct38 σ z)) / Complex.sin z - 1) *
      Complex.sin z := by field_simp; ring
  rw [he, norm_mul, norm_neg]
  exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)

/-! ### The critical product representation -/

def critProdG (φ : PotPair) (z : ℂ) : ℂ := 2 * singleProduct38 (lamG φ) z

theorem lamG_summable (φ : PotPair) :
    Summable (fun n : ℤ => ‖lamG φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
  obtain ⟨U, hU, C, -, h⟩ := critical_l2G φ
  exact (h φ (mem_of_mem_nhds hU)).1

theorem critProdG_circle_ratio (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      ‖deriv (discrim φ) z / critProdG φ z - 1‖ < ε := by
  let δ := min (1 / 4) (ε / 8)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hδε : 4 * δ < ε := by
    have h := min_le_right (1 / 4 : ℝ) (ε / 8)
    change δ ≤ ε / 8 at h
    linarith
  obtain ⟨Ng, hg⟩ := product_growthG (lamG φ) (lamG_summable φ) δ hδ
  obtain ⟨U, hU, R, herr⟩ := critical_asymp φ δ hδ
  obtain ⟨Na, hNa⟩ := exists_nat_ge (R / Real.pi)
  refine ⟨max Ng (Na + 1), fun n hn z hz => ?_⟩
  have hnG : Ng ≤ n := (le_max_left _ _).trans hn
  have hnA : Na + 1 ≤ n := (le_max_right _ _).trans hn
  have hs := productRepr_circle_sin_ne_zero38 hz
  have htD : (-2 : ℂ) * Complex.sin z ≠ 0 := mul_ne_zero (by norm_num) hs
  have hsep := productRepr_circle_separation38 hz
  have hRz : R < ‖z‖ := by
    have h1 : R ≤ (Na : ℝ) * Real.pi := (div_le_iff₀ Real.pi_pos).mp hNa
    have h2 : (Na : ℝ) + 1 ≤ n := by exact_mod_cast hnA
    rw [hz]
    nlinarith [Real.pi_pos]
  have hf := herr φ (mem_of_mem_nhds hU) z hRz hsep
  have hgm : ‖critProdG φ z - (-2 * Complex.sin z)‖ ≤ δ * ‖(-2 : ℂ) * Complex.sin z‖ := by
    have h := hg n hnG z hz
    have e : critProdG φ z - (-2 * Complex.sin z) = 2 * (singleProduct38 (lamG φ) z + Complex.sin z) := by
      unfold critProdG; ring
    rw [e, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
    nlinarith
  obtain ⟨-, hr⟩ := productRepr_relative_ratio38 _ _ _ δ hδ.le hδhalf htD hf hgm
  exact hr.trans_lt hδε

theorem analyticOrderAt_critProdG (φ : PotPair) (w : ℂ) :
    analyticOrderAt (critProdG φ) w = analyticOrderAt (deriv (discrim φ)) w := by
  have hd := Lib.product_entire (lamG φ) (lamG_summable φ)
  have hc : analyticOrderAt (fun _ : ℂ => (2 : ℂ)) w = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
  change analyticOrderAt ((fun _ : ℂ => (2 : ℂ)) * singleProduct38 (lamG φ)) w = _
  have had : AnalyticAt ℂ (singleProduct38 (lamG φ)) w := hd.2.1.analyticAt w
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) w := analyticAt_const
  rw [analyticOrderAt_mul hconst had, hc, zero_add]
  change analyticOrderAt (singleProduct38 (lamG φ)) w = _
  unfold singleProduct38
  rw [hd.2.2 w]
  exact ((lamG_enumeration φ).2.2 w).2

theorem discrimDeriv_eq_critProdG (φ : PotPair) : deriv (discrim φ) = critProdG φ := by
  apply Lib.entire_eq_of_ratio_tendsto_one
    (fun w => (analyticOnNhd_discrimDeriv38 φ w (mem_univ w)).differentiableAt)
    ((differentiable_singleProduct38 (lamG φ) (lamG_summable φ)).const_mul 2)
  · intro w
    exact (analyticOrderAt_critProdG φ w).le
  · intro ε hε
    exact critProdG_circle_ratio φ ε hε

theorem discrimDeriv_productG (φ : PotPair) (z : ℂ) :
    deriv (discrim φ) z = 2 * ∏'[symmetricIcc ℤ] k : ℤ, (lamG φ k - z) / (πn k : ℂ) :=
  congrFun (discrimDeriv_eq_critProdG φ) z

/-! ### The statement -/

theorem G1050_main :
    ((
  ∃ lambdaDot : PotPair → ℤ → ℂ,
    (∀ ψ : PotPair, ∀ z : ℂ,
        DifferentiableAt ℂ (fun w : ℂ => Matrix.trace (monodromyPair ψ w)) z) ∧
    (∀ ψ : PotPair, ∀ z : ℂ,
        analyticOrderAt (fun w : ℂ => deriv (fun v : ℂ => Matrix.trace (monodromyPair ψ v)) w) z =
          Set.encard {n : ℤ | lambdaDot ψ n = z}) ∧
    (∀ ψ : PotPair, ∃ U : Set PotPair, U ∈ nhds ψ ∧ ∃ C : ℝ, ∀ ψ' ∈ U,
        Summable (fun n : ℤ => ‖lambdaDot ψ' n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
        (∑' n : ℤ, ‖lambdaDot ψ' n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ C) ∧
    (∀ ψ : PotPair, ∀ z : ℂ,
        Filter.Tendsto
          (fun K : ℕ =>
            2 * ∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              (lambdaDot ψ m - z) / (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)))
          Filter.atTop
          (nhds (deriv (fun w : ℂ => Matrix.trace (monodromyPair ψ w)) z)))
  : Prop)) := by
  refine ⟨lamG, ?_, ?_, ?_, ?_⟩
  · intro ψ z
    exact (analyticOnNhd_discrim_z ψ z (Set.mem_univ z)).differentiableAt
  · intro ψ z
    exact ((lamG_enumeration ψ).2.2 z).2.symm
  · intro ψ
    obtain ⟨U, hU, C, -, h⟩ := critical_l2G ψ
    exact ⟨U, hU, C, fun ψ' hψ' => ⟨(h ψ' hψ').1, (h ψ' hψ').2⟩⟩
  · intro ψ z
    have hP := partial_prod_tendsto (lamG ψ) (lamG_summable ψ) z
    have hP2 := hP.const_mul (2 : ℂ)
    have hsp : (2 : ℂ) * singleProduct38 (lamG ψ) z = deriv (discrim ψ) z :=
      (discrimDeriv_productG ψ z).symm
    rw [hsp] at hP2
    refine hP2.congr (fun K => ?_)
    congr 1
    refine Finset.prod_congr rfl (fun m _ => ?_)
    rw [piN_cast]

end

end NlsGge.Atomic.G1050S2
