import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.G1.G1015
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairVolterraDefs
import NlsGge.GK38.DirichletCounting
import NlsGge.GK38.PoissonMixedTargets
import NlsGge.GK38.PoissonMixedRealNormingData
import NlsGge.GK38.GradFundamentalPairing
import NlsGge.GK38.DirichletRealWinding
import NlsGge.GK38.GradEigenRealState


                                                                                                                    
                                                                                                                                 
                                                                                                                          
                                                                                                                                 
                                                                                                                             
                                                                                                                                       
                                                                                                          

set_option autoImplicit false

                                                                             
section
                                                                                                                           
                                                                                                                            
                                                                                                                                       
                                                                                                                     
                                                                                                                            
                                                                                                                              
                                                                                                             

                                                                                                         
                                                                                     
                                                                                              
                                                                                             
                                                                                                         

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1087S2.K43.K42.K17.K16

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

end NlsGge.Atomic.G1087S2.K43.K42.K17.K16



/-! ### G1-017: high-frequency local uniform asymptotics -/

open NlsGge.Atomic.G1087S2.K43.K42.K17.K16

namespace NlsGge.Atomic.G1087S2.K43.K42.K17

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

end NlsGge.Atomic.G1087S2.K43.K42.K17

open NlsGge.Pilot

namespace NlsGge.Atomic.G1087S2.K43.K42.K17

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

end NlsGge.Atomic.G1087S2.K43.K42.K17

/-! ### The final statement -/

namespace NlsGge.Atomic.G1087S2.K43.K42.K17

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

end NlsGge.Atomic.G1087S2.K43.K42.K17

                                                                                
                                                                           
                                                                                                                  
                                                                                                                       
                                                  
                                                                                                                    
                                                                                                                      
                                                                                                                    
                                                                                                                               
                                                                                                      
                                                                               

namespace NlsGge.Atomic.G1087S2.K43.K42

open Filter Topology Set Metric NlsGge.GK38 NlsGge.Atomic.Volterra NlsGge.SpectralFoundations
open NlsGge.Atomic.G1004GenT NlsGge.Pilot

noncomputable section

open scoped Matrix.Norms.L2Operator in
/-- An entry of a `2 × 2` matrix is bounded by its `ℓ²`-operator norm. -/
theorem norm_entry_le_l2 (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : ‖A i j‖ ≤ ‖A‖ := by
  classical
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have e1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  have e2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin 2) ℂ).symm
    (Matrix.mulVec A ⇑(EuclideanSpace.single j (1 : ℂ)))) i
  have e3 : ((EuclideanSpace.equiv (Fin 2) ℂ).symm (Matrix.mulVec A ⇑(EuclideanSpace.single j (1 : ℂ)))) i =
      A i j := by
    simp [Matrix.mulVec_single_one]
  rw [e3] at e2
  rw [e1, mul_one] at h
  exact e2.trans h

/-- The M1 bridge: the unit-period Volterra series is the monodromy matrix. -/
theorem series_one_eq_monodromyPair (φ : PotPair) (z : ℂ) :
    ∑' n : ℕ, potentialVolterraTerm38 φ z n 1 = monodromyPair φ z := by
  have ht : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rw [tsum_terms_eq_fundContT φ z zero_le_one ht]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- Locally uniform asymptotics `χ_d = sin + o(e^{|Im z|})` from G1-017 (GK (5.2)). -/
theorem dirichlet_asymp_s3 (φ₀ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ R : ℝ, ∀ φ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖dirichletChar φ z - Complex.sin z‖ ≤ ε * Real.exp |z.im| := by
  obtain ⟨U, hU, Λ, h⟩ := NlsGge.Atomic.G1087S2.K43.K42.K17.G1017_whole φ₀ (ε / 2) (half_pos hε)
  refine ⟨U, hU, Λ + 1, fun φ hφ z hz => ?_⟩
  obtain ⟨-, h1, -⟩ := h φ hφ 1 zero_le_one le_rfl z (by linarith)
  have hE : freeZsFundamentalComplex z 1 = freeE z 1 := (freeE_eq z 1).symm
  rw [hE, series_one_eq_monodromyPair] at h1
  set D : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair φ z - freeE z 1 with hDdef
  have hn : ‖D‖ ≤ ε / 2 * Real.exp |z.im| := by
    have hpos := Real.exp_pos |z.im|
    have e : ‖D‖ = Real.exp |z.im| * (Real.exp (-|z.im| * 1) * ‖D‖) := by
      rw [← mul_assoc, mul_one, ← Real.exp_add]; simp
    rw [e]
    calc Real.exp |z.im| * (Real.exp (-|z.im| * 1) * ‖D‖) ≤ Real.exp |z.im| * (ε / 2) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = ε / 2 * Real.exp |z.im| := mul_comm _ _
  have hent : ∀ i j : Fin 2, ‖D i j‖ ≤ ε / 2 * Real.exp |z.im| :=
    fun i j => (norm_entry_le_l2 D i j).trans hn
  rw [dirichlet_residual_eq38]
  change ‖(D 1 0 + D 1 1 - D 0 0 - D 0 1) / (2 * Complex.I)‖ ≤ _
  rw [norm_div, norm_mul, Complex.norm_two, Complex.norm_I, mul_one]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have hh := norm_sub_le (D 1 0 + D 1 1 - D 0 0) (D 0 1)
  have hh' := norm_sub_le (D 1 0 + D 1 1) (D 0 0)
  have hh'' := norm_add_le (D 1 0) (D 1 1)
  have a1 := hent 1 0
  have a2 := hent 1 1
  have a3 := hent 0 0
  have a4 := hent 0 1
  nlinarith

/-- Local counting (GK Lemma 5.2) with the G1-017 asymptotics. -/
theorem dirichlet_counting_s3 (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ,
      ∀ φ : PotPair, φ ∈ U → RootCountingAt38 (dirichletChar φ) 1 N := by
  obtain ⟨U, hU, R, herr⟩ := dirichlet_asymp_s3 φ₀ (1 / (2 * sineOffDiscsConstant38))
    (one_div_pos.mpr (mul_pos (by norm_num) sineOffDiscsConstant38_pos))
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N : ℕ := K + 1
  have hNpos : 0 < N := Nat.succ_pos K
  have hRN : R ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  exact ⟨U, hU, N, fun φ hφ => dirichlet_counting_at38 φ N hNpos
    (fun z hz hsep => dirichlet_strict_comparison38 (herr φ hφ z (hRN.trans hz)) hsep)⟩

theorem mem_zm_iff (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ w, f w ≠ 0) {D : Set ℂ}
    (hD : Bornology.IsBounded D) {z : ℂ} :
    z ∈ Lib.zeroMultiset f D ↔ z ∈ D ∧ f z = 0 := by
  obtain ⟨r, hr⟩ := hD.subset_closedBall (0 : ℂ)
  obtain ⟨w, hw⟩ := hne
  have hDs : D ⊆ closedBall (0 : ℂ) (max r ‖w‖) :=
    hr.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hwb : w ∈ closedBall (0 : ℂ) (max r ‖w‖) := by
    simp [mem_closedBall, dist_zero_right]
  exact Lib.mem_zeroMultiset_iff_zero (hf.mono (subset_univ _)) hDs ⟨w, hwb, hw⟩

theorem natAbs_iff {N : ℕ} {n : ℤ} : N < n.natAbs ↔ (N : ℤ) < |n| := by
  rw [Int.abs_eq_natAbs]; exact_mod_cast Iff.rfl

theorem disc_clause (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ w, f w ≠ 0) (c : ℂ)
    (hcard : Multiset.card (Lib.zeroMultiset f (ball c (Real.pi / 4))) = 1) :
    ∃ z ∈ ball c (Real.pi / 4), f z = 0 ∧ analyticOrderAt f z = 1 ∧
      ∀ w ∈ ball c (Real.pi / 4), f w = 0 → w = z := by
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 hcard
  have hbd : Bornology.IsBounded (ball c (Real.pi / 4)) := isBounded_ball
  have hmem : ∀ w, w ∈ Lib.zeroMultiset f (ball c (Real.pi / 4)) ↔
      w ∈ ball c (Real.pi / 4) ∧ f w = 0 := fun w => mem_zm_iff f hf hne hbd
  have haM : a ∈ Lib.zeroMultiset f (ball c (Real.pi / 4)) := by rw [ha]; simp
  obtain ⟨haB, ha0⟩ := (hmem a).1 haM
  refine ⟨a, haB, ha0, ?_, fun w hw hw0 => ?_⟩
  · classical
    have hc := Lib.count_zeroMultiset_ball (c := c) (R := Real.pi / 4)
      (hf.mono (subset_univ _)) a
    rw [ha, Multiset.count_singleton_self, if_pos haB] at hc
    have hcn : analyticOrderNatAt f a = 1 := hc.symm
    unfold analyticOrderNatAt at hcn
    have hne' : analyticOrderAt f a ≠ ⊤ := fun h => by rw [h] at hcn; simp at hcn
    rw [← ENat.natCast_toNat hne', hcn]
    simp
  · have : w ∈ Lib.zeroMultiset f (ball c (Real.pi / 4)) := (hmem w).2 ⟨hw, hw0⟩
    rw [ha] at this
    simpa using this

theorem G1042_main :
    ((
  ∀ φ : PotPair,
  ∃ V : Set PotPair, IsOpen V ∧ φ ∈ V ∧ ∃ N : ℕ, 0 < N ∧ ∀ ψ ∈ V,
    (∀ n : ℤ, N < n.natAbs →
      (∃ z ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4),
          dirichletChar ψ z = 0 ∧ analyticOrderAt (fun w : ℂ => dirichletChar ψ w) z = 1 ∧
          ∀ w ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4),
            dirichletChar ψ w = 0 → w = z)) ∧
    Multiset.card (Lib.zeroMultiset (fun w : ℂ => dirichletChar ψ w)
      (Metric.ball (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 4))) = 2 * N + 1 ∧
    (∀ w : ℂ, dirichletChar ψ w = 0 →
      w ∈ Metric.ball (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 4) ∨
      ∃ n : ℤ, N < n.natAbs ∧ w ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4))
  : Prop)) := by
  intro φ
  obtain ⟨U, hU, N, h⟩ := dirichlet_counting_s3 φ
  refine ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, N, ?_, fun ψ hψ => ?_⟩
  · exact (h φ (mem_of_mem_nhds hU)).1
  obtain ⟨hN, hA, hne, -, hD, hB, hX⟩ := h ψ (interior_subset hψ)
  refine ⟨fun n hn => ?_, ?_, fun w hw => ?_⟩
  · have := hD n (natAbs_iff.1 hn)
    exact disc_clause (dirichletChar ψ) hA hne ((n : ℂ) * (Real.pi : ℂ)) this
  · have := hB
    rw [one_mul] at this
    exact this
  · rcases hX w hw with h1 | ⟨n, hn, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨n, natAbs_iff.2 hn, h2⟩

end

end NlsGge.Atomic.G1087S2.K43.K42

end

                                                                             
section
                                                                                                                   
                                                                                                                       
                                                                                                                                    
                                                                                                                          
                                                                                                            
                                                                                                   

set_option autoImplicit false

                                                                             
section
                                                                                                         
                                                                                     
                                                                                              
                                                                                             
                                                                                                         

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1087S2.K43.K19.K16

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

end NlsGge.Atomic.G1087S2.K43.K19.K16

end

open MeasureTheory Filter Topology Set
open NlsGge.GK38
/-! ### The first Volterra term -/

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1087S2.K43.K19.Aux

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
  refine NlsGge.Atomic.G1087S2.K43.K19.K16.odd_sparse_matrix_opNorm_le _ _ (le_max_of_le_left (norm_nonneg _))
    (fun i => ?_) (fun i => ?_)
  · fin_cases i
    · exact term1_entry00 a b z t
    · exact term1_entry11 a b z t
  · fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _


end

end NlsGge.Atomic.G1087S2.K43.K19.Aux

namespace NlsGge.Atomic.G1087S2.K43.K19.Aux

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

end NlsGge.Atomic.G1087S2.K43.K19.Aux

namespace NlsGge.Atomic.G1087S2.K43.K19.Aux

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

end NlsGge.Atomic.G1087S2.K43.K19.Aux

namespace NlsGge.Atomic.G1087S2.K43.K19

noncomputable section

open NlsGge.Atomic.G1087S2.K43.K19.Aux
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

end NlsGge.Atomic.G1087S2.K43.K19

end

namespace NlsGge.Atomic.G1087S2.K43

noncomputable section

open MeasureTheory Filter Topology Set
open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot
open scoped Matrix.Norms.L2Operator

theorem norm_sin_sub_ge (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) : ‖ζ‖ - ‖ζ‖ ^ 2 ≤ ‖Complex.sin ζ‖ := by
  have h1 := Complex.norm_exp_sub_one_sub_id_le (x := ζ * Complex.I) (by simpa using hζ)
  have h2 := Complex.norm_exp_sub_one_sub_id_le (x := -ζ * Complex.I) (by simpa using hζ)
  have key : (2 : ℂ) * (Complex.sin ζ - ζ) =
      ((Complex.exp (-ζ * Complex.I) - 1 - (-ζ * Complex.I)) -
        (Complex.exp (ζ * Complex.I) - 1 - ζ * Complex.I)) * Complex.I := by
    rw [mul_sub, Complex.two_sin]
    have : (-ζ * Complex.I) = -(ζ * Complex.I) := by ring
    rw [this]
    ring_nf
    simp [Complex.I_sq]
  have hn : ‖(2 : ℂ)‖ * ‖Complex.sin ζ - ζ‖ ≤ 2 * ‖ζ‖ ^ 2 := by
    rw [← norm_mul, key, norm_mul, Complex.norm_I, mul_one]
    calc _ ≤ ‖Complex.exp (-ζ * Complex.I) - 1 - (-ζ * Complex.I)‖ +
          ‖Complex.exp (ζ * Complex.I) - 1 - ζ * Complex.I‖ := norm_sub_le _ _
      _ ≤ _ := by
        simp only [norm_mul, norm_neg, Complex.norm_I, mul_one] at h1 h2 ⊢
        linarith
  simp at hn
  have h3 : ‖ζ‖ - ‖Complex.sin ζ‖ ≤ ‖Complex.sin ζ - ζ‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  linarith

theorem sin_ge_fifth (ζ : ℂ) (h : ‖ζ‖ < Real.pi / 4) : ‖ζ‖ / 5 ≤ ‖Complex.sin ζ‖ := by
  have hpi := Real.pi_lt_d2
  have h1 : ‖ζ‖ ≤ 1 := by linarith
  have h2 := norm_sin_sub_ge ζ h1
  have h0 := norm_nonneg ζ
  nlinarith

theorem norm_sin_sub_int (w : ℂ) (m : ℤ) : ‖Complex.sin (w - (m : ℂ) * Real.pi)‖ = ‖Complex.sin w‖ := by
  rw [Complex.sin_antiperiodic.sub_int_mul_eq m]
  rcases Int.units_eq_one_or m.negOnePow with h | h <;> simp [h]

/-- Displacement of a Dirichlet root from `nπ` in terms of the monodromy error. -/
theorem root_displacement (ψ : PotPair) {z : ℂ} {n : ℤ}
    (hz : z ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4))
    (h0 : dirichletChar ψ z = 0) :
    ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 ≤
      100 * ‖(∑' m : ℕ, potentialVolterraTerm38 ψ z m 1) - freeZsFundamentalComplex z 1‖ ^ 2 := by
  have hd : ‖z - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hsin := sin_ge_fifth (z - (n : ℂ) * (Real.pi : ℂ)) hd
  rw [norm_sin_sub_int] at hsin
  rw [K42.series_one_eq_monodromyPair, ← freeE_eq]
  set D : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair ψ z - freeE z 1 with hD
  have hres := dirichlet_residual_eq38 ψ z
  rw [h0, zero_sub] at hres
  have hsz : Complex.sin z = -((D 1 0 + D 1 1 - D 0 0 - D 0 1) / (2 * Complex.I)) := by
    rw [← hres]; ring
  have hent : ∀ i j : Fin 2, ‖D i j‖ ≤ ‖D‖ := fun i j => K42.norm_entry_le_l2 D i j
  have hb : ‖Complex.sin z‖ ≤ 2 * ‖D‖ := by
    rw [hsz, norm_neg, norm_div, norm_mul, Complex.norm_two, Complex.norm_I, mul_one]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hh := norm_sub_le (D 1 0 + D 1 1 - D 0 0) (D 0 1)
    have hh' := norm_sub_le (D 1 0 + D 1 1) (D 0 0)
    have hh'' := norm_add_le (D 1 0) (D 1 1)
    have a1 := hent 1 0
    have a2 := hent 1 1
    have a3 := hent 0 0
    have a4 := hent 0 1
    nlinarith
  have h1 : ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 10 * ‖D‖ := by linarith
  have h2 := norm_nonneg (z - (n : ℂ) * (Real.pi : ℂ))
  nlinarith [norm_nonneg D]

theorem G1043_whole : ((
  ∀ φ : PotPair,
  ∃ V : Set PotPair, IsOpen V ∧ φ ∈ V ∧ ∃ N : ℕ, ∃ C : ℝ, ∀ ψ ∈ V,
    ∃ μ : ℤ → ℂ,
      (∀ n : ℤ, N < n.natAbs →
        μ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) ∧ dirichletChar ψ (μ n) = 0 ∧
        ∀ w ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4),
          dirichletChar ψ w = 0 → w = μ n) ∧
      Summable (fun n : ℤ => if N < n.natAbs then ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 else 0) ≤ C
  : Prop)) := by
  intro φ
  obtain ⟨V0, hV0, hφ0, N, hNpos, hV⟩ := K42.G1042_main φ
  set R0 : ℝ := ‖φ.1‖ + ‖φ.2‖ + 2 with hR0def
  obtain ⟨C19, hC19⟩ := K19.G1019_whole R0 (Real.pi / 4)
  refine ⟨V0 ∩ Metric.ball φ 1, hV0.inter Metric.isOpen_ball,
    ⟨hφ0, Metric.mem_ball_self one_pos⟩, N, 100 * C19, ?_⟩
  intro ψ hψ
  obtain ⟨hψ0, hψb⟩ := hψ
  obtain ⟨hdisc, -, -⟩ := hV ψ hψ0
  classical
  let μ : ℤ → ℂ := fun n =>
    if h : N < n.natAbs then Classical.choose (hdisc n h) else (n : ℂ) * (Real.pi : ℂ)
  have hμ : ∀ n : ℤ, N < n.natAbs →
      μ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) ∧ dirichletChar ψ (μ n) = 0 ∧
        ∀ w ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4),
          dirichletChar ψ w = 0 → w = μ n := by
    intro n hn
    have hs := Classical.choose_spec (hdisc n hn)
    simp only [μ, dif_pos hn]
    exact ⟨hs.1, hs.2.1, hs.2.2.2⟩
  refine ⟨μ, fun n hn => hμ n hn, ?_⟩
  -- bound on the potential
  have hnorm : ‖ψ - φ‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hψb
  rw [Prod.norm_def, max_lt_iff] at hnorm
  have h1 : ‖ψ.1‖ ≤ ‖φ.1‖ + 1 := by
    have := norm_le_norm_add_norm_sub' ψ.1 φ.1
    have h2 : ‖(ψ - φ).1‖ < 1 := hnorm.1
    simp only [Prod.fst_sub] at h2
    linarith
  have h2 : ‖ψ.2‖ ≤ ‖φ.2‖ + 1 := by
    have := norm_le_norm_add_norm_sub' ψ.2 φ.2
    have h3 : ‖(ψ - φ).2‖ < 1 := hnorm.2
    simp only [Prod.snd_sub] at h3
    linarith
  have hR : Real.sqrt (‖ψ.1‖ ^ 2 + ‖ψ.2‖ ^ 2) ≤ R0 := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h0 := norm_nonneg ψ.1
    have h0' := norm_nonneg ψ.2
    nlinarith
  have hξ : ∀ n : ℤ, ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Real.pi / 4 := by
    intro n
    by_cases hn : N < n.natAbs
    · have h' : ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := by
        simpa [Metric.mem_ball, dist_eq_norm] using (hμ n hn).1
      exact h'.le
    · simp only [μ, dif_neg hn, sub_self, norm_zero]
      positivity
  obtain ⟨hs, hb⟩ := hC19 ψ μ hR hξ 1 zero_le_one le_rfl
  have hle : ∀ n : ℤ, (if N < n.natAbs then ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 else 0) ≤
      100 * ‖(∑' m : ℕ, potentialVolterraTerm38 ψ (μ n) m 1) - freeZsFundamentalComplex (μ n) 1‖ ^ 2 := by
    intro n
    by_cases hn : N < n.natAbs
    · rw [if_pos hn]
      exact root_displacement ψ (hμ n hn).1 (hμ n hn).2.1
    · rw [if_neg hn]
      positivity
  have hnn : ∀ n : ℤ, 0 ≤ (if N < n.natAbs then ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 else 0) := by
    intro n
    split_ifs <;> positivity
  have hsumm : Summable (fun n : ℤ => if N < n.natAbs then ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 else 0) :=
    Summable.of_nonneg_of_le hnn hle (hs.mul_left 100)
  refine ⟨hsumm, ?_⟩
  calc (∑' n : ℤ, if N < n.natAbs then ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 else 0)
      ≤ ∑' n : ℤ, 100 * ‖(∑' m : ℕ, potentialVolterraTerm38 ψ (μ n) m 1) -
          freeZsFundamentalComplex (μ n) 1‖ ^ 2 := hsumm.tsum_le_tsum hle (hs.mul_left 100)
    _ = 100 * ∑' n : ℤ, ‖(∑' m : ℕ, potentialVolterraTerm38 ψ (μ n) m 1) -
          freeZsFundamentalComplex (μ n) 1‖ ^ 2 := tsum_mul_left
    _ ≤ 100 * C19 := by gcongr

end

end NlsGge.Atomic.G1087S2.K43

                                                                                                    

                                                                                                                   
                                                                                                                        
                                                                                                                      
                                                                                                                                       
                                                                                                           

set_option autoImplicit false

                                                                             
section
                                                                                                                   
                                                                                                                       
                                                                                                                                    
                                                                                                                          
                                                                                                            
                                                                                                   

set_option autoImplicit false

                                                                             
section
                                                                                                         
                                                                                     
                                                                                              
                                                                                             
                                                                                                         

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1087S2.K29.K20.K19.K16

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

end NlsGge.Atomic.G1087S2.K29.K20.K19.K16

end

open MeasureTheory Filter Topology Set
open NlsGge.GK38
/-! ### The first Volterra term -/

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1087S2.K29.K20.K19.Aux

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
  refine NlsGge.Atomic.G1087S2.K29.K20.K19.K16.odd_sparse_matrix_opNorm_le _ _ (le_max_of_le_left (norm_nonneg _))
    (fun i => ?_) (fun i => ?_)
  · fin_cases i
    · exact term1_entry00 a b z t
    · exact term1_entry11 a b z t
  · fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _


end

end NlsGge.Atomic.G1087S2.K29.K20.K19.Aux

namespace NlsGge.Atomic.G1087S2.K29.K20.K19.Aux

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

end NlsGge.Atomic.G1087S2.K29.K20.K19.Aux

namespace NlsGge.Atomic.G1087S2.K29.K20.K19.Aux

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

end NlsGge.Atomic.G1087S2.K29.K20.K19.Aux

namespace NlsGge.Atomic.G1087S2.K29.K20.K19

noncomputable section

open NlsGge.Atomic.G1087S2.K29.K20.K19.Aux
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

end NlsGge.Atomic.G1087S2.K29.K20.K19

end

namespace NlsGge.Atomic.G1087S2.K29.K20

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
  have hcs := NlsGge.Atomic.G1087S2.K29.K20.K19.K16.cs_integral (t := 2 * Real.pi) hpi.le
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

end NlsGge.Atomic.G1087S2.K29.K20

                                                                                
                                                                           
                                                                                                                                        
                                                                                                                                              
                                                                                                                                         
                             
                                                                               

namespace NlsGge.Atomic.G1087S2.K29

open Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot

noncomputable section

open scoped Matrix.Norms.L2Operator in
/-- The trace as a continuous linear functional. -/
def trL : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
  { toLinearMap := Matrix.traceLinearMap (Fin 2) ℂ ℂ
    cont := LinearMap.continuous_of_finiteDimensional _ }

theorem trL_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : trL X = Matrix.trace X := rfl

open scoped Matrix.Norms.L2Operator in
/-- `X ↦ X 0 1 + X 1 0` as a continuous linear functional. -/
def offL : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
  { toLinearMap := Matrix.entryLinearMap ℂ ℂ 0 1 + Matrix.entryLinearMap ℂ ℂ 1 0
    cont := LinearMap.continuous_of_finiteDimensional _ }

theorem offL_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : offL X = X 0 1 + X 1 0 := rfl

theorem bridge (φ : PotPair) (z : ℂ) :
    (∑' m : ℕ, potentialVolterraTerm38 φ z m 1) = monodromyPair φ z :=
  NlsGge.Atomic.G1004GenT.tsum_terms_eq_fundContT φ z zero_le_one ⟨zero_le_one, le_rfl⟩

open scoped Matrix.Norms.L2Operator in
theorem entry_le_l2 (A : Matrix (Fin 2) (Fin 2) ℂ) (i k : Fin 2) : ‖A i k‖ ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single k (1:ℂ))
  have h1 : ‖(EuclideanSpace.single k (1:ℂ))‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le
    ((EuclideanSpace.equiv (Fin 2) ℂ).symm (A.mulVec (EuclideanSpace.single k (1:ℂ)))) i
  simpa [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply] using h2

open scoped Matrix.Norms.L2Operator in
theorem entry_facts (M E : Matrix (Fin 2) (Fin 2) ℂ) (h01 : E 0 1 = 0) (h10 : E 1 0 = 0)
    (e : ℝ) (h00 : ‖E 0 0‖ ≤ e) (h11 : ‖E 1 1‖ ≤ e) :
    ‖M 0 1‖ ≤ ‖M - E‖ ∧ ‖M 1 0‖ ≤ ‖M - E‖ ∧ ‖M 0 0‖ ≤ e + ‖M - E‖ ∧ ‖M 1 1‖ ≤ e + ‖M - E‖ := by
  have k : ∀ i j, ‖(M - E) i j‖ ≤ ‖M - E‖ := fun i j => entry_le_l2 _ i j
  have s : ∀ i j, M i j = E i j + (M - E) i j := fun i j => by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := k 0 1
    simpa [Matrix.sub_apply, h01] using this
  · have := k 1 0
    simpa [Matrix.sub_apply, h10] using this
  · calc ‖M 0 0‖ = ‖E 0 0 + (M - E) 0 0‖ := by rw [← s]
      _ ≤ ‖E 0 0‖ + ‖(M - E) 0 0‖ := norm_add_le _ _
      _ ≤ e + ‖M - E‖ := add_le_add h00 (k 0 0)
  · calc ‖M 1 1‖ = ‖E 1 1 + (M - E) 1 1‖ := by rw [← s]
      _ ≤ ‖E 1 1‖ + ‖(M - E) 1 1‖ := norm_add_le _ _
      _ ≤ e + ‖M - E‖ := add_le_add h11 (k 1 1)

theorem freeE_facts (z : ℂ) (R : ℝ) (hz : |z.im| ≤ R) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    freeZsFundamentalComplex z t 0 1 = 0 ∧ freeZsFundamentalComplex z t 1 0 = 0 ∧
    ‖freeZsFundamentalComplex z t 0 0‖ ≤ Real.exp R ∧ ‖freeZsFundamentalComplex z t 1 1‖ ≤ Real.exp R ∧
    freeZsFundamentalComplex z t 0 0 = Complex.exp (-(Complex.I * z * (t : ℂ))) ∧
    freeZsFundamentalComplex z t 1 1 = Complex.exp (Complex.I * z * (t : ℂ)) := by
  rw [freeZsFundamentalComplex_entries]
  have h1 : (-(Complex.I * z * (t : ℂ))).re = t * z.im := by
    simp [Complex.mul_re]; ring
  have h2 : (Complex.I * z * (t : ℂ)).re = -(t * z.im) := by
    simp [Complex.mul_re]; ring
  have hb : |t * z.im| ≤ R := by
    rw [abs_mul, abs_of_nonneg ht0]
    calc t * |z.im| ≤ 1 * |z.im| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ ≤ R := by linarith
  refine ⟨by simp, by simp, ?_, ?_, by simp, by simp⟩
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.norm_exp, h1]
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) hb)
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.norm_exp, h2]
    exact Real.exp_le_exp.2 (le_trans (neg_le_abs _) hb)

end

end NlsGge.Atomic.G1087S2.K29

namespace NlsGge.Atomic.G1087S2.K29

open Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot

noncomputable section

theorem n3 (x y z : ℂ) (a b c : ℝ) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) (hz : ‖z‖ ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖x * (y * z)‖ ≤ a * (b * c) := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul hx (mul_le_mul hy hz (norm_nonneg _) hb) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ha

theorem bGD (a b c d m1 m2 m3 m4 : ℂ) (B ε ee : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε) (he : 0 ≤ ee)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) (hm1 : ‖m1‖ ≤ B) (hm4 : ‖m4‖ ≤ B)
    (hbε : ‖b‖ ≤ ε) (hcε : ‖c‖ ≤ ε) (hm2 : ‖m2‖ ≤ ee) (hm3 : ‖m3‖ ≤ ee) :
    ‖m2 * (c * c) + (m4 - m1) * (c * d) - m3 * (d * d)‖ ≤ 2 * B ^ 2 * (ee + ε) ∧
    ‖m2 * (a * a) + (m4 - m1) * (a * b) - m3 * (b * b)‖ ≤ 2 * B ^ 2 * (ee + ε) := by
  have hdiff : ‖m4 - m1‖ ≤ 2 * B := by
    refine (norm_sub_le _ _).trans ?_; linarith
  constructor
  · have t1 := n3 m2 c c ee B B hm2 hc hc he hB
    have t2 := n3 (m4 - m1) c d (2 * B) ε B hdiff hcε hd (by linarith) hε
    have t3 := n3 m3 d d ee B B hm3 hd hd he hB
    calc ‖m2 * (c * c) + (m4 - m1) * (c * d) - m3 * (d * d)‖
        ≤ ‖m2 * (c * c)‖ + ‖(m4 - m1) * (c * d)‖ + ‖m3 * (d * d)‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ee * (B * B) + 2 * B * (ε * B) + ee * (B * B) := by gcongr
      _ = 2 * B ^ 2 * (ee + ε) := by ring
  · have t1 := n3 m2 a a ee B B hm2 ha ha he hB
    have t2 := n3 (m4 - m1) a b (2 * B) B ε hdiff ha hbε (by linarith) hB
    have t3 := n3 m3 b b ee B B hm3 hb hb he hB
    calc ‖m2 * (a * a) + (m4 - m1) * (a * b) - m3 * (b * b)‖
        ≤ ‖m2 * (a * a)‖ + ‖(m4 - m1) * (a * b)‖ + ‖m3 * (b * b)‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ee * (B * B) + 2 * B * (B * ε) + ee * (B * B) := by gcongr
      _ = 2 * B ^ 2 * (ee + ε) := by ring


theorem bLead0 (c d m1 m2 m3 m4 e1 e2 : ℂ) (B ε ee E : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε) (he : 0 ≤ ee) (hE : 0 ≤ E)
    (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) (hm4 : ‖m4‖ ≤ B) (hcε : ‖c‖ ≤ ε) (hm2 : ‖m2‖ ≤ ee) (hm3 : ‖m3‖ ≤ ee)
    (h1 : ‖m1 - e1‖ ≤ ee) (h2 : ‖d - e2‖ ≤ ε) (he1 : ‖e1‖ ≤ E) (he2 : ‖e2‖ ≤ E) :
    ‖(m4 * (c * c) + (m2 - m3) * (c * d) - m1 * (d * d)) - (-(e1 * (e2 * e2)))‖ ≤
      (3 * B ^ 2 + E * (B + E)) * (ee + ε) := by
  have hdiff : ‖m2 - m3‖ ≤ 2 * ee := by refine (norm_sub_le _ _).trans ?_; linarith
  have t1 := n3 m4 c c B ε B hm4 hcε hc hB hε
  have t2 := n3 (m2 - m3) c d (2 * ee) B B hdiff hc hd (by linarith) hB
  have t3 := n3 (m1 - e1) d d ee B B h1 hd hd he hB
  have hdd : ‖e2 + d‖ ≤ E + B := (norm_add_le _ _).trans (by linarith)
  have t4 : ‖e1 * ((d - e2) * (d + e2))‖ ≤ E * (ε * (B + E)) := by
    refine n3 e1 (d - e2) (d + e2) E ε (B + E) he1 h2 ?_ hE hε
    refine (norm_add_le _ _).trans ?_; linarith
  have hid : (m4 * (c * c) + (m2 - m3) * (c * d) - m1 * (d * d)) - (-(e1 * (e2 * e2))) =
      m4 * (c * c) + (m2 - m3) * (c * d) - (m1 - e1) * (d * d) - e1 * ((d - e2) * (d + e2)) := by ring
  rw [hid]
  calc ‖m4 * (c * c) + (m2 - m3) * (c * d) - (m1 - e1) * (d * d) - e1 * ((d - e2) * (d + e2))‖
      ≤ ‖m4 * (c * c)‖ + ‖(m2 - m3) * (c * d)‖ + ‖(m1 - e1) * (d * d)‖ + ‖e1 * ((d - e2) * (d + e2))‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ B * (ε * B) + 2 * ee * (B * B) + ee * (B * B) + E * (ε * (B + E)) := by gcongr
    _ ≤ (3 * B ^ 2 + E * (B + E)) * (ee + ε) := by nlinarith [mul_nonneg hB hB, mul_nonneg hE hB, mul_nonneg hE hE, mul_nonneg (mul_nonneg hB hB) hε, mul_nonneg (mul_nonneg hB hB) he, mul_nonneg hE (mul_nonneg hε hB), mul_nonneg hE (mul_nonneg hε hE), mul_nonneg hE (mul_nonneg he hB), mul_nonneg hE (mul_nonneg he hE)]

theorem bLead1 (a b m1 m2 m3 m4 e3 e4 : ℂ) (B ε ee E : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε) (he : 0 ≤ ee) (hE : 0 ≤ E)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hm1 : ‖m1‖ ≤ B) (hbε : ‖b‖ ≤ ε) (hm2 : ‖m2‖ ≤ ee) (hm3 : ‖m3‖ ≤ ee)
    (h4 : ‖m4 - e4‖ ≤ ee) (h3 : ‖a - e3‖ ≤ ε) (he3 : ‖e3‖ ≤ E) (he4 : ‖e4‖ ≤ E) :
    ‖(m4 * (a * a) + (m2 - m3) * (a * b) - m1 * (b * b)) - (e4 * (e3 * e3))‖ ≤
      (3 * B ^ 2 + E * (B + E)) * (ee + ε) := by
  have hdiff : ‖m2 - m3‖ ≤ 2 * ee := by refine (norm_sub_le _ _).trans ?_; linarith
  have t1 := n3 (m4 - e4) a a ee B B h4 ha ha he hB
  have t2 := n3 (m2 - m3) a b (2 * ee) B B hdiff ha hb (by linarith) hB
  have t3 := n3 m1 b b B ε B hm1 hbε hb hB hε
  have t4 : ‖e4 * ((a - e3) * (a + e3))‖ ≤ E * (ε * (B + E)) := by
    refine n3 e4 (a - e3) (a + e3) E ε (B + E) he4 h3 ?_ hE hε
    refine (norm_add_le _ _).trans ?_; linarith
  have hid : (m4 * (a * a) + (m2 - m3) * (a * b) - m1 * (b * b)) - (e4 * (e3 * e3)) =
      (m4 - e4) * (a * a) + (m2 - m3) * (a * b) - m1 * (b * b) + e4 * ((a - e3) * (a + e3)) := by ring
  rw [hid]
  calc ‖(m4 - e4) * (a * a) + (m2 - m3) * (a * b) - m1 * (b * b) + e4 * ((a - e3) * (a + e3))‖
      ≤ ‖(m4 - e4) * (a * a)‖ + ‖(m2 - m3) * (a * b)‖ + ‖m1 * (b * b)‖ + ‖e4 * ((a - e3) * (a + e3))‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ ee * (B * B) + 2 * ee * (B * B) + B * (ε * B) + E * (ε * (B + E)) := by gcongr
    _ ≤ (3 * B ^ 2 + E * (B + E)) * (ee + ε) := by nlinarith [mul_nonneg hB hB, mul_nonneg hE hB, mul_nonneg hE hE, mul_nonneg (mul_nonneg hB hB) hε, mul_nonneg (mul_nonneg hB hB) he, mul_nonneg hE (mul_nonneg hε hB), mul_nonneg hE (mul_nonneg hε hE), mul_nonneg hE (mul_nonneg he hB), mul_nonneg hE (mul_nonneg he hE)]

end

end NlsGge.Atomic.G1087S2.K29


namespace NlsGge.Atomic.G1087S2.K29

open Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot

noncomputable section

theorem sumsq_dom (x : ℤ → ℂ) (K : ℝ) (u v : ℤ → ℝ) (C1 C2 : ℝ) (hK : 0 ≤ K)
    (hu : Summable (fun n => u n ^ 2)) (hv : Summable (fun n => v n ^ 2))
    (hu1 : ∑' n, u n ^ 2 ≤ C1) (hv1 : ∑' n, v n ^ 2 ≤ C2)
    (hu0 : ∀ n, 0 ≤ u n) (hv0 : ∀ n, 0 ≤ v n)
    (hx : ∀ n, ‖x n‖ ≤ K * (u n + v n)) :
    Summable (fun n => ‖x n‖ ^ 2) ∧ ∑' n, ‖x n‖ ^ 2 ≤ 2 * K ^ 2 * (C1 + C2) := by
  have hpt : ∀ n, ‖x n‖ ^ 2 ≤ 2 * K ^ 2 * (u n ^ 2 + v n ^ 2) := by
    intro n
    have h0 : 0 ≤ ‖x n‖ := norm_nonneg _
    have h1 : ‖x n‖ ^ 2 ≤ (K * (u n + v n)) ^ 2 := pow_le_pow_left₀ h0 (hx n) 2
    nlinarith [sq_nonneg (u n - v n), sq_nonneg K, mul_nonneg (sq_nonneg K) (sq_nonneg (u n - v n))]
  have hs : Summable (fun n => 2 * K ^ 2 * (u n ^ 2 + v n ^ 2)) := (hu.add hv).mul_left _
  refine ⟨Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpt hs, ?_⟩
  calc ∑' n, ‖x n‖ ^ 2 ≤ ∑' n, 2 * K ^ 2 * (u n ^ 2 + v n ^ 2) :=
        (Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpt hs).tsum_le_tsum hpt hs
    _ = 2 * K ^ 2 * (∑' n, u n ^ 2 + ∑' n, v n ^ 2) := by
        rw [tsum_mul_left, hu.tsum_add hv]
    _ ≤ 2 * K ^ 2 * (C1 + C2) := by gcongr


theorem sumsq_dom' (x : ℤ → ℂ) (K : ℝ) (u v : ℤ → ℝ) (C1 C2 C : ℝ) (hK : 0 ≤ K)
    (hu : Summable (fun n => u n ^ 2)) (hv : Summable (fun n => v n ^ 2))
    (hu1 : ∑' n, u n ^ 2 ≤ C1) (hv1 : ∑' n, v n ^ 2 ≤ C2)
    (hu0 : ∀ n, 0 ≤ u n) (hv0 : ∀ n, 0 ≤ v n) (hC : 2 * K ^ 2 * (C1 + C2) ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ K * (u n + v n)) :
    Summable (fun n => ‖x n‖ ^ 2) ∧ ∑' n, ‖x n‖ ^ 2 ≤ C := by
  obtain ⟨h1, h2⟩ := sumsq_dom x K u v C1 C2 hK hu hv hu1 hv1 hu0 hv0 hx
  exact ⟨h1, h2.trans hC⟩

open scoped Matrix.Norms.L2Operator in
theorem fact_n (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) (R t C ε : ℝ) (hz : |z.im| ≤ R) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hε : ε = ‖M - freeZsFundamentalComplex z t‖) (hC : ε ^ 2 ≤ C) :
    ‖M 0 1‖ ≤ ε ∧ ‖M 1 0‖ ≤ ε ∧ ‖M 0 0‖ ≤ Real.exp R + 1 + C ∧ ‖M 1 1‖ ≤ Real.exp R + 1 + C ∧
    ‖M 0 1‖ ≤ Real.exp R + 1 + C ∧ ‖M 1 0‖ ≤ Real.exp R + 1 + C ∧
    ‖M 0 0 - Complex.exp (-(Complex.I * z * (t : ℂ)))‖ ≤ ε ∧
    ‖M 1 1 - Complex.exp (Complex.I * z * (t : ℂ))‖ ≤ ε ∧
    ‖Complex.exp (-(Complex.I * z * (t : ℂ)))‖ ≤ Real.exp R ∧ ‖Complex.exp (Complex.I * z * (t : ℂ))‖ ≤ Real.exp R := by
  obtain ⟨f01, f10, f00, f11, e00, e11⟩ := freeE_facts z R hz t ht0 ht1
  obtain ⟨a1, a2, a3, a4⟩ := entry_facts M _ f01 f10 (Real.exp R) f00 f11
  rw [← hε] at a1 a2 a3 a4
  have hε1 : ε ≤ 1 + C := by nlinarith [sq_nonneg (ε - 1), norm_nonneg (M - freeZsFundamentalComplex z t), hε ▸ norm_nonneg (M - freeZsFundamentalComplex z t)]
  have hE0 : 0 ≤ Real.exp R := (Real.exp_pos _).le
  have k : ∀ i j, ‖(M - freeZsFundamentalComplex z t) i j‖ ≤ ε := fun i j => hε ▸ entry_le_l2 _ i j
  refine ⟨a1, a2, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · have := k 0 0
    simpa [Matrix.sub_apply, e00] using this
  · have := k 1 1
    simpa [Matrix.sub_apply, e11] using this
  · rw [← e00]; exact f00
  · rw [← e11]; exact f11

open scoped Matrix.Norms.L2Operator in
theorem G1029_main :
((
  ∀ R0 R1 : ℝ, ∃ C : ℝ, ∀ (φ : PotPair) (ξ : ℤ → ℂ),
    Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ R0 →
    (∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) →
    let Dl : ℂ → ℂ := fun w => Matrix.trace (monodromyPair φ w)
    let dl : ℂ → ℂ := fun w => monodromyPair φ w 0 1 + monodromyPair φ w 1 0
    (∀ n : ℤ, DifferentiableAt ℂ Dl (ξ n) ∧ DifferentiableAt ℂ dl (ξ n)) ∧
    (Summable (fun n : ℤ => ‖deriv Dl (ξ n) - (-2 * Complex.sin (ξ n))‖ ^ 2) ∧
      (∑' n : ℤ, ‖deriv Dl (ξ n) - (-2 * Complex.sin (ξ n))‖ ^ 2) ≤ C) ∧
    (Summable (fun n : ℤ => ‖deriv dl (ξ n)‖ ^ 2) ∧
      (∑' n : ℤ, ‖deriv dl (ξ n)‖ ^ 2) ≤ C) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k : Fin 2,
      let Mf : ℤ → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun n u => ∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m u
      let Ml : ℤ → Matrix (Fin 2) (Fin 2) ℂ := fun n => monodromyPair φ (ξ n)
      let mc1 : ℤ → Fin 2 → ℂ := fun n => ![Mf n t 0 0, Mf n t 1 0]
      let mc2 : ℤ → Fin 2 → ℂ := fun n => ![Mf n t 0 1, Mf n t 1 1]
      let star : (Fin 2 → ℂ) → (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun g k => ![g 1 * k 1, g 0 * k 0]
      let GD : ℤ → ℂ := fun n =>
        Ml n 0 1 * star (mc1 n) (mc1 n) k + (Ml n 1 1 - Ml n 0 0) * star (mc1 n) (mc2 n) k
          - Ml n 1 0 * star (mc2 n) (mc2 n) k
      let Gd : ℤ → ℂ := fun n =>
        Ml n 1 1 * star (mc1 n) (mc1 n) k + (Ml n 0 1 - Ml n 1 0) * star (mc1 n) (mc2 n) k
          - Ml n 0 0 * star (mc2 n) (mc2 n) k
      let lead : ℤ → ℂ := fun n =>
        (![-Complex.exp (-(Complex.I * ξ n * (1 - 2 * (t : ℂ)))),
           Complex.exp (Complex.I * ξ n * (1 - 2 * (t : ℂ)))] : Fin 2 → ℂ) k
      (Summable (fun n : ℤ => ‖GD n‖ ^ 2) ∧ (∑' n : ℤ, ‖GD n‖ ^ 2) ≤ C) ∧
      (Summable (fun n : ℤ => ‖Gd n - lead n‖ ^ 2) ∧ (∑' n : ℤ, ‖Gd n - lead n‖ ^ 2) ≤ C))
  : Prop)) := by
  intro R0 R1
  obtain ⟨C19, h19⟩ := NlsGge.Atomic.G1087S2.K29.K20.K19.G1019_whole R0 R1
  obtain ⟨C20, h20⟩ := NlsGge.Atomic.G1087S2.K29.K20.G1020_whole R0 R1
  set R1' : ℝ := max R1 0 with hR1'
  set E : ℝ := Real.exp R1' with hE
  set C19' : ℝ := max C19 0 with hC19'
  set C20' : ℝ := max C20 0 with hC20'
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hC19'0 : 0 ≤ C19' := le_max_right _ _
  have hC20'0 : 0 ≤ C20' := le_max_right _ _
  have hC19le : C19 ≤ C19' := le_max_left _ _
  have hC20le : C20 ≤ C20' := le_max_left _ _
  set B : ℝ := E + 1 + C19' with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; linarith
  set K1 : ℝ := 2 * B ^ 2 with hK1
  set K2 : ℝ := 3 * B ^ 2 + E * (B + E) with hK2
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  have hK20 : 0 ≤ K2 := by rw [hK2]; positivity
  set TD : ℝ := 2 * 2 ^ 2 * (C20' + 0) with hTD
  set TG : ℝ := 2 * K1 ^ 2 * (C19' + C19') with hTG
  set TL : ℝ := 2 * K2 ^ 2 * (C19' + C19') with hTL
  have hTD0 : 0 ≤ TD := by rw [hTD]; positivity
  have hTG0 : 0 ≤ TG := by rw [hTG]; positivity
  have hTL0 : 0 ≤ TL := by rw [hTL]; positivity
  refine ⟨TD + TD + TG + TL, ?_⟩
  intro φ ξ hφ hξ Dl dl
  have hξim : ∀ n : ℤ, |(ξ n).im| ≤ R1' := by
    intro n
    have h1 : (ξ n - (n : ℂ) * (Real.pi : ℂ)).im = (ξ n).im := by simp
    have h2 := Complex.abs_im_le_norm (ξ n - (n : ℂ) * (Real.pi : ℂ))
    rw [h1] at h2
    exact h2.trans ((hξ n).trans (le_max_left _ _))
  obtain ⟨hDiff, hS20, hT20⟩ := h20 φ ξ hφ hξ 1 zero_le_one le_rfl
  have hone := h19 φ ξ hφ hξ 1 zero_le_one le_rfl
  -- the maps and their derivatives
  let M1 : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun w => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1
  let Ed : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun w => freeZsFundamentalComplex w 1
  let A : ℤ → Matrix (Fin 2) (Fin 2) ℂ := fun n => deriv M1 (ξ n) - deriv Ed (ξ n)
  have hDiff' : ∀ n : ℤ, DifferentiableAt ℂ M1 (ξ n) := hDiff
  have hEd : ∀ n : ℤ, HasDerivAt Ed (deriv Ed (ξ n)) (ξ n) := fun n =>
    (NlsGge.Atomic.G1087S2.K29.K20.differentiable_E 1 (ξ n)).hasDerivAt
  have hAs : Summable (fun n : ℤ => ‖A n‖ ^ 2) := hS20
  have hAt : ∑' n : ℤ, ‖A n‖ ^ 2 ≤ C20 := hT20
  have e1 : (fun w : ℂ => Matrix.trace (monodromyPair φ w)) = fun w => trL (M1 w) :=
    funext fun w => by
      show _ = trL (∑' m : ℕ, potentialVolterraTerm38 φ w m 1)
      rw [bridge, trL_apply]
  have e2 : (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) = fun w => offL (M1 w) :=
    funext fun w => by
      show _ = offL (∑' m : ℕ, potentialVolterraTerm38 φ w m 1)
      rw [bridge, offL_apply]
  have hdT : ∀ n : ℤ, deriv (fun w : ℂ => Matrix.trace (monodromyPair φ w)) (ξ n) =
      trL (deriv M1 (ξ n)) := fun n => by
    rw [e1]
    exact (trL.hasFDerivAt.comp_hasDerivAt (ξ n) (hDiff' n).hasDerivAt).deriv
  have hdO : ∀ n : ℤ, deriv (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) (ξ n) =
      offL (deriv M1 (ξ n)) := fun n => by
    rw [e2]
    exact (offL.hasFDerivAt.comp_hasDerivAt (ξ n) (hDiff' n).hasDerivAt).deriv
  have hTE : ∀ n : ℤ, trL (deriv Ed (ξ n)) = -2 * Complex.sin (ξ n) := by
    intro n
    have hT := trL.hasFDerivAt.comp_hasDerivAt (ξ n) (hEd n)
    have hf : (⇑trL ∘ Ed) = fun w : ℂ => 2 * Complex.cos w := by
      funext w
      show trL (freeZsFundamentalComplex w 1) = 2 * Complex.cos w
      rw [trL_apply, Matrix.trace_fin_two, freeZsFundamentalComplex_entries, Complex.two_cos]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_one, mul_one]
      rw [add_comm]; congr 2 <;> ring
    rw [hf] at hT
    have hC : HasDerivAt (fun w : ℂ => 2 * Complex.cos w) (-2 * Complex.sin (ξ n)) (ξ n) := by
      have := (Complex.hasDerivAt_cos (ξ n)).const_mul 2
      convert this using 1; ring
    exact hT.unique hC
  have hOE : ∀ n : ℤ, offL (deriv Ed (ξ n)) = 0 := by
    intro n
    have hT := offL.hasFDerivAt.comp_hasDerivAt (ξ n) (hEd n)
    have hf : (⇑offL ∘ Ed) = fun _ : ℂ => (0 : ℂ) := by
      funext w
      show offL (freeZsFundamentalComplex w 1) = 0
      rw [offL_apply, freeZsFundamentalComplex_entries]
      simp
    rw [hf] at hT
    exact hT.unique (hasDerivAt_const _ _)
  have hnT : ∀ n : ℤ, ‖trL (A n)‖ ≤ 2 * ‖A n‖ := by
    intro n
    rw [trL_apply, Matrix.trace_fin_two]
    have := entry_le_l2 (A n) 0 0
    have := entry_le_l2 (A n) 1 1
    calc ‖A n 0 0 + A n 1 1‖ ≤ ‖A n 0 0‖ + ‖A n 1 1‖ := norm_add_le _ _
      _ ≤ 2 * ‖A n‖ := by linarith
  have hnO : ∀ n : ℤ, ‖offL (A n)‖ ≤ 2 * ‖A n‖ := by
    intro n
    rw [offL_apply]
    have := entry_le_l2 (A n) 0 1
    have := entry_le_l2 (A n) 1 0
    calc ‖A n 0 1 + A n 1 0‖ ≤ ‖A n 0 1‖ + ‖A n 1 0‖ := norm_add_le _ _
      _ ≤ 2 * ‖A n‖ := by linarith
  have hzs : Summable (fun _ : ℤ => ((0 : ℝ)) ^ 2) := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_⟩
    · show DifferentiableAt ℂ (fun w : ℂ => Matrix.trace (monodromyPair φ w)) (ξ n)
      rw [e1]; exact trL.differentiableAt.comp (ξ n) (hDiff' n)
    · show DifferentiableAt ℂ (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) (ξ n)
      rw [e2]; exact offL.differentiableAt.comp (ξ n) (hDiff' n)
  · have hx : ∀ n : ℤ, deriv (fun w : ℂ => Matrix.trace (monodromyPair φ w)) (ξ n) - (-2 * Complex.sin (ξ n)) =
        trL (A n) := fun n => by
      rw [hdT, ← hTE n, ← map_sub]
    have key := sumsq_dom (fun n => trL (A n)) 2 (fun n => ‖A n‖) (fun _ => 0) C20 0 (by norm_num) hAs hzs hAt
      (by simp) (fun n => norm_nonneg _) (fun _ => le_rfl) (fun n => by simpa using hnT n)
    show Summable (fun n : ℤ => ‖deriv (fun w : ℂ => Matrix.trace (monodromyPair φ w)) (ξ n) -
      (-2 * Complex.sin (ξ n))‖ ^ 2) ∧ (∑' n : ℤ, ‖deriv (fun w : ℂ => Matrix.trace (monodromyPair φ w)) (ξ n) -
      (-2 * Complex.sin (ξ n))‖ ^ 2) ≤ TD + TD + TG + TL
    simp only [hx]
    refine ⟨key.1, key.2.trans ?_⟩
    have : 2 * 2 ^ 2 * (C20 + 0) ≤ TD := by rw [hTD]; nlinarith
    linarith
  · have hx : ∀ n : ℤ, deriv (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) (ξ n) =
        offL (A n) := fun n => by
      rw [hdO, show A n = deriv M1 (ξ n) - deriv Ed (ξ n) from rfl, map_sub, hOE, sub_zero]
    have key := sumsq_dom (fun n => offL (A n)) 2 (fun n => ‖A n‖) (fun _ => 0) C20 0 (by norm_num) hAs hzs hAt
      (by simp) (fun n => norm_nonneg _) (fun _ => le_rfl) (fun n => by simpa using hnO n)
    show Summable (fun n : ℤ => ‖deriv (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) (ξ n)‖ ^ 2) ∧
      (∑' n : ℤ, ‖deriv (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) (ξ n)‖ ^ 2) ≤ TD + TD + TG + TL
    simp only [hx]
    refine ⟨key.1, key.2.trans ?_⟩
    have : 2 * 2 ^ 2 * (C20 + 0) ≤ TD := by rw [hTD]; nlinarith
    linarith
  · intro t ht0 ht1 k
    obtain ⟨ε, hεd, hεs, hεsum⟩ : ∃ ε : ℤ → ℝ,
        (∀ n, ε n = ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖) ∧
        Summable (fun n => ε n ^ 2) ∧ ∑' n, ε n ^ 2 ≤ C19 := by
      obtain ⟨hs, hb⟩ := h19 φ ξ hφ hξ t ht0 ht1
      exact ⟨_, fun _ => rfl, hs, hb⟩
    obtain ⟨ee, hed, hes, heesum⟩ : ∃ ee : ℤ → ℝ,
        (∀ n, ee n = ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m 1) - freeZsFundamentalComplex (ξ n) 1‖) ∧
        Summable (fun n => ee n ^ 2) ∧ ∑' n, ee n ^ 2 ≤ C19 :=
      ⟨_, fun _ => rfl, hone.1, hone.2⟩
    have hε0 : ∀ n, 0 ≤ ε n := fun n => by rw [hεd n]; exact norm_nonneg _
    have hee0 : ∀ n, 0 ≤ ee n := fun n => by rw [hed n]; exact norm_nonneg _
    have hε2 : ∀ n, ε n ^ 2 ≤ C19' := fun n =>
      (hεs.le_tsum n (fun j _ => sq_nonneg _)).trans (hεsum.trans hC19le)
    have hee2 : ∀ n, ee n ^ 2 ≤ C19' := fun n =>
      (hes.le_tsum n (fun j _ => sq_nonneg _)).trans (heesum.trans hC19le)
    have Ft := fun n : ℤ => fact_n (∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) (ξ n) R1' t C19' (ε n)
      (hξim n) ht0 ht1 (hεd n) (hε2 n)
    have F1 := fun n : ℤ => fact_n (∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m 1) (ξ n) R1' 1 C19' (ee n)
      (hξim n) zero_le_one le_rfl (hed n) (hee2 n)
    have hle0 : ∀ n : ℤ, Complex.exp (-(Complex.I * ξ n * (((1 : ℝ)) : ℂ))) *
        (Complex.exp (Complex.I * ξ n * (t : ℂ)) * Complex.exp (Complex.I * ξ n * (t : ℂ))) =
        Complex.exp (-(Complex.I * ξ n * (1 - 2 * (t : ℂ)))) := fun n => by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    have hle1 : ∀ n : ℤ, Complex.exp (Complex.I * ξ n * (((1 : ℝ)) : ℂ)) *
        (Complex.exp (-(Complex.I * ξ n * (t : ℂ))) * Complex.exp (-(Complex.I * ξ n * (t : ℂ)))) =
        Complex.exp (Complex.I * ξ n * (1 - 2 * (t : ℂ))) := fun n => by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    have hsT : ∀ n : ℤ, TG ≤ TD + TD + TG + TL := fun n => by linarith
    fin_cases k
    · intro Mf' Ml mc1 mc2 star GD Gd lead
      simp only [GD, Gd, lead, star, mc1, mc2, Ml, Mf', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Fin.zero_eta]
      refine ⟨sumsq_dom' _ K1 ee ε C19 C19 _ hK10 hes hεs heesum hεsum hee0 hε0 ?_ (fun n => ?_),
        sumsq_dom' _ K2 ee ε C19 C19 _ hK20 hes hεs heesum hεsum hee0 hε0 ?_ (fun n => ?_)⟩
      · have h1 := mul_le_mul_of_nonneg_left (add_le_add hC19le hC19le) (by positivity : (0 : ℝ) ≤ 2 * K1 ^ 2)
        have : 2 * K1 ^ 2 * (C19' + C19') = TG := by rw [hTG]
        linarith
      · obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := Ft n
        have F1n := F1 n
        simp only [bridge] at F1n
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := F1n
        have := (bGD _ _ _ _ _ _ _ _ B (ε n) (ee n) hB0 (hε0 n) (hee0 n) t3 t5 t6 t4 f3 f4 t1 t2 f1 f2).1
        exact this
      · have h1 := mul_le_mul_of_nonneg_left (add_le_add hC19le hC19le) (by positivity : (0 : ℝ) ≤ 2 * K2 ^ 2)
        have : 2 * K2 ^ 2 * (C19' + C19') = TL := by rw [hTL]
        linarith
      · obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := Ft n
        have F1n := F1 n
        simp only [bridge] at F1n
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := F1n
        have := bLead0 _ _ _ _ _ _ _ _ B (ε n) (ee n) E hB0 (hε0 n) (hee0 n) hE0 t6 t4 f4 t2 f1 f2 f7 t8 f9 t10
        rw [hle0 n] at this
        exact this
    · intro Mf' Ml mc1 mc2 star GD Gd lead
      simp only [GD, Gd, lead, star, mc1, mc2, Ml, Mf', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Fin.mk_one]
      refine ⟨sumsq_dom' _ K1 ee ε C19 C19 _ hK10 hes hεs heesum hεsum hee0 hε0 ?_ (fun n => ?_),
        sumsq_dom' _ K2 ee ε C19 C19 _ hK20 hes hεs heesum hεsum hee0 hε0 ?_ (fun n => ?_)⟩
      · have h1 := mul_le_mul_of_nonneg_left (add_le_add hC19le hC19le) (by positivity : (0 : ℝ) ≤ 2 * K1 ^ 2)
        have : 2 * K1 ^ 2 * (C19' + C19') = TG := by rw [hTG]
        linarith
      · obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := Ft n
        have F1n := F1 n
        simp only [bridge] at F1n
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := F1n
        have := (bGD _ _ _ _ _ _ _ _ B (ε n) (ee n) hB0 (hε0 n) (hee0 n) t3 t5 t6 t4 f3 f4 t1 t2 f1 f2).2
        exact this
      · have h1 := mul_le_mul_of_nonneg_left (add_le_add hC19le hC19le) (by positivity : (0 : ℝ) ≤ 2 * K2 ^ 2)
        have : 2 * K2 ^ 2 * (C19' + C19') = TL := by rw [hTL]
        linarith
      · obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := Ft n
        have F1n := F1 n
        simp only [bridge] at F1n
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := F1n
        have := bLead1 _ _ _ _ _ _ _ _ B (ε n) (ee n) E hB0 (hε0 n) (hee0 n) hE0 t3 t5 f3 t1 f1 f2 f8 t7 t9 f10
        rw [hle1 n] at this
        exact this

end

end NlsGge.Atomic.G1087S2.K29


set_option autoImplicit false


namespace NlsGge.Atomic.G1087S2.P1

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38

/-- bridge: the Volterra series at time `t` is the production fundamental matrix. -/
theorem series_eq_fundPair (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    (∑' m : ℕ, potentialVolterraTerm38 φ z m t) i j = fundPair φ z ⟨t, ht⟩ i j := by
  have h := NlsGge.Atomic.G1004GenT.tsum_terms_eq_fundContT φ z zero_le_one ht
  rw [h]
  rfl

theorem fundColumn_eq (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    fundColumn38 φ z t j i = fundPair φ z ⟨t, ht⟩ i j := by
  unfold fundColumn38
  rw [ext38_of_mem _ ht]
  rfl

theorem state_apply (φ : PotPair) (z : ℂ) (a : PairVec38) (t : Set.Icc (0 : ℝ) 1) :
    state φ z a t = a 0 • fundColumn38 φ z t 0 + a 1 • fundColumn38 φ z t 1 := rfl

theorem mixedSquare_apply (v w : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1) :
    mixedSquare v w t = starProd38 (v t) (w t) := rfl

theorem norming_comp (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : Fin 2) :
    let Mf : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun u => ∑' m : ℕ, potentialVolterraTerm38 φ z m u
    let Ml : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair φ z
    let mc1 : Fin 2 → ℂ := ![Mf t 0 0, Mf t 1 0]
    let mc2 : Fin 2 → ℂ := ![Mf t 0 1, Mf t 1 1]
    let star : (Fin 2 → ℂ) → (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun g k => ![g 1 * k 1, g 0 * k 0]
    let GD : ℂ := Ml 0 1 * star mc1 mc1 k + (Ml 1 1 - Ml 0 0) * star mc1 mc2 k - Ml 1 0 * star mc2 mc2 k
    let Gd : ℂ := Ml 1 1 * star mc1 mc1 k + (Ml 0 1 - Ml 1 0) * star mc1 mc2 k - Ml 0 0 * star mc2 mc2 k
    Complex.I * normingKernel38 φ z ⟨t, ht⟩ k = (GD + Gd) / 2 := by
  intro Mf Ml mc1 mc2 star GD Gd
  have hM : ∀ i j, Mf t i j = fundPair φ z ⟨t, ht⟩ i j := fun i j => series_eq_fundPair φ z ht i j
  have hc : ∀ i j, fundColumn38 φ z t j i = fundPair φ z ⟨t, ht⟩ i j := fun i j => fundColumn_eq φ z ht i j
  have e2 : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  simp only [normingKernel38, ContinuousMap.smul_apply, mixedSquare_apply, state_apply, terminalSeed, starProd38,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  simp only [GD, Gd, star, mc1, mc2, hM, hc]
  fin_cases k <;> simp <;> field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem kappa_comp (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : Fin 2) :
    let Mf : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun u => ∑' m : ℕ, potentialVolterraTerm38 φ z m u
    let Ml : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair φ z
    let mc1 : Fin 2 → ℂ := ![Mf t 0 0, Mf t 1 0]
    let mc2 : Fin 2 → ℂ := ![Mf t 0 1, Mf t 1 1]
    let star : (Fin 2 → ℂ) → (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun g k => ![g 1 * k 1, g 0 * k 0]
    let GD : ℂ := Ml 0 1 * star mc1 mc1 k + (Ml 1 1 - Ml 0 0) * star mc1 mc2 k - Ml 1 0 * star mc2 mc2 k
    let Gd : ℂ := Ml 1 1 * star mc1 mc1 k + (Ml 0 1 - Ml 1 0) * star mc1 mc2 k - Ml 0 0 * star mc2 mc2 k
    Complex.I * pairKernelExt38 (kappaKernel38 φ z) t k =
      (2 / normingFactor φ z) * (normingSpectral38 φ z * (Complex.I * pairKernelExt38 (dirEigenKernel38 φ z) t k) +
        (GD + Gd) / 2) := by
  intro Mf Ml mc1 mc2 star GD Gd
  have hn : Complex.I * normingKernel38 φ z ⟨t, ht⟩ k = (GD + Gd) / 2 := norming_comp φ z ht k
  rw [pairKernelExt38_of_mem _ ht, pairKernelExt38_of_mem _ ht]
  simp only [kappaKernel38, ContinuousMap.smul_apply, ContinuousMap.add_apply, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul]
  rw [← hn]
  ring

end NlsGge.Atomic.G1087S2.P1


set_option autoImplicit false


namespace NlsGge.Atomic.G1087S2.P2

open MeasureTheory NlsGge.Pilot NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38

theorem state_apply' (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    state φ z ![1, 1] t 0 = fundPair φ z t 0 0 + fundPair φ z t 0 1 ∧
    state φ z ![1, 1] t 1 = fundPair φ z t 1 0 + fundPair φ z t 1 1 := by
  rw [state_eq_mulVec]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- pointwise lower bound of the squared size of the state, from det = 1 -/
theorem state_lower (φ : PotPair) (z : ℂ) (K : ℝ) (hK1 : 1 ≤ K)
    (hK : ∀ t : Set.Icc (0 : ℝ) 1, ∀ i j, ‖fundPair φ z t i j‖ ≤ K) (t : Set.Icc (0 : ℝ) 1) :
    1 / (2 * K ^ 2) ≤ ‖state φ z ![1, 1] t 0‖ ^ 2 + ‖state φ z ![1, 1] t 1‖ ^ 2 := by
  obtain ⟨h0, h1⟩ := state_apply' φ z t
  rw [h0, h1]
  set m00 := fundPair φ z t 0 0
  set m01 := fundPair φ z t 0 1
  set m10 := fundPair φ z t 1 0
  set m11 := fundPair φ z t 1 1
  have hdet : m00 * m11 - m01 * m10 = 1 := by
    have := det_fundPair38 φ z t
    rwa [Matrix.det_fin_two] at this
  have e : m11 * (m00 + m01) - m01 * (m10 + m11) = 1 := by linear_combination hdet
  have hK0 : 0 < K := by linarith
  have a1 : ‖m11‖ ≤ K := hK t 1 1
  have a2 : ‖m01‖ ≤ K := hK t 0 1
  have hle : 1 ≤ K * (‖m00 + m01‖ + ‖m10 + m11‖) := by
    have : ‖(1 : ℂ)‖ ≤ ‖m11‖ * ‖m00 + m01‖ + ‖m01‖ * ‖m10 + m11‖ := by
      rw [← e]
      calc ‖m11 * (m00 + m01) - m01 * (m10 + m11)‖ ≤ ‖m11 * (m00 + m01)‖ + ‖m01 * (m10 + m11)‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul, norm_mul]
    rw [norm_one] at this
    calc (1 : ℝ) ≤ _ := this
      _ ≤ K * ‖m00 + m01‖ + K * ‖m10 + m11‖ := by
        gcongr
      _ = _ := by ring
  set a := ‖m00 + m01‖
  set b := ‖m10 + m11‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hs : 1 / K ≤ a + b := by
    rw [div_le_iff₀ hK0]; linarith
  have hsq : (1 / K) ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
  have h2 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have : 1 / (2 * K ^ 2) = (1 / K) ^ 2 / 2 := by field_simp
  rw [this]
  linarith

theorem state_upper (φ : PotPair) (z : ℂ) (K : ℝ)
    (hK : ∀ t : Set.Icc (0 : ℝ) 1, ∀ i j, ‖fundPair φ z t i j‖ ≤ K) (t : Set.Icc (0 : ℝ) 1) (i : Fin 2) :
    ‖state φ z ![1, 1] t i‖ ≤ 2 * K := by
  obtain ⟨h0, h1⟩ := state_apply' φ z t
  fin_cases i
  · simp only [Fin.zero_eta, h0]
    calc ‖fundPair φ z t 0 0 + fundPair φ z t 0 1‖ ≤ ‖fundPair φ z t 0 0‖ + ‖fundPair φ z t 0 1‖ := norm_add_le _ _
      _ ≤ K + K := add_le_add (hK t 0 0) (hK t 0 1)
      _ = 2 * K := by ring
  · simp only [Fin.mk_one, h1]
    calc ‖fundPair φ z t 1 0 + fundPair φ z t 1 1‖ ≤ ‖fundPair φ z t 1 0‖ + ‖fundPair φ z t 1 1‖ := norm_add_le _ _
      _ ≤ K + K := add_le_add (hK t 1 0) (hK t 1 1)
      _ = 2 * K := by ring

theorem energy_lower (φ : PotPair) (z : ℂ) (K : ℝ) (hK1 : 1 ≤ K)
    (hK : ∀ t : Set.Icc (0 : ℝ) 1, ∀ i j, ‖fundPair φ z t i j‖ ≤ K) :
    1 / (2 * K ^ 2) ≤ energy (state φ z ![1, 1]) := by
  unfold energy
  have hint := (kernel_integrability (state φ z ![1, 1])).2.1
  have hc : IntervalIntegrable (fun _ : ℝ => 1 / (2 * K ^ 2)) volume 0 1 := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on (zero_le_one' ℝ) hc hint (fun s hs => by
    rw [pairKernelExt38_of_mem _ hs]
    exact state_lower φ z K hK1 hK ⟨s, hs⟩)
  simpa using hmono

/-- the Dirichlet-eigenfunction kernel of a real-type potential is bounded -/
theorem dirKernel_bound (v : PhysicalL2) (n : ℤ) (K : ℝ) (hK1 : 1 ≤ K)
    (hK : ∀ t : Set.Icc (0 : ℝ) 1, ∀ i j, ‖fundPair (realSlice v) (gkMu v n : ℂ) t i j‖ ≤ K)
    (t : Set.Icc (0 : ℝ) 1) (k : Fin 2) :
    ‖dirEigenKernel38 (realSlice v) (gkMu v n : ℂ) t k‖ ≤ 8 * K ^ 4 := by
  have hQ : Q (state (realSlice v) (gkMu v n : ℂ) ![1, 1]) = (energy (state (realSlice v) (gkMu v n : ℂ) ![1, 1]) : ℂ) :=
    real_denominator _ (dirState_real_symmetry v n)
  have hE := energy_lower (realSlice v) (gkMu v n : ℂ) K hK1 hK
  have hK0 : 0 < K := by linarith
  have hEpos : 0 < energy (state (realSlice v) (gkMu v n : ℂ) ![1, 1]) :=
    lt_of_lt_of_le (by positivity) hE
  simp only [dirEigenKernel38, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
  rw [hQ, norm_inv, Complex.norm_real, Real.norm_of_nonneg hEpos.le]
  have hsq : ‖(square (state (realSlice v) (gkMu v n : ℂ) ![1, 1])) t k‖ ≤ (2 * K) ^ 2 := by
    have hu0 := state_upper (realSlice v) (gkMu v n : ℂ) K hK t 0
    have hu1 := state_upper (realSlice v) (gkMu v n : ℂ) K hK t 1
    fin_cases k
    · simp only [square, starProd38, Fin.zero_eta]
      change ‖state (realSlice v) (gkMu v n : ℂ) ![1, 1] t 1 * state (realSlice v) (gkMu v n : ℂ) ![1, 1] t 1‖ ≤ _
      rw [norm_mul]; nlinarith [norm_nonneg (state (realSlice v) (gkMu v n : ℂ) ![1, 1] t 1)]
    · simp only [square, starProd38, Fin.mk_one]
      change ‖state (realSlice v) (gkMu v n : ℂ) ![1, 1] t 0 * state (realSlice v) (gkMu v n : ℂ) ![1, 1] t 0‖ ≤ _
      rw [norm_mul]; nlinarith [norm_nonneg (state (realSlice v) (gkMu v n : ℂ) ![1, 1] t 0)]
  set E := energy (state (realSlice v) (gkMu v n : ℂ) ![1, 1])
  have hinv : E⁻¹ ≤ 2 * K ^ 2 := by
    rw [inv_le_comm₀ hEpos (by positivity)]
    calc (2 * K ^ 2)⁻¹ = 1 / (2 * K ^ 2) := by rw [one_div]
      _ ≤ E := hE
  calc E⁻¹ * ‖(square (state (realSlice v) (gkMu v n : ℂ) ![1, 1])) t k‖ ≤ (2 * K ^ 2) * (2 * K) ^ 2 := by
        gcongr
    _ = 8 * K ^ 4 := by ring

end NlsGge.Atomic.G1087S2.P2


set_option autoImplicit false


namespace NlsGge.Atomic.G1087S2.P3

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38

open scoped Matrix.Norms.L2Operator in
theorem entry_le_l2 (A : Matrix (Fin 2) (Fin 2) ℂ) (i k : Fin 2) : ‖A i k‖ ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single k (1:ℂ))
  have h1 : ‖(EuclideanSpace.single k (1:ℂ))‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le
    ((EuclideanSpace.equiv (Fin 2) ℂ).symm (A.mulVec (EuclideanSpace.single k (1:ℂ)))) i
  simpa [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply] using h2

theorem abs_cos_sub_one_le (ε : ℝ) : |Real.cos ε - 1| ≤ |ε| := by
  have := Real.abs_cos_sub_cos_le ε 0
  simpa using this

theorem norm_exp_I_sub_one_le (θ : ℝ) : ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ ≤ |θ| := by
  simpa [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ))

theorem sq_signs (n : ℤ) : (-1 : ℂ) ^ n = 1 ∨ (-1 : ℂ) ^ n = -1 := by
  rcases Int.even_or_odd n with h | h
  · left; exact h.neg_one_zpow
  · right; exact h.neg_one_zpow

theorem neg_one_zpow_mul_self (n : ℤ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rcases sq_signs n with h | h <;> rw [h] <;> norm_num

open scoped Matrix.Norms.L2Operator in
theorem s_facts (v : PhysicalL2) (n : ℤ) (d : ℝ)
    (hd : ‖monodromyPair (realSlice v) (gkMu v n : ℂ) - freeZsFundamentalComplex (gkMu v n : ℂ) 1‖ ≤ d) :
    ∃ s : ℝ, 0 < s ∧ (-1 : ℂ) ^ n * normingFactor (realSlice v) (gkMu v n : ℂ) = (s : ℂ) ∧
      |s - 1| ≤ 2 * d + |gkMu v n - (n : ℝ) * Real.pi| ∧ s + 1 / s ≤ 2 + 2 * d := by
  set φ := realSlice v with hφ
  set g := gkMu v n with hg
  set M := monodromyPair φ (g : ℂ) with hM
  set E := freeZsFundamentalComplex (g : ℂ) 1 with hE
  set A := M - E with hAdef
  have hA : ∀ i j, ‖A i j‖ ≤ d := fun i j => (entry_le_l2 A i j).trans hd
  have hEmat : E = !![Complex.exp (-(Complex.I * (g : ℂ) * ((1 : ℝ) : ℂ))), 0;
      0, Complex.exp (Complex.I * (g : ℂ) * ((1 : ℝ) : ℂ))] := freeZsFundamentalComplex_entries _ _
  have hMij : ∀ i j, M i j = E i j + A i j := fun i j => by simp [hAdef]
  have hE01 : E 0 1 = 0 := by rw [hEmat]; simp
  have hE10 : E 1 0 = 0 := by rw [hEmat]; simp
  have hcosE : E 0 0 + E 1 1 = 2 * Complex.cos (g : ℂ) := by
    rw [hEmat, Complex.two_cos]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_one, mul_one]
    rw [add_comm]; congr 2 <;> ring
  have hroot : dirichletChar φ (g : ℂ) = 0 := gkMu_root38 v n
  have hpos := signedNorming_positive38 v n
  set s := signedNorming38 v n with hs
  have him : ((-1 : ℂ) ^ n * normingFactor φ (g : ℂ)).im = 0 := by
    have hU := normingFactor_real_im38 v g
    have hp : ((-1 : ℂ) ^ n).im = 0 := by
      have : ((-1 : ℂ) ^ n) = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_im]
    rw [Complex.mul_im, hp, hU]; ring
  have hsC : (-1 : ℂ) ^ n * normingFactor φ (g : ℂ) = (s : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]; exact him
  refine ⟨s, hpos, hsC, ?_, ?_⟩
  · -- |s - 1| bound
    have hB : ‖(A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2‖ ≤ 2 * d := by
      have h4 : ‖A 0 0 + A 0 1 + A 1 0 + A 1 1‖ ≤ 4 * d := by
        calc _ ≤ ‖A 0 0 + A 0 1 + A 1 0‖ + ‖A 1 1‖ := norm_add_le _ _
          _ ≤ (‖A 0 0 + A 0 1‖ + ‖A 1 0‖) + ‖A 1 1‖ := by gcongr; exact norm_add_le _ _
          _ ≤ ((‖A 0 0‖ + ‖A 0 1‖) + ‖A 1 0‖) + ‖A 1 1‖ := by gcongr; exact norm_add_le _ _
          _ ≤ 4 * d := by linarith [hA 0 0, hA 0 1, hA 1 0, hA 1 1]
      rw [norm_div]
      have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this, div_le_iff₀ (by norm_num)]
      linarith
    have hu : normingFactor φ (g : ℂ) = Complex.cos (g : ℂ) + (A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2 := by
      unfold normingFactor
      change (M 0 0 + M 0 1 + M 1 0 + M 1 1) / 2 = _
      rw [hMij 0 0, hMij 0 1, hMij 1 0, hMij 1 1, hE01, hE10]
      have : E 0 0 + E 1 1 = 2 * Complex.cos (g : ℂ) := hcosE
      linear_combination this / 2
    have hcos : (-1 : ℂ) ^ n * Complex.cos (g : ℂ) = ((Real.cos (g - (n : ℝ) * Real.pi) : ℝ) : ℂ) := by
      have h1 : Real.cos g = (-1 : ℝ) ^ n * Real.cos (g - (n : ℝ) * Real.pi) := by
        have : g = (g - (n : ℝ) * Real.pi) + (n : ℝ) * Real.pi := by ring
        conv_lhs => rw [this]
        rw [Real.cos_add, Real.sin_int_mul_pi, Real.cos_int_mul_pi]
        ring
      have hc0 : Complex.cos (g : ℂ) = ((Real.cos g : ℝ) : ℂ) := (Complex.ofReal_cos g).symm
      rw [hc0, h1]
      simp only [Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_neg, Complex.ofReal_one]
      have := neg_one_zpow_mul_self n
      calc (-1 : ℂ) ^ n * ((-1 : ℂ) ^ n * ((Real.cos (g - (n : ℝ) * Real.pi) : ℝ) : ℂ))
          = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * ((Real.cos (g - (n : ℝ) * Real.pi) : ℝ) : ℂ) := by ring
        _ = _ := by rw [this, one_mul]
    have hsm1 : (s : ℂ) - 1 = ((Real.cos (g - (n : ℝ) * Real.pi) - 1 : ℝ) : ℂ) +
        (-1 : ℂ) ^ n * ((A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2) := by
      rw [← hsC, hu]
      have e : (-1 : ℂ) ^ n * (Complex.cos (g : ℂ) + (A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2) - 1 =
          ((-1 : ℂ) ^ n * Complex.cos (g : ℂ) - 1) + (-1 : ℂ) ^ n * ((A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2) := by ring
      rw [e, hcos]
      simp only [Complex.ofReal_sub, Complex.ofReal_one]
    have h1 : |s - 1| = ‖(s : ℂ) - 1‖ := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, hsm1]
    calc _ ≤ ‖((Real.cos (g - (n : ℝ) * Real.pi) - 1 : ℝ) : ℂ)‖ +
          ‖(-1 : ℂ) ^ n * ((A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2)‖ := norm_add_le _ _
      _ ≤ |g - (n : ℝ) * Real.pi| + 2 * d := by
        gcongr
        · rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cos_sub_one_le _
        · rw [norm_mul]
          have : ‖(-1 : ℂ) ^ n‖ = 1 := by simp
          rw [this, one_mul]; exact hB
      _ = _ := by ring
  · -- s + 1/s bound
    have hΔ : discrim φ (g : ℂ) = 2 * Complex.cos (g : ℂ) + A 0 0 + A 1 1 := by
      rw [discrim_eq, ← hM]
      rw [hMij 0 0, hMij 1 1]
      have : E 0 0 + E 1 1 = 2 * Complex.cos (g : ℂ) := hcosE
      linear_combination this
    have hpoly := norming_trace_polynomial38 φ (g : ℂ) hroot
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hu' : normingFactor φ (g : ℂ) = (-1 : ℂ) ^ n * (s : ℂ) := by
      rw [← hsC, ← mul_assoc, neg_one_zpow_mul_self, one_mul]
    have key : (s : ℂ) + 1 / (s : ℂ) = (-1 : ℂ) ^ n * discrim φ (g : ℂ) := by
      rw [hu'] at hpoly
      have h11 := neg_one_zpow_mul_self n
      have hsq : ((-1 : ℂ) ^ n * (s : ℂ)) ^ 2 = (s : ℂ) ^ 2 := by
        rw [mul_pow, sq ((-1 : ℂ) ^ n), h11, one_mul]
      rw [hsq] at hpoly
      field_simp
      linear_combination hpoly
    have h2 : (s : ℝ) + 1 / s = ‖(s : ℂ) + 1 / (s : ℂ)‖ := by
      have : (s : ℂ) + 1 / (s : ℂ) = (((s : ℝ) + 1 / s : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2, key, norm_mul]
    have : ‖(-1 : ℂ) ^ n‖ = 1 := by simp
    rw [this, one_mul, hΔ]
    have hc : ‖Complex.cos (g : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    calc ‖2 * Complex.cos (g : ℂ) + A 0 0 + A 1 1‖ ≤ ‖2 * Complex.cos (g : ℂ)‖ + ‖A 0 0‖ + ‖A 1 1‖ := by
          calc _ ≤ ‖2 * Complex.cos (g : ℂ) + A 0 0‖ + ‖A 1 1‖ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ 2 * 1 + d + d := by
          gcongr
          · rw [norm_mul]; have : ‖(2 : ℂ)‖ = 2 := by simp
            rw [this]; gcongr
          · exact hA 0 0
          · exact hA 1 1
      _ = _ := by ring

open scoped Matrix.Norms.L2Operator in
/-- `X ↦ X 0 0 + X 0 1 + X 1 0 + X 1 1` as a continuous linear functional. -/
def sumL : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
  { toLinearMap := Matrix.entryLinearMap ℂ ℂ 0 0 + Matrix.entryLinearMap ℂ ℂ 0 1 +
      Matrix.entryLinearMap ℂ ℂ 1 0 + Matrix.entryLinearMap ℂ ℂ 1 1
    cont := LinearMap.continuous_of_finiteDimensional _ }

theorem sumL_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : sumL X = X 0 0 + X 0 1 + X 1 0 + X 1 1 := rfl

open scoped Matrix.Norms.L2Operator in
theorem norm_sumL_le (X : Matrix (Fin 2) (Fin 2) ℂ) : ‖sumL X‖ ≤ 4 * ‖X‖ := by
  rw [sumL_apply]
  have h1 := entry_le_l2 X 0 0
  have h2 := entry_le_l2 X 0 1
  have h3 := entry_le_l2 X 1 0
  have h4 := entry_le_l2 X 1 1
  calc ‖X 0 0 + X 0 1 + X 1 0 + X 1 1‖ ≤ ‖X 0 0 + X 0 1 + X 1 0‖ + ‖X 1 1‖ := norm_add_le _ _
    _ ≤ (‖X 0 0 + X 0 1‖ + ‖X 1 0‖) + ‖X 1 1‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖X 0 0‖ + ‖X 0 1‖) + ‖X 1 0‖) + ‖X 1 1‖ := by gcongr; exact norm_add_le _ _
    _ ≤ 4 * ‖X‖ := by linarith

open scoped Matrix.Norms.L2Operator in
/-- derivative of a sum of entries -/
theorem deriv_sumL (F : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) (hF : DifferentiableAt ℂ F z) :
    deriv (fun w => sumL (F w)) z = sumL (deriv F z) :=
  (sumL.hasFDerivAt.comp_hasDerivAt z hF.hasDerivAt).deriv

open scoped Matrix.Norms.L2Operator in
theorem sumL_E (w : ℂ) : sumL (freeZsFundamentalComplex w 1) = 2 * Complex.cos w := by
  rw [sumL_apply, freeZsFundamentalComplex_entries, Complex.two_cos]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_one, mul_one, add_zero, zero_add]
  rw [add_comm]; congr 2 <;> ring

open scoped Matrix.Norms.L2Operator in
theorem normingSpectral_eq (φ : PotPair) (z : ℂ) (hdiff : DifferentiableAt ℂ (fun w => monodromyPair φ w) z) :
    normingSpectral38 φ z = sumL (deriv (fun w => monodromyPair φ w) z) / 2 := by
  have hd : ∀ i j : Fin 2, deriv (fun w => monodromyPair φ w i j) z = deriv (fun w => monodromyPair φ w) z i j := by
    intro i j
    have e := (Matrix.entryLinearMap ℂ ℂ i j)
    let L : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
      { toLinearMap := Matrix.entryLinearMap ℂ ℂ i j
        cont := LinearMap.continuous_of_finiteDimensional _ }
    exact (L.hasFDerivAt.comp_hasDerivAt z hdiff.hasDerivAt).deriv
  have hs : ∀ i j : Fin 2, fundSpectralIntegral38 φ z ⟨1, zero_le_one, le_rfl⟩ i j =
      deriv (fun w => monodromyPair φ w) z i j := by
    intro i j
    rw [← hd, ← deriv_fundSpectralIntegral38 φ z ⟨1, zero_le_one, le_rfl⟩ i j]
    rfl
  have hs' : ∀ i j : Fin 2, fundSpectralIntegral38 φ z t1 i j =
      deriv (fun w => monodromyPair φ w) z i j := fun i j => hs i j
  unfold normingSpectral38
  rw [sumL_apply, hs', hs', hs', hs']

open scoped Matrix.Norms.L2Operator in
theorem ud_bound (φ : PotPair) (z : ℂ) (hdiff : DifferentiableAt ℂ (fun w => monodromyPair φ w) z)
    (hEd : DifferentiableAt ℂ (fun w => freeZsFundamentalComplex w 1) z) (D : ℝ)
    (hD : ‖deriv (fun w => monodromyPair φ w) z - deriv (fun w => freeZsFundamentalComplex w 1) z‖ ≤ D) :
    ‖normingSpectral38 φ z + Complex.sin z‖ ≤ 2 * D := by
  have h1 : deriv (fun w => sumL (freeZsFundamentalComplex w 1)) z = sumL (deriv (fun w => freeZsFundamentalComplex w 1) z) :=
    deriv_sumL _ z hEd
  have h2 : deriv (fun w => sumL (freeZsFundamentalComplex w 1)) z = -2 * Complex.sin z := by
    have : (fun w => sumL (freeZsFundamentalComplex w 1)) = fun w => 2 * Complex.cos w := funext sumL_E
    rw [this]
    have := (Complex.hasDerivAt_cos z).const_mul 2
    rw [this.deriv]; ring
  rw [normingSpectral_eq φ z hdiff]
  have e : sumL (deriv (fun w => monodromyPair φ w) z) / 2 + Complex.sin z =
      sumL (deriv (fun w => monodromyPair φ w) z - deriv (fun w => freeZsFundamentalComplex w 1) z) / 2 := by
    rw [map_sub]
    have : sumL (deriv (fun w => freeZsFundamentalComplex w 1) z) = -2 * Complex.sin z := by rw [← h1, h2]
    rw [this]; ring
  rw [e, norm_div]
  have h4 := norm_sumL_le (deriv (fun w => monodromyPair φ w) z - deriv (fun w => freeZsFundamentalComplex w 1) z)
  have : ‖(2 : ℂ)‖ = 2 := by simp
  rw [this, div_le_iff₀ (by norm_num)]
  nlinarith

end NlsGge.Atomic.G1087S2.P3


set_option autoImplicit false


namespace NlsGge.Atomic.G1087S2.P4

theorem norm_exp_I_sub_one_le (θ : ℝ) : ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ ≤ |θ| := by
  simpa [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ))

/-- the shifted lead term, compared with the lattice lead term -/
theorem lead_diff (n : ℤ) (ε : ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (ξ : ℂ)
    (hξ : ξ = (n : ℂ) * (Real.pi : ℂ) + (ε : ℂ)) (k : Fin 2) :
    ‖(-1 : ℂ) ^ n * (![-Complex.exp (-(Complex.I * ξ * (1 - 2 * (t : ℂ)))),
           Complex.exp (Complex.I * ξ * (1 - 2 * (t : ℂ)))] : Fin 2 → ℂ) k -
      (![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
        ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0] : Fin 2 → ℂ) k‖ ≤ |ε| := by
  have hpi : (-1 : ℂ) ^ n = Complex.exp ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hpi' : (-1 : ℂ) ^ n = Complex.exp ((n : ℂ) * (-((Real.pi : ℂ) * Complex.I))) := by
    rw [Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  have hθ : |ε * (1 - 2 * t)| ≤ |ε| := by
    rw [abs_mul]
    have : |1 - 2 * t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    calc |ε| * |1 - 2 * t| ≤ |ε| * 1 := by gcongr
      _ = |ε| := mul_one _
  fin_cases k
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply, zero_sub]
    have e : (-1 : ℂ) ^ n * -Complex.exp (-(Complex.I * ξ * (1 - 2 * (t : ℂ)))) -
        -Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) =
        -(Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) *
          (Complex.exp (Complex.I * ((-(ε * (1 - 2 * t)) : ℝ) : ℂ)) - 1)) := by
      rw [hpi, hξ, mul_neg, ← Complex.exp_add]
      have h2 : (n : ℂ) * ((Real.pi : ℂ) * Complex.I) + -(Complex.I * ((n : ℂ) * (Real.pi : ℂ) + (ε : ℂ)) * (1 - 2 * (t : ℂ))) =
          2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) + Complex.I * ((-(ε * (1 - 2 * t)) : ℝ) : ℂ) := by
        push_cast; ring
      rw [h2, Complex.exp_add]; ring
    rw [e, norm_neg, norm_mul]
    have h1 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)).re = 0 := by simp
      rw [this, Real.exp_zero]
    rw [h1, one_mul]
    refine (norm_exp_I_sub_one_le _).trans ?_
    rw [abs_neg]; exact hθ
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Pi.sub_apply, sub_zero, Matrix.cons_val_zero]
    have e : (-1 : ℂ) ^ n * Complex.exp (Complex.I * ξ * (1 - 2 * (t : ℂ))) -
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ)) =
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ)) *
          (Complex.exp (Complex.I * ((ε * (1 - 2 * t) : ℝ) : ℂ)) - 1) := by
      rw [hpi', hξ, ← Complex.exp_add]
      have h2 : (n : ℂ) * (-((Real.pi : ℂ) * Complex.I)) + Complex.I * ((n : ℂ) * (Real.pi : ℂ) + (ε : ℂ)) * (1 - 2 * (t : ℂ)) =
          -(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ) + Complex.I * ((ε * (1 - 2 * t) : ℝ) : ℂ) := by
        push_cast; ring
      rw [h2, Complex.exp_add]; ring
    rw [e, norm_mul]
    have h1 : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have : (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ)).re = 0 := by simp
      rw [this, Real.exp_zero]
    rw [h1, one_mul]
    exact (norm_exp_I_sub_one_le _).trans hθ

/-- the algebraic combination of the pieces of `i ∂κ_n - (e⁺ - e⁻)` -/
theorem term_bound (S u : ℂ) (s : ℝ) (hSS : S * S = 1) (hSu : S * u = (s : ℂ)) (hs : 0 < s)
    (Bs : ℝ) (h1s : 1 / s ≤ Bs) (ud GD Gd lead dk e : ℂ) (Kd : ℝ) (hdk : ‖dk‖ ≤ Kd) (he : ‖e‖ = 1)
    (ε : ℝ) (hlead : ‖S * lead - e‖ ≤ |ε|) :
    ‖(2 / u) * (ud * dk + (GD + Gd) / 2) - e‖ ≤
      Bs * (2 * ‖ud‖ * Kd + ‖GD‖ + ‖Gd - lead‖ + |ε| + |s - 1|) := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hu : u = S * (s : ℂ) := by
    calc u = (S * S) * u := by rw [hSS, one_mul]
      _ = S * (S * u) := by ring
      _ = _ := by rw [hSu]
  have hS0 : S ≠ 0 := by
    intro h; rw [h] at hSS; simp at hSS
  have hu0 : u ≠ 0 := by rw [hu]; exact mul_ne_zero hS0 hs0
  have hSn : ‖S‖ = 1 := by
    have h := congrArg norm hSS
    rw [norm_mul, norm_one] at h
    have : 0 ≤ ‖S‖ := norm_nonneg _
    nlinarith
  have hun : ‖u‖ = s := by
    rw [hu, norm_mul, hSn, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have e1 : (2 / u) * (ud * dk + (GD + Gd) / 2) - e =
      (2 * ud / u) * dk + GD / u + (Gd - lead) / u + ((S * lead - e) / (s : ℂ) + e * (1 / (s : ℂ) - 1)) := by
    rw [hu]
    field_simp
    have : S * S = 1 := hSS
    linear_combination (-lead) * hSS
  rw [e1]
  have hBs : 0 ≤ Bs := le_trans (by positivity) h1s
  have h1u : ‖(1 : ℂ) / u‖ ≤ Bs := by
    rw [norm_div, norm_one, hun]; exact h1s
  have hdiv : ∀ x : ℂ, ‖x / u‖ = ‖x‖ * (1 / s) := by
    intro x; rw [norm_div, hun]; ring
  have hdivs : ∀ x : ℂ, ‖x / (s : ℂ)‖ = ‖x‖ * (1 / s) := by
    intro x; rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]; ring
  have hone : ‖(1 / (s : ℂ) - 1)‖ ≤ (1 / s) * |s - 1| := by
    have : (1 / (s : ℂ) - 1) = (((1 - s) / s : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_sub_comm]
    rw [div_eq_mul_inv]; rw [mul_comm]; simp [one_div]
  have hn1 : ‖(2 * ud / u) * dk‖ ≤ (1 / s) * (2 * ‖ud‖ * Kd) := by
    rw [norm_mul, hdiv]
    have h2 : ‖2 * ud‖ = 2 * ‖ud‖ := by rw [norm_mul]; simp
    rw [h2]
    have hdk0 : 0 ≤ Kd := (norm_nonneg _).trans hdk
    calc 2 * ‖ud‖ * (1 / s) * ‖dk‖ ≤ 2 * ‖ud‖ * (1 / s) * Kd := by gcongr
      _ = _ := by ring
  have hn2 : ‖GD / u‖ ≤ (1 / s) * ‖GD‖ := by rw [hdiv]; ring_nf; rfl
  have hn3 : ‖(Gd - lead) / u‖ ≤ (1 / s) * ‖Gd - lead‖ := by rw [hdiv]; ring_nf; rfl
  have hn4 : ‖(S * lead - e) / (s : ℂ)‖ ≤ (1 / s) * |ε| := by
    rw [hdivs]; nlinarith [hlead, show (0:ℝ) < 1 / s by positivity]
  have hn5 : ‖e * (1 / (s : ℂ) - 1)‖ ≤ (1 / s) * |s - 1| := by
    rw [norm_mul, he, one_mul]; exact hone
  have hsum := norm_add_le ((2 * ud / u) * dk + GD / u + (Gd - lead) / u) ((S * lead - e) / (s : ℂ) + e * (1 / (s : ℂ) - 1))
  have h3 := norm_add_le ((2 * ud / u) * dk + GD / u) ((Gd - lead) / u)
  have h2 := norm_add_le ((2 * ud / u) * dk) (GD / u)
  have h45 := norm_add_le ((S * lead - e) / (s : ℂ)) (e * (1 / (s : ℂ) - 1))
  have hs1 : 1 / s ≤ Bs := h1s
  have hpos : 0 ≤ 2 * ‖ud‖ * Kd + ‖GD‖ + ‖Gd - lead‖ + |ε| + |s - 1| := by
    have hKd : 0 ≤ Kd := (norm_nonneg _).trans hdk
    positivity
  calc _ ≤ (1 / s) * (2 * ‖ud‖ * Kd + ‖GD‖ + ‖Gd - lead‖ + |ε| + |s - 1|) := by nlinarith
    _ ≤ Bs * (2 * ‖ud‖ * Kd + ‖GD‖ + ‖Gd - lead‖ + |ε| + |s - 1|) := by gcongr

end NlsGge.Atomic.G1087S2.P4


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.P5

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38

open scoped Matrix.Norms.L2Operator

theorem bridge1 (φ : PotPair) (z : ℂ) :
    (∑' m : ℕ, potentialVolterraTerm38 φ z m 1) = monodromyPair φ z :=
  NlsGge.Atomic.G1004GenT.tsum_terms_eq_fundContT φ z zero_le_one ⟨zero_le_one, le_rfl⟩

theorem sin_gkMu_le (v : PhysicalL2) (n : ℤ) : ‖Complex.sin (gkMu v n : ℂ)‖ ≤ |gkMu v n - (n : ℝ) * Real.pi| := by
  rw [← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
  have h1 : Real.sin (gkMu v n) = (-1 : ℝ) ^ n * Real.sin (gkMu v n - (n : ℝ) * Real.pi) := by
    have : gkMu v n = (gkMu v n - (n : ℝ) * Real.pi) + (n : ℝ) * Real.pi := by ring
    conv_lhs => rw [this]
    rw [Real.sin_add, Real.sin_int_mul_pi, Real.cos_int_mul_pi]
    ring
  rw [h1, abs_mul]
  have : |(-1 : ℝ) ^ n| = 1 := by simp
  rw [this, one_mul]
  exact Real.abs_sin_le_abs

theorem log_bound (s Bs : ℝ) (hs : 0 < s) (h1 : 1 ≤ Bs) (hsB : s ≤ Bs) (hiB : 1 / s ≤ Bs) :
    |Real.log s| ≤ Bs * |s - 1| := by
  rcases le_total 1 s with h | h
  · have := Real.log_le_sub_one_of_pos hs
    have h0 : 0 ≤ Real.log s := Real.log_nonneg h
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith : 0 ≤ s - 1)]
    nlinarith
  · have h0 : Real.log s ≤ 0 := Real.log_nonpos hs.le h
    rw [abs_of_nonpos h0, abs_of_nonpos (by linarith : s - 1 ≤ 0)]
    have := Real.log_le_sub_one_of_pos (one_div_pos.mpr hs)
    rw [one_div, Real.log_inv] at this
    have h2 : (s⁻¹ - 1) ≤ Bs * (1 - s) := by
      have : s⁻¹ - 1 = (1 - s) * s⁻¹ := by field_simp
      rw [this]
      calc (1 - s) * s⁻¹ ≤ (1 - s) * Bs :=
            mul_le_mul_of_nonneg_left (by rw [← one_div]; exact hiB) (by linarith)
        _ = _ := by ring
    linarith

theorem sq_sum_bound {f g : ℤ → ℝ} (hf : ∀ n, 0 ≤ f n) (hfg : ∀ n, f n ≤ g n) (hg : Summable g) :
    Summable f ∧ ∑' n, f n ≤ ∑' n, g n :=
  ⟨Summable.of_nonneg_of_le hf hfg hg, Summable.tsum_le_tsum hfg (Summable.of_nonneg_of_le hf hfg hg) hg⟩

end NlsGge.Atomic.G1087S2.P5


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.P6

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38

open scoped Matrix.Norms.L2Operator

noncomputable section

def GDf (φ : PotPair) (z : ℂ) (t : ℝ) (k : Fin 2) : ℂ :=
  let Mf : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun u => ∑' m : ℕ, potentialVolterraTerm38 φ z m u
  let Ml : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair φ z
  let mc1 : Fin 2 → ℂ := ![Mf t 0 0, Mf t 1 0]
  let mc2 : Fin 2 → ℂ := ![Mf t 0 1, Mf t 1 1]
  let star : (Fin 2 → ℂ) → (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun g k => ![g 1 * k 1, g 0 * k 0]
  Ml 0 1 * star mc1 mc1 k + (Ml 1 1 - Ml 0 0) * star mc1 mc2 k - Ml 1 0 * star mc2 mc2 k

def Gdf (φ : PotPair) (z : ℂ) (t : ℝ) (k : Fin 2) : ℂ :=
  let Mf : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun u => ∑' m : ℕ, potentialVolterraTerm38 φ z m u
  let Ml : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair φ z
  let mc1 : Fin 2 → ℂ := ![Mf t 0 0, Mf t 1 0]
  let mc2 : Fin 2 → ℂ := ![Mf t 0 1, Mf t 1 1]
  let star : (Fin 2 → ℂ) → (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun g k => ![g 1 * k 1, g 0 * k 0]
  Ml 1 1 * star mc1 mc1 k + (Ml 0 1 - Ml 1 0) * star mc1 mc2 k - Ml 0 0 * star mc2 mc2 k

def leadf (ξ : ℂ) (t : ℝ) (k : Fin 2) : ℂ :=
  (![-Complex.exp (-(Complex.I * ξ * (1 - 2 * (t : ℂ)))),
     Complex.exp (Complex.I * ξ * (1 - 2 * (t : ℂ)))] : Fin 2 → ℂ) k

def evec (n : ℤ) (t : ℝ) : Fin 2 → ℂ :=
  ![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
    ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0]

theorem norm_evec (n : ℤ) (t : ℝ) (k : Fin 2) : ‖evec n t k‖ = 1 := by
  fin_cases k
  · simp only [evec, Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply, zero_sub, norm_neg]
    rw [Complex.norm_exp]
    have : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  · simp only [evec, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Pi.sub_apply, sub_zero, Matrix.cons_val_zero]
    rw [Complex.norm_exp]
    have : (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]

theorem fund_entry_bound (v : PhysicalL2) (n : ℤ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (D : ℝ)
    (hD : ‖(∑' m : ℕ, potentialVolterraTerm38 (realSlice v) (gkMu v n : ℂ) m t) -
      freeZsFundamentalComplex (gkMu v n : ℂ) t‖ ≤ D) (i j : Fin 2) :
    ‖fundPair (realSlice v) (gkMu v n : ℂ) ⟨t, ht⟩ i j‖ ≤ 1 + D := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := ∑' m : ℕ, potentialVolterraTerm38 (realSlice v) (gkMu v n : ℂ) m t with hM
  set E := freeZsFundamentalComplex (gkMu v n : ℂ) t with hE
  have h1 : fundPair (realSlice v) (gkMu v n : ℂ) ⟨t, ht⟩ i j = M i j :=
    (NlsGge.Atomic.G1087S2.P1.series_eq_fundPair _ _ ht i j).symm
  have hA : ‖(M - E) i j‖ ≤ D := (NlsGge.Atomic.G1087S2.P3.entry_le_l2 (M - E) i j).trans hD
  have hEn : ‖E i j‖ ≤ 1 := by
    rw [hE, freeZsFundamentalComplex_entries]
    fin_cases i <;> fin_cases j <;> simp [Complex.norm_exp]
  rw [h1]
  have : M i j = E i j + (M - E) i j := by simp
  rw [this]
  calc ‖E i j + (M - E) i j‖ ≤ ‖E i j‖ + ‖(M - E) i j‖ := norm_add_le _ _
    _ ≤ 1 + D := add_le_add hEn hA

end

end NlsGge.Atomic.G1087S2.P6


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.P7

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38 NlsGge.Atomic.G1087S2.P6

open scoped Matrix.Norms.L2Operator

noncomputable section

theorem grad_term (v : PhysicalL2) (n : ℤ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : Fin 2)
    (D K g d : ℝ) (hK1 : 1 ≤ K)
    (hK : ∀ t' : Set.Icc (0 : ℝ) 1, ∀ i j, ‖fundPair (realSlice v) (gkMu v n : ℂ) t' i j‖ ≤ K)
    (hd : ‖monodromyPair (realSlice v) (gkMu v n : ℂ) - freeZsFundamentalComplex (gkMu v n : ℂ) 1‖ ≤ d)
    (hdD : d ≤ D) (hD0 : 0 ≤ D)
    (hdiff : DifferentiableAt ℂ (fun w => monodromyPair (realSlice v) w) (gkMu v n : ℂ))
    (hEd : DifferentiableAt ℂ (fun w => freeZsFundamentalComplex w 1) (gkMu v n : ℂ))
    (hg : ‖deriv (fun w => monodromyPair (realSlice v) w) (gkMu v n : ℂ) -
      deriv (fun w => freeZsFundamentalComplex w 1) (gkMu v n : ℂ)‖ ≤ g) :
    ‖(Complex.I • pairKernelExt38 (kappaKernel38 (realSlice v) (gkMu v n : ℂ)) t - evec n t) k‖ ≤
      (2 + 2 * D) * (4 * (8 * K ^ 4) * g + (2 * (8 * K ^ 4) + 2) * |gkMu v n - (n : ℝ) * Real.pi| + 2 * d +
        ‖GDf (realSlice v) (gkMu v n : ℂ) t k‖ + ‖Gdf (realSlice v) (gkMu v n : ℂ) t k - leadf (gkMu v n : ℂ) t k‖) := by
  set φ := realSlice v with hφ
  set z : ℂ := (gkMu v n : ℂ) with hz
  set ε : ℝ := gkMu v n - (n : ℝ) * Real.pi with hε
  obtain ⟨s, hs0, hsC, hs1, hs2⟩ := NlsGge.Atomic.G1087S2.P3.s_facts v n d hd
  have hBs : 1 / s ≤ 2 + 2 * D := by linarith
  have kc : Complex.I * pairKernelExt38 (kappaKernel38 φ z) t k =
      (2 / normingFactor φ z) * (normingSpectral38 φ z *
        (Complex.I * pairKernelExt38 (dirEigenKernel38 φ z) t k) +
        (GDf φ z t k + Gdf φ z t k) / 2) := NlsGge.Atomic.G1087S2.P1.kappa_comp φ z ht k
  have comp : (Complex.I • pairKernelExt38 (kappaKernel38 φ z) t - evec n t) k =
      Complex.I * pairKernelExt38 (kappaKernel38 φ z) t k - evec n t k := by
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hξ : z = (n : ℂ) * (Real.pi : ℂ) + (ε : ℂ) := by
    simp only [hz, hε]; push_cast; ring
  have hlead : ‖(-1 : ℂ) ^ n * leadf z t k - evec n t k‖ ≤ |ε| :=
    NlsGge.Atomic.G1087S2.P4.lead_diff n ε t ht z hξ k
  have hdk : ‖Complex.I * pairKernelExt38 (dirEigenKernel38 φ z) t k‖ ≤ 8 * K ^ 4 := by
    rw [norm_mul, Complex.norm_I, one_mul, pairKernelExt38_of_mem _ ht]
    exact NlsGge.Atomic.G1087S2.P2.dirKernel_bound v n K hK1 hK ⟨t, ht⟩ k
  have hSS : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := NlsGge.Atomic.G1087S2.P3.neg_one_zpow_mul_self n
  have key := NlsGge.Atomic.G1087S2.P4.term_bound ((-1 : ℂ) ^ n) (normingFactor φ z) s hSS hsC hs0
    (2 + 2 * D) hBs (normingSpectral38 φ z) (GDf φ z t k) (Gdf φ z t k) (leadf z t k)
    (Complex.I * pairKernelExt38 (dirEigenKernel38 φ z) t k) (evec n t k) (8 * K ^ 4) hdk (norm_evec n t k)
    ε hlead
  rw [comp, kc]
  have hud : ‖normingSpectral38 φ z‖ ≤ 2 * g + |ε| := by
    have h1 := NlsGge.Atomic.G1087S2.P3.ud_bound φ z hdiff hEd g hg
    have h2 : ‖Complex.sin z‖ ≤ |ε| := NlsGge.Atomic.G1087S2.P5.sin_gkMu_le v n
    calc ‖normingSpectral38 φ z‖ = ‖(normingSpectral38 φ z + Complex.sin z) - Complex.sin z‖ := by ring_nf
      _ ≤ ‖normingSpectral38 φ z + Complex.sin z‖ + ‖Complex.sin z‖ := norm_sub_le _ _
      _ ≤ 2 * g + |ε| := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hBs0 : 0 ≤ 2 + 2 * D := by linarith
  refine key.trans ?_
  have hs1' : |s - 1| ≤ 2 * d + |ε| := hs1
  have hKd : 0 ≤ 8 * K ^ 4 := by positivity
  have : 2 * ‖normingSpectral38 φ z‖ * (8 * K ^ 4) + ‖GDf φ z t k‖ + ‖Gdf φ z t k - leadf z t k‖ + |ε| + |s - 1| ≤
      4 * (8 * K ^ 4) * g + (2 * (8 * K ^ 4) + 2) * |ε| + 2 * d + ‖GDf φ z t k‖ + ‖Gdf φ z t k - leadf z t k‖ := by
    have h3 : 2 * ‖normingSpectral38 φ z‖ * (8 * K ^ 4) ≤ 2 * (2 * g + |ε|) * (8 * K ^ 4) := by gcongr
    nlinarith [h3, hs1']
  exact mul_le_mul_of_nonneg_left this hBs0

end

end NlsGge.Atomic.G1087S2.P7


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.P8

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38 NlsGge.Atomic.G1087S2.P6 NlsGge.Atomic.G1087S2.P7

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- bounded summability -/
def SB (f : ℤ → ℝ) (A : ℝ) : Prop := Summable f ∧ ∑' n, f n ≤ A

theorem SB.mono {f g : ℤ → ℝ} {A : ℝ} (h0 : ∀ n, 0 ≤ f n) (hfg : ∀ n, f n ≤ g n) (hg : SB g A) : SB f A :=
  ⟨Summable.of_nonneg_of_le h0 hfg hg.1,
    (Summable.tsum_le_tsum hfg (Summable.of_nonneg_of_le h0 hfg hg.1) hg.1).trans hg.2⟩

theorem SB.add {f g : ℤ → ℝ} {A B : ℝ} (hf : SB f A) (hg : SB g B) : SB (fun n => f n + g n) (A + B) :=
  ⟨hf.1.add hg.1, by rw [hf.1.tsum_add hg.1]; exact add_le_add hf.2 hg.2⟩

theorem SB.smul {f : ℤ → ℝ} {A : ℝ} (c : ℝ) (hc : 0 ≤ c) (hf : SB f A) : SB (fun n => c * f n) (c * A) :=
  ⟨hf.1.mul_left c, by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hf.2 hc⟩

theorem SB.le_sqrt {a : ℤ → ℝ} {C : ℝ} (h : SB (fun n => a n ^ 2) C) (n : ℤ) : |a n| ≤ Real.sqrt (max C 0) := by
  refine Real.le_sqrt_of_sq_le ?_
  have := h.1.le_tsum n (fun _ _ => sq_nonneg _)
  rw [sq_abs]
  exact this.trans (h.2.trans (le_max_left _ _))

theorem sq7 (a b c d e f g : ℝ) :
    (a + b + c + d + e + f + g) ^ 2 ≤ 7 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (a - f),
    sq_nonneg (a - g), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (b - f),
    sq_nonneg (b - g), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (c - f), sq_nonneg (c - g),
    sq_nonneg (d - e), sq_nonneg (d - f), sq_nonneg (d - g), sq_nonneg (e - f), sq_nonneg (e - g),
    sq_nonneg (f - g)]

theorem SB.weak {f : ℤ → ℝ} {A B : ℝ} (h : SB f A) (hAB : A ≤ B) : SB f B := ⟨h.1, h.2.trans hAB⟩

/-- the abstract gradient sum -/
theorem part_grad (Bs cg ce Cg Ce Cd C0 C1 D0 D1 : ℝ) (hBs : 0 ≤ Bs) (hcg : 0 ≤ cg) (hce : 0 ≤ ce)
    (g e d G0 G1 H0 H1 V : ℤ → ℝ)
    (hg0 : ∀ n, 0 ≤ g n) (he0 : ∀ n, 0 ≤ e n) (hd0 : ∀ n, 0 ≤ d n) (hG00 : ∀ n, 0 ≤ G0 n)
    (hG10 : ∀ n, 0 ≤ G1 n) (hH00 : ∀ n, 0 ≤ H0 n) (hH10 : ∀ n, 0 ≤ H1 n)
    (hV0 : ∀ n, 0 ≤ V n)
    (hV : ∀ n, V n ≤ Bs * (cg * g n + ce * e n + 2 * d n + (G0 n + G1 n) + (H0 n + H1 n)))
    (hg : SB (fun n => g n ^ 2) Cg) (he : SB (fun n => e n ^ 2) Ce) (hd : SB (fun n => d n ^ 2) Cd)
    (hG0 : SB (fun n => G0 n ^ 2) C0) (hG1 : SB (fun n => G1 n ^ 2) C1)
    (hH0 : SB (fun n => H0 n ^ 2) D0) (hH1 : SB (fun n => H1 n ^ 2) D1) :
    SB (fun n => V n ^ 2) (7 * Bs ^ 2 * (cg ^ 2 * Cg + ce ^ 2 * Ce + 4 * Cd + C0 + C1 + D0 + D1)) := by
  have hmaj : SB (fun n => 7 * Bs ^ 2 * (cg ^ 2 * g n ^ 2 + ce ^ 2 * e n ^ 2 + 4 * d n ^ 2 + G0 n ^ 2 + G1 n ^ 2 +
      H0 n ^ 2 + H1 n ^ 2)) (7 * Bs ^ 2 * (cg ^ 2 * Cg + ce ^ 2 * Ce + 4 * Cd + C0 + C1 + D0 + D1)) := by
    have h1 := (hg.smul (cg ^ 2) (sq_nonneg _))
    have h2 := (he.smul (ce ^ 2) (sq_nonneg _))
    have h3 := (hd.smul 4 (by norm_num))
    have hs := (((((h1.add h2).add h3).add hG0).add hG1).add hH0).add hH1
    exact (hs.smul (7 * Bs ^ 2) (by positivity))
  refine SB.mono (fun n => sq_nonneg _) (fun n => ?_) hmaj
  have hn : V n ^ 2 ≤ (Bs * (cg * g n + ce * e n + 2 * d n + (G0 n + G1 n) + (H0 n + H1 n))) ^ 2 :=
    pow_le_pow_left₀ (hV0 n) (hV n) 2
  refine hn.trans ?_
  have := sq7 (cg * g n) (ce * e n) (2 * d n) (G0 n) (G1 n) (H0 n) (H1 n)
  have e1 : cg * g n + ce * e n + 2 * d n + (G0 n + G1 n) + (H0 n + H1 n) =
      cg * g n + ce * e n + 2 * d n + G0 n + G1 n + H0 n + H1 n := by ring
  rw [e1, mul_pow]
  calc Bs ^ 2 * (cg * g n + ce * e n + 2 * d n + G0 n + G1 n + H0 n + H1 n) ^ 2
      ≤ Bs ^ 2 * (7 * ((cg * g n) ^ 2 + (ce * e n) ^ 2 + (2 * d n) ^ 2 + G0 n ^ 2 + G1 n ^ 2 + H0 n ^ 2 + H1 n ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- the abstract logarithm sum -/
theorem part_kappa (Bs Cd Ce : ℝ) (hBs : 0 ≤ Bs) (kap d e : ℤ → ℝ)
    (hpt : ∀ n, kap n ^ 2 ≤ 4 * Bs ^ 2 * (8 * d n ^ 2 + 2 * e n ^ 2))
    (hd : SB (fun n => d n ^ 2) Cd) (he : SB (fun n => e n ^ 2) Ce) :
    SB (fun n => kap n ^ 2) (4 * Bs ^ 2 * (8 * Cd + 2 * Ce)) := by
  have hmaj : SB (fun n => 4 * Bs ^ 2 * (8 * d n ^ 2 + 2 * e n ^ 2)) (4 * Bs ^ 2 * (8 * Cd + 2 * Ce)) :=
    (((hd.smul 8 (by norm_num)).add (he.smul 2 (by norm_num))).smul (4 * Bs ^ 2) (by positivity))
  exact SB.mono (fun n => sq_nonneg _) hpt hmaj

end

end NlsGge.Atomic.G1087S2.P8


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.P9

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38 NlsGge.Atomic.G1087S2.P6 NlsGge.Atomic.G1087S2.P7
  NlsGge.Atomic.G1087S2.P8

open scoped Matrix.Norms.L2Operator

noncomputable section

def DD (C19 : ℝ) : ℝ := Real.sqrt (max C19 0)
def Kdf (C19 : ℝ) : ℝ := 8 * (1 + DD C19) ^ 4
def CKf (Cμ C19 : ℝ) : ℝ := 4 * (2 + 2 * DD C19) ^ 2 * (8 * max C19 0 + 2 * max Cμ 0)
def CGf (Cμ C19 C20 C29 : ℝ) : ℝ := 7 * (2 + 2 * DD C19) ^ 2 *
  ((4 * Kdf C19) ^ 2 * max C20 0 + (2 * Kdf C19 + 2) ^ 2 * max Cμ 0 + 4 * max C19 0 + max C29 0 + max C29 0 +
    max C29 0 + max C29 0)

theorem per_v (v : PhysicalL2) (Cμ C19 C20 C29 : ℝ)
    (hEd : ∀ z : ℂ, DifferentiableAt ℂ (fun w : ℂ => freeZsFundamentalComplex w 1) z)
    (hμ : SB (fun n : ℤ => |gkMu v n - (n : ℝ) * Real.pi| ^ 2) Cμ)
    (h19 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → SB (fun n : ℤ =>
      ‖(∑' m : ℕ, potentialVolterraTerm38 (realSlice v) (gkMu v n : ℂ) m t) -
        freeZsFundamentalComplex (gkMu v n : ℂ) t‖ ^ 2) C19)
    (h20a : ∀ n : ℤ, DifferentiableAt ℂ
      (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 (realSlice v) w m 1) (gkMu v n : ℂ))
    (h20b : SB (fun n : ℤ =>
      ‖deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 (realSlice v) w m 1) (gkMu v n : ℂ) -
        deriv (fun w : ℂ => freeZsFundamentalComplex w 1) (gkMu v n : ℂ)‖ ^ 2) C20)
    (h29 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k : Fin 2,
      SB (fun n : ℤ => ‖GDf (realSlice v) (gkMu v n : ℂ) t k‖ ^ 2) C29 ∧
      SB (fun n : ℤ => ‖Gdf (realSlice v) (gkMu v n : ℂ) t k - leadf (gkMu v n : ℂ) t k‖ ^ 2) C29) :
    (∀ n : ℤ, (normingFactor (realSlice v) (gkMu v n : ℂ)).im = 0 ∧ 0 < signedNorming38 v n) ∧
    SB (fun n : ℤ => if 0 < n.natAbs then realKappa38 v n ^ 2 else 0) (CKf Cμ C19) ∧
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      SB (fun n : ℤ => if 0 < n.natAbs then
        ‖Complex.I • pairKernelExt38 (kappaKernel38 (realSlice v) (gkMu v n : ℂ)) t - evec n t‖ ^ 2 else 0)
        (CGf Cμ C19 C20 C29) := by
  have hbr := NlsGge.Atomic.G1087S2.P5.bridge1 (realSlice v)
  have e2 : (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 (realSlice v) w m 1) =
      fun w : ℂ => monodromyPair (realSlice v) w := funext hbr
  rw [e2] at h20a h20b
  obtain ⟨d, hdeq⟩ : ∃ d : ℤ → ℝ, ∀ n, d n = ‖monodromyPair (realSlice v) (gkMu v n : ℂ) -
      freeZsFundamentalComplex (gkMu v n : ℂ) 1‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hgeq⟩ : ∃ g : ℤ → ℝ, ∀ n, g n = ‖deriv (fun w : ℂ => monodromyPair (realSlice v) w) (gkMu v n : ℂ) -
      deriv (fun w : ℂ => freeZsFundamentalComplex w 1) (gkMu v n : ℂ)‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨ε, hεeq⟩ : ∃ ε : ℤ → ℝ, ∀ n, ε n = gkMu v n - (n : ℝ) * Real.pi := ⟨_, fun _ => rfl⟩
  have hd1 : SB (fun n : ℤ => d n ^ 2) C19 := by
    have h := h19 1 zero_le_one le_rfl
    have e : (fun n : ℤ => ‖(∑' m : ℕ, potentialVolterraTerm38 (realSlice v) (gkMu v n : ℂ) m 1) -
        freeZsFundamentalComplex (gkMu v n : ℂ) 1‖ ^ 2) = fun n : ℤ => d n ^ 2 := by
      funext n; rw [hdeq n, hbr]
    rw [e] at h; exact h
  have hg1 : SB (fun n : ℤ => g n ^ 2) C20 := by
    have e : (fun n : ℤ => ‖deriv (fun w : ℂ => monodromyPair (realSlice v) w) (gkMu v n : ℂ) -
        deriv (fun w : ℂ => freeZsFundamentalComplex w 1) (gkMu v n : ℂ)‖ ^ 2) = fun n : ℤ => g n ^ 2 := by
      funext n; rw [hgeq n]
    rw [e] at h20b; exact h20b
  have he1 : SB (fun n : ℤ => |ε n| ^ 2) Cμ := by
    have e : (fun n : ℤ => |gkMu v n - (n : ℝ) * Real.pi| ^ 2) = fun n : ℤ => |ε n| ^ 2 := by
      funext n; rw [hεeq n]
    rw [e] at hμ; exact hμ
  set D := DD C19 with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hd0 : ∀ n, 0 ≤ d n := fun n => by rw [hdeq n]; exact norm_nonneg _
  have hg0 : ∀ n, 0 ≤ g n := fun n => by rw [hgeq n]; exact norm_nonneg _
  have hdle : ∀ n, d n ≤ D := fun n => by
    have := hd1.le_sqrt n
    rwa [abs_of_nonneg (hd0 n)] at this
  have hK : ∀ n : ℤ, ∀ t' : Set.Icc (0 : ℝ) 1, ∀ i j,
      ‖fundPair (realSlice v) (gkMu v n : ℂ) t' i j‖ ≤ 1 + D := by
    intro n t' i j
    obtain ⟨t, ht⟩ := t'
    have hb := (h19 t ht.1 ht.2).le_sqrt n
    rw [abs_of_nonneg (norm_nonneg _)] at hb
    exact fund_entry_bound v n ht D hb i j
  have hs : ∀ n : ℤ, ∃ s : ℝ, 0 < s ∧ (-1 : ℂ) ^ n * normingFactor (realSlice v) (gkMu v n : ℂ) = (s : ℂ) ∧
      |s - 1| ≤ 2 * d n + |ε n| ∧ s + 1 / s ≤ 2 + 2 * d n := by
    intro n
    obtain ⟨s, hs0, hsC, hs1, hs2⟩ := NlsGge.Atomic.G1087S2.P3.s_facts v n (d n) (hdeq n).ge
    exact ⟨s, hs0, hsC, by rw [hεeq n]; exact hs1, hs2⟩
  refine ⟨fun n => ⟨normingFactor_real_im38 v (gkMu v n), signedNorming_positive38 v n⟩, ?_, ?_⟩
  · -- the logarithms
    have hkp : ∀ n, realKappa38 v n ^ 2 ≤ 4 * (2 + 2 * D) ^ 2 * (8 * d n ^ 2 + 2 * |ε n| ^ 2) := by
      intro n
      obtain ⟨s, hs0, hsC, hs1, hs2⟩ := hs n
      have hsn : signedNorming38 v n = s := by
        have : ((-1 : ℂ) ^ n * normingFactor (realSlice v) (gkMu v n : ℂ)).re = s := by
          rw [hsC, Complex.ofReal_re]
        exact this
      have hi : 0 < 1 / s := by positivity
      have hsB : s ≤ 2 + 2 * D := by
        have := hdle n; linarith
      have hiB : 1 / s ≤ 2 + 2 * D := by
        have := hdle n; linarith
      have hlog := NlsGge.Atomic.G1087S2.P5.log_bound s (2 + 2 * D) hs0 (by linarith) hsB hiB
      have hk : realKappa38 v n = 2 * Real.log s := by unfold realKappa38; rw [hsn]
      rw [hk]
      have h1 : |Real.log s| ^ 2 ≤ ((2 + 2 * D) * |s - 1|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hlog 2
      have h2 : |s - 1| ^ 2 ≤ (2 * d n + |ε n|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hs1 2
      have h3 : (2 * d n + |ε n|) ^ 2 ≤ 8 * d n ^ 2 + 2 * |ε n| ^ 2 := by
        nlinarith [sq_nonneg (2 * d n - |ε n|), sq_nonneg (d n), sq_nonneg (|ε n|)]
      have h4 : (2 * Real.log s) ^ 2 = 4 * |Real.log s| ^ 2 := by rw [mul_pow, sq_abs]; ring
      rw [h4]
      calc 4 * |Real.log s| ^ 2 ≤ 4 * (((2 + 2 * D) * |s - 1|) ^ 2) := by gcongr
        _ = 4 * (2 + 2 * D) ^ 2 * |s - 1| ^ 2 := by rw [mul_pow]; ring
        _ ≤ 4 * (2 + 2 * D) ^ 2 * (8 * d n ^ 2 + 2 * |ε n| ^ 2) := by
          have : 0 ≤ 4 * (2 + 2 * D) ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_left (h2.trans h3) this
    have hsb := part_kappa (2 + 2 * D) (max C19 0) (max Cμ 0) (by linarith) (fun n => realKappa38 v n) d
      (fun n => |ε n|) hkp (hd1.weak (le_max_left _ _)) (he1.weak (le_max_left _ _))
    refine SB.mono (fun n => ?_) (fun n => ?_) hsb
    · by_cases h : 0 < n.natAbs
      · rw [if_pos h]; exact sq_nonneg _
      · rw [if_neg h]
    · by_cases h : 0 < n.natAbs
      · rw [if_pos h]
      · rw [if_neg h]; exact sq_nonneg _
  · intro t ht
    have hH := fun k : Fin 2 => h29 t ht.1 ht.2 k
    obtain ⟨hG0, hH0⟩ := hH 0
    obtain ⟨hG1, hH1⟩ := hH 1
    have hV : ∀ n, ‖Complex.I • pairKernelExt38 (kappaKernel38 (realSlice v) (gkMu v n : ℂ)) t - evec n t‖ ≤
        (2 + 2 * D) * (4 * Kdf C19 * g n + (2 * Kdf C19 + 2) * |ε n| + 2 * d n +
          (‖GDf (realSlice v) (gkMu v n : ℂ) t 0‖ + ‖GDf (realSlice v) (gkMu v n : ℂ) t 1‖) +
          (‖Gdf (realSlice v) (gkMu v n : ℂ) t 0 - leadf (gkMu v n : ℂ) t 0‖ +
            ‖Gdf (realSlice v) (gkMu v n : ℂ) t 1 - leadf (gkMu v n : ℂ) t 1‖)) := by
      intro n
      have hk : ∀ k : Fin 2, ‖(Complex.I • pairKernelExt38 (kappaKernel38 (realSlice v) (gkMu v n : ℂ)) t -
          evec n t) k‖ ≤ (2 + 2 * D) * (4 * (8 * (1 + D) ^ 4) * g n + (2 * (8 * (1 + D) ^ 4) + 2) * |ε n| +
            2 * d n + ‖GDf (realSlice v) (gkMu v n : ℂ) t k‖ +
            ‖Gdf (realSlice v) (gkMu v n : ℂ) t k - leadf (gkMu v n : ℂ) t k‖) := by
        intro k
        have := grad_term v n ht k D (1 + D) (g n) (d n) (by linarith) (hK n) (hdeq n).ge (hdle n) hD0
          (h20a n) (hEd _) (hgeq n).ge
        rw [hεeq n]; exact this
      have hKd : Kdf C19 = 8 * (1 + D) ^ 4 := rfl
      rw [hKd]
      have hR0 : 0 ≤ (2 + 2 * D) * (4 * (8 * (1 + D) ^ 4) * g n + (2 * (8 * (1 + D) ^ 4) + 2) * |ε n| + 2 * d n +
          (‖GDf (realSlice v) (gkMu v n : ℂ) t 0‖ + ‖GDf (realSlice v) (gkMu v n : ℂ) t 1‖) +
          (‖Gdf (realSlice v) (gkMu v n : ℂ) t 0 - leadf (gkMu v n : ℂ) t 0‖ +
            ‖Gdf (realSlice v) (gkMu v n : ℂ) t 1 - leadf (gkMu v n : ℂ) t 1‖)) := by
        have := hg0 n; have := hd0 n
        positivity
      refine (pi_norm_le_iff_of_nonneg hR0).2 (fun k => ?_)
      refine (hk k).trans ?_
      have hn1 := norm_nonneg (GDf (realSlice v) (gkMu v n : ℂ) t 0)
      have hn2 := norm_nonneg (GDf (realSlice v) (gkMu v n : ℂ) t 1)
      have hn3 := norm_nonneg (Gdf (realSlice v) (gkMu v n : ℂ) t 0 - leadf (gkMu v n : ℂ) t 0)
      have hn4 := norm_nonneg (Gdf (realSlice v) (gkMu v n : ℂ) t 1 - leadf (gkMu v n : ℂ) t 1)
      have hBs0 : 0 ≤ 2 + 2 * D := by linarith
      refine mul_le_mul_of_nonneg_left ?_ hBs0
      fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one] <;> linarith
    have hpg := part_grad (2 + 2 * D) (4 * Kdf C19) (2 * Kdf C19 + 2) (max C20 0) (max Cμ 0) (max C19 0)
      (max C29 0) (max C29 0) (max C29 0) (max C29 0) (by linarith)
      (by have : 0 ≤ Kdf C19 := by unfold Kdf; positivity
          positivity)
      (by have : 0 ≤ Kdf C19 := by unfold Kdf; positivity
          positivity)
      g (fun n => |ε n|) d (fun n => ‖GDf (realSlice v) (gkMu v n : ℂ) t 0‖)
      (fun n => ‖GDf (realSlice v) (gkMu v n : ℂ) t 1‖)
      (fun n => ‖Gdf (realSlice v) (gkMu v n : ℂ) t 0 - leadf (gkMu v n : ℂ) t 0‖)
      (fun n => ‖Gdf (realSlice v) (gkMu v n : ℂ) t 1 - leadf (gkMu v n : ℂ) t 1‖)
      (fun n => ‖Complex.I • pairKernelExt38 (kappaKernel38 (realSlice v) (gkMu v n : ℂ)) t - evec n t‖)
      hg0 (fun n => abs_nonneg _) hd0 (fun n => norm_nonneg _) (fun n => norm_nonneg _)
      (fun n => norm_nonneg _) (fun n => norm_nonneg _) (fun n => norm_nonneg _) hV
      (hg1.weak (le_max_left _ _)) (he1.weak (le_max_left _ _)) (hd1.weak (le_max_left _ _))
      (hG0.weak (le_max_left _ _)) (hG1.weak (le_max_left _ _))
      (hH0.weak (le_max_left _ _)) (hH1.weak (le_max_left _ _))
    refine SB.mono (fun n => ?_) (fun n => ?_) hpg
    · by_cases h : 0 < n.natAbs
      · rw [if_pos h]; exact sq_nonneg _
      · rw [if_neg h]
    · by_cases h : 0 < n.natAbs
      · rw [if_pos h]
      · rw [if_neg h]; exact sq_nonneg _

end

end NlsGge.Atomic.G1087S2.P9


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.Final

open Filter Topology NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38
  NlsGge.Atomic.G1087S2.P6 NlsGge.Atomic.G1087S2.P8 NlsGge.Atomic.G1087S2.P9

noncomputable section

theorem natAbs_lt_abs (N : ℕ) (n : ℤ) (h : N < n.natAbs) : (N : ℤ) < |n| := by
  rw [Int.abs_eq_natAbs]; exact_mod_cast h

theorem mu_tail (ψ : PotPair) (N₁ N₂ : ℕ) (μ : ℤ → ℂ)
    (hcnt : RootCountingAt38 (dirichletChar ψ) 1 N₂)
    (hμ : ∀ n : ℤ, N₁ < n.natAbs →
      μ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) ∧ dirichletChar ψ (μ n) = 0 ∧
        ∀ w ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4), dirichletChar ψ w = 0 → w = μ n)
    (n : ℤ) (hn : max N₁ N₂ < n.natAbs) : muSeq ψ n = μ n := by
  have hn1 : N₁ < n.natAbs := lt_of_le_of_lt (le_max_left _ _) hn
  have hn2 : N₂ < n.natAbs := lt_of_le_of_lt (le_max_right _ _) hn
  have he : muSeq ψ = criticalCandidate38 (dirichletChar ψ) N₂ := muSeq_eq_candidate38 ψ hcnt
  have hm := criticalCandidate_small_multiset38 hcnt (natAbs_lt_abs N₂ n hn2)
  have hmem : muSeq ψ n ∈ Lib.zeroMultiset (dirichletChar ψ) (Metric.ball (countingCenter38 n) (Real.pi / 4)) := by
    rw [← hm, he]; exact Multiset.mem_singleton_self _
  have := (NlsGge.Atomic.G1087S2.K43.K42.mem_zm_iff (dirichletChar ψ) hcnt.2.1 hcnt.2.2.1
    Metric.isBounded_ball).1 hmem
  obtain ⟨h1, h2, h3⟩ := hμ n hn1
  exact h3 _ this.1 this.2

theorem eps_l2 (v : PhysicalL2) (R1 : ℝ) (N₁ N₂ : ℕ) (C₁ : ℝ)
    (hdisp : ∀ n : ℤ, |gkMu v n - (n : ℝ) * Real.pi| ≤ R1)
    (μ : ℤ → ℂ)
    (hcnt : RootCountingAt38 (dirichletChar (realSlice v)) 1 N₂)
    (hμ : ∀ n : ℤ, N₁ < n.natAbs →
      μ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) ∧ dirichletChar (realSlice v) (μ n) = 0 ∧
        ∀ w ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4), dirichletChar (realSlice v) w = 0 → w = μ n)
    (hsum : SB (fun n : ℤ => if N₁ < n.natAbs then ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 else 0) C₁) :
    SB (fun n : ℤ => |gkMu v n - (n : ℝ) * Real.pi| ^ 2)
      (C₁ + ((Finset.Icc (-(max N₁ N₂ : ℕ) : ℤ) (max N₁ N₂ : ℕ)).card : ℝ) * R1 ^ 2) := by
  set N : ℕ := max N₁ N₂ with hN
  set s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hs
  have hR0 : 0 ≤ R1 := (abs_nonneg _).trans (hdisp 0)
  have hg : SB (fun n : ℤ => if n ∈ s then R1 ^ 2 else 0) ((s.card : ℝ) * R1 ^ 2) := by
    have hfin : ∀ b ∉ s, (fun n : ℤ => if n ∈ s then R1 ^ 2 else 0) b = 0 := by
      intro b hb; simp [hb]
    refine ⟨summable_of_ne_finset_zero hfin, ?_⟩
    rw [tsum_eq_sum hfin, Finset.sum_congr rfl (fun x hx => if_pos hx), Finset.sum_const, nsmul_eq_mul]
  have hadd := hsum.add hg
  refine SB.mono (fun n => sq_nonneg _) (fun n => ?_) hadd
  by_cases hn : N < n.natAbs
  · have hn1 : N₁ < n.natAbs := lt_of_le_of_lt (le_max_left _ _) hn
    have hmu := mu_tail (realSlice v) N₁ N₂ μ hcnt hμ n hn
    have hge : muSeq (realSlice v) n = (gkMu v n : ℂ) := muSeq_eq_gkMu38 v n
    have : ((gkMu v n : ℝ) : ℂ) = μ n := hge.symm.trans hmu
    have hn' : ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ = |gkMu v n - (n : ℝ) * Real.pi| := by
      rw [← this]
      have e : ((gkMu v n : ℝ) : ℂ) - (n : ℂ) * (Real.pi : ℂ) = (((gkMu v n - (n : ℝ) * Real.pi : ℝ)) : ℂ) := by
        push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs]
    have hns : n ∉ s := by
      rw [hs, Finset.mem_Icc, not_and_or]
      rcases Int.natAbs_eq n with h | h
      · right; omega
      · left; omega
    simp only [if_pos hn1, if_neg hns, add_zero, hn']
    exact le_rfl
  · have hns : n ∈ s := by
      rw [hs, Finset.mem_Icc]; omega
    simp only [if_pos hns]
    have hnn : (0 : ℝ) ≤ (if N₁ < n.natAbs then ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 else 0) := by
      split_ifs <;> positivity
    have := pow_le_pow_left₀ (abs_nonneg _) (hdisp n) 2
    linarith

end

end NlsGge.Atomic.G1087S2.Final


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.Final

open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.Pilot Filter Topology
  NlsGge.SpectralFoundations NlsGge.Atomic.G1087S2.P6 NlsGge.Atomic.G1087S2.P8 NlsGge.Atomic.G1087S2.P9

open scoped Matrix.Norms.L2Operator

noncomputable section

theorem G1087_real :
  (∀ u₀ : PhysicalL2, ∃ V : Set PhysicalL2, V ∈ nhds u₀ ∧ ∃ N : ℕ, ∃ C : ℝ, ∀ v ∈ V,
    (∀ n : ℤ, (normingFactor (realSlice v) (gkMu v n : ℂ)).im = 0 ∧ 0 < signedNorming38 v n) ∧
    Summable (fun n : ℤ => if N < n.natAbs then (realKappa38 v n) ^ 2 else 0) ∧
    (∑' n : ℤ, if N < n.natAbs then (realKappa38 v n) ^ 2 else 0) ≤ C ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      Summable (fun n : ℤ => if N < n.natAbs then
          ‖Complex.I • pairKernelExt38 (kappaKernel38 (realSlice v) (gkMu v n : ℂ)) t -
            (![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
              ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0] : Fin 2 → ℂ)‖ ^ 2
          else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then
          ‖Complex.I • pairKernelExt38 (kappaKernel38 (realSlice v) (gkMu v n : ℂ)) t -
            (![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
              ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0] : Fin 2 → ℂ)‖ ^ 2
          else 0) ≤ C)) := by
  intro u₀
  obtain ⟨V₁, hV₁o, hV₁m, N₁, C₁, hV₁⟩ := NlsGge.Atomic.G1087S2.K43.G1043_whole (realSlice u₀)
  obtain ⟨U₂, hU₂, N₂, hN₂⟩ := NlsGge.Atomic.G1087S2.K43.K42.dirichlet_counting_s3 (realSlice u₀)
  set R1 : ℝ := ‖u₀‖ + 1 with hR1
  set R0 : ℝ := 2 * R1 with hR0
  obtain ⟨C19, h19⟩ := NlsGge.Atomic.G1087S2.K29.K20.K19.G1019_whole R0 R1
  obtain ⟨C20, h20⟩ := NlsGge.Atomic.G1087S2.K29.K20.G1020_whole R0 R1
  obtain ⟨C29, h29⟩ := NlsGge.Atomic.G1087S2.K29.G1029_main R0 R1
  set N : ℕ := max N₁ N₂ with hN
  set Cμ : ℝ := C₁ + ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) * R1 ^ 2 with hCμ
  have hVm : ((realSlice ⁻¹' V₁) ∩ (realSlice ⁻¹' U₂) ∩ Metric.ball u₀ 1 : Set PhysicalL2) ∈ nhds u₀ := by
    refine Filter.inter_mem (Filter.inter_mem ?_ ?_) (Metric.ball_mem_nhds u₀ one_pos)
    · exact realSlice.continuous.continuousAt.preimage_mem_nhds (hV₁o.mem_nhds hV₁m)
    · exact realSlice.continuous.continuousAt.preimage_mem_nhds hU₂
  refine ⟨_, hVm, 0, max (CKf Cμ C19) (CGf Cμ C19 C20 C29), ?_⟩
  intro v hv
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  have hvn : ‖v‖ ≤ R1 := by
    have h1 : ‖v - u₀‖ < 1 := by simpa [dist_eq_norm] using hv3
    have h2 : ‖v‖ ≤ ‖v - u₀‖ + ‖u₀‖ := by simpa using norm_add_le (v - u₀) u₀
    rw [hR1]; linarith
  have hdisp : ∀ n : ℤ, |gkMu v n - (n : ℝ) * Real.pi| ≤ R1 :=
    fun n => (gkMu_global_displacement38 v n).trans hvn
  have hφ : Real.sqrt (‖(realSlice v).1‖ ^ 2 + ‖(realSlice v).2‖ ^ 2) ≤ R0 := by
    have h1 : ‖(realSlice v).1‖ = ‖v‖ := rfl
    have h2 : ‖(realSlice v).2‖ = ‖v‖ := starLp.norm_map v
    rw [h1, h2]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have : 0 ≤ ‖v‖ := norm_nonneg _
    rw [hR0]; nlinarith
  have hξ : ∀ n : ℤ, ‖((gkMu v n : ℝ) : ℂ) - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1 := by
    intro n
    have e : ((gkMu v n : ℝ) : ℂ) - (n : ℂ) * (Real.pi : ℂ) = (((gkMu v n - (n : ℝ) * Real.pi : ℝ)) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]; exact hdisp n
  obtain ⟨μ, hμp, hs1, hs2⟩ := hV₁ (realSlice v) hv1
  have hcnt := hN₂ (realSlice v) hv2
  have hμ : SB (fun n : ℤ => |gkMu v n - (n : ℝ) * Real.pi| ^ 2) Cμ :=
    eps_l2 v R1 N₁ N₂ C₁ hdisp μ hcnt hμp ⟨hs1, hs2⟩
  have h19v : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → SB (fun n : ℤ =>
      ‖(∑' m : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38 (realSlice v) (gkMu v n : ℂ) m t) -
        freeZsFundamentalComplex (gkMu v n : ℂ) t‖ ^ 2) C19 :=
    fun t h0 h1 => h19 (realSlice v) (fun n => (gkMu v n : ℂ)) hφ hξ t h0 h1
  have h20v := h20 (realSlice v) (fun n => (gkMu v n : ℂ)) hφ hξ 1 zero_le_one le_rfl
  have h29v : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k : Fin 2,
      SB (fun n : ℤ => ‖GDf (realSlice v) (gkMu v n : ℂ) t k‖ ^ 2) C29 ∧
      SB (fun n : ℤ => ‖Gdf (realSlice v) (gkMu v n : ℂ) t k - leadf (gkMu v n : ℂ) t k‖ ^ 2) C29 := by
    obtain ⟨-, -, -, h29'⟩ := h29 (realSlice v) (fun n => (gkMu v n : ℂ)) hφ hξ
    exact fun t h0 h1 k => h29' t h0 h1 k
  have hEd : ∀ z : ℂ, DifferentiableAt ℂ (fun w : ℂ => freeZsFundamentalComplex w 1) z :=
    fun z => (NlsGge.Atomic.G1087S2.K29.K20.differentiable_E 1) z
  obtain ⟨hA, hK, hG⟩ := per_v v Cμ C19 C20 C29 hEd hμ h19v h20v.1 h20v.2 h29v
  refine ⟨hA, hK.1, hK.2.trans (le_max_left _ _), fun t ht => ?_⟩
  have hGt := hG t ht
  exact ⟨hGt.1, hGt.2.trans (le_max_right _ _)⟩

end

end NlsGge.Atomic.G1087S2.Final



set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.U1

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38 Filter Topology

open scoped Matrix.Norms.L2Operator

noncomputable section

theorem exp_quarter_pi_lt_three : Real.exp (Real.pi / 4) < 3 := by
  have h1 : Real.pi / 4 < 1 := by linarith [Real.pi_lt_four]
  calc Real.exp (Real.pi / 4) < Real.exp 1 := Real.exp_lt_exp.mpr h1
    _ < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)

/-- (U1) uniform smallness of the monodromy error away from the origin, in a neighbourhood. -/
theorem eps_unif (φ₀ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ Λ : ℝ, ∀ ψ ∈ U, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, Λ < ‖z‖ →
      |z.im| ≤ Real.pi / 4 →
      ‖(∑' m : ℕ, potentialVolterraTerm38 ψ z m t) - freeZsFundamentalComplex z t‖ ≤ 3 * ε := by
  obtain ⟨U, hU, Λ, hΛ⟩ := NlsGge.Atomic.G1087S2.K43.K42.K17.G1017_whole φ₀ ε hε
  refine ⟨U, hU, Λ, fun ψ hψ t ht0 ht1 z hz hz2 => ?_⟩
  obtain ⟨-, h1, -⟩ := hΛ ψ hψ t ht0 ht1 z hz
  have hw : Real.exp (|z.im| * t) ≤ Real.exp (Real.pi / 4) := by
    apply Real.exp_le_exp.mpr
    have : |z.im| * t ≤ |z.im| := by nlinarith [abs_nonneg z.im]
    linarith
  have h2 : ‖(∑' m : ℕ, potentialVolterraTerm38 ψ z m t) - freeZsFundamentalComplex z t‖ ≤
      Real.exp (|z.im| * t) * ε := by
    have hpos : 0 < Real.exp (-|z.im| * t) := Real.exp_pos _
    have e : Real.exp (|z.im| * t) * Real.exp (-|z.im| * t) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (|z.im| * t)).le
    rw [← mul_assoc, e, one_mul] at this
    exact this
  calc _ ≤ Real.exp (|z.im| * t) * ε := h2
    _ ≤ Real.exp (Real.pi / 4) * ε := by gcongr
    _ ≤ 3 * ε := by
        have := exp_quarter_pi_lt_three
        nlinarith

end

end NlsGge.Atomic.G1087S2.U1


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.U2

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38

open scoped Matrix.Norms.L2Operator

noncomputable section

theorem sin_root_bound (ψ : PotPair) (z : ℂ) (h0 : dirichletChar ψ z = 0) :
    ‖Complex.sin z‖ ≤ 2 * ‖monodromyPair ψ z - freeZsFundamentalComplex z 1‖ := by
  rw [← freeE_eq]
  set D : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair ψ z - freeE z 1 with hD
  have hres := dirichlet_residual_eq38 ψ z
  rw [h0, zero_sub] at hres
  have hsz : Complex.sin z = -((D 1 0 + D 1 1 - D 0 0 - D 0 1) / (2 * Complex.I)) := by
    rw [← hres]; ring
  have hent : ∀ i j : Fin 2, ‖D i j‖ ≤ ‖D‖ := fun i j => NlsGge.Atomic.G1087S2.P3.entry_le_l2 D i j
  rw [hsz, norm_neg, norm_div, norm_mul, Complex.norm_two, Complex.norm_I, mul_one]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hh := norm_sub_le (D 1 0 + D 1 1 - D 0 0) (D 0 1)
  have hh' := norm_sub_le (D 1 0 + D 1 1) (D 0 0)
  have hh'' := norm_add_le (D 1 0) (D 1 1)
  have a1 := hent 1 0
  have a2 := hent 1 1
  have a3 := hent 0 0
  have a4 := hent 0 1
  nlinarith

theorem root_facts (ψ : PotPair) {z : ℂ} {n : ℤ}
    (hz : z ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4)) (h0 : dirichletChar ψ z = 0) :
    ‖Complex.sin z‖ ≤ 2 * ‖monodromyPair ψ z - freeZsFundamentalComplex z 1‖ ∧
    ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 10 * ‖monodromyPair ψ z - freeZsFundamentalComplex z 1‖ := by
  refine ⟨sin_root_bound ψ z h0, ?_⟩
  have h := NlsGge.Atomic.G1087S2.K43.root_displacement ψ hz h0
  rw [NlsGge.Atomic.G1087S2.P5.bridge1] at h
  have h10 : 0 ≤ 10 * ‖monodromyPair ψ z - freeZsFundamentalComplex z 1‖ := by positivity
  refine (sq_le_sq₀ (norm_nonneg _) h10).1 ?_
  calc ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 ≤ 100 * ‖monodromyPair ψ z - freeZsFundamentalComplex z 1‖ ^ 2 := h
    _ = (10 * ‖monodromyPair ψ z - freeZsFundamentalComplex z 1‖) ^ 2 := by ring

end

end NlsGge.Atomic.G1087S2.U2


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.U3

noncomputable section

/-- complex shifted lead term compared with the lattice lead term -/
theorem lead_diff_c (n : ℤ) (ε : ℂ) (hε : ‖ε‖ ≤ 1) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (ξ : ℂ)
    (hξ : ξ = (n : ℂ) * (Real.pi : ℂ) + ε) (k : Fin 2) :
    ‖(-1 : ℂ) ^ n * (![-Complex.exp (-(Complex.I * ξ * (1 - 2 * (t : ℂ)))),
           Complex.exp (Complex.I * ξ * (1 - 2 * (t : ℂ)))] : Fin 2 → ℂ) k -
      (![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
        ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0] : Fin 2 → ℂ) k‖ ≤ 2 * ‖ε‖ := by
  have hpi : (-1 : ℂ) ^ n = Complex.exp ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hpi' : (-1 : ℂ) ^ n = Complex.exp ((n : ℂ) * (-((Real.pi : ℂ) * Complex.I))) := by
    rw [Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  have hc : ‖(1 - 2 * (t : ℂ))‖ ≤ 1 := by
    have : (1 - 2 * (t : ℂ)) = (((1 - 2 * t : ℝ)) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hθ : ‖ε * (1 - 2 * (t : ℂ))‖ ≤ ‖ε‖ := by
    rw [norm_mul]
    calc ‖ε‖ * ‖(1 - 2 * (t : ℂ))‖ ≤ ‖ε‖ * 1 := by gcongr
      _ = ‖ε‖ := mul_one _
  have hexp1 : ‖Complex.I * (ε * (1 - 2 * (t : ℂ)))‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, one_mul]; exact hθ.trans hε
  have hE1 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  have hE2 : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  fin_cases k
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply, zero_sub]
    have e : (-1 : ℂ) ^ n * -Complex.exp (-(Complex.I * ξ * (1 - 2 * (t : ℂ)))) -
        -Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) =
        -(Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) *
          (Complex.exp (Complex.I * (-(ε * (1 - 2 * (t : ℂ))))) - 1)) := by
      rw [hpi, hξ, mul_neg, ← Complex.exp_add]
      have h2 : (n : ℂ) * ((Real.pi : ℂ) * Complex.I) + -(Complex.I * ((n : ℂ) * (Real.pi : ℂ) + ε) * (1 - 2 * (t : ℂ))) =
          2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) + Complex.I * (-(ε * (1 - 2 * (t : ℂ)))) := by
        ring
      rw [h2, Complex.exp_add]; ring
    rw [e, norm_neg, norm_mul, hE1, one_mul]
    have hx : ‖Complex.I * (-(ε * (1 - 2 * (t : ℂ))))‖ ≤ 1 := by rw [mul_neg, norm_neg]; exact hexp1
    refine (Complex.norm_exp_sub_one_le hx).trans ?_
    rw [mul_neg, norm_neg, norm_mul, Complex.norm_I, one_mul]
    linarith
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Pi.sub_apply, sub_zero, Matrix.cons_val_zero]
    have e : (-1 : ℂ) ^ n * Complex.exp (Complex.I * ξ * (1 - 2 * (t : ℂ))) -
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ)) =
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ)) *
          (Complex.exp (Complex.I * (ε * (1 - 2 * (t : ℂ)))) - 1) := by
      rw [hpi', hξ, ← Complex.exp_add]
      have h2 : (n : ℂ) * (-((Real.pi : ℂ) * Complex.I)) + Complex.I * ((n : ℂ) * (Real.pi : ℂ) + ε) * (1 - 2 * (t : ℂ)) =
          -(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ) + Complex.I * (ε * (1 - 2 * (t : ℂ))) := by
        ring
      rw [h2, Complex.exp_add]; ring
    rw [e, norm_mul, hE2, one_mul]
    refine (Complex.norm_exp_sub_one_le hexp1).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    linarith

/-- complex combination bound -/
theorem term_bound_c (S u s' : ℂ) (hSS : S * S = 1) (hSu : S * u = s') (hs' : ‖s' - 1‖ ≤ 1 / 2)
    (ud GD Gd lead dk e : ℂ) (Kd : ℝ) (hdk : ‖dk‖ ≤ Kd) (he : ‖e‖ = 1)
    (δ : ℝ) (hlead : ‖S * lead - e‖ ≤ δ) :
    ‖(2 / u) * (ud * dk + (GD + Gd) / 2) - e‖ ≤
      2 * (2 * ‖ud‖ * Kd + ‖GD‖ + ‖Gd - lead‖ + δ + ‖s' - 1‖) := by
  have hs1 : 1 / 2 ≤ ‖s'‖ := by
    have := norm_sub_norm_le (1 : ℂ) s'
    rw [norm_one, ← norm_neg (1 - s'), neg_sub] at this
    linarith
  have hs0 : s' ≠ 0 := by intro h; rw [h, norm_zero] at hs1; linarith
  have hu : u = S * s' := by
    calc u = (S * S) * u := by rw [hSS, one_mul]
      _ = S * (S * u) := by ring
      _ = S * s' := by rw [hSu]
  have hS0 : S ≠ 0 := by intro h; rw [h] at hSS; simp at hSS
  have hSn : ‖S‖ = 1 := by
    have h := congrArg norm hSS
    rw [norm_mul, norm_one] at h
    have : 0 ≤ ‖S‖ := norm_nonneg _
    nlinarith
  have hun : ‖u‖ = ‖s'‖ := by rw [hu, norm_mul, hSn, one_mul]
  have hu0 : u ≠ 0 := by rw [hu]; exact mul_ne_zero hS0 hs0
  have e1 : (2 / u) * (ud * dk + (GD + Gd) / 2) - e =
      (2 * ud / u) * dk + GD / u + (Gd - lead) / u + ((S * lead - e) / s' + e * (1 / s' - 1)) := by
    rw [hu]
    field_simp
    linear_combination (-lead) * hSS
  rw [e1]
  have hinv : 1 / ‖s'‖ ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hdiv : ∀ x : ℂ, ‖x / u‖ ≤ ‖x‖ * 2 := by
    intro x; rw [norm_div, hun, div_eq_mul_one_div]; gcongr
  have hdivs : ∀ x : ℂ, ‖x / s'‖ ≤ ‖x‖ * 2 := by
    intro x; rw [norm_div, div_eq_mul_one_div]; gcongr
  have hone : ‖(1 / s' - 1)‖ ≤ 2 * ‖s' - 1‖ := by
    have : (1 / s' - 1) = (1 - s') / s' := by field_simp
    rw [this, norm_div, ← norm_neg (1 - s'), neg_sub, div_eq_mul_one_div]
    nlinarith [norm_nonneg (s' - 1)]
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans hdk
  have hn1 : ‖(2 * ud / u) * dk‖ ≤ 2 * (2 * ‖ud‖ * Kd) := by
    rw [norm_mul]
    have h2 : ‖2 * ud / u‖ ≤ ‖2 * ud‖ * 2 := hdiv _
    have h3 : ‖2 * ud‖ = 2 * ‖ud‖ := by rw [norm_mul]; simp
    rw [h3] at h2
    calc ‖2 * ud / u‖ * ‖dk‖ ≤ (2 * ‖ud‖ * 2) * Kd := by gcongr
      _ = _ := by ring
  have hn2 : ‖GD / u‖ ≤ 2 * ‖GD‖ := by have := hdiv GD; linarith
  have hn3 : ‖(Gd - lead) / u‖ ≤ 2 * ‖Gd - lead‖ := by have := hdiv (Gd - lead); linarith
  have hn4 : ‖(S * lead - e) / s'‖ ≤ 2 * δ := by
    have := hdivs (S * lead - e)
    nlinarith [norm_nonneg (S * lead - e)]
  have hn5 : ‖e * (1 / s' - 1)‖ ≤ 2 * ‖s' - 1‖ := by
    rw [norm_mul, he, one_mul]; exact hone
  have h1 := norm_add_le ((2 * ud / u) * dk + GD / u + (Gd - lead) / u) ((S * lead - e) / s' + e * (1 / s' - 1))
  have h3 := norm_add_le ((2 * ud / u) * dk + GD / u) ((Gd - lead) / u)
  have h2 := norm_add_le ((2 * ud / u) * dk) (GD / u)
  have h45 := norm_add_le ((S * lead - e) / s') (e * (1 / s' - 1))
  nlinarith

end

end NlsGge.Atomic.G1087S2.U3


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.U4

open MeasureTheory NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38
  NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38 NlsGge.GK38.PoissonMixed38

open scoped Matrix.Norms.L2Operator

noncomputable section

theorem norm_E_entry_lt (z : ℂ) (hz : |z.im| ≤ Real.pi / 4) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖freeZsFundamentalComplex z t i j‖ < 3 := by
  have h3 := NlsGge.Atomic.G1087S2.U1.exp_quarter_pi_lt_three
  have hb : Real.exp (|z.im| * t) ≤ Real.exp (Real.pi / 4) := by
    apply Real.exp_le_exp.mpr
    have : |z.im| * t ≤ |z.im| := by nlinarith [abs_nonneg z.im, ht.1, ht.2]
    linarith
  rw [freeZsFundamentalComplex_entries]
  fin_cases i <;> fin_cases j <;> simp [Complex.norm_exp]
  · calc Real.exp (z.im * t) ≤ Real.exp (|z.im| * t) := by
          apply Real.exp_le_exp.mpr; nlinarith [le_abs_self z.im, ht.1]
      _ < 3 := lt_of_le_of_lt hb h3
  · calc Real.exp (-(z.im * t)) ≤ Real.exp (|z.im| * t) := by
          apply Real.exp_le_exp.mpr; nlinarith [neg_abs_le z.im, ht.1]
      _ < 3 := lt_of_le_of_lt hb h3

theorem state_small (φ : PotPair) (z : ℂ) (hz : |z.im| ≤ Real.pi / 4) (δ : ℝ) (hδ : δ ≤ 1 / 50)
    (hs : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ‖(∑' m : ℕ, potentialVolterraTerm38 φ z m t) - freeZsFundamentalComplex z t‖ ≤ δ) :
    ‖Q (state φ z ![1, 1]) - 2‖ ≤ 24 * δ + 8 * δ ^ 2 ∧ ∀ t : Set.Icc (0 : ℝ) 1, ∀ i j, ‖fundPair φ z t i j‖ ≤ 4 := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hs 0 ⟨le_rfl, zero_le_one⟩)
  -- pointwise decomposition
  have hdec : ∀ t : Set.Icc (0 : ℝ) 1, ∀ i j : Fin 2,
      fundPair φ z t i j = freeZsFundamentalComplex z t i j +
        ((∑' m : ℕ, potentialVolterraTerm38 φ z m t) - freeZsFundamentalComplex z t) i j := by
    intro t i j
    rw [← NlsGge.Atomic.G1087S2.P1.series_eq_fundPair φ z t.2 i j]
    simp
  have hA : ∀ t : Set.Icc (0 : ℝ) 1, ∀ i j : Fin 2,
      ‖((∑' m : ℕ, potentialVolterraTerm38 φ z m t) - freeZsFundamentalComplex z t) i j‖ ≤ δ :=
    fun t i j => (NlsGge.Atomic.G1087S2.P3.entry_le_l2 _ i j).trans (hs t t.2)
  refine ⟨?_, fun t i j => ?_⟩
  · -- the denominator
    have hint := (kernel_integrability (state φ z ![1, 1])).1
    have hpt : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖pairKernelExt38 (state φ z ![1, 1]) s 0 * pairKernelExt38 (state φ z ![1, 1]) s 1 - 1‖ ≤ 12 * δ + 4 * δ ^ 2 := by
      intro s hs'
      rw [pairKernelExt38_of_mem _ hs']
      obtain ⟨h0, h1⟩ := NlsGge.Atomic.G1087S2.P2.state_apply' φ z ⟨s, hs'⟩
      have hd : ∀ i j : Fin 2, fundPair φ z ⟨s, hs'⟩ i j = freeZsFundamentalComplex z s i j +
          ((∑' m : ℕ, potentialVolterraTerm38 φ z m s) - freeZsFundamentalComplex z s) i j :=
        fun i j => hdec ⟨s, hs'⟩ i j
      have hE01 : freeZsFundamentalComplex z s 0 1 = 0 := by rw [freeZsFundamentalComplex_entries]; simp
      have hE10 : freeZsFundamentalComplex z s 1 0 = 0 := by rw [freeZsFundamentalComplex_entries]; simp
      have hpq : freeZsFundamentalComplex z s 0 0 * freeZsFundamentalComplex z s 1 1 = 1 := by
        rw [freeZsFundamentalComplex_entries]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
      have hp := norm_E_entry_lt z hz s hs' 0 0
      have hq := norm_E_entry_lt z hz s hs' 1 1
      have a00 := hA ⟨s, hs'⟩ 0 0
      have a01 := hA ⟨s, hs'⟩ 0 1
      have a10 := hA ⟨s, hs'⟩ 1 0
      have a11 := hA ⟨s, hs'⟩ 1 1
      rw [h0, h1, hd 0 0, hd 0 1, hd 1 0, hd 1 1, hE01, hE10]
      set A := (∑' m : ℕ, potentialVolterraTerm38 φ z m s) - freeZsFundamentalComplex z s with hAdef
      set p := freeZsFundamentalComplex z s 0 0 with hpdef
      set q := freeZsFundamentalComplex z s 1 1 with hqdef
      have e : (p + A 0 0 + (0 + A 0 1)) * (0 + A 1 0 + (q + A 1 1)) - 1 =
          p * (A 1 0 + A 1 1) + q * (A 0 0 + A 0 1) + (A 0 0 + A 0 1) * (A 1 0 + A 1 1) := by
        linear_combination hpq
      rw [e]
      have b1 : ‖A 1 0 + A 1 1‖ ≤ 2 * δ := by
        calc _ ≤ ‖A 1 0‖ + ‖A 1 1‖ := norm_add_le _ _
          _ ≤ 2 * δ := by linarith
      have b2 : ‖A 0 0 + A 0 1‖ ≤ 2 * δ := by
        calc _ ≤ ‖A 0 0‖ + ‖A 0 1‖ := norm_add_le _ _
          _ ≤ 2 * δ := by linarith
      calc ‖p * (A 1 0 + A 1 1) + q * (A 0 0 + A 0 1) + (A 0 0 + A 0 1) * (A 1 0 + A 1 1)‖
          ≤ ‖p * (A 1 0 + A 1 1)‖ + ‖q * (A 0 0 + A 0 1)‖ + ‖(A 0 0 + A 0 1) * (A 1 0 + A 1 1)‖ := by
            calc _ ≤ ‖p * (A 1 0 + A 1 1) + q * (A 0 0 + A 0 1)‖ + ‖(A 0 0 + A 0 1) * (A 1 0 + A 1 1)‖ :=
                  norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_add_le _ _
        _ ≤ 3 * (2 * δ) + 3 * (2 * δ) + (2 * δ) * (2 * δ) := by
            rw [norm_mul, norm_mul, norm_mul]
            have n1 := norm_nonneg p
            have n2 := norm_nonneg q
            have n3 := norm_nonneg (A 1 0 + A 1 1)
            have n4 := norm_nonneg (A 0 0 + A 0 1)
            gcongr
        _ = 12 * δ + 4 * δ ^ 2 := by ring
    have hQ : Q (state φ z ![1, 1]) - 2 =
        2 * ∫ s in (0 : ℝ)..1, (pairKernelExt38 (state φ z ![1, 1]) s 0 *
          pairKernelExt38 (state φ z ![1, 1]) s 1 - 1) := by
      unfold Q
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
      simp
      ring
    rw [hQ, norm_mul, Complex.norm_two]
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun s => pairKernelExt38 (state φ z ![1, 1]) s 0 * pairKernelExt38 (state φ z ![1, 1]) s 1 - 1)
      (C := 12 * δ + 4 * δ ^ 2) (fun s hs => hpt s (by simpa [Set.uIoc_of_le zero_le_one] using
        (Set.Ioc_subset_Icc_self hs)))
    simp at hI
    linarith
  · rw [hdec t i j]
    calc _ ≤ ‖freeZsFundamentalComplex z t i j‖ + ‖((∑' m : ℕ, potentialVolterraTerm38 φ z m t) -
          freeZsFundamentalComplex z t) i j‖ := norm_add_le _ _
      _ ≤ 3 + 1 / 50 := add_le_add (norm_E_entry_lt z hz t t.2 i j).le ((hA t i j).trans hδ)
      _ ≤ 4 := by norm_num

theorem dir_bound_c (φ : PotPair) (z : ℂ) (hz : |z.im| ≤ Real.pi / 4) (δ : ℝ) (hδ : δ ≤ 1 / 50)
    (hs : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ‖(∑' m : ℕ, potentialVolterraTerm38 φ z m t) - freeZsFundamentalComplex z t‖ ≤ δ)
    (t : Set.Icc (0 : ℝ) 1) (k : Fin 2) :
    ‖dirEigenKernel38 φ z t k‖ ≤ 43 := by
  obtain ⟨hQ0, hK⟩ := state_small φ z hz δ hδ hs
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hs 0 ⟨le_rfl, zero_le_one⟩)
  have hQ : ‖Q (state φ z ![1, 1]) - 2‖ ≤ 1 / 2 := by nlinarith
  have hQn : 3 / 2 ≤ ‖Q (state φ z ![1, 1])‖ := by
    have := norm_sub_norm_le (2 : ℂ) (Q (state φ z ![1, 1]))
    rw [← norm_neg (2 - Q (state φ z ![1, 1])), neg_sub] at this
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have hu0 := NlsGge.Atomic.G1087S2.P2.state_upper φ z 4 hK t 0
  have hu1 := NlsGge.Atomic.G1087S2.P2.state_upper φ z 4 hK t 1
  have hsq : ‖(square (state φ z ![1, 1])) t k‖ ≤ 64 := by
    fin_cases k
    · simp only [square, starProd38, Fin.zero_eta]
      change ‖state φ z ![1, 1] t 1 * state φ z ![1, 1] t 1‖ ≤ _
      rw [norm_mul]; nlinarith [norm_nonneg (state φ z ![1, 1] t 1)]
    · simp only [square, starProd38, Fin.mk_one]
      change ‖state φ z ![1, 1] t 0 * state φ z ![1, 1] t 0‖ ≤ _
      rw [norm_mul]; nlinarith [norm_nonneg (state φ z ![1, 1] t 0)]
  simp only [dirEigenKernel38, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
  have hinv : ‖Q (state φ z ![1, 1])‖⁻¹ ≤ 2 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ‖Q (state φ z ![1, 1])‖⁻¹ * ‖(square (state φ z ![1, 1])) t k‖ ≤ (2 / 3) * 64 := by gcongr
    _ ≤ 43 := by norm_num

end

end NlsGge.Atomic.G1087S2.U4


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.U5a

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38

open scoped Matrix.Norms.L2Operator

noncomputable section

theorem cos_sub_one_le (ε : ℂ) (h : ‖ε‖ ≤ 1) : ‖Complex.cos ε - 1‖ ≤ 2 * ‖ε‖ := by
  have e : Complex.cos ε - 1 = ((Complex.exp (ε * Complex.I) - 1) + (Complex.exp (-ε * Complex.I) - 1)) / 2 := by
    rw [Complex.cos]; ring
  have h1 : ‖ε * Complex.I‖ ≤ 1 := by rw [norm_mul, Complex.norm_I, mul_one]; exact h
  have h2 : ‖-ε * Complex.I‖ ≤ 1 := by rw [neg_mul, norm_neg]; exact h1
  have b1 := Complex.norm_exp_sub_one_le h1
  have b2 := Complex.norm_exp_sub_one_le h2
  rw [norm_mul, Complex.norm_I, mul_one] at b1
  rw [norm_mul, norm_neg, Complex.norm_I, mul_one] at b2
  rw [e, norm_div]
  have h2' : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2', div_le_iff₀ (by norm_num)]
  calc ‖(Complex.exp (ε * Complex.I) - 1) + (Complex.exp (-ε * Complex.I) - 1)‖
      ≤ ‖Complex.exp (ε * Complex.I) - 1‖ + ‖Complex.exp (-ε * Complex.I) - 1‖ := norm_add_le _ _
    _ ≤ 2 * ‖ε‖ * 2 := by linarith

/-- `s' = (-1)^n u(z)` is close to one when `z` is close to `n π` and `M - E` is small. -/
theorem sprime (φ : PotPair) (z : ℂ) (n : ℤ) (d : ℝ)
    (hd : ‖monodromyPair φ z - freeZsFundamentalComplex z 1‖ ≤ d) (hε : ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1) :
    ‖(-1 : ℂ) ^ n * normingFactor φ z - 1‖ ≤ 2 * d + 2 * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := by
  set M := monodromyPair φ z with hM
  set E := freeZsFundamentalComplex z 1 with hE
  set A := M - E with hAdef
  have hA : ∀ i j, ‖A i j‖ ≤ d := fun i j => (NlsGge.Atomic.G1087S2.P3.entry_le_l2 A i j).trans hd
  have hEmat : E = !![Complex.exp (-(Complex.I * z * ((1 : ℝ) : ℂ))), 0;
      0, Complex.exp (Complex.I * z * ((1 : ℝ) : ℂ))] := freeZsFundamentalComplex_entries _ _
  have hMij : ∀ i j, M i j = E i j + A i j := fun i j => by simp [hAdef]
  have hE01 : E 0 1 = 0 := by rw [hEmat]; simp
  have hE10 : E 1 0 = 0 := by rw [hEmat]; simp
  have hcosE : E 0 0 + E 1 1 = 2 * Complex.cos z := by
    rw [hEmat, Complex.two_cos]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_one, mul_one]
    rw [add_comm]; congr 2 <;> ring
  have hB : ‖(A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2‖ ≤ 2 * d := by
    have h4 : ‖A 0 0 + A 0 1 + A 1 0 + A 1 1‖ ≤ 4 * d := by
      calc _ ≤ ‖A 0 0 + A 0 1 + A 1 0‖ + ‖A 1 1‖ := norm_add_le _ _
        _ ≤ (‖A 0 0 + A 0 1‖ + ‖A 1 0‖) + ‖A 1 1‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ((‖A 0 0‖ + ‖A 0 1‖) + ‖A 1 0‖) + ‖A 1 1‖ := by gcongr; exact norm_add_le _ _
        _ ≤ 4 * d := by linarith [hA 0 0, hA 0 1, hA 1 0, hA 1 1]
    rw [norm_div]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this, div_le_iff₀ (by norm_num)]
    linarith
  have hu : normingFactor φ z = Complex.cos z + (A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2 := by
    unfold normingFactor
    change (M 0 0 + M 0 1 + M 1 0 + M 1 1) / 2 = _
    rw [hMij 0 0, hMij 0 1, hMij 1 0, hMij 1 1, hE01, hE10]
    have : E 0 0 + E 1 1 = 2 * Complex.cos z := hcosE
    linear_combination this / 2
  -- cos z = (-1)^n cos ε
  set ε : ℂ := z - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have hcos : (-1 : ℂ) ^ n * Complex.cos z = Complex.cos ε := by
    have hz : z = ε + ((n * Real.pi : ℝ) : ℂ) := by simp only [hεdef]; push_cast; ring
    have h1 : Complex.cos ((n * Real.pi : ℝ) : ℂ) = (-1 : ℂ) ^ n := by
      rw [← Complex.ofReal_cos, Real.cos_int_mul_pi]
      simp
    have h2 : Complex.sin ((n * Real.pi : ℝ) : ℂ) = 0 := by
      rw [← Complex.ofReal_sin, Real.sin_int_mul_pi]; simp
    rw [hz, Complex.cos_add, h1, h2, mul_zero, sub_zero]
    have hh := NlsGge.Atomic.G1087S2.P3.neg_one_zpow_mul_self n
    calc (-1 : ℂ) ^ n * (Complex.cos ε * (-1 : ℂ) ^ n) = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * Complex.cos ε := by ring
      _ = _ := by rw [hh, one_mul]
  have hsm1 : (-1 : ℂ) ^ n * normingFactor φ z - 1 =
      (Complex.cos ε - 1) + (-1 : ℂ) ^ n * ((A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2) := by
    rw [hu]
    have e : (-1 : ℂ) ^ n * (Complex.cos z + (A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2) - 1 =
        ((-1 : ℂ) ^ n * Complex.cos z - 1) + (-1 : ℂ) ^ n * ((A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2) := by ring
    rw [e, hcos]
  rw [hsm1]
  calc _ ≤ ‖Complex.cos ε - 1‖ + ‖(-1 : ℂ) ^ n * ((A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2)‖ := norm_add_le _ _
    _ ≤ 2 * ‖ε‖ + 2 * d := by
      gcongr
      · exact cos_sub_one_le ε hε
      · rw [norm_mul]
        have : ‖(-1 : ℂ) ^ n‖ = 1 := by simp
        rw [this, one_mul]; exact hB
    _ = _ := by ring

end

end NlsGge.Atomic.G1087S2.U5a


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.U5b

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38 NlsGge.Atomic.G1087S2.P6

open scoped Matrix.Norms.L2Operator

noncomputable section

theorem grad_term_c (φ : PotPair) (z : ℂ) (n : ℤ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : Fin 2) (d g : ℝ)
    (hd : ‖monodromyPair φ z - freeZsFundamentalComplex z 1‖ ≤ d) (hd0 : d ≤ 3 / 200)
    (hroot : dirichletChar φ z = 0) (hball : z ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4))
    (hsm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ‖(∑' m : ℕ, potentialVolterraTerm38 φ z m t) - freeZsFundamentalComplex z t‖ ≤ 3 / 200)
    (hdiff : DifferentiableAt ℂ (fun w => monodromyPair φ w) z)
    (hEd : DifferentiableAt ℂ (fun w => freeZsFundamentalComplex w 1) z)
    (hg : ‖deriv (fun w => monodromyPair φ w) z - deriv (fun w => freeZsFundamentalComplex w 1) z‖ ≤ g) :
    ‖(Complex.I • pairKernelExt38 (kappaKernel38 φ z) t - evec n t) k‖ ≤
      2 * (2 * (2 * g + 2 * d) * 43 + ‖GDf φ z t k‖ + ‖Gdf φ z t k - leadf z t k‖ + 2 * (10 * d) + 22 * d) := by
  obtain ⟨hsin, heps⟩ := NlsGge.Atomic.G1087S2.U2.root_facts φ hball hroot
  have hd00 : 0 ≤ d := (norm_nonneg _).trans hd
  have heps1 : ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 := by linarith
  have hs1 := NlsGge.Atomic.G1087S2.U5a.sprime φ z n d hd heps1
  have hs1' : ‖(-1 : ℂ) ^ n * normingFactor φ z - 1‖ ≤ 22 * d := by linarith
  have hs12 : ‖(-1 : ℂ) ^ n * normingFactor φ z - 1‖ ≤ 1 / 2 := by linarith
  have him : |z.im| ≤ Real.pi / 4 := by
    have h1 : (z - (n : ℂ) * (Real.pi : ℂ)).im = z.im := by simp
    have h2 := Complex.abs_im_le_norm (z - (n : ℂ) * (Real.pi : ℂ))
    rw [h1] at h2
    linarith [Real.pi_gt_three]
  have kc : Complex.I * pairKernelExt38 (kappaKernel38 φ z) t k =
      (2 / normingFactor φ z) * (normingSpectral38 φ z *
        (Complex.I * pairKernelExt38 (dirEigenKernel38 φ z) t k) +
        (GDf φ z t k + Gdf φ z t k) / 2) := NlsGge.Atomic.G1087S2.P1.kappa_comp φ z ht k
  have comp : (Complex.I • pairKernelExt38 (kappaKernel38 φ z) t - evec n t) k =
      Complex.I * pairKernelExt38 (kappaKernel38 φ z) t k - evec n t k := by
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hξ : z = (n : ℂ) * (Real.pi : ℂ) + (z - (n : ℂ) * (Real.pi : ℂ)) := by ring
  have hlead := NlsGge.Atomic.G1087S2.U3.lead_diff_c n (z - (n : ℂ) * (Real.pi : ℂ)) heps1 t ht z hξ k
  have hdk : ‖Complex.I * pairKernelExt38 (dirEigenKernel38 φ z) t k‖ ≤ 43 := by
    rw [norm_mul, Complex.norm_I, one_mul, pairKernelExt38_of_mem _ ht]
    exact NlsGge.Atomic.G1087S2.U4.dir_bound_c φ z him (3 / 200) (by norm_num) hsm ⟨t, ht⟩ k
  have hSS : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := NlsGge.Atomic.G1087S2.P3.neg_one_zpow_mul_self n
  have key := NlsGge.Atomic.G1087S2.U3.term_bound_c ((-1 : ℂ) ^ n) (normingFactor φ z)
    ((-1 : ℂ) ^ n * normingFactor φ z) hSS rfl hs12 (normingSpectral38 φ z) (GDf φ z t k) (Gdf φ z t k)
    (leadf z t k) (Complex.I * pairKernelExt38 (dirEigenKernel38 φ z) t k) (evec n t k) 43 hdk
    (norm_evec n t k) (2 * ‖z - (n : ℂ) * (Real.pi : ℂ)‖) hlead
  rw [comp, kc]
  have hud : ‖normingSpectral38 φ z‖ ≤ 2 * g + 2 * d := by
    have h1 := NlsGge.Atomic.G1087S2.P3.ud_bound φ z hdiff hEd g hg
    calc ‖normingSpectral38 φ z‖ = ‖(normingSpectral38 φ z + Complex.sin z) - Complex.sin z‖ := by ring_nf
      _ ≤ ‖normingSpectral38 φ z + Complex.sin z‖ + ‖Complex.sin z‖ := norm_sub_le _ _
      _ ≤ 2 * g + 2 * d := by linarith
  refine key.trans ?_
  have : 2 * ‖normingSpectral38 φ z‖ * 43 + ‖GDf φ z t k‖ + ‖Gdf φ z t k - leadf z t k‖ +
      2 * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ + ‖(-1 : ℂ) ^ n * normingFactor φ z - 1‖ ≤
      2 * (2 * g + 2 * d) * 43 + ‖GDf φ z t k‖ + ‖Gdf φ z t k - leadf z t k‖ + 2 * (10 * d) + 22 * d := by
    have h3 : 2 * ‖normingSpectral38 φ z‖ * 43 ≤ 2 * (2 * g + 2 * d) * 43 := by gcongr
    linarith
  linarith

end

end NlsGge.Atomic.G1087S2.U5b


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.U5c

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38 NlsGge.Atomic.G1087S2.P6 NlsGge.Atomic.G1087S2.P8

open scoped Matrix.Norms.L2Operator

noncomputable section

def CGc (C19 C20 C29 : ℝ) : ℝ :=
  7 * 2 ^ 2 * (172 ^ 2 * max C20 0 + 212 ^ 2 * max C19 0 + 4 * max C19 0 + max C29 0 + max C29 0 +
    max C29 0 + max C29 0)

theorem per_phi_c (φ : PotPair) (N : ℕ) (ξ : ℤ → ℂ) (C19 C20 C29 : ℝ)
    (hEd : ∀ z : ℂ, DifferentiableAt ℂ (fun w : ℂ => freeZsFundamentalComplex w 1) z)
    (hroot : ∀ n : ℤ, N < n.natAbs → dirichletChar φ (ξ n) = 0 ∧
      ξ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4))
    (hsm : ∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖ ≤ 3 / 200)
    (h19 : SB (fun n : ℤ => ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m 1) -
      freeZsFundamentalComplex (ξ n) 1‖ ^ 2) C19)
    (h20a : ∀ n : ℤ, DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1) (ξ n))
    (h20b : SB (fun n : ℤ => ‖deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1) (ξ n) -
      deriv (fun w : ℂ => freeZsFundamentalComplex w 1) (ξ n)‖ ^ 2) C20)
    (h29 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k : Fin 2,
      SB (fun n : ℤ => ‖GDf φ (ξ n) t k‖ ^ 2) C29 ∧
      SB (fun n : ℤ => ‖Gdf φ (ξ n) t k - leadf (ξ n) t k‖ ^ 2) C29) :
    (∀ n : ℤ, N < n.natAbs → parity n * normingFactor φ (ξ n) ∈ Complex.slitPlane) ∧
    SB (fun n : ℤ => if N < n.natAbs then ‖2 * Complex.log (parity n * normingFactor φ (ξ n))‖ ^ 2 else 0)
      (4356 * max C19 0) ∧
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      SB (fun n : ℤ => if N < n.natAbs then
        ‖Complex.I • pairKernelExt38 (kappaKernel38 φ (ξ n)) t - evec n t‖ ^ 2 else 0) (CGc C19 C20 C29) := by
  have hbr := NlsGge.Atomic.G1087S2.P5.bridge1 φ
  have e2 : (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1) = fun w : ℂ => monodromyPair φ w :=
    funext hbr
  rw [e2] at h20a h20b
  obtain ⟨d, hdeq⟩ : ∃ d : ℤ → ℝ, ∀ n, d n = ‖monodromyPair φ (ξ n) - freeZsFundamentalComplex (ξ n) 1‖ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨g, hgeq⟩ : ∃ g : ℤ → ℝ, ∀ n, g n = ‖deriv (fun w : ℂ => monodromyPair φ w) (ξ n) -
      deriv (fun w : ℂ => freeZsFundamentalComplex w 1) (ξ n)‖ := ⟨_, fun _ => rfl⟩
  have hd1 : SB (fun n : ℤ => d n ^ 2) C19 := by
    have e : (fun n : ℤ => ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m 1) -
        freeZsFundamentalComplex (ξ n) 1‖ ^ 2) = fun n : ℤ => d n ^ 2 := by
      funext n; rw [hdeq n, hbr]
    rw [e] at h19; exact h19
  have hg1 : SB (fun n : ℤ => g n ^ 2) C20 := by
    have e : (fun n : ℤ => ‖deriv (fun w : ℂ => monodromyPair φ w) (ξ n) -
        deriv (fun w : ℂ => freeZsFundamentalComplex w 1) (ξ n)‖ ^ 2) = fun n : ℤ => g n ^ 2 := by
      funext n; rw [hgeq n]
    rw [e] at h20b; exact h20b
  have hd0 : ∀ n, 0 ≤ d n := fun n => by rw [hdeq n]; exact norm_nonneg _
  have hg0 : ∀ n, 0 ≤ g n := fun n => by rw [hgeq n]; exact norm_nonneg _
  have hdsm : ∀ n : ℤ, N < n.natAbs → d n ≤ 3 / 200 := by
    intro n hn
    have := hsm n hn 1 ⟨zero_le_one, le_rfl⟩
    rw [hbr] at this
    rw [hdeq n]; exact this
  -- facts for large indices
  have hfacts : ∀ n : ℤ, N < n.natAbs →
      ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 10 * d n ∧ ‖(-1 : ℂ) ^ n * normingFactor φ (ξ n) - 1‖ ≤ 22 * d n := by
    intro n hn
    obtain ⟨h0, hb⟩ := hroot n hn
    obtain ⟨-, heps⟩ := NlsGge.Atomic.G1087S2.U2.root_facts φ hb h0
    have hdn := hdsm n hn
    have heps' : ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 10 * d n := by rw [hdeq n]; exact heps
    have heps1 : ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 := by linarith [hd0 n]
    have := NlsGge.Atomic.G1087S2.U5a.sprime φ (ξ n) n (d n) (hdeq n).ge heps1
    exact ⟨heps', by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨-, hs⟩ := hfacts n hn
    have hd := hdsm n hn
    have h12 : ‖(-1 : ℂ) ^ n * normingFactor φ (ξ n) - 1‖ ≤ 1 / 2 := by linarith
    have hre : |((-1 : ℂ) ^ n * normingFactor φ (ξ n) - 1).re| ≤ 1 / 2 :=
      (Complex.abs_re_le_norm _).trans h12
    rw [Complex.mem_slitPlane_iff]
    left
    have : (((-1 : ℂ) ^ n * normingFactor φ (ξ n)) - 1).re = ((-1 : ℂ) ^ n * normingFactor φ (ξ n)).re - 1 := by simp
    rw [this] at hre
    have := (abs_le.mp hre).1
    change 0 < ((-1 : ℂ) ^ n * normingFactor φ (ξ n)).re
    linarith
  · have hmaj : SB (fun n : ℤ => 4356 * d n ^ 2) (4356 * max C19 0) :=
      (hd1.weak (le_max_left _ _)).smul 4356 (by norm_num)
    refine SB.mono (fun n => ?_) (fun n => ?_) hmaj
    · split_ifs <;> positivity
    · by_cases hn : N < n.natAbs
      · rw [if_pos hn]
        obtain ⟨-, hs⟩ := hfacts n hn
        have hd := hdsm n hn
        have h12 : ‖(-1 : ℂ) ^ n * normingFactor φ (ξ n) - 1‖ ≤ 1 / 2 := by linarith
        have hlog : ‖Complex.log (1 + ((-1 : ℂ) ^ n * normingFactor φ (ξ n) - 1))‖ ≤
            (3 / 2) * ‖(-1 : ℂ) ^ n * normingFactor φ (ξ n) - 1‖ := Complex.norm_log_one_add_half_le_self h12
        rw [add_sub_cancel] at hlog
        have hp : parity n = (-1 : ℂ) ^ n := rfl
        rw [hp]
        have h2 : ‖2 * Complex.log ((-1 : ℂ) ^ n * normingFactor φ (ξ n))‖ ≤ 66 * d n := by
          rw [norm_mul]
          have : ‖(2 : ℂ)‖ = 2 := by simp
          rw [this]
          nlinarith [norm_nonneg (Complex.log ((-1 : ℂ) ^ n * normingFactor φ (ξ n)))]
        calc ‖2 * Complex.log ((-1 : ℂ) ^ n * normingFactor φ (ξ n))‖ ^ 2 ≤ (66 * d n) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h2 2
          _ = 4356 * d n ^ 2 := by ring
      · rw [if_neg hn]; positivity
  · intro t ht
    have hH := fun k : Fin 2 => h29 t ht.1 ht.2 k
    obtain ⟨hG0, hH0⟩ := hH 0
    obtain ⟨hG1, hH1⟩ := hH 1
    obtain ⟨V, hVdef⟩ : ∃ V : ℤ → ℝ, ∀ n, V n = if N < n.natAbs then
        ‖Complex.I • pairKernelExt38 (kappaKernel38 φ (ξ n)) t - evec n t‖ else 0 := ⟨_, fun _ => rfl⟩
    have hV : ∀ n, V n ≤ 2 * (172 * g n + 212 * d n + 2 * d n +
        (‖GDf φ (ξ n) t 0‖ + ‖GDf φ (ξ n) t 1‖) +
        (‖Gdf φ (ξ n) t 0 - leadf (ξ n) t 0‖ + ‖Gdf φ (ξ n) t 1 - leadf (ξ n) t 1‖)) := by
      intro n
      have hn0 := norm_nonneg (GDf φ (ξ n) t 0)
      have hn1 := norm_nonneg (GDf φ (ξ n) t 1)
      have hn2 := norm_nonneg (Gdf φ (ξ n) t 0 - leadf (ξ n) t 0)
      have hn3 := norm_nonneg (Gdf φ (ξ n) t 1 - leadf (ξ n) t 1)
      have hR0 : 0 ≤ 2 * (172 * g n + 212 * d n + 2 * d n +
          (‖GDf φ (ξ n) t 0‖ + ‖GDf φ (ξ n) t 1‖) +
          (‖Gdf φ (ξ n) t 0 - leadf (ξ n) t 0‖ + ‖Gdf φ (ξ n) t 1 - leadf (ξ n) t 1‖)) := by
        have := hg0 n; have := hd0 n
        positivity
      rw [hVdef n]
      by_cases hn : N < n.natAbs
      · rw [if_pos hn]
        obtain ⟨h0, hb⟩ := hroot n hn
        refine (pi_norm_le_iff_of_nonneg hR0).2 (fun k => ?_)
        have hk := NlsGge.Atomic.G1087S2.U5b.grad_term_c φ (ξ n) n ht k (d n) (g n) (hdeq n).ge (hdsm n hn) h0 hb
          (hsm n hn) (h20a n) (hEd _) (hgeq n).ge
        refine hk.trans ?_
        fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one] <;> linarith
      · rw [if_neg hn]; exact hR0
    have hV0 : ∀ n, 0 ≤ V n := fun n => by rw [hVdef n]; split_ifs <;> positivity
    have hpg := part_grad 2 172 212 (max C20 0) (max C19 0) (max C19 0) (max C29 0) (max C29 0) (max C29 0)
      (max C29 0) (by norm_num) (by norm_num) (by norm_num)
      g d d (fun n => ‖GDf φ (ξ n) t 0‖) (fun n => ‖GDf φ (ξ n) t 1‖)
      (fun n => ‖Gdf φ (ξ n) t 0 - leadf (ξ n) t 0‖) (fun n => ‖Gdf φ (ξ n) t 1 - leadf (ξ n) t 1‖) V
      hg0 hd0 hd0 (fun n => norm_nonneg _) (fun n => norm_nonneg _) (fun n => norm_nonneg _)
      (fun n => norm_nonneg _) hV0 hV
      (hg1.weak (le_max_left _ _)) (hd1.weak (le_max_left _ _)) (hd1.weak (le_max_left _ _))
      (hG0.weak (le_max_left _ _)) (hG1.weak (le_max_left _ _))
      (hH0.weak (le_max_left _ _)) (hH1.weak (le_max_left _ _))
    refine SB.mono (fun n => ?_) (fun n => ?_) hpg
    · split_ifs <;> positivity
    · rw [hVdef n]; split_ifs <;> simp

end

end NlsGge.Atomic.G1087S2.U5c


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.Uniform

open Filter Topology NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38
  NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- For `N₂ < |n|`, the canonical Dirichlet label is the root in the disc `D_n`. -/
theorem muSeq_root_ball (ψ : PotPair) (N₂ : ℕ) (hcnt : RootCountingAt38 (dirichletChar ψ) 1 N₂)
    (n : ℤ) (hn : N₂ < n.natAbs) :
    muSeq ψ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) ∧ dirichletChar ψ (muSeq ψ n) = 0 := by
  have hn' : (N₂ : ℤ) < |n| := by rw [Int.abs_eq_natAbs]; exact_mod_cast hn
  have he : muSeq ψ = criticalCandidate38 (dirichletChar ψ) N₂ := muSeq_eq_candidate38 ψ hcnt
  have hm := criticalCandidate_small_multiset38 hcnt hn'
  have hmem : muSeq ψ n ∈ Lib.zeroMultiset (dirichletChar ψ)
      (Metric.ball (countingCenter38 n) (Real.pi / 4)) := by
    rw [← hm, he]; exact Multiset.mem_singleton_self _
  exact (NlsGge.Atomic.G1087S2.K43.K42.mem_zm_iff (dirichletChar ψ) hcnt.2.1 hcnt.2.2.1
    Metric.isBounded_ball).1 hmem

/-- (U1+U2 public) Uniform smallness of the monodromy error at the Dirichlet roots `μ_n(ψ)` for `|n| > N`,
on a neighbourhood of `φ₀`, for every time `t ∈ [0,1]`. -/
theorem err_small (φ₀ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, ∀ ψ ∈ V, ∀ n : ℤ, N < n.natAbs →
      muSeq ψ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) ∧ dirichletChar ψ (muSeq ψ n) = 0 ∧
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        ‖(∑' m : ℕ, potentialVolterraTerm38 ψ (muSeq ψ n) m t) - freeZsFundamentalComplex (muSeq ψ n) t‖ ≤ ε := by
  obtain ⟨U₂, hU₂, N₂, hN₂⟩ := NlsGge.Atomic.G1087S2.K43.K42.dirichlet_counting_s3 φ₀
  obtain ⟨U₃, hU₃, Λ, hΛ⟩ := NlsGge.Atomic.G1087S2.U1.eps_unif φ₀ (ε / 3) (by positivity)
  refine ⟨U₂ ∩ U₃, Filter.inter_mem hU₂ hU₃, max N₂ ⌈Λ / Real.pi⌉₊, ?_⟩
  intro ψ hψ n hn
  obtain ⟨h2, h3⟩ := hψ
  have hn2 : N₂ < n.natAbs := lt_of_le_of_lt (le_max_left _ _) hn
  have hn3 : ⌈Λ / Real.pi⌉₊ < n.natAbs := lt_of_le_of_lt (le_max_right _ _) hn
  obtain ⟨hb, h0⟩ := muSeq_root_ball ψ N₂ (hN₂ ψ h2) n hn2
  refine ⟨hb, h0, fun t ht => ?_⟩
  have hd : ‖muSeq ψ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hb
  have him : |(muSeq ψ n).im| ≤ Real.pi / 4 := by
    have h1 : (muSeq ψ n - (n : ℂ) * (Real.pi : ℂ)).im = (muSeq ψ n).im := by simp
    have h2 := Complex.abs_im_le_norm (muSeq ψ n - (n : ℂ) * (Real.pi : ℂ))
    rw [h1] at h2; linarith
  have hz : Λ < ‖muSeq ψ n‖ := by
    have hnn : ‖(n : ℂ) * (Real.pi : ℂ)‖ = (n.natAbs : ℝ) * Real.pi := by
      rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      simp [Int.cast_abs]
    have h1 : ‖(n : ℂ) * (Real.pi : ℂ)‖ ≤ ‖muSeq ψ n‖ + ‖muSeq ψ n - (n : ℂ) * (Real.pi : ℂ)‖ := by
      calc ‖(n : ℂ) * (Real.pi : ℂ)‖ = ‖muSeq ψ n - (muSeq ψ n - (n : ℂ) * (Real.pi : ℂ))‖ := by ring_nf
        _ ≤ ‖muSeq ψ n‖ + ‖muSeq ψ n - (n : ℂ) * (Real.pi : ℂ)‖ := norm_sub_le _ _
    have h2 : Λ / Real.pi ≤ (⌈Λ / Real.pi⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈Λ / Real.pi⌉₊ : ℝ) + 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast hn3
    have h4 : Λ ≤ Real.pi * ((n.natAbs : ℝ) - 1) := by
      have := (div_le_iff₀ Real.pi_pos).mp (h2.trans (by linarith : (⌈Λ / Real.pi⌉₊ : ℝ) ≤ (n.natAbs : ℝ) - 1))
      linarith
    rw [hnn] at h1
    nlinarith [Real.pi_pos]
  have := hΛ ψ h3 t ht.1 ht.2 (muSeq ψ n) hz him
  linarith

/-- the labels are close to the lattice points, uniformly -/
theorem mu_small (φ₀ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, ∀ ψ ∈ V, ∀ n : ℤ, N < n.natAbs →
      ‖muSeq ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ ε := by
  obtain ⟨V, hV, N, h⟩ := err_small φ₀ (ε / 10) (by positivity)
  refine ⟨V, hV, N, fun ψ hψ n hn => ?_⟩
  obtain ⟨hb, h0, hs⟩ := h ψ hψ n hn
  obtain ⟨-, heps⟩ := NlsGge.Atomic.G1087S2.U2.root_facts ψ hb h0
  have h1 := hs 1 ⟨zero_le_one, le_rfl⟩
  rw [NlsGge.Atomic.G1087S2.P5.bridge1] at h1
  linarith

/-- uniform smallness of `Q_n - 2` (the denominator of the Dirichlet-eigenfunction gradient) -/
theorem Q_small (φ₀ : PotPair) (η : ℝ) (hη : 0 < η) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, ∀ ψ ∈ V, ∀ n : ℤ, N < n.natAbs →
      ‖Q (state ψ (muSeq ψ n) ![1, 1]) - 2‖ ≤ η := by
  set δ : ℝ := min (1 / 50) (η / 25) with hδ
  have hδp : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨V, hV, N, h⟩ := err_small φ₀ δ hδp
  refine ⟨V, hV, N, fun ψ hψ n hn => ?_⟩
  obtain ⟨hb, h0, hs⟩ := h ψ hψ n hn
  have him : |(muSeq ψ n).im| ≤ Real.pi / 4 := by
    have hd : ‖muSeq ψ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hb
    have h1 : (muSeq ψ n - (n : ℂ) * (Real.pi : ℂ)).im = (muSeq ψ n).im := by simp
    have h2 := Complex.abs_im_le_norm (muSeq ψ n - (n : ℂ) * (Real.pi : ℂ))
    rw [h1] at h2; linarith
  obtain ⟨hQ, -⟩ := NlsGge.Atomic.G1087S2.U4.state_small ψ (muSeq ψ n) him δ (min_le_left _ _) hs
  have hd1 : δ ≤ 1 / 50 := min_le_left _ _
  have hd2 : δ ≤ η / 25 := min_le_right _ _
  nlinarith

/-- uniform smallness of `(-1)^n u(μ_n) - 1` -/
theorem u_small (φ₀ : PotPair) (η : ℝ) (hη : 0 < η) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, ∀ ψ ∈ V, ∀ n : ℤ, N < n.natAbs →
      ‖parity n * normingFactor ψ (muSeq ψ n) - 1‖ ≤ η := by
  set δ : ℝ := min (3 / 200) (η / 22) with hδ
  have hδp : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨V, hV, N, h⟩ := err_small φ₀ δ hδp
  refine ⟨V, hV, N, fun ψ hψ n hn => ?_⟩
  obtain ⟨hb, h0, hs⟩ := h ψ hψ n hn
  obtain ⟨-, heps⟩ := NlsGge.Atomic.G1087S2.U2.root_facts ψ hb h0
  have h1 := hs 1 ⟨zero_le_one, le_rfl⟩
  rw [NlsGge.Atomic.G1087S2.P5.bridge1] at h1
  have hd1 : δ ≤ 3 / 200 := min_le_left _ _
  have hd2 : δ ≤ η / 22 := min_le_right _ _
  have heps1 : ‖muSeq ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 := by linarith
  have := NlsGge.Atomic.G1087S2.U5a.sprime ψ (muSeq ψ n) n δ h1 heps1
  have hp : parity n = (-1 : ℂ) ^ n := rfl
  rw [hp]
  linarith

end

end NlsGge.Atomic.G1087S2.Uniform


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.Final

open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.Pilot Filter Topology
  NlsGge.SpectralFoundations NlsGge.Atomic.G1087S2.P6 NlsGge.Atomic.G1087S2.P8 NlsGge.Atomic.G1087S2.U5c

open scoped Matrix.Norms.L2Operator

noncomputable section

theorem G1087_complex :
  (∀ φ₀ : PotPair, ∃ V : Set PotPair, V ∈ nhds φ₀ ∧ ∃ N : ℕ, ∃ C : ℝ, ∀ φ ∈ V,
    (∀ n : ℤ, N < n.natAbs → parity n * normingFactor φ (muSeq φ n) ∈ Complex.slitPlane) ∧
    Summable (fun n : ℤ => if N < n.natAbs then
        ‖2 * Complex.log (parity n * normingFactor φ (muSeq φ n))‖ ^ 2 else 0) ∧
    (∑' n : ℤ, if N < n.natAbs then
        ‖2 * Complex.log (parity n * normingFactor φ (muSeq φ n))‖ ^ 2 else 0) ≤ C ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      Summable (fun n : ℤ => if N < n.natAbs then
          ‖Complex.I • pairKernelExt38 (kappaKernel38 φ (muSeq φ n)) t -
            (![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
              ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0] : Fin 2 → ℂ)‖ ^ 2
          else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then
          ‖Complex.I • pairKernelExt38 (kappaKernel38 φ (muSeq φ n)) t -
            (![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
              ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0] : Fin 2 → ℂ)‖ ^ 2
          else 0) ≤ C)) := by
  intro φ₀
  obtain ⟨V₀, hV₀, N, hcore⟩ := NlsGge.Atomic.G1087S2.Uniform.err_small φ₀ (3 / 200) (by norm_num)
  set R0 : ℝ := 2 * (‖φ₀‖ + 1) with hR0
  set R1 : ℝ := Real.pi / 4 with hR1
  obtain ⟨C19, h19⟩ := NlsGge.Atomic.G1087S2.K29.K20.K19.G1019_whole R0 R1
  obtain ⟨C20, h20⟩ := NlsGge.Atomic.G1087S2.K29.K20.G1020_whole R0 R1
  obtain ⟨C29, h29⟩ := NlsGge.Atomic.G1087S2.K29.G1029_main R0 R1
  refine ⟨V₀ ∩ Metric.ball φ₀ 1, Filter.inter_mem hV₀ (Metric.ball_mem_nhds φ₀ one_pos), N,
    max (4356 * max C19 0) (CGc C19 C20 C29), ?_⟩
  intro φ hφ
  obtain ⟨hφ0, hφb⟩ := hφ
  set ξ : ℤ → ℂ := fun n => if N < n.natAbs then muSeq φ n else (n : ℂ) * (Real.pi : ℂ) with hξdef
  have hξ : ∀ n : ℤ, N < n.natAbs → ξ n = muSeq φ n := fun n hn => by simp [hξdef, hn]
  have hφR : Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ R0 := by
    have h1 : ‖φ - φ₀‖ < 1 := by simpa [dist_eq_norm] using hφb
    have h2 : ‖φ‖ ≤ ‖φ - φ₀‖ + ‖φ₀‖ := by simpa using norm_add_le (φ - φ₀) φ₀
    have h3 : ‖φ.1‖ ≤ ‖φ‖ := norm_fst_le φ
    have h4 : ‖φ.2‖ ≤ ‖φ‖ := norm_snd_le φ
    refine Real.sqrt_le_iff.2 ⟨by rw [hR0]; positivity, ?_⟩
    have := norm_nonneg φ.1; have := norm_nonneg φ.2; have := norm_nonneg φ₀
    rw [hR0]; nlinarith
  have hξb : ∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1 := by
    intro n
    by_cases hn : N < n.natAbs
    · rw [hξ n hn]
      obtain ⟨hb, -, -⟩ := hcore φ hφ0 n hn
      have : ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hb
      exact this.le
    · simp [hξdef, hn]; positivity
  have hroot : ∀ n : ℤ, N < n.natAbs → dirichletChar φ (ξ n) = 0 ∧
      ξ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) := by
    intro n hn
    obtain ⟨hb, h0, -⟩ := hcore φ hφ0 n hn
    rw [hξ n hn]; exact ⟨h0, hb⟩
  have hsm : ∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ‖(∑' m : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38 φ (ξ n) m t) -
        freeZsFundamentalComplex (ξ n) t‖ ≤ 3 / 200 := by
    intro n hn t ht
    obtain ⟨-, -, hs⟩ := hcore φ hφ0 n hn
    rw [hξ n hn]; exact hs t ht
  have h19v : SB (fun n : ℤ => ‖(∑' m : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38 φ (ξ n) m 1) -
      freeZsFundamentalComplex (ξ n) 1‖ ^ 2) C19 := h19 φ ξ hφR hξb 1 zero_le_one le_rfl
  have h20v := h20 φ ξ hφR hξb 1 zero_le_one le_rfl
  have h29v : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k : Fin 2,
      SB (fun n : ℤ => ‖GDf φ (ξ n) t k‖ ^ 2) C29 ∧
      SB (fun n : ℤ => ‖Gdf φ (ξ n) t k - leadf (ξ n) t k‖ ^ 2) C29 := by
    obtain ⟨-, -, -, h29'⟩ := h29 φ ξ hφR hξb
    exact fun t h0 h1 k => h29' t h0 h1 k
  have hEd : ∀ z : ℂ, DifferentiableAt ℂ (fun w : ℂ => freeZsFundamentalComplex w 1) z :=
    fun z => (NlsGge.Atomic.G1087S2.K29.K20.differentiable_E 1) z
  obtain ⟨hslit, hlog, hgrad⟩ := per_phi_c φ N ξ C19 C20 C29 hEd hroot hsm h19v h20v.1 h20v.2 h29v
  have eL : (fun n : ℤ => if N < n.natAbs then
      ‖2 * Complex.log (parity n * normingFactor φ (muSeq φ n))‖ ^ 2 else 0) =
      fun n : ℤ => if N < n.natAbs then
        ‖2 * Complex.log (parity n * normingFactor φ (ξ n))‖ ^ 2 else 0 := by
    funext n; by_cases hn : N < n.natAbs
    · rw [if_pos hn, if_pos hn, hξ n hn]
    · rw [if_neg hn, if_neg hn]
  have hL' : SB (fun n : ℤ => if N < n.natAbs then
      ‖2 * Complex.log (parity n * normingFactor φ (muSeq φ n))‖ ^ 2 else 0)
      (max (4356 * max C19 0) (CGc C19 C20 C29)) := by
    rw [eL]; exact SB.weak hlog (le_max_left _ _)
  refine ⟨fun n hn => by rw [← hξ n hn]; exact hslit n hn, hL'.1, hL'.2, fun t ht => ?_⟩
  have eG : (fun n : ℤ => if N < n.natAbs then
      ‖Complex.I • pairKernelExt38 (kappaKernel38 φ (muSeq φ n)) t - evec n t‖ ^ 2 else 0) =
      fun n : ℤ => if N < n.natAbs then
        ‖Complex.I • pairKernelExt38 (kappaKernel38 φ (ξ n)) t - evec n t‖ ^ 2 else 0 := by
    funext n; by_cases hn : N < n.natAbs
    · rw [if_pos hn, if_pos hn, hξ n hn]
    · rw [if_neg hn, if_neg hn]
  have hG' : SB (fun n : ℤ => if N < n.natAbs then
      ‖Complex.I • pairKernelExt38 (kappaKernel38 φ (muSeq φ n)) t - evec n t‖ ^ 2 else 0)
      (max (4356 * max C19 0) (CGc C19 C20 C29)) := by
    rw [eG]; exact SB.weak (hgrad t ht) (le_max_right _ _)
  exact ⟨hG'.1, hG'.2⟩

end

end NlsGge.Atomic.G1087S2.Final


set_option autoImplicit false
namespace NlsGge.Atomic.G1087S2.Main

open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.Pilot Filter Topology

noncomputable section

theorem G1087_main :
((
  (∀ u₀ : PhysicalL2, ∃ V : Set PhysicalL2, V ∈ nhds u₀ ∧ ∃ N : ℕ, ∃ C : ℝ, ∀ v ∈ V,
    (∀ n : ℤ, (normingFactor (realSlice v) (gkMu v n : ℂ)).im = 0 ∧ 0 < signedNorming38 v n) ∧
    Summable (fun n : ℤ => if N < n.natAbs then (realKappa38 v n) ^ 2 else 0) ∧
    (∑' n : ℤ, if N < n.natAbs then (realKappa38 v n) ^ 2 else 0) ≤ C ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      Summable (fun n : ℤ => if N < n.natAbs then
          ‖Complex.I • pairKernelExt38 (kappaKernel38 (realSlice v) (gkMu v n : ℂ)) t -
            (![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
              ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0] : Fin 2 → ℂ)‖ ^ 2
          else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then
          ‖Complex.I • pairKernelExt38 (kappaKernel38 (realSlice v) (gkMu v n : ℂ)) t -
            (![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
              ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0] : Fin 2 → ℂ)‖ ^ 2
          else 0) ≤ C)) ∧
  (∀ φ₀ : PotPair, ∃ V : Set PotPair, V ∈ nhds φ₀ ∧ ∃ N : ℕ, ∃ C : ℝ, ∀ φ ∈ V,
    (∀ n : ℤ, N < n.natAbs → parity n * normingFactor φ (muSeq φ n) ∈ Complex.slitPlane) ∧
    Summable (fun n : ℤ => if N < n.natAbs then
        ‖2 * Complex.log (parity n * normingFactor φ (muSeq φ n))‖ ^ 2 else 0) ∧
    (∑' n : ℤ, if N < n.natAbs then
        ‖2 * Complex.log (parity n * normingFactor φ (muSeq φ n))‖ ^ 2 else 0) ≤ C ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      Summable (fun n : ℤ => if N < n.natAbs then
          ‖Complex.I • pairKernelExt38 (kappaKernel38 φ (muSeq φ n)) t -
            (![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
              ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0] : Fin 2 → ℂ)‖ ^ 2
          else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then
          ‖Complex.I • pairKernelExt38 (kappaKernel38 φ (muSeq φ n)) t -
            (![0, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ))] -
              ![Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)), 0] : Fin 2 → ℂ)‖ ^ 2
          else 0) ≤ C))
  : Prop)) := ⟨NlsGge.Atomic.G1087S2.Final.G1087_real, NlsGge.Atomic.G1087S2.Final.G1087_complex⟩

end

end NlsGge.Atomic.G1087S2.Main
