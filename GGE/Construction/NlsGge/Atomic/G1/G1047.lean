import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1040
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairVolterraProbe

                                                                                                                            
                                                                                                                             
                                                                                                                              
                                                                                                                            
                                                                                                                             
                                                                                                                          
                                              

                                                                                                                           
                                                                                                                            
                                                                                                                               
                                                                                                                     
                                                                                                                            
                                                                                                                              
                                                                                                             

                                                                                                         
                                                                                     
                                                                                              
                                                                                             
                                                                                                         

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1047S2.K17.K16

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
  unfold discrim at this
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

end NlsGge.Atomic.G1047S2.K17.K16



/-! ### G1-017: high-frequency local uniform asymptotics -/

open NlsGge.Atomic.G1047S2.K17.K16

namespace NlsGge.Atomic.G1047S2.K17

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

end NlsGge.Atomic.G1047S2.K17

open NlsGge.Pilot

namespace NlsGge.Atomic.G1047S2.K17

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

end NlsGge.Atomic.G1047S2.K17

/-! ### The final statement -/

namespace NlsGge.Atomic.G1047S2.K17

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

end NlsGge.Atomic.G1047S2.K17



/-! ### G1-047: characteristic comparison outside the discs -/

namespace NlsGge.Atomic.G1047S2

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

end NlsGge.Atomic.G1047S2
