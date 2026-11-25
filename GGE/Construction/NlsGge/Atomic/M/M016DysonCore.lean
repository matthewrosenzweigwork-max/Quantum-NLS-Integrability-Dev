import Mathlib
import NlsGge.GK38.PairVolterraPower
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairAsymptoticsVolterra
import NlsGge.GK38.PairRealBridge


                                                                                                       
                                                                                                           
                                                                                                                
                                                                                          
                                                                                             
                                                                                                                    
                                                                                                      
                                                                                                 
                                                                                                          
                                                    
                                                                                                            
                                                                                          
                                                                                           
                                                                                                  
                                  

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M016DysonAux

/-! ### The free propagator on the imaginary axis -/

theorem exp_free_one (τ y : ℝ) :
    Complex.exp (-(Complex.I * (Complex.I * (τ : ℂ)) * (y : ℂ))) = (Real.exp (τ * y) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (-(τ : ℂ) * y) * Complex.I_sq

theorem exp_free_two (τ y : ℝ) :
    Complex.exp (Complex.I * (Complex.I * (τ : ℂ)) * (y : ℂ)) = (Real.exp (-(τ * y)) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination ((τ : ℂ) * y) * Complex.I_sq

/-- Entry recursion of the Volterra operator at `z = iτ`, first row. -/
theorem volterraP_entry_zero (φ : PotPair) (τ : ℝ) (N : PairCont38) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin 2) :
    volterraP φ (Complex.I * τ) N ⟨x, hx⟩ 0 j =
      ∫ s in (0 : ℝ)..x, (Real.exp (τ * (x - s)) : ℂ) *
        (Complex.I * potRepFst38 φ s) * ext38 N s 1 j := by
  rw [volterraP_apply, volterraFun_apply]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [freeE, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, zero_mul, add_zero, mul_zero, zero_add]
  rw [exp_free_one]

/-- Entry recursion of the Volterra operator at `z = iτ`, second row. -/
theorem volterraP_entry_one (φ : PotPair) (τ : ℝ) (N : PairCont38) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin 2) :
    volterraP φ (Complex.I * τ) N ⟨x, hx⟩ 1 j =
      ∫ s in (0 : ℝ)..x, (Real.exp (-(τ * (x - s))) : ℂ) *
        (-(Complex.I * potRepSnd38 φ s)) * ext38 N s 0 j := by
  rw [volterraP_apply, volterraFun_apply]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [freeE, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, zero_mul, add_zero, mul_zero, zero_add]
  rw [exp_free_two]

theorem freeFundP_entries (τ : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    freeFundP (Complex.I * τ) ⟨x, hx⟩ 0 0 = (Real.exp (τ * x) : ℂ) ∧
    freeFundP (Complex.I * τ) ⟨x, hx⟩ 1 0 = 0 ∧
    freeFundP (Complex.I * τ) ⟨x, hx⟩ 0 1 = 0 ∧
    freeFundP (Complex.I * τ) ⟨x, hx⟩ 1 1 = (Real.exp (-(τ * x)) : ℂ) := by
  have h : freeFundP (Complex.I * τ) ⟨x, hx⟩ = freeE (Complex.I * τ) x := rfl
  rw [h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [freeE, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    first | exact exp_free_one τ x | exact exp_free_two τ x | rfl

/-! ### Scalar majorants -/

/-- `J(x) = ∫₀ˣ e^{-2τs} |φ₁(s)| ds`. -/
def majJ (φ : PotPair) (τ x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, Real.exp (-(2 * τ * s)) * ‖potRepFst38 φ s‖

/-- `K(x) = e^{-2τx} ∫₀ˣ e^{2τs} |φ₂(s)| ds = ∫₀ˣ e^{-2τ(x-s)} |φ₂(s)| ds`. -/
def majK (φ : PotPair) (τ x : ℝ) : ℝ :=
  Real.exp (-(2 * τ * x)) * ∫ s in (0 : ℝ)..x, Real.exp (2 * τ * s) * ‖potRepSnd38 φ s‖

/-- `W(x) = e^{-2τx} ∫₀ˣ e^{2τs} |φ₂(s)| J(s) ds` (the cyclic/wrap pairing). -/
def majW (φ : PotPair) (τ x : ℝ) : ℝ :=
  Real.exp (-(2 * τ * x)) *
    ∫ s in (0 : ℝ)..x, Real.exp (2 * τ * s) * ‖potRepSnd38 φ s‖ * majJ φ τ s

/-- `A' = ∫₀¹ |φ₁(s)| K(s) ds` (the decaying pairing). -/
def majA (φ : PotPair) (τ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ‖potRepFst38 φ s‖ * majK φ τ s

theorem ii_fst (φ : PotPair) : IntervalIntegrable (fun s => ‖potRepFst38 φ s‖) volume 0 1 :=
  intervalIntegrable_norm_coverRep38_one φ.1

theorem ii_snd (φ : PotPair) : IntervalIntegrable (fun s => ‖potRepSnd38 φ s‖) volume 0 1 :=
  intervalIntegrable_norm_coverRep38_one φ.2

theorem sub01 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : uIcc (0 : ℝ) x ⊆ uIcc 0 1 := by
  rw [uIcc_of_le hx.1, uIcc_of_le zero_le_one]
  exact Icc_subset_Icc le_rfl hx.2

theorem majJ_nonneg (φ : PotPair) (τ : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ majJ φ τ x :=
  intervalIntegral.integral_nonneg hx fun s _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem majK_nonneg (φ : PotPair) (τ : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ majK φ τ x :=
  mul_nonneg (Real.exp_pos _).le
    (intervalIntegral.integral_nonneg hx fun s _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))

theorem primitive_continuousOn {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1) :
    ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, f s) (Icc (0 : ℝ) 1) := by
  have := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1) (f := f)
    (by rw [uIcc_of_le zero_le_one]
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hf)
  rwa [uIcc_of_le zero_le_one] at this

theorem ii_J_integrand (φ : PotPair) (τ : ℝ) :
    IntervalIntegrable (fun s => Real.exp (-(2 * τ * s)) * ‖potRepFst38 φ s‖) volume 0 1 :=
  (ii_fst φ).continuousOn_mul (Continuous.continuousOn (by fun_prop))

theorem ii_K_integrand (φ : PotPair) (τ : ℝ) :
    IntervalIntegrable (fun s => Real.exp (2 * τ * s) * ‖potRepSnd38 φ s‖) volume 0 1 :=
  (ii_snd φ).continuousOn_mul (Continuous.continuousOn (by fun_prop))

theorem continuousOn_majJ (φ : PotPair) (τ : ℝ) : ContinuousOn (majJ φ τ) (Icc (0 : ℝ) 1) :=
  primitive_continuousOn (ii_J_integrand φ τ)

theorem continuousOn_majK (φ : PotPair) (τ : ℝ) : ContinuousOn (majK φ τ) (Icc (0 : ℝ) 1) :=
  (Continuous.continuousOn (by fun_prop)).mul (primitive_continuousOn (ii_K_integrand φ τ))

theorem ii_W_integrand (φ : PotPair) (τ : ℝ) :
    IntervalIntegrable (fun s => Real.exp (2 * τ * s) * ‖potRepSnd38 φ s‖ * majJ φ τ s)
      volume 0 1 :=
  (ii_K_integrand φ τ).mul_continuousOn (by rw [uIcc_of_le zero_le_one]; exact continuousOn_majJ φ τ)

theorem continuousOn_majW (φ : PotPair) (τ : ℝ) : ContinuousOn (majW φ τ) (Icc (0 : ℝ) 1) :=
  (Continuous.continuousOn (by fun_prop)).mul (primitive_continuousOn (ii_W_integrand φ τ))

end NlsGge.ThirdConsultation.M016DysonAux

namespace NlsGge.ThirdConsultation.M016DysonAux

/-- The `k`-th Dyson (Neumann) term `𝒱^k E` at `z = iτ`. -/
def dysonTerm (φ : PotPair) (τ : ℝ) (k : ℕ) : PairCont38 :=
  (volterraP φ (Complex.I * τ) ^ k) (freeFundP (Complex.I * τ))

theorem dysonTerm_succ (φ : PotPair) (τ : ℝ) (k : ℕ) :
    dysonTerm φ τ (k + 1) = volterraP φ (Complex.I * τ) (dysonTerm φ τ k) := by
  unfold dysonTerm
  rw [pow_succ', ContinuousLinearMap.mul_apply]

theorem int_zero {f : ℝ → ℂ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (h : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), s ≤ x → f s = 0) : ∫ s in (0 : ℝ)..x, f s = 0 := by
  refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun s hs => ?_).trans
    intervalIntegral.integral_zero
  rw [uIcc_of_le hx.1] at hs
  exact h s ⟨hs.1, hs.2.trans hx.2⟩ hs.2

theorem int_norm_le {f : ℝ → ℂ} {g : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hg : IntervalIntegrable g volume 0 x)
    (h : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), s ≤ x → ‖f s‖ ≤ g s) :
    ‖∫ s in (0 : ℝ)..x, f s‖ ≤ ∫ s in (0 : ℝ)..x, g s :=
  intervalIntegral.norm_integral_le_of_norm_le hx.1
    (Eventually.of_forall fun s hs => h s ⟨hs.1.le, hs.2.trans hx.2⟩ hs.2) hg

theorem norm_kernel (a : ℝ) (c E : ℂ) :
    ‖(Real.exp a : ℂ) * (Complex.I * c) * E‖ = Real.exp a * ‖c‖ * ‖E‖ := by
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

theorem norm_kernel' (a : ℝ) (c E : ℂ) :
    ‖(Real.exp a : ℂ) * (-(Complex.I * c)) * E‖ = Real.exp a * ‖c‖ * ‖E‖ := by
  rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

theorem majA_nonneg (φ : PotPair) (τ : ℝ) : 0 ≤ majA φ τ :=
  intervalIntegral.integral_nonneg zero_le_one fun s hs =>
    mul_nonneg (norm_nonneg _) (majK_nonneg φ τ hs.1)

theorem ii_fK (φ : PotPair) (τ : ℝ) :
    IntervalIntegrable (fun s => ‖potRepFst38 φ s‖ * majK φ τ s) volume 0 1 :=
  (ii_fst φ).mul_continuousOn (by rw [uIcc_of_le zero_le_one]; exact continuousOn_majK φ τ)

theorem int_fK_le (φ : PotPair) (τ : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..x, ‖potRepFst38 φ s‖ * majK φ τ s ≤ majA φ τ :=
  intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
    (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
      mul_nonneg (norm_nonneg _) (majK_nonneg φ τ hs.1.le)) (ii_fK φ τ)

theorem majJ_mono (φ : PotPair) (τ : ℝ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) :
    majJ φ τ r ≤ majJ φ τ s :=
  intervalIntegral.integral_mono_interval le_rfl hr hrs
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t _ =>
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    ((ii_J_integrand φ τ).mono_set (sub01 ⟨hr.trans hrs, hs⟩))

theorem majW_le (φ : PotPair) (τ : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    majW φ τ s ≤ majJ φ τ s * majK φ τ s := by
  unfold majW majK
  have hmono : ∫ r in (0 : ℝ)..s, Real.exp (2 * τ * r) * ‖potRepSnd38 φ r‖ * majJ φ τ r ≤
      ∫ r in (0 : ℝ)..s, majJ φ τ s * (Real.exp (2 * τ * r) * ‖potRepSnd38 φ r‖) := by
    refine intervalIntegral.integral_mono_on hs.1
      ((ii_W_integrand φ τ).mono_set (sub01 hs))
      (((ii_K_integrand φ τ).mono_set (sub01 hs)).const_mul _) fun r hr => ?_
    have hJ := majJ_mono φ τ hr.1 hr.2 hs.2
    have h0 : 0 ≤ Real.exp (2 * τ * r) * ‖potRepSnd38 φ r‖ :=
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    nlinarith
  calc Real.exp (-(2 * τ * s)) *
        ∫ r in (0 : ℝ)..s, Real.exp (2 * τ * r) * ‖potRepSnd38 φ r‖ * majJ φ τ r
      ≤ Real.exp (-(2 * τ * s)) *
        ∫ r in (0 : ℝ)..s, majJ φ τ s * (Real.exp (2 * τ * r) * ‖potRepSnd38 φ r‖) :=
        mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

/-! ### Column 0 invariants: `|N_{2m}₀₀| ≤ e^{τx} A'^m`, `|N_{2m+1}₁₀| ≤ e^{τx} A'^m K(x)` -/

theorem col0_odd (φ : PotPair) (τ : ℝ) (m : ℕ)
    (hE : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), dysonTerm φ τ (2 * m) ⟨s, hs⟩ 1 0 = 0 ∧
      ‖dysonTerm φ τ (2 * m) ⟨s, hs⟩ 0 0‖ ≤ Real.exp (τ * s) * majA φ τ ^ m)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    dysonTerm φ τ (2 * m + 1) ⟨x, hx⟩ 0 0 = 0 ∧
      ‖dysonTerm φ τ (2 * m + 1) ⟨x, hx⟩ 1 0‖ ≤
        Real.exp (τ * x) * majA φ τ ^ m * majK φ τ x := by
  rw [dysonTerm_succ, volterraP_entry_zero, volterraP_entry_one]
  refine ⟨int_zero hx fun s hs _ => by rw [ext38_of_mem _ hs, (hE s hs).1, mul_zero], ?_⟩
  have hA := pow_nonneg (majA_nonneg φ τ) m
  refine (int_norm_le hx (g := fun s => (Real.exp (τ * x) * majA φ τ ^ m * Real.exp (-(2 * τ * x))) *
      (Real.exp (2 * τ * s) * ‖potRepSnd38 φ s‖))
    (((ii_K_integrand φ τ).mono_set (sub01 hx)).const_mul _) fun s hs _ => ?_).trans_eq ?_
  · rw [norm_kernel', ext38_of_mem _ hs]
    have hb := (hE s hs).2
    have hid : Real.exp (-(τ * (x - s))) * Real.exp (τ * s) =
        Real.exp (τ * x) * Real.exp (-(2 * τ * x)) * Real.exp (2 * τ * s) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (-(τ * (x - s))) * ‖potRepSnd38 φ s‖ * ‖dysonTerm φ τ (2 * m) ⟨s, hs⟩ 0 0‖
        ≤ Real.exp (-(τ * (x - s))) * ‖potRepSnd38 φ s‖ * (Real.exp (τ * s) * majA φ τ ^ m) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      _ = (Real.exp (-(τ * (x - s))) * Real.exp (τ * s)) * majA φ τ ^ m * ‖potRepSnd38 φ s‖ := by
          ring
      _ = _ := by rw [hid]; ring
  · rw [intervalIntegral.integral_const_mul]
    unfold majK
    ring

theorem col0_even_succ (φ : PotPair) (τ : ℝ) (m : ℕ)
    (hO : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), dysonTerm φ τ (2 * m + 1) ⟨s, hs⟩ 0 0 = 0 ∧
      ‖dysonTerm φ τ (2 * m + 1) ⟨s, hs⟩ 1 0‖ ≤ Real.exp (τ * s) * majA φ τ ^ m * majK φ τ s)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    dysonTerm φ τ (2 * (m + 1)) ⟨x, hx⟩ 1 0 = 0 ∧
      ‖dysonTerm φ τ (2 * (m + 1)) ⟨x, hx⟩ 0 0‖ ≤ Real.exp (τ * x) * majA φ τ ^ (m + 1) := by
  have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
  rw [h2, dysonTerm_succ, volterraP_entry_zero, volterraP_entry_one]
  refine ⟨int_zero hx fun s hs _ => by rw [ext38_of_mem _ hs, (hO s hs).1, mul_zero], ?_⟩
  have hA := pow_nonneg (majA_nonneg φ τ) m
  refine (int_norm_le hx (g := fun s => (Real.exp (τ * x) * majA φ τ ^ m) *
      (‖potRepFst38 φ s‖ * majK φ τ s))
    (((ii_fK φ τ).mono_set (sub01 hx)).const_mul _) fun s hs _ => ?_).trans ?_
  · rw [norm_kernel, ext38_of_mem _ hs]
    have hb := (hO s hs).2
    have hid : Real.exp (τ * (x - s)) * Real.exp (τ * s) = Real.exp (τ * x) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (τ * (x - s)) * ‖potRepFst38 φ s‖ * ‖dysonTerm φ τ (2 * m + 1) ⟨s, hs⟩ 1 0‖
        ≤ Real.exp (τ * (x - s)) * ‖potRepFst38 φ s‖ *
            (Real.exp (τ * s) * majA φ τ ^ m * majK φ τ s) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      _ = (Real.exp (τ * (x - s)) * Real.exp (τ * s)) * majA φ τ ^ m *
            (‖potRepFst38 φ s‖ * majK φ τ s) := by ring
      _ = _ := by rw [hid]
  · rw [intervalIntegral.integral_const_mul, pow_succ]
    have := int_fK_le φ τ hx
    have he := (Real.exp_pos (τ * x)).le
    calc Real.exp (τ * x) * majA φ τ ^ m * ∫ s in (0 : ℝ)..x, ‖potRepFst38 φ s‖ * majK φ τ s
        ≤ Real.exp (τ * x) * majA φ τ ^ m * majA φ τ :=
          mul_le_mul_of_nonneg_left this (mul_nonneg he hA)
      _ = _ := by ring

theorem col0 (φ : PotPair) (τ : ℝ) (m : ℕ) :
    (∀ x (hx : x ∈ Icc (0 : ℝ) 1), dysonTerm φ τ (2 * m) ⟨x, hx⟩ 1 0 = 0 ∧
      ‖dysonTerm φ τ (2 * m) ⟨x, hx⟩ 0 0‖ ≤ Real.exp (τ * x) * majA φ τ ^ m) ∧
    (∀ x (hx : x ∈ Icc (0 : ℝ) 1), dysonTerm φ τ (2 * m + 1) ⟨x, hx⟩ 0 0 = 0 ∧
      ‖dysonTerm φ τ (2 * m + 1) ⟨x, hx⟩ 1 0‖ ≤ Real.exp (τ * x) * majA φ τ ^ m * majK φ τ x) := by
  induction m with
  | zero =>
    have hE : ∀ x (hx : x ∈ Icc (0 : ℝ) 1), dysonTerm φ τ (2 * 0) ⟨x, hx⟩ 1 0 = 0 ∧
        ‖dysonTerm φ τ (2 * 0) ⟨x, hx⟩ 0 0‖ ≤ Real.exp (τ * x) * majA φ τ ^ 0 := by
      intro x hx
      have hF := freeFundP_entries τ hx
      have h0 : dysonTerm φ τ (2 * 0) = freeFundP (Complex.I * τ) := by
        simp [dysonTerm]
      rw [h0, hF.1, hF.2.1, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, pow_zero,
        mul_one]
      exact ⟨rfl, le_rfl⟩
    exact ⟨hE, col0_odd φ τ 0 hE⟩
  | succ m ih =>
    have hE := col0_even_succ φ τ m ih.2
    exact ⟨hE, col0_odd φ τ (m + 1) hE⟩

/-! ### Column 1 invariants: `|N_{2m+1}₀₁| ≤ e^{τx} A'^m J(x)`, `|N_{2m+2}₁₁| ≤ e^{τx} A'^m W(x)` -/

theorem col1_even (φ : PotPair) (τ : ℝ) (m : ℕ)
    (hO : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), dysonTerm φ τ (2 * m + 1) ⟨s, hs⟩ 1 1 = 0 ∧
      ‖dysonTerm φ τ (2 * m + 1) ⟨s, hs⟩ 0 1‖ ≤ Real.exp (τ * s) * majA φ τ ^ m * majJ φ τ s)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    dysonTerm φ τ (2 * m + 2) ⟨x, hx⟩ 0 1 = 0 ∧
      ‖dysonTerm φ τ (2 * m + 2) ⟨x, hx⟩ 1 1‖ ≤
        Real.exp (τ * x) * majA φ τ ^ m * majW φ τ x := by
  rw [dysonTerm_succ, volterraP_entry_zero, volterraP_entry_one]
  refine ⟨int_zero hx fun s hs _ => by rw [ext38_of_mem _ hs, (hO s hs).1, mul_zero], ?_⟩
  have hA := pow_nonneg (majA_nonneg φ τ) m
  refine (int_norm_le hx (g := fun s => (Real.exp (τ * x) * majA φ τ ^ m * Real.exp (-(2 * τ * x))) *
      (Real.exp (2 * τ * s) * ‖potRepSnd38 φ s‖ * majJ φ τ s))
    (((ii_W_integrand φ τ).mono_set (sub01 hx)).const_mul _) fun s hs _ => ?_).trans_eq ?_
  · rw [norm_kernel', ext38_of_mem _ hs]
    have hb := (hO s hs).2
    have hid : Real.exp (-(τ * (x - s))) * Real.exp (τ * s) =
        Real.exp (τ * x) * Real.exp (-(2 * τ * x)) * Real.exp (2 * τ * s) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (-(τ * (x - s))) * ‖potRepSnd38 φ s‖ * ‖dysonTerm φ τ (2 * m + 1) ⟨s, hs⟩ 0 1‖
        ≤ Real.exp (-(τ * (x - s))) * ‖potRepSnd38 φ s‖ *
            (Real.exp (τ * s) * majA φ τ ^ m * majJ φ τ s) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      _ = (Real.exp (-(τ * (x - s))) * Real.exp (τ * s)) * majA φ τ ^ m *
            ‖potRepSnd38 φ s‖ * majJ φ τ s := by ring
      _ = _ := by rw [hid]; ring
  · rw [intervalIntegral.integral_const_mul]
    unfold majW
    ring

theorem col1_odd_succ (φ : PotPair) (τ : ℝ) (m : ℕ)
    (hE : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), dysonTerm φ τ (2 * m + 2) ⟨s, hs⟩ 0 1 = 0 ∧
      ‖dysonTerm φ τ (2 * m + 2) ⟨s, hs⟩ 1 1‖ ≤ Real.exp (τ * s) * majA φ τ ^ m * majW φ τ s)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    dysonTerm φ τ (2 * (m + 1) + 1) ⟨x, hx⟩ 1 1 = 0 ∧
      ‖dysonTerm φ τ (2 * (m + 1) + 1) ⟨x, hx⟩ 0 1‖ ≤
        Real.exp (τ * x) * majA φ τ ^ (m + 1) * majJ φ τ x := by
  have h2 : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by ring
  rw [h2, dysonTerm_succ, volterraP_entry_zero, volterraP_entry_one]
  refine ⟨int_zero hx fun s hs _ => by rw [ext38_of_mem _ hs, (hE s hs).1, mul_zero], ?_⟩
  have hA := pow_nonneg (majA_nonneg φ τ) m
  have hJx := majJ_nonneg φ τ hx.1
  refine (int_norm_le hx (g := fun s => (Real.exp (τ * x) * majA φ τ ^ m * majJ φ τ x) *
      (‖potRepFst38 φ s‖ * majK φ τ s))
    (((ii_fK φ τ).mono_set (sub01 hx)).const_mul _) fun s hs hsx => ?_).trans ?_
  · rw [norm_kernel, ext38_of_mem _ hs]
    have hb := (hE s hs).2
    have hW := majW_le φ τ hs
    have hJ := majJ_mono φ τ hs.1 hsx hx.2
    have hK := majK_nonneg φ τ hs.1
    have hid : Real.exp (τ * (x - s)) * Real.exp (τ * s) = Real.exp (τ * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have hex := (Real.exp_pos (τ * x)).le
    have hf := norm_nonneg (potRepFst38 φ s)
    calc Real.exp (τ * (x - s)) * ‖potRepFst38 φ s‖ * ‖dysonTerm φ τ (2 * m + 2) ⟨s, hs⟩ 1 1‖
        ≤ Real.exp (τ * (x - s)) * ‖potRepFst38 φ s‖ *
            (Real.exp (τ * s) * majA φ τ ^ m * majW φ τ s) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (Real.exp_pos _).le hf)
      _ = (Real.exp (τ * (x - s)) * Real.exp (τ * s)) * majA φ τ ^ m *
            (‖potRepFst38 φ s‖ * majW φ τ s) := by ring
      _ = Real.exp (τ * x) * majA φ τ ^ m * (‖potRepFst38 φ s‖ * majW φ τ s) := by rw [hid]
      _ ≤ Real.exp (τ * x) * majA φ τ ^ m * (‖potRepFst38 φ s‖ * (majJ φ τ x * majK φ τ s)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hf) (mul_nonneg hex hA)
          exact hW.trans (mul_le_mul_of_nonneg_right hJ hK)
      _ = _ := by ring
  · rw [intervalIntegral.integral_const_mul, pow_succ]
    have := int_fK_le φ τ hx
    have he := (Real.exp_pos (τ * x)).le
    calc Real.exp (τ * x) * majA φ τ ^ m * majJ φ τ x *
          ∫ s in (0 : ℝ)..x, ‖potRepFst38 φ s‖ * majK φ τ s
        ≤ Real.exp (τ * x) * majA φ τ ^ m * majJ φ τ x * majA φ τ :=
          mul_le_mul_of_nonneg_left this (mul_nonneg (mul_nonneg he hA) hJx)
      _ = _ := by ring

theorem col1_odd_zero (φ : PotPair) (τ : ℝ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    dysonTerm φ τ (2 * 0 + 1) ⟨x, hx⟩ 1 1 = 0 ∧
      ‖dysonTerm φ τ (2 * 0 + 1) ⟨x, hx⟩ 0 1‖ ≤ Real.exp (τ * x) * majA φ τ ^ 0 * majJ φ τ x := by
  have h0 : dysonTerm φ τ (2 * 0 + 1) = volterraP φ (Complex.I * τ) (freeFundP (Complex.I * τ)) := by
    simp [dysonTerm]
  rw [h0, volterraP_entry_zero, volterraP_entry_one, pow_zero, mul_one]
  refine ⟨int_zero hx fun s hs _ => by
    rw [ext38_of_mem _ hs, (freeFundP_entries τ hs).2.2.1, mul_zero], ?_⟩
  refine (int_norm_le hx (g := fun s => Real.exp (τ * x) * (Real.exp (-(2 * τ * s)) * ‖potRepFst38 φ s‖))
    (((ii_J_integrand φ τ).mono_set (sub01 hx)).const_mul _) fun s hs _ => ?_).trans_eq ?_
  · rw [norm_kernel, ext38_of_mem _ hs, (freeFundP_entries τ hs).2.2.2, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have hid : Real.exp (τ * (x - s)) * Real.exp (-(τ * s)) =
        Real.exp (τ * x) * Real.exp (-(2 * τ * s)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have heq : Real.exp (τ * (x - s)) * ‖potRepFst38 φ s‖ * Real.exp (-(τ * s)) =
        Real.exp (τ * x) * (Real.exp (-(2 * τ * s)) * ‖potRepFst38 φ s‖) := by
      rw [show Real.exp (τ * (x - s)) * ‖potRepFst38 φ s‖ * Real.exp (-(τ * s)) =
        (Real.exp (τ * (x - s)) * Real.exp (-(τ * s))) * ‖potRepFst38 φ s‖ by ring, hid]
      ring
    exact heq.le
  · rw [intervalIntegral.integral_const_mul]
    rfl

theorem col1 (φ : PotPair) (τ : ℝ) (m : ℕ) :
    (∀ x (hx : x ∈ Icc (0 : ℝ) 1), dysonTerm φ τ (2 * m + 1) ⟨x, hx⟩ 1 1 = 0 ∧
      ‖dysonTerm φ τ (2 * m + 1) ⟨x, hx⟩ 0 1‖ ≤ Real.exp (τ * x) * majA φ τ ^ m * majJ φ τ x) ∧
    (∀ x (hx : x ∈ Icc (0 : ℝ) 1), dysonTerm φ τ (2 * m + 2) ⟨x, hx⟩ 0 1 = 0 ∧
      ‖dysonTerm φ τ (2 * m + 2) ⟨x, hx⟩ 1 1‖ ≤ Real.exp (τ * x) * majA φ τ ^ m * majW φ τ x) := by
  induction m with
  | zero =>
    have hO := col1_odd_zero φ τ
    exact ⟨hO, col1_even φ τ 0 hO⟩
  | succ m ih =>
    have hO := col1_odd_succ φ τ m ih.2
    exact ⟨hO, col1_even φ τ (m + 1) hO⟩

end NlsGge.ThirdConsultation.M016DysonAux

namespace NlsGge.ThirdConsultation.M016DysonAux

/-- The endpoint `1 ∈ [0,1]`. -/
abbrev one01 : Icc (0 : ℝ) 1 := ⟨1, by norm_num, le_rfl⟩

/-- Trace of a matrix-valued continuous function at the endpoint. -/
def trOne (N : PairCont38) : ℂ := N one01 0 0 + N one01 1 1

theorem trOne_add (N N' : PairCont38) : trOne (N + N') = trOne N + trOne N' := by
  unfold trOne
  simp only [ContinuousMap.add_apply, Matrix.add_apply, Pi.add_apply]
  ring

theorem trOne_sum (s : Finset ℕ) (f : ℕ → PairCont38) :
    trOne (∑ k ∈ s, f k) = ∑ k ∈ s, trOne (f k) := by
  induction s using Finset.induction_on with
  | empty =>
    unfold trOne
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, trOne_add, ih]

/-- The fundamental solution solves the Volterra equation `M = E + 𝒱 M`. -/
theorem fund_fixed (φ : PotPair) (z : ℂ) :
    fundContP φ z = freeFundP z + volterraP φ z (fundContP φ z) :=
  sub_eq_iff_eq_add.mp (fundCont_sub_volterra φ z)

theorem discrim_eq_trOne (φ : PotPair) (z : ℂ) : NlsGge.GK38.discrim φ z = trOne (fundContP φ z) := by
  unfold NlsGge.GK38.discrim trOne
  rw [Matrix.trace_fin_two]
  rfl

/-- Truncated Dyson expansion of the discriminant at `z = iτ`. -/
theorem discrim_partial (φ : PotPair) (τ : ℝ) (n : ℕ) :
    NlsGge.GK38.discrim φ (Complex.I * τ) =
      (∑ k ∈ Finset.range n, trOne (dysonTerm φ τ k)) +
        trOne ((volterraP φ (Complex.I * τ) ^ n) (fundContP φ (Complex.I * τ))) := by
  rw [discrim_eq_trOne]
  conv_lhs => rw [volterra_solution_eq_sum φ _ _ _ (fund_fixed φ _) n]
  rw [trOne_add, trOne_sum]
  rfl

/-- **Leaf (a), convergence of the full Dyson series** for the trace at `z = iτ`. -/
theorem dyson_tendsto (φ : PotPair) (τ : ℝ) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, trOne (dysonTerm φ τ k)) atTop
      (𝓝 (NlsGge.GK38.discrim φ (Complex.I * τ))) := by
  set z : ℂ := Complex.I * τ
  set M := fundContP φ z
  have hrem : Tendsto (fun n => trOne ((volterraP φ z ^ n) M)) atTop (𝓝 0) := by
    have hfac := (FloorSemiring.tendsto_pow_div_factorial_atTop (potPrim38 φ 1)).const_mul
      (2 * Real.exp (|z.im| * 1) * ‖M‖)
    rw [mul_zero] at hfac
    refine squeeze_zero_norm (fun n => ?_) hfac
    unfold trOne
    have h0 := norm_volterra_pow_entry_le φ z n M one01.2 0 0
    have h1 := norm_volterra_pow_entry_le φ z n M one01.2 1 1
    calc ‖((volterraP φ z ^ n) M) one01 0 0 + ((volterraP φ z ^ n) M) one01 1 1‖
        ≤ ‖((volterraP φ z ^ n) M) one01 0 0‖ + ‖((volterraP φ z ^ n) M) one01 1 1‖ := norm_add_le _ _
      _ ≤ _ := by
          have e : one01 = ⟨(1 : ℝ), one01.2⟩ := rfl
          rw [e] at h0 h1 ⊢
          simp only at h0 h1
          linarith
  have h := (tendsto_const_nhds (x := NlsGge.GK38.discrim φ z)).sub hrem
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  rw [discrim_partial φ τ n]
  ring

/-- Order 0: `tr E(1) = e^τ + e^{-τ}`. -/
theorem trOne_zero (φ : PotPair) (τ : ℝ) :
    trOne (dysonTerm φ τ 0) = (Real.exp τ : ℂ) + (Real.exp (-τ) : ℂ) := by
  have h : dysonTerm φ τ 0 = freeFundP (Complex.I * τ) := by simp [dysonTerm]
  unfold trOne
  rw [h, (freeFundP_entries τ one01.2).1, (freeFundP_entries τ one01.2).2.2.2]
  simp only [one01, mul_one]

/-- Odd orders have zero trace. -/
theorem trOne_odd (φ : PotPair) (τ : ℝ) (m : ℕ) : trOne (dysonTerm φ τ (2 * m + 1)) = 0 := by
  unfold trOne
  rw [((col0 φ τ m).2 1 one01.2).1, ((col1 φ τ m).1 1 one01.2).1, add_zero]

/-- Even orders `≥ 4`: `|tr N_{2m+4}(1)| ≤ e^τ (A' + W(1)) A'^{m+1}`. -/
theorem trOne_even_le (φ : PotPair) (τ : ℝ) (m : ℕ) :
    ‖trOne (dysonTerm φ τ (2 * (m + 2)))‖ ≤
      Real.exp τ * (majA φ τ + majW φ τ 1) * majA φ τ ^ (m + 1) := by
  unfold trOne
  have h0 := ((col0 φ τ (m + 2)).1 1 one01.2).2
  have h1 := ((col1 φ τ (m + 1)).2 1 one01.2).2
  have e : 2 * (m + 2) = 2 * (m + 1) + 2 := by ring
  rw [e] at h0 ⊢
  simp only [mul_one] at h0 h1
  calc ‖dysonTerm φ τ (2 * (m + 1) + 2) one01 0 0 + dysonTerm φ τ (2 * (m + 1) + 2) one01 1 1‖
      ≤ ‖dysonTerm φ τ (2 * (m + 1) + 2) one01 0 0‖ + ‖dysonTerm φ τ (2 * (m + 1) + 2) one01 1 1‖ :=
        norm_add_le _ _
    _ ≤ Real.exp τ * majA φ τ ^ (m + 2) + Real.exp τ * majA φ τ ^ (m + 1) * majW φ τ 1 :=
        add_le_add h0 h1
    _ = _ := by ring

/-- The even-index partial sums beyond order 3. -/
theorem partial_even_bound (φ : PotPair) (τ : ℝ) (L : ℕ) :
    ‖(∑ k ∈ Finset.range (2 * (L + 2)), trOne (dysonTerm φ τ k)) -
        ∑ k ∈ Finset.range 4, trOne (dysonTerm φ τ k)‖ ≤
      Real.exp τ * (majA φ τ + majW φ τ 1) * ∑ i ∈ Finset.range L, majA φ τ ^ (i + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have e : 2 * (L + 1 + 2) = 2 * (L + 2) + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := L)]
    have hodd : trOne (dysonTerm φ τ (2 * (L + 2) + 1)) = 0 := trOne_odd φ τ (L + 2)
    rw [hodd, add_zero]
    have heven := trOne_even_le φ τ L
    calc ‖(∑ k ∈ Finset.range (2 * (L + 2)), trOne (dysonTerm φ τ k)) +
          trOne (dysonTerm φ τ (2 * (L + 2))) - ∑ k ∈ Finset.range 4, trOne (dysonTerm φ τ k)‖
        ≤ ‖(∑ k ∈ Finset.range (2 * (L + 2)), trOne (dysonTerm φ τ k)) -
            ∑ k ∈ Finset.range 4, trOne (dysonTerm φ τ k)‖ +
          ‖trOne (dysonTerm φ τ (2 * (L + 2)))‖ := by
          rw [add_sub_right_comm]; exact norm_add_le _ _
      _ ≤ Real.exp τ * (majA φ τ + majW φ τ 1) * ∑ i ∈ Finset.range L, majA φ τ ^ (i + 1) +
            Real.exp τ * (majA φ τ + majW φ τ 1) * majA φ τ ^ (L + 1) := add_le_add ih heven
      _ = _ := by ring

/-- **Remainder bound.** For `A' < 1`:
`‖Δ(iτ) - Σ_{k<4} tr N_k(1)‖ ≤ e^τ (A' + W(1)) A'/(1-A')`. -/
theorem dyson_remainder_le (φ : PotPair) (τ : ℝ) (hA : majA φ τ < 1) :
    ‖NlsGge.GK38.discrim φ (Complex.I * τ) - ∑ k ∈ Finset.range 4, trOne (dysonTerm φ τ k)‖ ≤
      Real.exp τ * (majA φ τ + majW φ τ 1) * (majA φ τ / (1 - majA φ τ)) := by
  have hA0 := majA_nonneg φ τ
  have hW0 : 0 ≤ majW φ τ 1 :=
    mul_nonneg (Real.exp_pos _).le (intervalIntegral.integral_nonneg zero_le_one fun s hs =>
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (majJ_nonneg φ τ hs.1))
  have hlim : Tendsto (fun L => (∑ k ∈ Finset.range (2 * (L + 2)), trOne (dysonTerm φ τ k)) -
      ∑ k ∈ Finset.range 4, trOne (dysonTerm φ τ k)) atTop
      (𝓝 (NlsGge.GK38.discrim φ (Complex.I * τ) - ∑ k ∈ Finset.range 4, trOne (dysonTerm φ τ k))) := by
    refine ((dyson_tendsto φ τ).comp ?_).sub_const _
    exact tendsto_atTop_mono (fun L => by show L ≤ 2 * (L + 2); omega) tendsto_id
  refine le_of_tendsto' hlim.norm fun L => (partial_even_bound φ τ L).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.exp_pos _).le (add_nonneg hA0 hW0))
  have hgeom : ∑ i ∈ Finset.range L, majA φ τ ^ (i + 1) = majA φ τ * ∑ i ∈ Finset.range L, majA φ τ ^ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hgeom, ← mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ hA0
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := L) hA0 hA
  rwa [← Finset.range_eq_Ico, pow_zero] at this

end NlsGge.ThirdConsultation.M016DysonAux
