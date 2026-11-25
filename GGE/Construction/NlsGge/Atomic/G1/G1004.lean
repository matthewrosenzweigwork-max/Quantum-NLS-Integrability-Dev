                                                                                                                                  
import Mathlib
import NlsGge.Atomic.G1.G1003
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairAnalytic
import NlsGge.GK38.PairAnalyticOp
import NlsGge.GK38.PairVolterraDefs
import NlsGge.GK38.PairVolterraOp
import NlsGge.GK38.PairVolterraPower

section
                                                                                              
                                                                                                
                                                                                                         
                                                                             
                                                                                                         
                                                                                                       
                                                            

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.Atomic.G1004GenT

open NlsGge.GK38 NlsGge.Pilot

noncomputable section

/-- Continuous matrix functions on `[0,T]` (the `[0,1]` type `PairCont38` at `T = 1`). -/
abbrev PairContT (T : ℝ) : Type := C(Set.Icc (0 : ℝ) T, Fin 2 → Fin 2 → ℂ)

/-! ### Periodicity and unit windows -/

theorem ae_shift_nat_T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E}
    (hg : ∀ᵐ t : ℝ, g (t + 1) = g t) (k : ℕ) : ∀ᵐ t : ℝ, g (t + k) = g t := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : ∀ᵐ t : ℝ, g ((t + k) + 1) = g (t + k) :=
      (measurePreserving_add_right (volume : Measure ℝ) (k : ℝ)).quasiMeasurePreserving.ae hg
    filter_upwards [h1, ih] with t h1 ih
    rw [show t + ((k + 1 : ℕ) : ℝ) = (t + k) + 1 by push_cast; ring, h1, ih]

theorem intervalIntegrable_unit_window_T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : ∀ᵐ t : ℝ, g (t + 1) = g t) (h01 : IntervalIntegrable g volume 0 1)
    (k : ℕ) : IntervalIntegrable g volume (k : ℝ) ((k : ℝ) + 1) := by
  have hAe : (fun x => g (x + -(k : ℝ))) =ᵐ[volume] g := by
    filter_upwards [(measurePreserving_add_right (volume : Measure ℝ) (-(k : ℝ))).quasiMeasurePreserving.ae
      (ae_shift_nat_T hg k)] with x hx
    simpa using hx.symm
  have h3 := h01.comp_add_right (-(k : ℝ))
  have e1 : (0 : ℝ) - -(k : ℝ) = (k : ℝ) := by ring
  have e2 : (1 : ℝ) - -(k : ℝ) = (k : ℝ) + 1 := by ring
  rw [e1, e2] at h3
  exact h3.congr_ae hAe.restrict

theorem intervalIntegrable_nat_of_periodic_ae_T {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} (hg : ∀ᵐ t : ℝ, g (t + 1) = g t)
    (h01 : IntervalIntegrable g volume 0 1) (n : ℕ) :
    IntervalIntegrable g volume 0 (n : ℝ) := by
  have hstep : ∀ k < n, IntervalIntegrable g volume ((fun j : ℕ => (j : ℝ)) k)
      ((fun j : ℕ => (j : ℝ)) (k + 1)) := fun k _ => by
    have h := intervalIntegrable_unit_window_T hg h01 k
    push_cast
    exact h
  have := IntervalIntegrable.trans_iterate hstep
  simpa using this

theorem intervalIntegrable_of_periodic_T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : ∀ᵐ t : ℝ, g (t + 1) = g t) (h01 : IntervalIntegrable g volume 0 1)
    {T : ℝ} (hT : 0 ≤ T) : IntervalIntegrable g volume 0 T :=
  (intervalIntegrable_nat_of_periodic_ae_T hg h01 (Nat.ceil T)).mono_set (by
    rw [Set.uIcc_of_le hT, Set.uIcc_of_le (Nat.cast_nonneg _)]
    exact Set.Icc_subset_Icc le_rfl (Nat.le_ceil T))

theorem integral_nat_of_periodic_ae_T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : ∀ᵐ t : ℝ, g (t + 1) = g t) (h01 : IntervalIntegrable g volume 0 1)
    (n : ℕ) : ∫ s in (0 : ℝ)..(n : ℝ), g s = n • ∫ s in (0 : ℝ)..1, g s := by
  have hint : ∀ k < n, IntervalIntegrable g volume ((fun j : ℕ => (j : ℝ)) k)
      ((fun j : ℕ => (j : ℝ)) (k + 1)) := fun k _ => by
    have h := intervalIntegrable_unit_window_T hg h01 k
    push_cast
    exact h
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
    (a := fun j : ℕ => (j : ℝ)) hint
  have hsum' : ∑ k ∈ Finset.range n, ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x =
      ∫ x in (0 : ℝ)..(n : ℝ), g x := by
    simpa using hsum
  have hterm : ∀ k : ℕ, ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x = ∫ x in (0 : ℝ)..1, g x := by
    intro k
    have h := intervalIntegral.integral_comp_add_right g (k : ℝ) (a := 0) (b := 1)
    rw [zero_add, add_comm (1 : ℝ) (k : ℝ)] at h
    push_cast
    rw [← h]
    exact intervalIntegral.integral_congr_ae (by
      filter_upwards [ae_shift_nat_T hg k] with x hx using fun _ => hx)
  rw [← hsum']
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  simp [Finset.sum_const, Finset.card_range]

/-! ### The weight `potW38` on `[0,T]` -/

theorem potW38_periodic_ae_T (φ : PotPair) : ∀ᵐ t : ℝ, potW38 φ (t + 1) = potW38 φ t := by
  filter_upwards [coverRep38_periodic_ae φ.1, coverRep38_periodic_ae φ.2] with t h1 h2
  simp only [potW38, potRepFst38, potRepSnd38, h1, h2]

theorem intervalIntegrable_potW38_T (φ : PotPair) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (potW38 φ) volume 0 T :=
  intervalIntegrable_of_periodic_T (potW38_periodic_ae_T φ) (intervalIntegrable_potW38 φ) hT

/-- The weight bound: `∫₀ᵀ potW38 φ ≤ ⌈T⌉₊ · potL1Norm38 φ` (book `(1.2)` weight on `[0,T]`). -/
theorem integral_potW38_le_ceil (φ : PotPair) {T : ℝ} (hT : 0 ≤ T) :
    ∫ s in (0 : ℝ)..T, potW38 φ s ≤ (Nat.ceil T : ℝ) * potL1Norm38 φ := by
  have hle : ∫ s in (0 : ℝ)..T, potW38 φ s ≤ ∫ s in (0 : ℝ)..((Nat.ceil T : ℕ) : ℝ), potW38 φ s :=
    intervalIntegral.integral_mono_interval le_rfl hT (Nat.le_ceil T)
      (Filter.Eventually.of_forall fun s => potW38_nonneg φ s)
      (intervalIntegrable_nat_of_periodic_ae_T (potW38_periodic_ae_T φ) (intervalIntegrable_potW38 φ)
        (Nat.ceil T))
  calc ∫ s in (0 : ℝ)..T, potW38 φ s
      ≤ ∫ s in (0 : ℝ)..((Nat.ceil T : ℕ) : ℝ), potW38 φ s := hle
    _ = (Nat.ceil T : ℝ) * ∫ s in (0 : ℝ)..1, potW38 φ s := by
        rw [integral_nat_of_periodic_ae_T (potW38_periodic_ae_T φ) (intervalIntegrable_potW38 φ)
          (Nat.ceil T), nsmul_eq_mul]
    _ = (Nat.ceil T : ℝ) * potL1Norm38 φ := by rw [potL1Norm38_eq_integral]

/-! ### The coefficient on `[0,T]` and the extension `ext38T` -/

theorem intervalIntegrable_coverRep38_T (f : PhysicalL2) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (coverRep38 f) volume 0 T :=
  intervalIntegrable_of_periodic_T (coverRep38_periodic_ae f) (intervalIntegrable_coverRep38_one f) hT

theorem intervalIntegrable_potCoeff38_entryT (φ : PotPair) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    IntervalIntegrable (fun s => potCoeff38 φ s i j) volume 0 T := by
  fin_cases i <;> fin_cases j <;> simp only [potCoeff38]
  · exact intervalIntegrable_const
  · simpa [potRepFst38] using (intervalIntegrable_coverRep38_T φ.1 hT).const_mul Complex.I
  · simpa [potRepSnd38] using (intervalIntegrable_coverRep38_T φ.2 hT).const_mul (-Complex.I)
  · exact intervalIntegrable_const

/-- The constant-on-the-ends extension of `N : PairContT T` to `ℝ`. -/
def ext38T {T : ℝ} (hT : 0 ≤ T) (N : PairContT T) : ℝ → PairMat38 := Set.IccExtend hT N

theorem continuous_ext38T {T : ℝ} (hT : 0 ≤ T) (N : PairContT T) : Continuous (ext38T hT N) :=
  N.continuous.Icc_extend'

theorem ext38T_of_mem {T : ℝ} (hT : 0 ≤ T) (N : PairContT T) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T) : ext38T hT N s = N ⟨s, hs⟩ :=
  Set.IccExtend_of_mem _ _ hs

theorem norm_ext38T_entry_le {T : ℝ} (hT : 0 ≤ T) (N : PairContT T) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    ‖ext38T hT N s i j‖ ≤ ‖N‖ := by
  rw [ext38T_of_mem hT N hs]
  exact (norm_le_pi_norm (N ⟨s, hs⟩ i) j).trans
    ((norm_le_pi_norm (N ⟨s, hs⟩) i).trans (N.norm_coe_le_norm ⟨s, hs⟩))

end

end NlsGge.Atomic.G1004GenT

end

section
                                                                                                    
                                                                                             
                                                                                                   
                                                                                                               
                                                                                              

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.Atomic.G1004GenT

open NlsGge.GK38

noncomputable section

theorem uIcc_zero_subsetT {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Set.uIcc (0 : ℝ) t ⊆ Set.uIcc 0 T := by
  rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hT]
  exact Set.Icc_subset_Icc le_rfl ht.2

theorem intervalIntegrable_triple_entryT (φ : PotPair) {T : ℝ} (hT : 0 ≤ T) {K N : ℝ → PairMat38}
    (hK : Continuous K) (hN : Continuous N) (i j : Fin 2) :
    IntervalIntegrable (fun s => (K s * potCoeff38 φ s * N s) i j) volume 0 T := by
  simp_rw [mul3_apply]
  refine intervalIntegrable_fsum _ fun l _ => intervalIntegrable_fsum _ fun k _ => ?_
  have hK' : Continuous fun s => K s i k := (continuous_apply k).comp ((continuous_apply i).comp hK)
  have hN' : Continuous fun s => N s l j := (continuous_apply j).comp ((continuous_apply l).comp hN)
  exact (((intervalIntegrable_potCoeff38_entryT φ hT k l).continuousOn_mul
    hK'.continuousOn).mul_continuousOn hN'.continuousOn)

theorem intervalIntegrable_triple_entryT_of_mem (φ : PotPair) {T : ℝ} (hT : 0 ≤ T) {K N : ℝ → PairMat38}
    (hK : Continuous K) (hN : Continuous N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    IntervalIntegrable (fun s => (K s * potCoeff38 φ s * N s) i j) volume 0 t :=
  (intervalIntegrable_triple_entryT φ hT hK hN i j).mono_set (uIcc_zero_subsetT hT ht)

/-! ### The operator on `[0,T]` -/

/-- `(𝒱 N)(t) = ∫₀ᵗ E_z(t-s) Φ̃(s) N(s) ds`, entrywise, on `[0,T]`. -/
def volterraFunT (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T) (t : ℝ) : PairMat38 :=
  Matrix.of fun i j => ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * ext38T hT N s) i j

/-- The `t`-independent kernel integral `∫₀ᵗ E_z(-s) Φ̃(s) N(s) ds` on `[0,T]`. -/
def volterraKerT (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T) (t : ℝ) : PairMat38 :=
  Matrix.of fun i j => ∫ s in (0 : ℝ)..t, (freeE z (-s) * potCoeff38 φ s * ext38T hT N s) i j

theorem volterraFunT_apply (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T) (t : ℝ)
    (i j : Fin 2) :
    volterraFunT φ z hT N t i j =
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * ext38T hT N s) i j := rfl

theorem volterraFunT_eq (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T) (t : ℝ) :
    volterraFunT φ z hT N t = freeE z t * volterraKerT φ z hT N t := by
  ext i j
  rw [freeE_mul_apply, volterraFunT_apply]
  simp only [volterraKerT, Matrix.of_apply]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [sub_eq_add_neg, freeE_add, mul_assoc, mul_assoc, ← mul_assoc (freeE z (-s)), freeE_mul_apply]

theorem continuousOn_volterraKerT_entry (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T)
    (i j : Fin 2) :
    ContinuousOn (fun t => volterraKerT φ z hT N t i j) (Set.Icc (0 : ℝ) T) := by
  have hKc : Continuous fun s : ℝ => freeE z (-s) := (continuous_freeE z).comp continuous_neg
  have hint := intervalIntegrable_triple_entryT φ hT hKc (continuous_ext38T hT N) i j
  have h2 := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hint
  have h3 := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := T) (by
    rwa [Set.uIcc_of_le hT])
  rw [Set.uIcc_of_le hT] at h3
  exact h3

/-- `𝒱 N` as a continuous function on `[0,T]`. -/
def volterraMapT (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T) : PairContT T where
  toFun t := fun i j => volterraFunT φ z hT N t i j
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hk := (continuousOn_volterraKerT_entry φ z hT N i j).domRestrict
    have he : Continuous fun t : Set.Icc (0 : ℝ) T => freeE z t i i :=
      ((continuous_apply i).comp ((continuous_apply i).comp (continuous_freeE z))).comp
        continuous_subtype_val
    refine (he.mul hk).congr fun t => ?_
    show freeE z t i i * volterraKerT φ z hT N t i j = volterraFunT φ z hT N t i j
    rw [volterraFunT_eq, freeE_mul_apply]

theorem volterraMapT_apply (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T)
    (t : Set.Icc (0 : ℝ) T) (i j : Fin 2) : volterraMapT φ z hT N t i j = volterraFunT φ z hT N t i j :=
  rfl

theorem volterraMapT_add (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N₁ N₂ : PairContT T) :
    volterraMapT φ z hT (N₁ + N₂) = volterraMapT φ z hT N₁ + volterraMapT φ z hT N₂ := by
  ext t i j
  have hadd : ∀ s, ext38T hT (N₁ + N₂) s = ext38T hT N₁ s + ext38T hT N₂ s := fun s => rfl
  simp only [volterraMapT_apply, ContinuousMap.add_apply, Pi.add_apply, volterraFunT_apply, hadd,
    mul_add, Matrix.add_apply]
  exact intervalIntegral.integral_add
    (intervalIntegrable_triple_entryT_of_mem φ hT ((continuous_freeE z).comp
      (continuous_const.sub continuous_id)) (continuous_ext38T hT N₁) t.2 i j)
    (intervalIntegrable_triple_entryT_of_mem φ hT ((continuous_freeE z).comp
      (continuous_const.sub continuous_id)) (continuous_ext38T hT N₂) t.2 i j)

theorem volterraMapT_smul (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (c : ℂ) (N : PairContT T) :
    volterraMapT φ z hT (c • N) = c • volterraMapT φ z hT N := by
  ext t i j
  have hsmul : ∀ s, ext38T hT (c • N) s = c • ext38T hT N s := fun s => rfl
  simp only [volterraMapT_apply, ContinuousMap.smul_apply, Pi.smul_apply, volterraFunT_apply, hsmul,
    Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  exact intervalIntegral.integral_const_mul c _

theorem norm_volterraFunT_entry_le (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T)
    (β : ℝ → ℝ) (hβ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i j, ‖ext38T hT N s i j‖ ≤ β s)
    (hint : IntervalIntegrable (fun s => potW38 φ s * β s) volume 0 T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    ‖volterraFunT φ z hT N t i j‖ ≤
      ∫ s in (0 : ℝ)..t, Real.exp (|z.im| * (t - s)) * (potW38 φ s * β s) := by
  rw [volterraFunT_apply]
  refine intervalIntegral.norm_integral_le_of_norm_le ht.1 ?_ ?_
  · refine Filter.Eventually.of_forall fun s hs => ?_
    have hs' : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans ht.2⟩
    exact norm_triple_entry_le z (sub_nonneg.mpr hs.2) φ s (ext38T hT N s) (hβ s hs') i j
  · have hc : Continuous fun s : ℝ => Real.exp (|z.im| * (t - s)) := by fun_prop
    exact (hint.mono_set (uIcc_zero_subsetT hT ht)).continuousOn_mul hc.continuousOn

/-- Entry bound with the window weight: `‖𝒱 N (t)‖ ≤ e^{|Im z| T} · (⌈T⌉₊ · potL1Norm38 φ) · ‖N‖`. -/
theorem norm_volterraFunT_entry_le_const (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    ‖volterraFunT φ z hT N t i j‖ ≤
      Real.exp (|z.im| * T) * ((Nat.ceil T : ℝ) * potL1Norm38 φ) * ‖N‖ := by
  have hint : IntervalIntegrable (fun s => potW38 φ s * ‖N‖) volume 0 T :=
    (intervalIntegrable_potW38_T φ hT).mul_const _
  refine (norm_volterraFunT_entry_le φ z hT N (fun _ => ‖N‖)
    (fun s hs i j => norm_ext38T_entry_le hT N hs i j) hint ht i j).trans ?_
  have hw : IntervalIntegrable (fun s => potW38 φ s) volume 0 t :=
    (intervalIntegrable_potW38_T φ hT).mono_set (uIcc_zero_subsetT hT ht)
  have hc : Continuous fun s : ℝ => Real.exp (|z.im| * (t - s)) := by fun_prop
  calc ∫ s in (0 : ℝ)..t, Real.exp (|z.im| * (t - s)) * (potW38 φ s * ‖N‖)
      ≤ ∫ s in (0 : ℝ)..t, Real.exp (|z.im| * T) * (potW38 φ s * ‖N‖) := by
        refine intervalIntegral.integral_mono_on ht.1 ?_ ?_ fun s hs => ?_
        · exact (hw.mul_const _).continuousOn_mul hc.continuousOn
        · exact (hw.mul_const _).const_mul _
        · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
            (mul_nonneg (potW38_nonneg φ s) (norm_nonneg N))
          have hab : 0 ≤ |z.im| := abs_nonneg _
          have h3 : t - s ≤ T := by linarith [hs.1, ht.2]
          exact mul_le_mul_of_nonneg_left h3 hab
    _ = Real.exp (|z.im| * T) * ‖N‖ * ∫ s in (0 : ℝ)..t, potW38 φ s := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]; ring
    _ ≤ Real.exp (|z.im| * T) * ‖N‖ * ∫ s in (0 : ℝ)..T, potW38 φ s := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (Filter.Eventually.of_forall fun s => potW38_nonneg φ s) (intervalIntegrable_potW38_T φ hT)
    _ ≤ Real.exp (|z.im| * T) * ‖N‖ * ((Nat.ceil T : ℝ) * potL1Norm38 φ) :=
        mul_le_mul_of_nonneg_left (integral_potW38_le_ceil φ hT) (by positivity)
    _ = _ := by ring

/-- The Volterra operator on `PairContT T` (sup norm). -/
def volterraPT (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) : PairContT T →L[ℂ] PairContT T :=
  LinearMap.mkContinuous
    { toFun := volterraMapT φ z hT
      map_add' := volterraMapT_add φ z hT
      map_smul' := fun c N => by simpa using volterraMapT_smul φ z hT c N }
    (Real.exp (|z.im| * T) * ((Nat.ceil T : ℝ) * potL1Norm38 φ)) fun N => by
      have hC : 0 ≤ Real.exp (|z.im| * T) * ((Nat.ceil T : ℝ) * potL1Norm38 φ) * ‖N‖ := by
        have := potL1Norm38_nonneg φ
        positivity
      refine ((ContinuousMap.norm_le _ hC).2 fun t => ?_)
      refine (pi_norm_le_iff_of_nonneg hC).2 fun i => (pi_norm_le_iff_of_nonneg hC).2 fun j => ?_
      exact norm_volterraFunT_entry_le_const φ z hT N t.2 i j

theorem norm_volterraPT_le (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖volterraPT φ z hT‖ ≤ Real.exp (|z.im| * T) * ((Nat.ceil T : ℝ) * potL1Norm38 φ) :=
  LinearMap.mkContinuous_norm_le _ (by
    have := potL1Norm38_nonneg φ
    positivity) _

end

end NlsGge.Atomic.G1004GenT


end

section
                                                                                                  
                                                 

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.Atomic.G1004GenT

open NlsGge.GK38

noncomputable section

theorem volterraPT_apply (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T)
    (t : Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    volterraPT φ z hT N t i j = volterraFunT φ z hT N t i j := rfl

theorem potPrim38_le_T (φ : PotPair) {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    potPrim38 φ t ≤ (Nat.ceil T : ℝ) * potL1Norm38 φ := by
  refine le_trans ?_ (integral_potW38_le_ceil φ hT)
  exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (Filter.Eventually.of_forall fun s => potW38_nonneg φ s) (intervalIntegrable_potW38_T φ hT)

theorem continuousOn_potPrim38_T (φ : PotPair) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (potPrim38 φ) (Set.Icc (0 : ℝ) T) := by
  have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := T)
    (f := potW38 φ)
    (by rw [Set.uIcc_of_le hT]
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp (intervalIntegrable_potW38_T φ hT))
  rwa [Set.uIcc_of_le hT] at h

/-- Weighted iterate estimate on `[0,T]`. -/
theorem norm_volterraT_pow_entry_le_weighted (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (N : PairContT T) (γ : ℝ)
    (hN : ∀ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2),
      ‖N ⟨s, hs⟩ i j‖ ≤ Real.exp (|z.im| * s) * γ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    ‖((volterraPT φ z hT ^ n) N) ⟨t, ht⟩ i j‖ ≤
      Real.exp (|z.im| * t) * (potPrim38 φ t ^ n / n.factorial) * γ := by
  induction n generalizing t i j with
  | zero =>
    simp only [pow_zero, one_apply_eq_self, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    exact hN t ht i j
  | succ n ih =>
    set M : PairContT T := (volterraPT φ z hT ^ n) N with hM
    have hpow : (volterraPT φ z hT ^ (n + 1)) N = volterraPT φ z hT M := by
      rw [pow_succ', mul_apply_eq_comp]
    rw [hpow, volterraPT_apply]
    set a : ℝ := |z.im| with ha
    set β : ℝ → ℝ := fun s => Real.exp (a * s) * (potPrim38 φ s ^ n / n.factorial) * γ with hβdef
    have hβ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i j, ‖ext38T hT M s i j‖ ≤ β s := fun s hs i j => by
      rw [ext38T_of_mem hT M hs]; exact ih hs i j
    have hβc : ContinuousOn β (Set.uIcc 0 T) := by
      rw [Set.uIcc_of_le hT]
      have h1 : ContinuousOn (fun s : ℝ => Real.exp (a * s)) (Set.Icc 0 T) := by fun_prop
      have h2 := continuousOn_potPrim38_T φ hT
      simp only [hβdef]
      exact ((h1.mul ((h2.pow n).div_const _)).mul continuousOn_const)
    have hint : IntervalIntegrable (fun s => potW38 φ s * β s) volume 0 T :=
      (intervalIntegrable_potW38_T φ hT).mul_continuousOn hβc
    refine (norm_volterraFunT_entry_le φ z hT M β hβ hint ht i j).trans (le_of_eq ?_)
    have hcalc : ∀ s ∈ Set.uIcc (0 : ℝ) t, Real.exp (a * (t - s)) * (potW38 φ s * β s) =
        (Real.exp (a * t) * γ / n.factorial) * (potW38 φ s * potPrim38 φ s ^ n) := by
      intro s _
      have h : Real.exp (a * (t - s)) * Real.exp (a * s) = Real.exp (a * t) := by
        rw [← Real.exp_add]; ring_nf
      simp only [hβdef]
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      linear_combination (potW38 φ s * potPrim38 φ s ^ n * γ) * h
    rw [intervalIntegral.integral_congr hcalc, intervalIntegral.integral_const_mul]
    have hw : IntervalIntegrable (potW38 φ) volume 0 t :=
      (intervalIntegrable_potW38_T φ hT).mono_set (uIcc_zero_subsetT hT ht)
    have hkey := integral_mul_primitive_pow hw n
    have : ∫ s in (0 : ℝ)..t, potW38 φ s * potPrim38 φ s ^ n =
        potPrim38 φ t ^ (n + 1) / (n + 1) := hkey
    rw [this, Nat.factorial_succ]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp

theorem norm_volterraT_pow_entry_le (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (N : PairContT T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    ‖((volterraPT φ z hT ^ n) N) ⟨t, ht⟩ i j‖ ≤
      Real.exp (|z.im| * t) * (potPrim38 φ t ^ n / n.factorial) * ‖N‖ := by
  refine norm_volterraT_pow_entry_le_weighted φ z hT n N ‖N‖ (fun s hs i j => ?_) ht i j
  have h1 : 1 ≤ Real.exp (|z.im| * s) := Real.one_le_exp (mul_nonneg (abs_nonneg _) hs.1)
  exact ((norm_le_pi_norm (N ⟨s, hs⟩ i) j).trans ((norm_le_pi_norm (N ⟨s, hs⟩) i).trans
      (N.norm_coe_le_norm ⟨s, hs⟩))).trans (le_mul_of_one_le_left (norm_nonneg _) h1)

/-- `‖𝒱ⁿ‖ ≤ e^{|Im z| T} (⌈T⌉ ‖φ‖₁)ⁿ / n!`. -/
theorem norm_volterraPT_pow_le (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    ‖volterraPT φ z hT ^ n‖ ≤
      Real.exp (|z.im| * T) * (((Nat.ceil T : ℝ) * potL1Norm38 φ) ^ n / n.factorial) := by
  have hL := potL1Norm38_nonneg φ
  have hLT : 0 ≤ (Nat.ceil T : ℝ) * potL1Norm38 φ := by positivity
  have hC : 0 ≤ Real.exp (|z.im| * T) * (((Nat.ceil T : ℝ) * potL1Norm38 φ) ^ n / n.factorial) := by
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun N => ?_
  have hC' : 0 ≤ Real.exp (|z.im| * T) *
      (((Nat.ceil T : ℝ) * potL1Norm38 φ) ^ n / n.factorial) * ‖N‖ := by positivity
  refine (ContinuousMap.norm_le _ hC').2 fun t => ?_
  refine (pi_norm_le_iff_of_nonneg hC').2 fun i => (pi_norm_le_iff_of_nonneg hC').2 fun j => ?_
  refine (norm_volterraT_pow_entry_le φ z hT n N t.2 i j).trans ?_
  have h1 : Real.exp (|z.im| * (t : ℝ)) ≤ Real.exp (|z.im| * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.2.2 (abs_nonneg _))
  have h2 : potPrim38 φ t ^ n ≤ ((Nat.ceil T : ℝ) * potL1Norm38 φ) ^ n :=
    pow_le_pow_left₀ (potPrim38_nonneg φ t.2.1) (potPrim38_le_T φ hT t.2) n
  have hf : (0 : ℝ) < n.factorial := by positivity
  have h3 : potPrim38 φ t ^ n / n.factorial ≤ ((Nat.ceil T : ℝ) * potL1Norm38 φ) ^ n / n.factorial :=
    div_le_div_of_nonneg_right h2 hf.le
  have h4 : 0 ≤ potPrim38 φ t ^ n / n.factorial := by
    have := potPrim38_nonneg φ t.2.1; positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h3 h4 (Real.exp_nonneg _)) (norm_nonneg _)

theorem exists_norm_volterraPT_pow_lt_one (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ n : ℕ, ‖volterraPT φ z hT ^ n‖ < 1 := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop
    ((Nat.ceil T : ℝ) * potL1Norm38 φ)).const_mul (Real.exp (|z.im| * T))
  rw [mul_zero] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
  exact ⟨n, (norm_volterraPT_pow_le φ z hT n).trans_lt hn⟩

theorem isUnit_one_sub_volterraPT (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    IsUnit (1 - volterraPT φ z hT) := by
  obtain ⟨n, hn⟩ := exists_norm_volterraPT_pow_lt_one φ z hT
  have h1 : IsUnit (1 - volterraPT φ z hT ^ n) :=
    ⟨Units.oneSub (volterraPT φ z hT ^ n) hn, Units.val_oneSub (volterraPT φ z hT ^ n) hn⟩
  have h2 : (1 - volterraPT φ z hT) * ∑ i ∈ Finset.range n, volterraPT φ z hT ^ i =
      1 - volterraPT φ z hT ^ n :=
    mul_neg_geom_sum (R := PairContT T →L[ℂ] PairContT T) _ _
  rw [← h2] at h1
  have hc : Commute (1 - volterraPT φ z hT) (∑ i ∈ Finset.range n, volterraPT φ z hT ^ i) :=
    Commute.sum_right _ _ _ fun i _ =>
      Commute.sub_left (R := PairContT T →L[ℂ] PairContT T) (Commute.one_left _)
        (Commute.self_pow _ _)
  exact ((Commute.isUnit_mul_iff hc).mp h1).1

end

end NlsGge.Atomic.G1004GenT


end

section
                                                                                              
                                                                                               

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.Atomic.G1004GenT

open NlsGge.GK38

noncomputable section

/-! ### Linearity of `φ ↦ 𝒱_φ` on `[0,T]` -/

theorem volterraFunT_sub (φ ψ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    volterraFunT (φ - ψ) z hT N t i j =
      volterraFunT φ z hT N t i j - volterraFunT ψ z hT N t i j := by
  simp only [volterraFunT_apply]
  have hK : Continuous fun s : ℝ => freeE z (t - s) := (continuous_freeE z).comp
    (continuous_const.sub continuous_id)
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_triple_entryT_of_mem φ hT hK (continuous_ext38T hT N) ht i j)
    (intervalIntegrable_triple_entryT_of_mem ψ hT hK (continuous_ext38T hT N) ht i j)]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [potCoeff38_sub_ae φ ψ] with s hs _
  rw [hs, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]

theorem volterraFunT_smul_potential (c : ℂ) (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (N : PairContT T) (t : ℝ) (i j : Fin 2) :
    volterraFunT (c • φ) z hT N t i j = c * volterraFunT φ z hT N t i j := by
  simp only [volterraFunT_apply]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [potCoeff38_smul_ae c φ] with s hs _
  rw [hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

theorem volterraPT_sub (φ ψ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    volterraPT (φ - ψ) z hT = volterraPT φ z hT - volterraPT ψ z hT := by
  ext N t i j
  exact volterraFunT_sub φ ψ z hT N t.2 i j

theorem volterraPT_smul_potential (c : ℂ) (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    volterraPT (c • φ) z hT = c • volterraPT φ z hT := by
  ext N t i j
  exact volterraFunT_smul_potential c φ z hT N t i j

theorem volterraPT_add (φ ψ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    volterraPT (φ + ψ) z hT = volterraPT φ z hT + volterraPT ψ z hT := by
  have h : φ + ψ = φ - (-1 : ℂ) • ψ := by simp [sub_eq_add_neg]
  have e : (-1 : ℂ) • volterraPT ψ z hT = -volterraPT ψ z hT := by ext N t i j; simp
  rw [h, volterraPT_sub, volterraPT_smul_potential, e]
  ext N t i j; simp

/-! ### Left multiplication by a diagonal of scalar functions, on `[0,T]` -/

abbrev ScalT (T : ℝ) : Type := C(Set.Icc (0 : ℝ) T, ℂ)

def mulRowFunT {T : ℝ} (i : Fin 2) (a : ScalT T) (N : PairContT T) : PairContT T where
  toFun t := fun i' j => if i' = i then a t * N t i' j else 0
  continuous_toFun := by
    refine continuous_pi fun i' => continuous_pi fun j => ?_
    by_cases h : i' = i
    · simp only [h, ite_true]
      exact a.continuous.mul ((continuous_apply j).comp ((continuous_apply i).comp N.continuous))
    · simp only [h, ite_false]; exact continuous_const

@[simp] theorem mulRowFunT_apply {T : ℝ} (i : Fin 2) (a : ScalT T) (N : PairContT T)
    (t : Set.Icc (0 : ℝ) T) (i' j : Fin 2) :
    mulRowFunT i a N t i' j = if i' = i then a t * N t i' j else 0 := rfl

theorem norm_mulRowFunT_le {T : ℝ} (i : Fin 2) (a : ScalT T) (N : PairContT T) :
    ‖mulRowFunT i a N‖ ≤ ‖a‖ * ‖N‖ := by
  have hC : 0 ≤ ‖a‖ * ‖N‖ := by positivity
  refine (ContinuousMap.norm_le _ hC).2 fun t => ?_
  refine (pi_norm_le_iff_of_nonneg hC).2 fun i' => (pi_norm_le_iff_of_nonneg hC).2 fun j => ?_
  rw [mulRowFunT_apply]
  split_ifs
  · rw [norm_mul]
    refine mul_le_mul (a.norm_coe_le_norm t) ?_ (norm_nonneg _) (norm_nonneg _)
    exact (norm_le_pi_norm (N t i') j).trans
      ((norm_le_pi_norm (N t) i').trans (N.norm_coe_le_norm t))
  · simpa using hC

def mulRowLT (T : ℝ) (i : Fin 2) : ScalT T →L[ℂ] PairContT T →L[ℂ] PairContT T :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (mulRowFunT i)
      (fun a b N => by
        ext t i' j; by_cases h : i' = i <;> simp [h, add_mul])
      (fun c a N => by
        ext t i' j; by_cases h : i' = i <;> simp [h, mul_assoc])
      (fun a N M => by
        ext t i' j; by_cases h : i' = i <;> simp [h, mul_add])
      (fun c a N => by
        ext t i' j; by_cases h : i' = i
        · simp [h]; ring
        · simp [h]))
    1 (fun a N => by simpa using norm_mulRowFunT_le i a N)

@[simp] theorem mulRowLT_apply (T : ℝ) (i : Fin 2) (a : ScalT T) (N : PairContT T) :
    mulRowLT T i a N = mulRowFunT i a N := rfl

theorem analyticAt_mulRowLT (T : ℝ) (i : Fin 2) (a : ScalT T) :
    AnalyticAt ℂ (fun a : ScalT T => mulRowLT T i a) a :=
  ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ScalT T) (F := PairContT T →L[ℂ] PairContT T)
    (mulRowLT T i) a

/-! ### The free solution as an exponential in `C([0,T], ℂ)` -/

def genT (T : ℝ) (i : Fin 2) : ScalT T :=
  ⟨fun t => sgn38 i * Complex.I * (t : ℝ), by unfold sgn38; fun_prop⟩

def expGenT (T : ℝ) (z : ℂ) (i : Fin 2) : ScalT T := NormedSpace.exp (z • genT T i)

theorem expGenT_apply (T : ℝ) (z : ℂ) (i : Fin 2) (t : Set.Icc (0 : ℝ) T) :
    expGenT T z i t = Complex.exp (z * (sgn38 i * Complex.I * (t : ℝ))) := by
  unfold expGenT
  have h := NormedSpace.map_exp (𝔸 := ScalT T) (𝔹 := ℂ) (ContinuousMap.evalAlgHom ℂ ℂ t)
    (AddMonoidHomClass.continuous_of_bound _ 1 fun g => by
      simpa using g.norm_coe_le_norm t) (z • genT T i)
  simp only [ContinuousMap.evalAlgHom_apply] at h
  rw [h, ← Complex.exp_eq_exp_ℂ]
  simp [genT]

theorem expGenT_eq_freeE (T : ℝ) (z : ℂ) (i : Fin 2) (t : Set.Icc (0 : ℝ) T) :
    expGenT T z i t = freeE z t i i := by
  rw [expGenT_apply, freeE_diag]

theorem analyticOnNhd_expGenT (T : ℝ) (i : Fin 2) :
    AnalyticOnNhd ℂ (fun z => expGenT T z i) Set.univ := by
  intro z _
  have h1 : AnalyticAt ℂ (fun w : ℂ => w • genT T i) z :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (genT T i)).analyticAt z
  exact (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp h1

def mulFreeT (T : ℝ) (z : ℂ) : PairContT T →L[ℂ] PairContT T :=
  mulRowLT T 0 (expGenT T z 0) + mulRowLT T 1 (expGenT T z 1)

theorem analyticOnNhd_mulFreeT (T : ℝ) : AnalyticOnNhd ℂ (mulFreeT T) Set.univ := fun z hz =>
  ((analyticAt_mulRowLT T 0 _).comp (analyticOnNhd_expGenT T 0 z hz)).add
    ((analyticAt_mulRowLT T 1 _).comp (analyticOnNhd_expGenT T 1 z hz))

theorem mulFreeT_apply (T : ℝ) (z : ℂ) (N : PairContT T) (t : Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    mulFreeT T z N t i j = freeE z t i i * N t i j := by
  fin_cases i <;> simp [mulFreeT, expGenT_eq_freeE]

theorem ext38T_mulFreeT {T : ℝ} (hT : 0 ≤ T) (z : ℂ) (N : PairContT T) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ext38T hT (mulFreeT T z N) s = freeE z s * ext38T hT N s := by
  ext i j
  rw [freeE_mul_apply, ext38T_of_mem hT _ hs, ext38T_of_mem hT _ hs]
  exact mulFreeT_apply T z N ⟨s, hs⟩ i j

theorem volterraFunT_factor (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (N : PairContT T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    volterraFunT φ z hT N t i j =
      freeE z t i i * volterraFunT φ 0 hT (mulFreeT T z N) t i j := by
  simp only [volterraFunT_apply, freeE_zero_potential, one_mul]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' : s ∈ Set.Icc (0 : ℝ) T := by
    rw [Set.uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  show (freeE z (t - s) * potCoeff38 φ s * ext38T hT N s) i j =
    freeE z t i i * (potCoeff38 φ s * ext38T hT (mulFreeT T z N) s) i j
  rw [ext38T_mulFreeT hT z N hs', ← freeE_mul_apply, sub_eq_add_neg, freeE_add, mul_assoc,
    mul_assoc, ← mul_assoc (freeE z (-s)), freeE_neg_mul_potCoeff38, mul_assoc (potCoeff38 φ s)]

theorem volterraPT_eq_mul (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    volterraPT φ z hT = mulFreeT T z * volterraPT φ 0 hT * mulFreeT T z := by
  ext N t i j
  rw [volterraPT_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    mulFreeT_apply, volterraPT_apply]
  exact volterraFunT_factor φ z hT N t.2 i j

def volterraZeroLT {T : ℝ} (hT : 0 ≤ T) : PotPair →L[ℂ] (PairContT T →L[ℂ] PairContT T) :=
  LinearMap.mkContinuous
    { toFun := fun φ => volterraPT φ 0 hT
      map_add' := fun φ ψ => volterraPT_add φ ψ 0 hT
      map_smul' := fun c φ => by
        show volterraPT (c • φ) 0 hT = c • volterraPT φ 0 hT
        exact volterraPT_smul_potential c φ 0 hT }
    (2 * (Nat.ceil T : ℝ)) fun φ => by
      refine (norm_volterraPT_le φ 0 hT).trans ?_
      have h := potL1Norm38_le_two_mul φ
      have hc : (0 : ℝ) ≤ Nat.ceil T := Nat.cast_nonneg _
      simp only [Complex.zero_im, abs_zero, zero_mul, Real.exp_zero, one_mul]
      calc (Nat.ceil T : ℝ) * potL1Norm38 φ ≤ (Nat.ceil T : ℝ) * (2 * ‖φ‖) :=
            mul_le_mul_of_nonneg_left h hc
        _ = 2 * (Nat.ceil T : ℝ) * ‖φ‖ := by ring

@[simp] theorem volterraZeroLT_apply {T : ℝ} (hT : 0 ≤ T) (φ : PotPair) :
    volterraZeroLT hT φ = volterraPT φ 0 hT := rfl

theorem analyticAt_volterraZeroLT {T : ℝ} (hT : 0 ≤ T) (φ : PotPair) :
    AnalyticAt ℂ (fun φ : PotPair => volterraZeroLT hT φ) φ :=
  ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := PotPair) (F := PairContT T →L[ℂ] PairContT T)
    (volterraZeroLT hT) φ

theorem analyticAt_mul_opT {T : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → PairContT T →L[ℂ] PairContT T} {p : E} (hf : AnalyticAt ℂ f p)
    (hg : AnalyticAt ℂ g p) : AnalyticAt ℂ (fun x => f x * g x) p :=
  (analyticAt_mul (𝕜 := ℂ) (A := PairContT T →L[ℂ] PairContT T) (f p, g p)).comp₂ hf hg

theorem analyticOnNhd_volterraPT {T : ℝ} (hT : 0 ≤ T) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => volterraPT p.1 p.2 hT) Set.univ := by
  intro p _
  have hz : AnalyticAt ℂ (fun p : PotPair × ℂ => mulFreeT T p.2) p :=
    (analyticOnNhd_mulFreeT T p.2 (Set.mem_univ _)).comp analyticAt_snd
  have hφ : AnalyticAt ℂ (fun p : PotPair × ℂ => volterraZeroLT hT p.1) p :=
    (analyticAt_volterraZeroLT hT p.1).comp analyticAt_fst
  have := analyticAt_mul_opT (analyticAt_mul_opT hz hφ) hz
  refine this.congr (Filter.Eventually.of_forall fun q => ?_)
  exact (volterraPT_eq_mul q.1 q.2 hT).symm

end

end NlsGge.Atomic.G1004GenT


end

section
                                                                                              
                                                                    

set_option autoImplicit false

open Filter Topology MeasureTheory NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.Atomic.G1004GenT

noncomputable section

def idContT (T : ℝ) : PairContT T := ContinuousMap.const _ (fun i j => if i = j then (1 : ℂ) else 0)

/-- `E_z` as an element of `PairContT T`. -/
def freeFundT (T : ℝ) (z : ℂ) : PairContT T :=
  ⟨fun t => fun i j => freeE z t i j, by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp (continuous_freeE z))).comp
      continuous_subtype_val⟩

theorem freeFundT_eq (T : ℝ) (z : ℂ) : freeFundT T z = mulFreeT T z (idContT T) := by
  ext t i j
  rw [mulFreeT_apply]
  show freeE z t i j = freeE z t i i * (if i = j then (1 : ℂ) else 0)
  fin_cases i <;> fin_cases j <;> simp [freeE]

theorem analyticOnNhd_freeFundT (T : ℝ) : AnalyticOnNhd ℂ (freeFundT T) Set.univ := by
  intro z hz
  have : freeFundT T = fun z => mulFreeT T z (idContT T) := funext (freeFundT_eq T)
  rw [this]
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := PairContT T →L[ℂ] PairContT T)
    (F := PairContT T) (ContinuousLinearMap.apply ℂ (PairContT T) (idContT T)) (mulFreeT T z)).comp
      (analyticOnNhd_mulFreeT T z hz)

/-- The fundamental solution on `[0,T]`: `(1 - 𝒱)⁻¹ E_z`. -/
def fundContT (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) : PairContT T :=
  Ring.inverse (1 - volterraPT φ z hT) (freeFundT T z)

theorem fundContT_eq_add (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    fundContT φ z hT = freeFundT T z + volterraPT φ z hT (fundContT φ z hT) := by
  have hu := isUnit_one_sub_volterraPT φ z hT
  have h := congrArg (fun S => S (freeFundT T z)) (Ring.mul_inverse_cancel _ hu)
  have h' : fundContT φ z hT - volterraPT φ z hT (fundContT φ z hT) = freeFundT T z := by
    simpa [fundContT, ContinuousLinearMap.sub_apply] using h
  rw [← h']; abel

theorem fundContT_eq_sum (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    fundContT φ z hT = (∑ k ∈ Finset.range n, (volterraPT φ z hT ^ k) (freeFundT T z)) +
      (volterraPT φ z hT ^ n) (fundContT φ z hT) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (volterraPT φ z hT ^ n) (fundContT φ z hT) =
        (volterraPT φ z hT ^ n) (freeFundT T z) +
          (volterraPT φ z hT ^ (n + 1)) (fundContT φ z hT) := by
      conv_lhs => rw [fundContT_eq_add φ z hT]
      rw [map_add, pow_succ, mul_apply_eq_comp]
    rw [Finset.sum_range_succ, add_assoc, ← h1]
    exact ih

theorem analyticAt_apply_opT {T : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Op : E → PairContT T →L[ℂ] PairContT T} {u : E → PairContT T} {p : E}
    (hT : AnalyticAt ℂ Op p) (hu : AnalyticAt ℂ u p) : AnalyticAt ℂ (fun x => Op x (u x)) p :=
  ((ContinuousLinearMap.id ℂ (PairContT T →L[ℂ] PairContT T)).analyticAt_bilinear
    (Op p, u p)).comp₂ hT hu

theorem analyticAt_ringInverse_one_sub_volterraPT {T : ℝ} (hT : 0 ≤ T) (p : PotPair × ℂ) :
    AnalyticAt ℂ (fun q : PotPair × ℂ => Ring.inverse (1 - volterraPT q.1 q.2 hT)) p := by
  have hV : AnalyticAt ℂ (fun q : PotPair × ℂ => (1 : PairContT T →L[ℂ] PairContT T) -
      volterraPT q.1 q.2 hT) p :=
    analyticAt_const.sub (analyticOnNhd_volterraPT hT p (Set.mem_univ _))
  have h0 : AnalyticAt ℂ Ring.inverse ((1 : PairContT T →L[ℂ] PairContT T) -
      volterraPT p.1 p.2 hT) :=
    analyticAt_inverse (𝕜 := ℂ) (A := PairContT T →L[ℂ] PairContT T)
      (IsUnit.unit (isUnit_one_sub_volterraPT p.1 p.2 hT))
  exact AnalyticAt.comp (g := Ring.inverse)
    (f := fun q : PotPair × ℂ => (1 : PairContT T →L[ℂ] PairContT T) - volterraPT q.1 q.2 hT) h0 hV

theorem analyticOnNhd_fundContT {T : ℝ} (hT : 0 ≤ T) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => fundContT p.1 p.2 hT) Set.univ := by
  intro p _
  exact analyticAt_apply_opT (analyticAt_ringInverse_one_sub_volterraPT hT p)
    ((analyticOnNhd_freeFundT T p.2 (Set.mem_univ _)).comp analyticAt_snd)

/-- The entry `(i,j)` at time `t`, as a continuous linear functional. -/
def fundEntryLT {T : ℝ} (t : Set.Icc (0 : ℝ) T) (i j : Fin 2) : PairContT T →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) j).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => Fin 2 → ℂ) i).comp
      (ContinuousMap.evalCLM ℂ t))

theorem analyticOnNhd_fundEntryT {T : ℝ} (hT : 0 ≤ T) (t : Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => fundContT p.1 p.2 hT t i j) Set.univ := fun p hp =>
  AnalyticAt.comp (f := fun q : PotPair × ℂ => fundContT q.1 q.2 hT)
    (g := ⇑(fundEntryLT t i j))
    (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := PairContT T) (F := ℂ) (fundEntryLT t i j)
      (fundContT p.1 p.2 hT)) (analyticOnNhd_fundContT hT p hp)

end

end NlsGge.Atomic.G1004GenT


end

section
                                                                                             
                                                                             

set_option autoImplicit false

open MeasureTheory Filter Topology NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Pilot

namespace NlsGge.Atomic.G1004GenT

noncomputable section

theorem term_eq_powT (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T),
      potentialVolterraTerm38 φ z n t = ((volterraPT φ z hT ^ n) (freeFundT T z)) ⟨t, ht⟩ := by
  induction n with
  | zero =>
    intro t ht
    simp only [potentialVolterraTerm38, freeKernelVolterraTerm38, pow_zero]
    rw [← freeE_eq]
    rfl
  | succ n ih =>
    intro t ht
    ext i j
    rw [pow_succ', ContinuousLinearMap.mul_apply, volterraPT_apply, volterraFunT_apply]
    show (potentialVolterraTerm38 φ z (n + 1) t) i j = _
    simp only [potentialVolterraTerm38, freeKernelVolterraTerm38]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ∈ Set.Icc (0 : ℝ) T := by
      have := Set.uIcc_subset_Icc (Set.left_mem_Icc.2 hT) ht hs
      exact this
    have h1 := ih s hs'
    have h2 : ext38T hT ((volterraPT φ z hT ^ n) (freeFundT T z)) s =
        ((volterraPT φ z hT ^ n) (freeFundT T z)) ⟨s, hs'⟩ := ext38T_of_mem hT _ hs'
    simp only [potentialVolterraTerm38] at h1
    rw [h2, ← h1, ← freeE_eq]
    rfl

theorem hasSum_powT (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    HasSum (fun n : ℕ => (volterraPT φ z hT ^ n) (freeFundT T z)) (fundContT φ z hT) := by
  set L : ℝ := (Nat.ceil T : ℝ) * potL1Norm38 φ with hL
  have hL0 : 0 ≤ L := by have := potL1Norm38_nonneg φ; positivity
  set c : ℝ := Real.exp (|z.im| * T) with hc
  have hbound : ∀ n : ℕ, ‖(volterraPT φ z hT ^ n) (freeFundT T z)‖ ≤
      ‖freeFundT T z‖ * c * (L ^ n / n.factorial) := by
    intro n
    calc ‖(volterraPT φ z hT ^ n) (freeFundT T z)‖ ≤ ‖volterraPT φ z hT ^ n‖ * ‖freeFundT T z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (c * (L ^ n / n.factorial)) * ‖freeFundT T z‖ :=
          mul_le_mul_of_nonneg_right (norm_volterraPT_pow_le φ z hT n) (norm_nonneg _)
      _ = ‖freeFundT T z‖ * c * (L ^ n / n.factorial) := by ring
  have hsum : Summable (fun n : ℕ => (volterraPT φ z hT ^ n) (freeFundT T z)) :=
    Summable.of_norm_bounded
      (((Real.summable_pow_div_factorial L).mul_left (‖freeFundT T z‖ * c))
        |>.congr (fun n => by ring)) hbound
  refine hsum.hasSum_iff_tendsto_nat.2 ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hrem : ∀ n : ℕ,
      ‖(∑ k ∈ Finset.range n, (volterraPT φ z hT ^ k) (freeFundT T z)) - fundContT φ z hT‖ ≤
        ‖fundContT φ z hT‖ * c * (L ^ n / n.factorial) := by
    intro n
    have h := fundContT_eq_sum φ z hT n
    have h2 : (∑ k ∈ Finset.range n, (volterraPT φ z hT ^ k) (freeFundT T z)) -
        fundContT φ z hT = -((volterraPT φ z hT ^ n) (fundContT φ z hT)) := by
      conv_rhs => rw [eq_sub_of_add_eq' h.symm]
      abel
    rw [h2, norm_neg]
    calc ‖(volterraPT φ z hT ^ n) (fundContT φ z hT)‖
        ≤ ‖volterraPT φ z hT ^ n‖ * ‖fundContT φ z hT‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (c * (L ^ n / n.factorial)) * ‖fundContT φ z hT‖ :=
          mul_le_mul_of_nonneg_right (norm_volterraPT_pow_le φ z hT n) (norm_nonneg _)
      _ = ‖fundContT φ z hT‖ * c * (L ^ n / n.factorial) := by ring
  refine squeeze_zero (fun n => norm_nonneg _) hrem ?_
  have := (FloorSemiring.tendsto_pow_div_factorial_atTop L).const_mul (‖fundContT φ z hT‖ * c)
  simpa using this

theorem hasSum_entryT (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (t : Set.Icc (0 : ℝ) T)
    (i j : Fin 2) :
    HasSum (fun n : ℕ => ((volterraPT φ z hT ^ n) (freeFundT T z)) t i j)
      (fundContT φ z hT t i j) := by
  have h := (fundEntryLT t i j).hasSum (hasSum_powT φ z hT)
  simpa [fundEntryLT] using h

section MatrixPart

open scoped Matrix.Norms.L2Operator

theorem summable_termsT (φ : PotPair) (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun n : ℕ => potentialVolterraTerm38 φ z n t) := by
  refine Summable.of_norm_bounded
    (((Real.summable_pow_div_factorial (Real.sqrt t * potentialL2NormOn38 φ t)).mul_left
      (Real.exp (|z.im| * t)))) (fun n => ?_)
  have := NlsGge.Atomic.G1.potentialVolterraTerm38_norm_le φ z n ht
  rwa [mul_div_assoc] at this

theorem tsum_terms_eq_fundContT (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∑' n : ℕ, potentialVolterraTerm38 φ z n t = (fun i j => fundContT φ z hT ⟨t, ht⟩ i j) := by
  have hS := (summable_termsT φ z ht.1).hasSum
  ext i j
  have hent : Continuous (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) :=
    LinearMap.continuous_of_finiteDimensional _
  have h1 : HasSum (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)
      ((∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j) :=
    hS.map (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) hent
  have h2 : HasSum (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)
      (fundContT φ z hT ⟨t, ht⟩ i j) := by
    have e : (fun n : ℕ => potentialVolterraTerm38 φ z n t i j) =
        fun n : ℕ => ((volterraPT φ z hT ^ n) (freeFundT T z)) ⟨t, ht⟩ i j :=
      funext fun n => by rw [term_eq_powT φ z hT n t ht]
    rw [e]
    exact hasSum_entryT φ z hT ⟨t, ht⟩ i j
  exact h1.unique h2

/-- Analyticity from entries (finite-dimensional matrices). -/
theorem analyticAt_of_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → PairMat38} {x : E} (hf : ∀ i j, AnalyticAt ℂ (fun p => f p i j) x) :
    AnalyticAt ℂ f x := by
  have hrep : f = fun p => ∑ i : Fin 2, ∑ j : Fin 2, (f p i j) • Matrix.single i j (1 : ℂ) := by
    funext p
    conv_lhs => rw [Matrix.matrix_eq_sum_single (f p)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_single]; simp
  rw [hrep]
  refine Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => ?_
  exact (hf i j).smul analyticAt_const

/-- (A) for all `t ≥ 0`. -/
theorem analytic_all (t : ℝ) (ht0 : 0 ≤ t) :
    AnalyticOnNhd ℂ (fun p : ℂ × PotPair => ∑' n : ℕ, potentialVolterraTerm38 p.2 p.1 n t)
      Set.univ := by
  have ht : t ∈ Set.Icc (0 : ℝ) t := ⟨ht0, le_rfl⟩
  intro p _
  have hfun : (fun p : ℂ × PotPair => ∑' n : ℕ, potentialVolterraTerm38 p.2 p.1 n t) =
      fun p => (fun i j => fundContT p.2 p.1 ht0 ⟨t, ht⟩ i j : PairMat38) :=
    funext fun p => tsum_terms_eq_fundContT p.2 p.1 ht0 ht
  rw [hfun]
  refine analyticAt_of_entries fun i j => ?_
  have hswap : AnalyticAt ℂ (fun q : ℂ × PotPair => (q.2, q.1)) p :=
    AnalyticAt.prod analyticAt_snd analyticAt_fst
  have h1 : AnalyticAt ℂ (fun q : PotPair × ℂ => fundContT q.1 q.2 ht0 ⟨t, ht⟩ i j) (p.2, p.1) :=
    analyticOnNhd_fundEntryT ht0 ⟨t, ht⟩ i j (p.2, p.1) (Set.mem_univ _)
  exact AnalyticAt.comp (g := fun q : PotPair × ℂ => fundContT q.1 q.2 ht0 ⟨t, ht⟩ i j)
    (f := fun q : ℂ × PotPair => (q.2, q.1)) h1 hswap

end MatrixPart

/-! ### (B) the M-test -/

section BPart

open scoped Matrix.Norms.L2Operator
open NlsGge.Atomic.G1

private theorem coverRep_periodic_two (f : PhysicalL2) :
    Function.Periodic (coverRep38 f) 2 := by
  intro t
  simp only [coverRep38, AddCircle.coe_add, AddCircle.coe_period, add_zero]

private theorem coverRep_sq_periodic_two (f : PhysicalL2) :
    Function.Periodic (fun t => ‖coverRep38 f t‖ ^ 2) 2 := by
  intro t
  change ‖coverRep38 f (t + 2)‖ ^ 2 = ‖coverRep38 f t‖ ^ 2
  rw [coverRep_periodic_two f t]

private theorem intervalIntegrable_sq_any (f : PhysicalL2) (a b : ℝ) :
    IntervalIntegrable (fun t => ‖coverRep38 f t‖ ^ 2) volume a b :=
  (coverRep_sq_periodic_two f).intervalIntegrable₀ (by norm_num)
    (intervalIntegrable_coverRep38_sq_two f) a b

/-- Integral of a periodic square density over `[0, 2m]`. -/
private theorem integral_sq_two_mul (f : PhysicalL2) (m : ℕ) :
    ∫ t in (0 : ℝ)..(2 * m), ‖coverRep38 f t‖ ^ 2 = m * (2 * ‖f‖ ^ 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hint : ∀ a b : ℝ, IntervalIntegrable (fun t => ‖coverRep38 f t‖ ^ 2) volume a b :=
      intervalIntegrable_sq_any f
    have e : (2 : ℝ) * ((m + 1 : ℕ) : ℝ) = 2 * m + 2 := by push_cast; ring
    rw [e, ← intervalIntegral.integral_add_adjacent_intervals (hint 0 (2 * m)) (hint (2 * m) (2 * m + 2)),
      ih]
    have hp := (coverRep_sq_periodic_two f).intervalIntegral_add_eq (2 * m) 0
    rw [hp, zero_add, integral_sq_coverRep38_two]
    push_cast; ring

/-- The local `L²` norm of the potential on `[0,t]`, `t ≤ T`, is bounded by `2 √m ‖φ‖`-type constant. -/
private theorem potentialL2NormOn_le (φ : PotPair) {B : ℝ} (hφ : ‖φ‖ ≤ B) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    potentialL2NormOn38 φ t ≤ 2 * Real.sqrt (⌈T / 2⌉₊ : ℝ) * B := by
  set m : ℕ := ⌈T / 2⌉₊ with hm
  have h2m : T ≤ 2 * (m : ℝ) := by
    have := Nat.le_ceil (T / 2)
    linarith
  have hB : 0 ≤ B := le_trans (norm_nonneg _) hφ
  have h1 : ‖φ.1‖ ≤ B := le_trans (le_max_left _ _) hφ
  have h2 : ‖φ.2‖ ≤ B := le_trans (le_max_right _ _) hφ
  unfold potentialL2NormOn38 pairL2NormOn38 potRepFst38 potRepSnd38
  have hdens : (∫ s in (0 : ℝ)..t, ‖coverRep38 φ.1 s‖ ^ 2 + ‖coverRep38 φ.2 s‖ ^ 2) ≤
      (m : ℝ) * (2 * B ^ 2) * 2 := by
    have hi1 := intervalIntegrable_sq_any φ.1
    have hi2 := intervalIntegrable_sq_any φ.2
    rw [intervalIntegral.integral_add (hi1 0 t) (hi2 0 t)]
    have mono : ∀ f : PhysicalL2, ∫ s in (0 : ℝ)..t, ‖coverRep38 f s‖ ^ 2 ≤
        ∫ s in (0 : ℝ)..(2 * m), ‖coverRep38 f s‖ ^ 2 := by
      intro f
      refine intervalIntegral.integral_mono_interval le_rfl ht (htT.trans h2m) ?_
        (intervalIntegrable_sq_any f 0 (2 * m))
      exact Filter.Eventually.of_forall (fun s => by positivity)
    have a1 := mono φ.1
    have a2 := mono φ.2
    rw [integral_sq_two_mul] at a1 a2
    have b1 : ‖φ.1‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have b2 : ‖φ.2‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left b1 hm0, mul_le_mul_of_nonneg_left b2 hm0]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc (∫ s in (0 : ℝ)..t, ‖coverRep38 φ.1 s‖ ^ 2 + ‖coverRep38 φ.2 s‖ ^ 2)
      ≤ (m : ℝ) * (2 * B ^ 2) * 2 := hdens
    _ = (2 * Real.sqrt (m : ℝ) * B) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]; ring

/-- Uniform M-test bound on a bounded parameter set. -/
private theorem term_bound (T R B : ℝ) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) {z : ℂ}
    (hz : ‖z‖ ≤ R) {φ : PotPair} (hφ : ‖φ‖ ≤ B) :
    ‖potentialVolterraTerm38 φ z n t‖ ≤
      Real.exp (R * T) *
        (Real.sqrt T * (2 * Real.sqrt (⌈T / 2⌉₊ : ℝ) * B)) ^ n / (n.factorial : ℝ) := by
  obtain ⟨ht0, htT⟩ := ht
  have hb := potentialVolterraTerm38_norm_le φ z n ht0
  refine hb.trans ?_
  have hL := potentialL2NormOn_le φ hφ ht0 htT
  have hL0 : 0 ≤ potentialL2NormOn38 φ t := by
    unfold potentialL2NormOn38 pairL2NormOn38; exact Real.sqrt_nonneg _
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hexp : Real.exp (|z.im| * t) ≤ Real.exp (R * T) := by
    apply Real.exp_le_exp.2
    have h1 : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hz
    have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hz
    exact mul_le_mul h1 htT ht0 hR0
  have hbase : Real.sqrt t * potentialL2NormOn38 φ t ≤
      Real.sqrt T * (2 * Real.sqrt (⌈T / 2⌉₊ : ℝ) * B) :=
    mul_le_mul (Real.sqrt_le_sqrt htT) hL hL0 (Real.sqrt_nonneg _)
  have hpow : (Real.sqrt t * potentialL2NormOn38 φ t) ^ n ≤
      (Real.sqrt T * (2 * Real.sqrt (⌈T / 2⌉₊ : ℝ) * B)) ^ n :=
    pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hL0) hbase n
  exact div_le_div_of_nonneg_right
    (mul_le_mul hexp hpow (by positivity) (Real.exp_pos _).le) hfac.le

/-- Part (B) of G1-004 COMMAND01. -/
theorem volterra_series_uniform (T R B : ℝ) :
    (∀ p ∈ {p : ℝ × ℂ × PotPair | p.1 ∈ Set.Icc 0 T ∧ ‖p.2.1‖ ≤ R ∧ ‖p.2.2‖ ≤ B},
        Summable (fun n : ℕ => potentialVolterraTerm38 p.2.2 p.2.1 n p.1)) ∧
      TendstoUniformlyOn
        (fun (N : ℕ) (p : ℝ × ℂ × PotPair) =>
          ∑ n ∈ Finset.range N, potentialVolterraTerm38 p.2.2 p.2.1 n p.1)
        (fun p : ℝ × ℂ × PotPair => ∑' n : ℕ, potentialVolterraTerm38 p.2.2 p.2.1 n p.1)
        Filter.atTop
        {p : ℝ × ℂ × PotPair | p.1 ∈ Set.Icc 0 T ∧ ‖p.2.1‖ ≤ R ∧ ‖p.2.2‖ ≤ B} := by
  set c : ℝ := Real.sqrt T * (2 * Real.sqrt (⌈T / 2⌉₊ : ℝ) * B) with hc
  have hu : Summable (fun n : ℕ => Real.exp (R * T) * (c ^ n / (n.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial c).mul_left _
  have hbd : ∀ n : ℕ, ∀ p ∈ {p : ℝ × ℂ × PotPair | p.1 ∈ Set.Icc 0 T ∧ ‖p.2.1‖ ≤ R ∧ ‖p.2.2‖ ≤ B},
      ‖potentialVolterraTerm38 p.2.2 p.2.1 n p.1‖ ≤
        Real.exp (R * T) * (c ^ n / (n.factorial : ℝ)) := by
    intro n p hp
    have := term_bound T R B n hp.1 hp.2.1 hp.2.2
    rw [mul_div_assoc] at this
    exact this
  refine ⟨fun p hp => Summable.of_norm_bounded hu (fun n => hbd n p hp), ?_⟩
  exact tendstoUniformlyOn_tsum_nat hu hbd


end BPart

open scoped Matrix.Norms.L2Operator in
/-- G1-004 COMMAND01, whole proposition. -/
theorem G1004_whole :
    ((∀ t : ℝ, 0 ≤ t →
        AnalyticOnNhd ℂ
          (fun p : ℂ × PotPair => ∑' n : ℕ, potentialVolterraTerm38 p.2 p.1 n t)
          Set.univ)
      ∧
      (∀ T R B : ℝ,
        (∀ p ∈ {p : ℝ × ℂ × PotPair | p.1 ∈ Set.Icc 0 T ∧ ‖p.2.1‖ ≤ R ∧ ‖p.2.2‖ ≤ B},
            Summable (fun n : ℕ => potentialVolterraTerm38 p.2.2 p.2.1 n p.1)) ∧
        TendstoUniformlyOn
          (fun (N : ℕ) (p : ℝ × ℂ × PotPair) =>
            ∑ n ∈ Finset.range N, potentialVolterraTerm38 p.2.2 p.2.1 n p.1)
          (fun p : ℝ × ℂ × PotPair => ∑' n : ℕ, potentialVolterraTerm38 p.2.2 p.2.1 n p.1)
          Filter.atTop
          {p : ℝ × ℂ × PotPair | p.1 ∈ Set.Icc 0 T ∧ ‖p.2.1‖ ≤ R ∧ ‖p.2.2‖ ≤ B})
      : Prop) :=
  ⟨analytic_all, volterra_series_uniform⟩

end

end NlsGge.Atomic.G1004GenT


end
