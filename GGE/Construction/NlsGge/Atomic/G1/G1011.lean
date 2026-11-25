                                                                                                                                                                                                                                                                                                                                                          
import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1003
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairAnalytic
import NlsGge.GK38.PairAnalyticOp
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterraDefs
import NlsGge.GK38.PairVolterraOp
import NlsGge.GK38.PairVolterraPower

                                                                                 
                                                                                                        
                                                                                              
                                                                                                   
                                                                                                        
                                                                                         

section
                                                                                              
                                       

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set AbsolutelyContinuousOnInterval

namespace NlsGge.Atomic.G1011S2.Aux5

theorem ac_primitive_complex {k : ℝ → ℂ} {T : ℝ} (hk : IntervalIntegrable k volume 0 T) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in (0 : ℝ)..t, k s) 0 T := by
  have h0 : (0 : ℝ) ∈ uIcc 0 T := left_mem_uIcc
  have hP := hk.norm.absolutelyContinuousOnInterval_intervalIntegral h0
  unfold AbsolutelyContinuousOnInterval at hP ⊢
  refine squeeze_zero' (Eventually.of_forall fun E => Finset.sum_nonneg fun i _ => dist_nonneg)
    ?_ hP
  refine eventually_inf_principal.2 (Eventually.of_forall fun E hE => ?_)
  refine Finset.sum_le_sum fun i hi => ?_
  obtain ⟨ha, hb⟩ := hE.1 i hi
  set a := (E.2 i).1
  set b := (E.2 i).2
  have hint : ∀ x y : ℝ, x ∈ uIcc 0 T → y ∈ uIcc 0 T → IntervalIntegrable k volume x y :=
    fun x y hx hy => hk.mono_set (uIcc_subset_uIcc hx hy)
  have e1 : (∫ s in (0 : ℝ)..a, k s) - ∫ s in (0 : ℝ)..b, k s = ∫ s in b..a, k s := by
    rw [intervalIntegral.integral_interval_sub_left (hint 0 a h0 ha) (hint 0 b h0 hb)]
  have e2 : (∫ s in (0 : ℝ)..a, ‖k s‖) - ∫ s in (0 : ℝ)..b, ‖k s‖ = ∫ s in b..a, ‖k s‖ := by
    rw [intervalIntegral.integral_interval_sub_left ((hint 0 a h0 ha).norm)
      ((hint 0 b h0 hb).norm)]
  rw [dist_eq_norm, dist_eq_norm, e1, e2, Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

end NlsGge.Atomic.G1011S2.Aux5


end

section
                                                                                                  
                                                                                                    
                                                                                                         

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT NlsGge.Atomic.G1011S2.Aux5

namespace NlsGge.Atomic.G1011S2.K5

noncomputable section

/-- The entries of the atomic series are those of the Neumann fundamental solution (default
product topology on matrices). -/
theorem tsum_entry (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    (∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j = fundContT φ z hT ⟨t, ht⟩ i j := by
  have hent : ∀ i j : Fin 2, HasSum (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)
      (fundContT φ z hT ⟨t, ht⟩ i j) := by
    intro i j
    have e : (fun n : ℕ => potentialVolterraTerm38 φ z n t i j) =
        fun n : ℕ => ((volterraPT φ z hT ^ n) (freeFundT T z)) ⟨t, ht⟩ i j :=
      funext fun n => by rw [term_eq_powT φ z hT n t ht]
    rw [e]
    exact hasSum_entryT φ z hT ⟨t, ht⟩ i j
  have hS : Summable (fun n : ℕ => potentialVolterraTerm38 φ z n t) :=
    Pi.summable.2 fun i => Pi.summable.2 fun j => (hent i j).summable
  have hcont : Continuous (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) :=
    (continuous_id.matrix_elem i j)
  have h1 : HasSum (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)
      ((∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j) :=
    hS.hasSum.map (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) hcont
  exact h1.unique (hent i j)

theorem tsum_matrix (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∑' n : ℕ, potentialVolterraTerm38 φ z n t) = ext38T hT (fundContT φ z hT) t := by
  ext i j
  rw [tsum_entry φ z hT ht i j, ext38T_of_mem hT _ ht]

/-- The integral equation for the Neumann fundamental solution, entrywise. -/
theorem fundContT_entry_eq (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    fundContT φ z hT ⟨t, ht⟩ i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * ext38T hT (fundContT φ z hT) s) i j := by
  have h := congrArg (fun G : PairContT T => G ⟨t, ht⟩ i j) (fundContT_eq_add φ z hT)
  simp only [ContinuousMap.add_apply, Pi.add_apply] at h
  rw [h]
  rfl

/-- Restricted variant of G1-005 (absolute continuity for `0 ≤ T`). -/
theorem G1005_restricted :
    (∀ (φ : PotPair) (z : ℂ),
      (∀ t : ℝ, 0 ≤ t →
        (∀ i j : Fin 2, Summable (fun n : ℕ => potentialVolterraTerm38 φ z n t i j)) ∧
        (∀ i j : Fin 2,
          IntervalIntegrable
            (fun s : ℝ => (freeZsFundamentalComplex z (t - s) *
              rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) s *
              (∑' n : ℕ, potentialVolterraTerm38 φ z n s)) i j) MeasureTheory.volume 0 t) ∧
        (∀ i j : Fin 2,
          (∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j =
            (freeZsFundamentalComplex z t) i j +
            ∫ s in (0 : ℝ)..t,
              (freeZsFundamentalComplex z (t - s) *
                rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) s *
                (∑' n : ℕ, potentialVolterraTerm38 φ z n s)) i j)) ∧
      (∑' n : ℕ, potentialVolterraTerm38 φ z n 0 = 1) ∧
      (∀ T : ℝ, 0 ≤ T → ∀ i j : Fin 2,
        AbsolutelyContinuousOnInterval
          (fun t : ℝ => (∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j) 0 T)) := by
  intro φ z
  refine ⟨fun t ht0 => ?_, ?_, fun T hT i j => ?_⟩
  · have ht : t ∈ Set.Icc (0 : ℝ) t := ⟨ht0, le_rfl⟩
    set F : PairContT t := fundContT φ z ht0 with hF
    have hmat : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        (∑' n : ℕ, potentialVolterraTerm38 φ z n s) = ext38T ht0 F s := by
      intro s hs
      rw [Set.uIcc_of_le ht0] at hs
      exact tsum_matrix φ z ht0 hs
    have hbase : ∀ i j : Fin 2, IntervalIntegrable
        (fun s : ℝ => (freeE z (t - s) * potCoeff38 φ s * ext38T ht0 F s) i j) volume 0 t := by
      intro i j
      have hK : Continuous fun s : ℝ => freeE z (t - s) :=
        (continuous_freeE z).comp (continuous_const.sub continuous_id)
      exact intervalIntegrable_triple_entryT_of_mem φ ht0 hK (continuous_ext38T ht0 F) ht i j
    have hcongr : ∀ i j : Fin 2, ∀ s ∈ Set.uIcc (0 : ℝ) t,
        (freeZsFundamentalComplex z (t - s) * rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) s *
          (∑' n : ℕ, potentialVolterraTerm38 φ z n s)) i j =
        (freeE z (t - s) * potCoeff38 φ s * ext38T ht0 F s) i j := by
      intro i j s hs
      rw [hmat s hs, ← freeE_eq]
      rfl
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · have e : (fun n : ℕ => potentialVolterraTerm38 φ z n t i j) =
          fun n : ℕ => ((volterraPT φ z ht0 ^ n) (freeFundT t z)) ⟨t, ht⟩ i j :=
        funext fun n => by rw [term_eq_powT φ z ht0 n t ht]
      rw [e]
      exact (hasSum_entryT φ z ht0 ⟨t, ht⟩ i j).summable
    · refine (hbase i j).congr ?_
      have : Set.EqOn (fun s : ℝ => (freeE z (t - s) * potCoeff38 φ s * ext38T ht0 F s) i j)
          (fun s : ℝ => (freeZsFundamentalComplex z (t - s) *
            rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) s *
            (∑' n : ℕ, potentialVolterraTerm38 φ z n s)) i j) (Set.uIoc 0 t) :=
        fun s hs => (hcongr i j s (Set.uIoc_subset_uIcc hs)).symm
      exact this
    · rw [tsum_entry φ z ht0 ht i j, fundContT_entry_eq φ z ht0 ht i j, ← freeE_eq]
      congr 1
      exact intervalIntegral.integral_congr fun s hs => (hcongr i j s hs).symm
  · ext i j
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 0 := ⟨le_rfl, le_rfl⟩
    rw [tsum_entry φ z (le_refl (0 : ℝ)) h0 i j, fundContT_entry_eq φ z (le_refl (0 : ℝ)) h0 i j]
    simp [freeE_zero]
  · have hFT : ∀ t ∈ Set.Icc (0 : ℝ) T,
        (∑' n : ℕ, potentialVolterraTerm38 φ z n t) i j =
          freeE z t i j + freeE z t i i *
            ∫ s in (0 : ℝ)..t, (freeE z (-s) * potCoeff38 φ s *
              ext38T hT (fundContT φ z hT) s) i j := by
      intro t ht
      rw [tsum_entry φ z hT ht i j, fundContT_entry_eq φ z hT ht i j]
      congr 1
      have := congrArg (fun X : PairMat38 => X i j) (volterraFunT_eq φ z hT (fundContT φ z hT) t)
      simp only [volterraFunT_apply, freeE_mul_apply] at this
      rw [this]
      rfl
    have hkint : IntervalIntegrable (fun s : ℝ => (freeE z (-s) * potCoeff38 φ s *
        ext38T hT (fundContT φ z hT) s) i j) volume 0 T := by
      have hKc : Continuous fun s : ℝ => freeE z (-s) := (continuous_freeE z).comp continuous_neg
      exact intervalIntegrable_triple_entryT φ hT hKc (continuous_ext38T hT _) i j
    have hKac := ac_primitive_complex hkint
    have hdiff : ∀ a b : Fin 2, ContDiffOn ℝ 1 (fun t : ℝ => freeE z t a b) (Set.uIcc 0 T) := by
      intro a b
      refine ContDiff.contDiffOn ?_
      unfold freeE
      fin_cases a <;> fin_cases b <;> simp <;>
        first
        | exact contDiff_const
        | exact Complex.contDiff_exp.comp
            (contDiff_const.mul Complex.ofRealCLM.contDiff) |>.comp contDiff_id
        | exact Complex.contDiff_exp.comp (((contDiff_const.mul Complex.ofRealCLM.contDiff)).neg)
    have hE1 := (hdiff i j).absolutelyContinuousOnInterval
    have hE2 := (hdiff i i).absolutelyContinuousOnInterval
    have hAC := hE1.add (hE2.fun_smul hKac)
    refine hAC.congr ?_
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    simp only [Pi.add_apply, smul_eq_mul, hFT t ht]

end

end NlsGge.Atomic.G1011S2.K5


end



                                                                                           
                                                                                                     
                                                                                                      
                                                                                              
                                                                                            
                                                                                       

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT

open NlsGge.Atomic.G1011S2.K5 NlsGge.Atomic.G1011S2.Aux5

namespace NlsGge.Atomic.G1011S2.K10

noncomputable section

/-! ### Copied from G1-005 (private) -/

def kerEnt (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) (s : ℝ) : ℂ :=
  (freeE z (-s) * potCoeff38 φ s * ext38T hT (fundContT φ z hT) s) i j

/-- Its primitive. -/
def Kint (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, kerEnt φ z hT i j s

/-- `A = 1 + K`. -/
def Aent (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) (t : ℝ) : ℂ :=
  (if i = j then 1 else 0) + Kint φ z hT i j t

theorem kerEnt_integrable (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    IntervalIntegrable (kerEnt φ z hT i j) volume 0 T := by
  have hKc : Continuous fun s : ℝ => freeE z (-s) := (continuous_freeE z).comp continuous_neg
  exact intervalIntegrable_triple_entryT φ hT hKc (continuous_ext38T hT _) i j

theorem Aent_ac (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t => Aent φ z hT i j t) 0 T := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (if i = j then (1 : ℂ) else 0)) 0 T :=
    (contDiff_const.contDiffOn (s := Set.uIcc (0 : ℝ) T) (n := 1)).absolutelyContinuousOnInterval
  exact hc.add (ac_primitive_complex (kerEnt_integrable φ z hT i j))

theorem Aent_zero (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    Aent φ z hT i j 0 = if i = j then 1 else 0 := by
  simp [Aent, Kint]

theorem freeE_diag (z : ℂ) (t : ℝ) (i j : Fin 2) :
    freeE z t i j = freeE z t i i * (if i = j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> simp [freeE]

theorem Mf_eq (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (i j : Fin 2) :
    ext38T hT (fundContT φ z hT) t i j = freeE z t i i * Aent φ z hT i j t := by
  rw [ext38T_of_mem hT _ ht, fundContT_entry_eq φ z hT ht i j]
  have h1 := congrArg (fun X : PairMat38 => X i j) (volterraFunT_eq φ z hT (fundContT φ z hT) t)
  simp only [volterraFunT_apply, freeE_mul_apply] at h1
  rw [h1, freeE_diag z t i j, Aent, mul_add]
  rfl

theorem ker_rows (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ b2 b3 : ℂ, (∀ j : Fin 2, kerEnt φ z hT 0 j t = b2 * Aent φ z hT 1 j t) ∧
      (∀ j : Fin 2, kerEnt φ z hT 1 j t = b3 * Aent φ z hT 0 j t) := by
  refine ⟨freeE z (-t) 0 0 * (Complex.I * potRepFst38 φ t) * freeE z t 1 1,
    freeE z (-t) 1 1 * (-(Complex.I * potRepSnd38 φ t)) * freeE z t 0 0, fun j => ?_, fun j => ?_⟩
  · simp only [kerEnt, Matrix.mul_apply, Fin.sum_univ_two, Mf_eq φ z hT ht]
    simp [freeE, potCoeff38]
    ring
  · simp only [kerEnt, Matrix.mul_apply, Fin.sum_univ_two, Mf_eq φ z hT ht]
    simp [freeE, potCoeff38]
    ring

/-- The determinant of `A`. -/
def detA (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : ℂ :=
  Aent φ z hT 0 0 t * Aent φ z hT 1 1 t - Aent φ z hT 0 1 t * Aent φ z hT 1 0 t

theorem detA_ac (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => detA φ z hT t) 0 T := by
  have h := ((Aent_ac φ z hT 0 0).fun_smul (Aent_ac φ z hT 1 1)).sub
    ((Aent_ac φ z hT 0 1).fun_smul (Aent_ac φ z hT 1 0))
  refine h.congr ?_
  intro t _
  simp [detA, smul_eq_mul]

theorem detA_deriv_zero (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t : ℝ, t ∈ Set.uIcc 0 T → HasDerivAt (fun t => detA φ z hT t) 0 t := by
  have hae : ∀ᵐ t : ℝ, t ∈ Set.uIcc 0 T → ∀ i j : Fin 2,
      HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, kerEnt φ z hT i j s) (kerEnt φ z hT i j t) t := by
    have h : ∀ i j : Fin 2, ∀ᵐ t : ℝ, t ∈ Set.uIcc 0 T →
        HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, kerEnt φ z hT i j s) (kerEnt φ z hT i j t) t := by
      intro i j
      filter_upwards [(kerEnt_integrable φ z hT i j).ae_hasDerivAt_integral] with t ht htm
      exact ht htm 0 left_mem_uIcc
    have h' := ae_all_iff.2 fun i : Fin 2 => ae_all_iff.2 fun j : Fin 2 => h i j
    filter_upwards [h'] with t ht htm i j using ht i j htm
  filter_upwards [hae] with t ht htm
  have htI : t ∈ Set.Icc (0 : ℝ) T := by rwa [Set.uIcc_of_le hT] at htm
  have hA : ∀ i j : Fin 2, HasDerivAt (fun x => Aent φ z hT i j x) (kerEnt φ z hT i j t) t := by
    intro i j
    have := (hasDerivAt_const t (if i = j then (1 : ℂ) else 0)).add (ht htm i j)
    rw [zero_add] at this
    exact this
  obtain ⟨b2, b3, h2, h3⟩ := ker_rows φ z hT htI
  have hd := ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))
  have hv : kerEnt φ z hT 0 0 t * Aent φ z hT 1 1 t + Aent φ z hT 0 0 t * kerEnt φ z hT 1 1 t -
      (kerEnt φ z hT 0 1 t * Aent φ z hT 1 0 t + Aent φ z hT 0 1 t * kerEnt φ z hT 1 0 t) = 0 := by
    rw [h2 0, h2 1, h3 0, h3 1]
    ring
  rw [hv] at hd
  exact hd

theorem detA_eq_one (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    detA φ z hT T = 1 := by
  obtain ⟨C, hC⟩ := (detA_ac φ z hT).const_of_ae_hasDerivAt_zero (detA_deriv_zero φ z hT)
  have h0 : detA φ z hT 0 = 1 := by
    simp [detA, Aent_zero]
  have hT' : T ∈ Set.uIcc (0 : ℝ) T := right_mem_uIcc
  rw [hC T hT', ← hC 0 left_mem_uIcc, h0]

theorem G1010_det (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    Matrix.det (∑' n : ℕ, potentialVolterraTerm38 φ z n T) = 1 := by
  have hT' : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  rw [tsum_matrix φ z hT hT', Matrix.det_fin_two]
  simp only [Mf_eq φ z hT hT']
  have hE : freeE z T 0 0 * freeE z T 1 1 = 1 := by
    simp only [freeE, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [← Complex.exp_add]
    simp
  have hdet := detA_eq_one φ z hT
  unfold detA at hdet
  calc freeE z T 0 0 * Aent φ z hT 0 0 T * (freeE z T 1 1 * Aent φ z hT 1 1 T) -
        freeE z T 0 0 * Aent φ z hT 0 1 T * (freeE z T 1 1 * Aent φ z hT 1 0 T)
      = (freeE z T 0 0 * freeE z T 1 1) *
        (Aent φ z hT 0 0 T * Aent φ z hT 1 1 T - Aent φ z hT 0 1 T * Aent φ z hT 1 0 T) := by ring
    _ = 1 := by rw [hE, hdet, one_mul]

theorem G1010_whole :
    ((∀ (φ : PotPair) (z : ℂ) (t : ℝ), 0 ≤ t →
      Matrix.det (∑' n : ℕ, potentialVolterraTerm38 φ z n t) = 1) : Prop) :=
  fun φ z _ ht => G1010_det φ z ht

end

end NlsGge.Atomic.G1011S2.K10



                                                                                     
                                                                                           
                                            

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set AbsolutelyContinuousOnInterval

namespace NlsGge.Atomic.G1011S2

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℂ

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

theorem ac_prim {k : ℝ → ℂ} {T : ℝ} (hk : IntervalIntegrable k volume 0 T) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in (0 : ℝ)..t, k s) 0 T := by
  have h0 : (0 : ℝ) ∈ uIcc 0 T := left_mem_uIcc
  have hP := hk.norm.absolutelyContinuousOnInterval_intervalIntegral h0
  unfold AbsolutelyContinuousOnInterval at hP ⊢
  refine squeeze_zero' (Eventually.of_forall fun E => Finset.sum_nonneg fun i _ => dist_nonneg)
    ?_ hP
  refine eventually_inf_principal.2 (Eventually.of_forall fun E hE => ?_)
  refine Finset.sum_le_sum fun i hi => ?_
  obtain ⟨ha, hb⟩ := hE.1 i hi
  set a := (E.2 i).1
  set b := (E.2 i).2
  have hint : ∀ x y : ℝ, x ∈ uIcc 0 T → y ∈ uIcc 0 T → IntervalIntegrable k volume x y :=
    fun x y hx hy => hk.mono_set (uIcc_subset_uIcc hx hy)
  have e1 : (∫ s in (0 : ℝ)..a, k s) - ∫ s in (0 : ℝ)..b, k s = ∫ s in b..a, k s := by
    rw [intervalIntegral.integral_interval_sub_left (hint 0 a h0 ha) (hint 0 b h0 hb)]
  have e2 : (∫ s in (0 : ℝ)..a, ‖k s‖) - ∫ s in (0 : ℝ)..b, ‖k s‖ = ∫ s in b..a, ‖k s‖ := by
    rw [intervalIntegral.integral_interval_sub_left ((hint 0 a h0 ha).norm)
      ((hint 0 b h0 hb).norm)]
  rw [dist_eq_norm, dist_eq_norm, e1, e2, Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

theorem ac_const (c : ℂ) (T : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 T :=
  (contDiff_const.contDiffOn (s := uIcc (0 : ℝ) T) (n := 1)).absolutelyContinuousOnInterval

theorem ae_hasDerivAt_of_primitive {F k : ℝ → ℂ} {c0 : ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hk : IntervalIntegrable k volume 0 T)
    (hF : ∀ x : ℝ, 0 ≤ x → F x = c0 + ∫ s in (0 : ℝ)..x, k s) :
    ∀ᵐ t : ℝ, t ∈ uIcc 0 T → HasDerivAt F (k t) t := by
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (0 : ℝ))
  filter_upwards [hk.ae_hasDerivAt_integral, h0] with t ht ht0 htm
  have hd : HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, k s) (k t) t := ht htm 0 left_mem_uIcc
  have htm' : t ∈ Icc (0 : ℝ) T := by rwa [uIcc_of_le hT] at htm
  have hpos : 0 < t := lt_of_le_of_ne htm'.1 (Ne.symm ht0)
  have hev : (fun x => c0 + ∫ s in (0 : ℝ)..x, k s) =ᶠ[𝓝 t] F := by
    filter_upwards [lt_mem_nhds hpos] with x hx using (hF x hx.le).symm
  exact (hd.const_add c0).congr_of_eventuallyEq hev.symm

theorem hasDerivAt_mulVec_apply {F : ℝ → Mat2} {D : Mat2} {w : ℝ → Fin 2 → ℂ}
    {w' : Fin 2 → ℂ} {t : ℝ}
    (hF : ∀ i j, HasDerivAt (fun x => F x i j) (D i j) t)
    (hw : ∀ i, HasDerivAt (fun x => w x i) (w' i) t) (i : Fin 2) :
    HasDerivAt (fun x => ((F x).mulVec (w x)) i) ((D.mulVec (w t) + (F t).mulVec w') i) t := by
  have h := ((hF i 0).mul (hw 0)).add ((hF i 1).mul (hw 1))
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply]
  convert h using 1
  ring

theorem adj_hasDerivAt {N : ℝ → Mat2} {D : Mat2} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun x => N x i j) (D i j) t) :
    ∀ i j, HasDerivAt (fun x => (N x).adjugate i j) (D.adjugate i j) t := by
  intro i j
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
    simp [Matrix.adjugate_fin_two]
  · exact h 1 1
  · exact (h 0 1).neg
  · exact (h 1 0).neg
  · exact h 0 0

theorem adj_ac {N : ℝ → Mat2} {T : ℝ}
    (h : ∀ i j, AbsolutelyContinuousOnInterval (fun x => N x i j) 0 T) :
    ∀ i j, AbsolutelyContinuousOnInterval (fun x => (N x).adjugate i j) 0 T := by
  intro i j
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
    simp [Matrix.adjugate_fin_two]
  · exact h 1 1
  · exact (h 0 1).neg
  · exact (h 1 0).neg
  · exact h 0 0

theorem mulVec_ac {F : ℝ → Mat2} {w : ℝ → Fin 2 → ℂ} {T : ℝ}
    (hF : ∀ i j, AbsolutelyContinuousOnInterval (fun t => F t i j) 0 T)
    (hw : ∀ j, AbsolutelyContinuousOnInterval (fun t => w t j) 0 T) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t => ((F t).mulVec (w t)) i) 0 T := by
  have h := ((hF i 0).fun_smul (hw 0)).add ((hF i 1).fun_smul (hw 1))
  refine h.congr (fun x _ => ?_)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem adj_mul_of_diag0 {B : Mat2} (h0 : B 0 0 = 0) (h1 : B 1 1 = 0) (Nm : Mat2) :
    (B * Nm).adjugate = -(Nm.adjugate * B) := by
  ext i j
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct, h0, h1] <;> ring

theorem alg1 {Bm Nm : Mat2} (u h : Fin 2 → ℂ) (hB : (Bm * Nm).adjugate = -(Nm.adjugate * Bm)) :
    (Bm * Nm).adjugate.mulVec u + Nm.adjugate.mulVec (Bm.mulVec u - h) +
      Nm.adjugate.mulVec h = 0 := by
  rw [hB, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  abel

structure CoreData (N B : ℝ → Mat2) (h : ℝ → Fin 2 → ℂ) : Prop where
  Bint : ∀ T : ℝ, 0 ≤ T → ∀ i j : Fin 2, IntervalIntegrable (fun s => B s i j) volume 0 T
  hint : ∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2, IntervalIntegrable (fun s => h s i) volume 0 T
  Neq : ∀ t : ℝ, 0 ≤ t → ∀ i j : Fin 2,
    N t i j = (1 : Mat2) i j + ∫ s in (0 : ℝ)..t, (B s * N s) i j
  Nac : ∀ T : ℝ, 0 ≤ T → ∀ i j : Fin 2,
    AbsolutelyContinuousOnInterval (fun t => N t i j) 0 T
  det1 : ∀ t : ℝ, 0 ≤ t → (N t).det = 1
  B00 : ∀ s, B s 0 0 = 0
  B11 : ∀ s, B s 1 1 = 0

def Hint (N : ℝ → Mat2) (h : ℝ → Fin 2 → ℂ) (t : ℝ) (i : Fin 2) : ℂ :=
  ∫ s in (0 : ℝ)..t, ((N s).adjugate.mulVec (h s)) i

namespace CoreData

variable {N B : ℝ → Mat2} {h : ℝ → Fin 2 → ℂ} (hc : CoreData N B h)
include hc

theorem Ncont {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    ContinuousOn (fun s => N s i j) (uIcc 0 T) := (hc.Nac T hT i j).continuousOn

theorem adjcont {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    ContinuousOn (fun s => (N s).adjugate i j) (uIcc 0 T) :=
  (adj_ac (hc.Nac T hT) i j).continuousOn

theorem BN_int {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    IntervalIntegrable (fun s => (B s * N s) i j) volume 0 T := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hc.Bint T hT i 0).mul_continuousOn (hc.Ncont hT 0 j)).add
    ((hc.Bint T hT i 1).mul_continuousOn (hc.Ncont hT 1 j))

theorem N_ae {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t : ℝ, t ∈ uIcc 0 T → ∀ i j : Fin 2,
      HasDerivAt (fun x => N x i j) ((B t * N t) i j) t := by
  have h' : ∀ i j : Fin 2, ∀ᵐ t : ℝ, t ∈ uIcc 0 T →
      HasDerivAt (fun x => N x i j) ((B t * N t) i j) t := fun i j =>
    ae_hasDerivAt_of_primitive hT (hc.BN_int hT i j) (fun x hx => hc.Neq x hx i j)
  have h2 := ae_all_iff.2 fun i : Fin 2 => ae_all_iff.2 fun j : Fin 2 => h' i j
  filter_upwards [h2] with t ht htm i j using ht i j htm

theorem k_int {u : ℝ → Fin 2 → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hu : ∀ j, ContinuousOn (fun s => u s j) (uIcc 0 T)) (i : Fin 2) :
    IntervalIntegrable (fun s => ((B s).mulVec (u s)) i - h s i) volume 0 T := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (((hc.Bint T hT i 0).mul_continuousOn (hu 0)).add
    ((hc.Bint T hT i 1).mul_continuousOn (hu 1))).sub (hc.hint T hT i)

theorem adjh_int {T : ℝ} (hT : 0 ≤ T) (i : Fin 2) :
    IntervalIntegrable (fun s => ((N s).adjugate.mulVec (h s)) i) volume 0 T := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact ((hc.hint T hT 0).continuousOn_mul (hc.adjcont hT i 0)).add
    ((hc.hint T hT 1).continuousOn_mul (hc.adjcont hT i 1))

theorem Hint_ac {T : ℝ} (hT : 0 ≤ T) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t => Hint N h t i) 0 T :=
  ac_prim (hc.adjh_int hT i)

theorem Hint_ae {T : ℝ} (hT : 0 ≤ T) (i : Fin 2) :
    ∀ᵐ t : ℝ, t ∈ uIcc 0 T →
      HasDerivAt (fun x => Hint N h x i) (((N t).adjugate.mulVec (h t)) i) t :=
  ae_hasDerivAt_of_primitive (c0 := 0) hT (hc.adjh_int hT i) (fun x _ => by simp [Hint])

theorem N_zero : N 0 = 1 := by
  ext i j
  rw [hc.Neq 0 le_rfl i j]
  simp

theorem N_mul_adj {t : ℝ} (ht : 0 ≤ t) : N t * (N t).adjugate = 1 := by
  rw [Matrix.mul_adjugate, hc.det1 t ht, one_smul]

theorem adj_mul_N {t : ℝ} (ht : 0 ≤ t) : (N t).adjugate * N t = 1 := by
  rw [Matrix.adjugate_mul, hc.det1 t ht, one_smul]

theorem fwd {u : ℝ → Fin 2 → ℂ} {v0 : Fin 2 → ℂ}
    (hcont : ∀ T : ℝ, 0 ≤ T → ∀ j, ContinuousOn (fun s => u s j) (uIcc 0 T))
    (hD : ∀ t : ℝ, 0 ≤ t → ∀ i,
      u t i = v0 i + ∫ s in (0 : ℝ)..t, (((B s).mulVec (u s)) i - h s i)) :
    ∀ t : ℝ, 0 ≤ t → ∀ i, u t i = ((N t).mulVec (fun j => v0 j - Hint N h t j)) i := by
  intro T hT
  have hkint := fun i => hc.k_int hT (hcont T hT) i
  have huac : ∀ j, AbsolutelyContinuousOnInterval (fun t => u t j) 0 T := by
    intro j
    have hp := (ac_const (v0 j) T).add (ac_prim (hkint j))
    refine hp.congr (fun x hx => ?_)
    rw [uIcc_of_le hT] at hx
    simp only [Pi.add_apply]
    exact (hD x hx.1 j).symm
  have hqac : ∀ i, AbsolutelyContinuousOnInterval
      (fun t => ((N t).adjugate.mulVec (u t)) i - v0 i + Hint N h t i) 0 T := by
    intro i
    exact (((mulVec_ac (adj_ac (hc.Nac T hT)) huac i).sub (ac_const (v0 i) T)).add
      (hc.Hint_ac hT i))
  have hae : ∀ᵐ t : ℝ, t ∈ uIcc 0 T → ∀ i, HasDerivAt
      (fun x => ((N x).adjugate.mulVec (u x)) i - v0 i + Hint N h x i) 0 t := by
    have h1 := hc.N_ae hT
    have h2 : ∀ j, ∀ᵐ t : ℝ, t ∈ uIcc 0 T →
        HasDerivAt (fun x => u x j) (((B t).mulVec (u t) - h t) j) t := fun j =>
      ae_hasDerivAt_of_primitive hT (hkint j) (fun x hx => hD x hx j)
    have h3 : ∀ i, ∀ᵐ t : ℝ, t ∈ uIcc 0 T →
        HasDerivAt (fun x => Hint N h x i) (((N t).adjugate.mulVec (h t)) i) t := fun i =>
      hc.Hint_ae hT i
    have h2' := ae_all_iff.2 h2
    have h3' := ae_all_iff.2 h3
    filter_upwards [h1, h2', h3'] with t ht1 ht2 ht3 htm i
    have hadj := adj_hasDerivAt (D := B t * N t) (fun a b => ht1 htm a b)
    have hmv := hasDerivAt_mulVec_apply hadj (fun j => ht2 j htm) i
    have hfull := (hmv.sub_const (v0 i)).add (ht3 i htm)
    refine hfull.congr_deriv ?_
    have key := alg1 (u t) (h t) (adj_mul_of_diag0 (hc.B00 t) (hc.B11 t) (N t))
    have := congrFun key i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    simp only [Pi.add_apply]
    linear_combination this
  have hconst : ∀ i, ∀ x ∈ uIcc 0 T,
      ((N x).adjugate.mulVec (u x)) i - v0 i + Hint N h x i =
        ((N 0).adjugate.mulVec (u 0)) i - v0 i + Hint N h 0 i := by
    intro i
    obtain ⟨C, hC⟩ := (hqac i).const_of_ae_hasDerivAt_zero
      (by filter_upwards [hae] with t ht htm using ht htm i)
    intro x hx
    exact (hC x hx).trans (hC 0 left_mem_uIcc).symm
  have hq0 : ∀ i, ((N 0).adjugate.mulVec (u 0)) i - v0 i + Hint N h 0 i = 0 := by
    intro i
    rw [hc.N_zero, Matrix.adjugate_one, Matrix.one_mulVec]
    have := hD 0 le_rfl i
    simp only [Hint, intervalIntegral.integral_same, add_zero] at this ⊢
    rw [this]
    ring
  have hv : (N T).adjugate.mulVec (u T) = fun j => v0 j - Hint N h T j := by
    funext i
    have := hconst i T right_mem_uIcc
    rw [hq0 i] at this
    linear_combination this
  intro i
  have h1 : u T = (N T).mulVec ((N T).adjugate.mulVec (u T)) := by
    rw [Matrix.mulVec_mulVec, hc.N_mul_adj hT, Matrix.one_mulVec]
  have h2 : u T i = ((N T).mulVec ((N T).adjugate.mulVec (u T))) i := by
    rw [← h1]
  rw [h2, hv]


theorem bwd {u : ℝ → Fin 2 → ℂ} {v0 : Fin 2 → ℂ}
    (hu : ∀ t : ℝ, 0 ≤ t → ∀ i,
      u t i = ((N t).mulVec (fun j => v0 j - Hint N h t j)) i) :
    (∀ T : ℝ, 0 ≤ T → ∀ i, AbsolutelyContinuousOnInterval (fun t => u t i) 0 T) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ i,
      u t i = v0 i + ∫ s in (0 : ℝ)..t, (((B s).mulVec (u s)) i - h s i)) := by
  have huac : ∀ T : ℝ, 0 ≤ T → ∀ i,
      AbsolutelyContinuousOnInterval (fun t => u t i) 0 T := by
    intro T hT i
    have hcac : ∀ j, AbsolutelyContinuousOnInterval (fun t => v0 j - Hint N h t j) 0 T :=
      fun j => (ac_const (v0 j) T).sub (hc.Hint_ac hT j)
    have hm := mulVec_ac (hc.Nac T hT) hcac i
    refine hm.congr (fun x hx => ?_)
    rw [uIcc_of_le hT] at hx
    exact (hu x hx.1 i).symm
  refine ⟨huac, ?_⟩
  intro T hT i
  have hcont : ∀ j, ContinuousOn (fun s => u s j) (uIcc 0 T) :=
    fun j => (huac T hT j).continuousOn
  have hkint := fun i => hc.k_int hT hcont i
  have hP : AbsolutelyContinuousOnInterval
      (fun t => u t i - v0 i - ∫ s in (0 : ℝ)..t, (((B s).mulVec (u s)) i - h s i)) 0 T :=
    (((huac T hT i).sub (ac_const (v0 i) T)).sub (ac_prim (hkint i)))
  have hae : ∀ᵐ t : ℝ, t ∈ uIcc 0 T → HasDerivAt
      (fun x => u x i - v0 i - ∫ s in (0 : ℝ)..x, (((B s).mulVec (u s)) i - h s i)) 0 t := by
    have h1 := hc.N_ae hT
    have h3 : ∀ j, ∀ᵐ t : ℝ, t ∈ uIcc 0 T →
        HasDerivAt (fun x => Hint N h x j) (((N t).adjugate.mulVec (h t)) j) t :=
      fun j => hc.Hint_ae hT j
    have h4 := ae_hasDerivAt_of_primitive
      (F := fun x => ∫ s in (0 : ℝ)..x, (((B s).mulVec (u s)) i - h s i)) (c0 := 0) hT
      (hkint i) (fun x _ => by simp)
    have h3' := ae_all_iff.2 h3
    have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [ae_iff]
      simpa using (measure_singleton (0 : ℝ))
    filter_upwards [h1, h3', h4, h0] with t ht1 ht3 ht4 ht0 htm
    have htm' : t ∈ Icc (0 : ℝ) T := by rwa [uIcc_of_le hT] at htm
    have hpos : 0 < t := lt_of_le_of_ne htm'.1 (Ne.symm ht0)
    have hw : ∀ j, HasDerivAt (fun x => v0 j - Hint N h x j)
        (-(((N t).adjugate.mulVec (h t)) j)) t := fun j => (ht3 j htm).const_sub (v0 j)
    have hmv := hasDerivAt_mulVec_apply (fun a b => ht1 htm a b) hw i
    have hev : (fun x => ((N x).mulVec (fun j => v0 j - Hint N h x j)) i) =ᶠ[𝓝 t]
        fun x => u x i := by
      filter_upwards [lt_mem_nhds hpos] with x hx using (hu x hx.le i).symm
    have hui := hmv.congr_of_eventuallyEq hev.symm
    have hfin := (hui.sub_const (v0 i)).sub (ht4 htm)
    refine hfin.congr_deriv ?_
    have hut : u t = (N t).mulVec (fun j => v0 j - Hint N h t j) := funext (hu t hpos.le)
    have key : (B t * N t).mulVec (fun j => v0 j - Hint N h t j) +
        (N t).mulVec (-((N t).adjugate.mulVec (h t))) = (B t).mulVec (u t) - h t := by
      have e1 : (B t * N t).mulVec (fun j => v0 j - Hint N h t j) =
          (B t).mulVec ((N t).mulVec (fun j => v0 j - Hint N h t j)) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      have e2 : (N t).mulVec (-((N t).adjugate.mulVec (h t))) = -(h t) := by
        rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hc.N_mul_adj hpos.le, Matrix.one_mulVec]
      rw [e2, hut, e1]
      abel
    have := congrFun key i
    simp only [Pi.add_apply, Pi.sub_apply] at this
    simp only [Pi.add_apply, Pi.neg_apply]
    linear_combination this
  obtain ⟨C, hC⟩ := hP.const_of_ae_hasDerivAt_zero hae
  have hT0 := hC T right_mem_uIcc
  have h00 := hC 0 left_mem_uIcc
  have hu0 : u 0 i = v0 i := by
    rw [hu 0 le_rfl i, hc.N_zero, Matrix.one_mulVec]
    simp [Hint]
  have hz : u 0 i - v0 i - ∫ s in (0 : ℝ)..0, (((B s).mulVec (u s)) i - h s i) = 0 := by
    simp [hu0]
  have hfin : u T i - v0 i - ∫ s in (0 : ℝ)..T, (((B s).mulVec (u s)) i - h s i) = 0 :=
    hT0.trans (h00.symm.trans hz)
  linear_combination hfin

end CoreData

end NlsGge.Atomic.G1011S2


/-! ### Specialization to the NLS potential -/

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.Atomic.G1011S2

theorem freeE_mul_apply' (z : ℂ) (a : ℝ) (X : Mat2) (i j : Fin 2) :
    (freeE z a * X) i j = freeE z a i i * X i j := by
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
    simp [freeE, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_freeE_apply' (z : ℂ) (a : ℝ) (X : Mat2) (i j : Fin 2) :
    (X * freeE z a) i j = X i j * freeE z a j j := by
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
    simp [freeE, Matrix.mul_apply, Fin.sum_univ_two]

theorem freeE_mulVec_apply (z : ℂ) (a : ℝ) (v : Fin 2 → ℂ) (i : Fin 2) :
    ((freeE z a).mulVec v) i = freeE z a i i * v i := by
  rcases fin2_cases i with rfl | rfl <;>
    simp [freeE, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem freeE_mul_neg (z : ℂ) (a : ℝ) : freeE z a * freeE z (-a) = 1 := by
  rw [← freeE_add]; simp [freeE_zero]

theorem freeE_neg_mul (z : ℂ) (a : ℝ) : freeE z (-a) * freeE z a = 1 := by
  rw [← freeE_add]; simp [freeE_zero]

theorem freeE_diag_inv (z : ℂ) (a : ℝ) (i : Fin 2) :
    freeE z a i i * freeE z (-a) i i = 1 := by
  have h := congrFun (congrFun (freeE_mul_neg z a) i) i
  rw [freeE_mul_apply'] at h
  simpa using h

theorem freeE_det (z : ℂ) (a : ℝ) : (freeE z a).det = 1 := by
  have h : Complex.exp (-(Complex.I * z * a)) * Complex.exp (Complex.I * z * a) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [Matrix.det_fin_two]
  simpa [freeE] using h

theorem freeE_cont (z : ℂ) (i : Fin 2) : Continuous (fun t : ℝ => freeE z t i i) :=
  (continuous_freeE z).matrix_elem i i

theorem freeEneg_cont (z : ℂ) (i : Fin 2) : Continuous (fun t : ℝ => freeE z (-t) i i) :=
  ((continuous_freeE z).comp continuous_neg).matrix_elem i i

theorem freeE_cd (z : ℂ) (i : Fin 2) : ContDiff ℝ 1 (fun t : ℝ => freeE z t i i) := by
  rcases fin2_cases i with rfl | rfl
  · have h := NlsGge.Atomic.G1008.ph_zero z
    change ContDiff ℝ 1 (fun t : ℝ => NlsGge.Atomic.G1008.ph z t 0)
    simp only [h]
    exact Complex.contDiff_exp.comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg)
  · have h := NlsGge.Atomic.G1008.ph_one z
    change ContDiff ℝ 1 (fun t : ℝ => NlsGge.Atomic.G1008.ph z t 1)
    simp only [h]
    exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem freeEneg_cd (z : ℂ) (i : Fin 2) : ContDiff ℝ 1 (fun t : ℝ => freeE z (-t) i i) :=
  (freeE_cd z i).comp contDiff_neg

def PCm (φ : PotPair) (s : ℝ) : Mat2 := rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) s

def Mf (φ : PotPair) (z : ℂ) (t : ℝ) : Mat2 := ∑' n : ℕ, potentialVolterraTerm38 φ z n t

def Nf (φ : PotPair) (z : ℂ) (t : ℝ) : Mat2 := freeE z (-t) * Mf φ z t

def Bf (φ : PotPair) (z : ℂ) (s : ℝ) : Mat2 := freeE z (-s) * PCm φ s * freeE z s

def Rm : Mat2 := !![Complex.I, 0; 0, -Complex.I]

def hf (z : ℂ) (g : ℝ → Fin 2 → ℂ) (s : ℝ) : Fin 2 → ℂ :=
  (freeE z (-s)).mulVec (Rm.mulVec (g s))

theorem Rm_apply0 (v : Fin 2 → ℂ) : (Rm.mulVec v) 0 = Complex.I * v 0 := by
  simp [Rm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Rm_apply1 (v : Fin 2 → ℂ) : (Rm.mulVec v) 1 = -(Complex.I * v 1) := by
  simp [Rm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem PC_int (φ : PotPair) {T : ℝ} (i j : Fin 2) :
    IntervalIntegrable (fun s => PCm φ s i j) volume 0 T := by
  have ha : IntervalIntegrable (potRepFst38 φ) volume 0 T :=
    NlsGge.Atomic.G1008.intervalIntegrable_cr_any φ.1 0 T
  have hb : IntervalIntegrable (potRepSnd38 φ) volume 0 T :=
    NlsGge.Atomic.G1008.intervalIntegrable_cr_any φ.2 0 T
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl
  · simpa [PCm, rawPotCoeff38] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 T)
  · simpa [PCm, rawPotCoeff38] using ha.const_mul Complex.I
  · simpa [PCm, rawPotCoeff38, neg_mul] using hb.const_mul (-Complex.I)
  · simpa [PCm, rawPotCoeff38] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 T)

theorem g_int {g : ℝ → Fin 2 → ℂ}
    (hg : ∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
      MemLp (fun s : ℝ => g s i) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    {T : ℝ} (hT : 0 ≤ T) (i : Fin 2) : IntervalIntegrable (fun s => g s i) volume 0 T := by
  have h1 : Integrable (fun s : ℝ => g s i) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    (hg T hT i).integrable (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 h1

theorem Mf_eq (φ : PotPair) (z : ℂ) (s : ℝ) : Mf φ z s = freeE z s * Nf φ z s := by
  rw [Nf, ← Matrix.mul_assoc, freeE_mul_neg, Matrix.one_mul]

theorem E_PC (φ : PotPair) (z : ℂ) (s : ℝ) :
    freeE z (-s) * PCm φ s = Bf φ z s * freeE z (-s) := by
  rw [Bf, Matrix.mul_assoc (freeE z (-s) * PCm φ s), Matrix.mul_assoc (freeE z (-s)),
    freeE_mul_neg, Matrix.mul_one]

theorem BN_eq (φ : PotPair) (z : ℂ) (s : ℝ) :
    Bf φ z s * Nf φ z s = freeE z (-s) * (PCm φ s * Mf φ z s) := by
  rw [Bf, Nf, Matrix.mul_assoc (freeE z (-s) * PCm φ s), ← Matrix.mul_assoc (freeE z s),
    freeE_mul_neg, Matrix.one_mul, Matrix.mul_assoc]

end NlsGge.Atomic.G1011S2

namespace NlsGge.Atomic.G1011S2

theorem coreData (φ : PotPair) (z : ℂ) (g : ℝ → Fin 2 → ℂ)
    (hg : ∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
      MemLp (fun s : ℝ => g s i) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    CoreData (Nf φ z) (Bf φ z) (hf z g) := by
  have h5 := K5.G1005_restricted φ z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT i j
    have hent : ∀ s, Bf φ z s i j = freeE z (-s) i i * PCm φ s i j * freeE z s j j := by
      intro s
      rw [Bf, mul_freeE_apply', freeE_mul_apply']
    simp_rw [hent]
    exact (((PC_int φ i j).continuousOn_mul (freeEneg_cont z i).continuousOn).mul_continuousOn
      (freeE_cont z j).continuousOn)
  · intro T hT i
    have hent : ∀ s, hf z g s i = freeE z (-s) i i * (Rm.mulVec (g s)) i := by
      intro s
      rw [hf, freeE_mulVec_apply]
    simp_rw [hent]
    have hint : IntervalIntegrable (fun s => (Rm.mulVec (g s)) i) volume 0 T := by
      rcases fin2_cases i with rfl | rfl
      · simp_rw [Rm_apply0]
        exact (g_int hg hT 0).const_mul Complex.I
      · simp_rw [Rm_apply1]
        exact ((g_int hg hT 1).const_mul Complex.I).neg
    exact hint.continuousOn_mul (freeEneg_cont z i).continuousOn
  · intro t ht i j
    have hM := (h5.1 t ht).2.2 i j
    have hint : ∫ s in (0 : ℝ)..t, (freeZsFundamentalComplex z (t - s) * PCm φ s * Mf φ z s) i j =
        freeE z t i i * ∫ s in (0 : ℝ)..t, freeE z (-s) i i * (PCm φ s * Mf φ z s) i j := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      rw [← freeE_eq, Matrix.mul_assoc, freeE_mul_apply']
      have : freeE z (t - s) i i = freeE z t i i * freeE z (-s) i i := by
        have h := congrFun (congrFun (freeE_add z t (-s)) i) i
        rw [freeE_mul_apply'] at h
        rw [sub_eq_add_neg]
        exact h
      rw [this]
      ring
    have hBN : ∫ s in (0 : ℝ)..t, (Bf φ z s * Nf φ z s) i j =
        ∫ s in (0 : ℝ)..t, freeE z (-s) i i * (PCm φ s * Mf φ z s) i j := by
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      rw [BN_eq, freeE_mul_apply']
    rw [hBN]
    have hMt : Mf φ z t i j = freeE z t i j + freeE z t i i *
        ∫ s in (0 : ℝ)..t, freeE z (-s) i i * (PCm φ s * Mf φ z s) i j := by
      rw [← hint, freeE_eq z t]
      exact hM
    have h1 : freeE z (-t) i i * freeE z t i j = (1 : Mat2) i j := by
      have h := congrFun (congrFun (freeE_neg_mul z t) i) j
      rw [freeE_mul_apply'] at h
      exact h
    have h2 : freeE z (-t) i i * freeE z t i i = 1 := by
      have := freeE_diag_inv z t i
      linear_combination this
    show (freeE z (-t) * Mf φ z t) i j = _
    rw [freeE_mul_apply', hMt, mul_add, h1, ← mul_assoc, h2, one_mul]
  · intro T hT i j
    have hM := (h5.2.2 T hT i j)
    have := ((freeEneg_cd z i).contDiffOn (s := uIcc (0 : ℝ) T)).absolutelyContinuousOnInterval.fun_smul hM
    refine this.congr (fun x _ => ?_)
    show freeE z (-x) i i • Mf φ z x i j = (freeE z (-x) * Mf φ z x) i j
    rw [freeE_mul_apply', smul_eq_mul]
  · intro t ht
    have h := K10.G1010_det φ z ht
    show (freeE z (-t) * Mf φ z t).det = 1
    rw [Matrix.det_mul, freeE_det]
    simpa [Mf] using h
  · intro s
    rw [Bf, mul_freeE_apply', freeE_mul_apply']
    simp [PCm, rawPotCoeff38]
  · intro s
    rw [Bf, mul_freeE_apply', freeE_mul_apply']
    simp [PCm, rawPotCoeff38]

end NlsGge.Atomic.G1011S2

namespace NlsGge.Atomic.G1011S2

def ufn (z : ℂ) (f : ℝ → Fin 2 → ℂ) (t : ℝ) : Fin 2 → ℂ := (freeE z (-t)).mulVec (f t)

def kvec (φ : PotPair) (z : ℂ) (g : ℝ → Fin 2 → ℂ) (f : ℝ → Fin 2 → ℂ) (s : ℝ) : Fin 2 → ℂ :=
  (Bf φ z s).mulVec (ufn z f s) - hf z g s

theorem ivInt_apply {v : ℝ → Fin 2 → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hv : ∀ i, IntervalIntegrable (fun s => v s i) volume 0 t) (i : Fin 2) :
    (∫ s in (0 : ℝ)..t, v s) i = ∫ s in (0 : ℝ)..t, v s i := by
  rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
  exact eval_integral (fun j => (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 (hv j)) i

theorem uf_cont {f : ℝ → Fin 2 → ℂ} (z : ℂ)
    (hfc : ∀ T : ℝ, 0 ≤ T → ∀ j, ContinuousOn (fun s => f s j) (uIcc 0 T)) :
    ∀ T : ℝ, 0 ≤ T → ∀ j, ContinuousOn (fun s => ufn z f s j) (uIcc 0 T) := by
  intro T hT j
  have h : (fun s => ufn z f s j) = fun s => freeE z (-s) j j * f s j :=
    funext fun s => freeE_mulVec_apply z (-s) (f s) j
  rw [h]
  exact (freeEneg_cont z j).continuousOn.mul (hfc T hT j)

theorem f_eq (z : ℂ) (f : ℝ → Fin 2 → ℂ) (t : ℝ) : f t = (freeE z t).mulVec (ufn z f t) := by
  rw [ufn, Matrix.mulVec_mulVec, freeE_mul_neg, Matrix.one_mulVec]

theorem duh_conv (φ : PotPair) (z : ℂ) (g : ℝ → Fin 2 → ℂ)
    (hg : ∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
      MemLp (fun s : ℝ => g s i) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (v0 : Fin 2 → ℂ) {f : ℝ → Fin 2 → ℂ}
    (hfc : ∀ T : ℝ, 0 ≤ T → ∀ j, ContinuousOn (fun s => f s j) (uIcc 0 T))
    {t : ℝ} (ht : 0 ≤ t) :
    (f t = (freeE z t).mulVec v0 + ∫ s in (0 : ℝ)..t, (freeE z (t - s)).mulVec
        ((PCm φ s).mulVec (f s) - Rm.mulVec (g s))) ↔
    ∀ i, ufn z f t i = v0 i + ∫ s in (0 : ℝ)..t, (kvec φ z g f s) i := by
  have hcd := coreData φ z g hg
  have huc := uf_cont z hfc
  have hk : ∀ s, (freeE z (t - s)).mulVec ((PCm φ s).mulVec (f s) - Rm.mulVec (g s)) =
      (freeE z t).mulVec (kvec φ z g f s) := by
    intro s
    have e1 : freeE z (t - s) = freeE z t * freeE z (-s) := by rw [sub_eq_add_neg, freeE_add]
    rw [e1, ← Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, E_PC, ← Matrix.mulVec_mulVec]
    rfl
  have hkint : ∀ j, IntervalIntegrable (fun s => (kvec φ z g f s) j) volume 0 t :=
    fun j => hcd.k_int (u := ufn z f) ht (huc t ht) j
  have hfun : (fun s => (freeE z (t - s)).mulVec
        ((PCm φ s).mulVec (f s) - Rm.mulVec (g s))) =
      fun s => (freeE z t).mulVec (kvec φ z g f s) := funext hk
  have hKi : ∀ i, (∫ s in (0 : ℝ)..t, (freeE z t).mulVec (kvec φ z g f s)) i =
      freeE z t i i * ∫ s in (0 : ℝ)..t, (kvec φ z g f s) i := by
    intro i
    have hint : ∀ j, IntervalIntegrable (fun s => ((freeE z t).mulVec (kvec φ z g f s)) j)
        volume 0 t := by
      intro j
      have h : (fun s => ((freeE z t).mulVec (kvec φ z g f s)) j) =
          fun s => freeE z t j j * (kvec φ z g f s) j :=
        funext fun s => freeE_mulVec_apply z t _ j
      rw [h]
      exact (hkint j).const_mul _
    rw [ivInt_apply ht hint i]
    have h : (fun s => ((freeE z t).mulVec (kvec φ z g f s)) i) =
        fun s => freeE z t i i * (kvec φ z g f s) i :=
      funext fun s => freeE_mulVec_apply z t _ i
    rw [h]
    exact intervalIntegral.integral_const_mul _ _
  rw [hfun]
  constructor
  · intro hD i
    have h1 := congrFun hD i
    rw [Pi.add_apply, freeE_mulVec_apply, hKi i] at h1
    have hu : ufn z f t i = freeE z (-t) i i * f t i := freeE_mulVec_apply z (-t) (f t) i
    rw [hu, h1]
    have h2 := freeE_diag_inv z t i
    linear_combination (v0 i + ∫ s in (0 : ℝ)..t, (kvec φ z g f s) i) * h2
  · intro hu
    funext i
    rw [Pi.add_apply, freeE_mulVec_apply, hKi i]
    have h3 := hu i
    have hu' : ufn z f t i = freeE z (-t) i i * f t i := freeE_mulVec_apply z (-t) (f t) i
    rw [hu'] at h3
    have h2 := freeE_diag_inv z t i
    linear_combination (-(f t i)) * h2 + (freeE z t i i) * h3

theorem Mf_inv (φ : PotPair) (z : ℂ) {s : ℝ} (hs : 0 ≤ s) {g : ℝ → Fin 2 → ℂ}
    (hcd : CoreData (Nf φ z) (Bf φ z) (hf z g)) :
    (Mf φ z s)⁻¹ = (Nf φ z s).adjugate * freeE z (-s) := by
  apply Matrix.inv_eq_right_inv
  rw [Mf_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (Nf φ z s), hcd.N_mul_adj hs, Matrix.one_mul,
    freeE_mul_neg]

theorem formula_iff (φ : PotPair) (z : ℂ) (g : ℝ → Fin 2 → ℂ)
    (hg : ∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
      MemLp (fun s : ℝ => g s i) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (v0 : Fin 2 → ℂ) (f : ℝ → Fin 2 → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (f t = (Mf φ z t).mulVec (v0 - ∫ s in (0 : ℝ)..t,
        ((Mf φ z s)⁻¹).mulVec (Rm.mulVec (g s)))) ↔
    ∀ i, ufn z f t i = ((Nf φ z t).mulVec (fun j => v0 j - Hint (Nf φ z) (hf z g) t j)) i := by
  have hcd := coreData φ z g hg
  have hI : (∫ s in (0 : ℝ)..t, ((Mf φ z s)⁻¹).mulVec (Rm.mulVec (g s))) =
      ∫ s in (0 : ℝ)..t, ((Nf φ z s).adjugate).mulVec (hf z g s) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le ht] at hs
    rw [Mf_inv φ z hs.1 hcd, ← Matrix.mulVec_mulVec]
    rfl
  have hH : (v0 - ∫ s in (0 : ℝ)..t, ((Mf φ z s)⁻¹).mulVec (Rm.mulVec (g s))) =
      fun j => v0 j - Hint (Nf φ z) (hf z g) t j := by
    rw [hI]
    funext j
    rw [Pi.sub_apply, ivInt_apply ht (hcd.adjh_int ht) j]
    rfl
  rw [hH]
  constructor
  · intro h i
    have h1 : ufn z f t = (Nf φ z t).mulVec (fun j => v0 j - Hint (Nf φ z) (hf z g) t j) := by
      rw [ufn, h, Matrix.mulVec_mulVec]
      rfl
    exact congrFun h1 i
  · intro h
    have h1 : ufn z f t = (Nf φ z t).mulVec (fun j => v0 j - Hint (Nf φ z) (hf z g) t j) :=
      funext h
    rw [f_eq z f t, h1, Matrix.mulVec_mulVec, ← Mf_eq]

theorem G1011_main (φ : PotPair) (z : ℂ) (g : ℝ → Fin 2 → ℂ) (v0 : Fin 2 → ℂ)
    (hg : ∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
      MemLp (fun s : ℝ => g s i) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (f : ℝ → Fin 2 → ℂ) :
    ((∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
        AbsolutelyContinuousOnInterval (fun t => f t i) 0 T) ∧
      (∀ t : ℝ, 0 ≤ t → f t = (freeE z t).mulVec v0 +
        ∫ s in (0 : ℝ)..t, (freeE z (t - s)).mulVec
          ((rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) s).mulVec (f s) -
            Rm.mulVec (g s)))) ↔
    ∀ t : ℝ, 0 ≤ t →
      f t = (∑' n : ℕ, potentialVolterraTerm38 φ z n t).mulVec
        (v0 - ∫ s in (0 : ℝ)..t,
          ((∑' n : ℕ, potentialVolterraTerm38 φ z n s)⁻¹).mulVec (Rm.mulVec (g s))) := by
  have hcd := coreData φ z g hg
  constructor
  · rintro ⟨hAC, hDuh⟩
    have hfc : ∀ T : ℝ, 0 ≤ T → ∀ j, ContinuousOn (fun s => f s j) (uIcc 0 T) :=
      fun T hT j => (hAC T hT j).continuousOn
    have hDu : ∀ t : ℝ, 0 ≤ t → ∀ i,
        ufn z f t i = v0 i + ∫ s in (0 : ℝ)..t, (((Bf φ z s).mulVec (ufn z f s)) i - hf z g s i) :=
      fun t ht i => (duh_conv φ z g hg v0 hfc ht).1 (hDuh t ht) i
    have hfwd := hcd.fwd (u := ufn z f) (v0 := v0) (uf_cont z hfc) hDu
    intro t ht
    exact (formula_iff φ z g hg v0 f ht).2 (hfwd t ht)
  · intro hF
    have hu : ∀ t : ℝ, 0 ≤ t → ∀ i,
        ufn z f t i = ((Nf φ z t).mulVec (fun j => v0 j - Hint (Nf φ z) (hf z g) t j)) i :=
      fun t ht => (formula_iff φ z g hg v0 f ht).1 (hF t ht)
    obtain ⟨huac, hDu⟩ := hcd.bwd hu
    have hAC : ∀ T : ℝ, 0 ≤ T → ∀ i, AbsolutelyContinuousOnInterval (fun t => f t i) 0 T := by
      intro T hT i
      have h := ((freeE_cd z i).contDiffOn (s := uIcc (0 : ℝ) T)).absolutelyContinuousOnInterval.fun_smul
        (huac T hT i)
      refine h.congr (fun x _ => ?_)
      show freeE z x i i • ufn z f x i = f x i
      rw [smul_eq_mul]
      have := congrFun (f_eq z f x) i
      rw [freeE_mulVec_apply] at this
      exact this.symm
    refine ⟨hAC, fun t ht => ?_⟩
    have hfc : ∀ T : ℝ, 0 ≤ T → ∀ j, ContinuousOn (fun s => f s j) (uIcc 0 T) :=
      fun T hT j => (hAC T hT j).continuousOn
    exact (duh_conv φ z g hg v0 hfc ht).2 (hDu t ht)

end NlsGge.Atomic.G1011S2

namespace NlsGge.Atomic.G1011S2

theorem G1011_whole : ((
  ∀ (φ : PotPair) (z : ℂ) (g : ℝ → (Fin 2 → ℂ)) (v0 : Fin 2 → ℂ),
  let R : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]
  let Sol : (ℝ → (Fin 2 → ℂ)) → Prop := fun f =>
    (∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => f t i) 0 T) ∧
    (∀ t : ℝ, 0 ≤ t → f t = Matrix.mulVec (freeE z t) v0 +
      ∫ s in (0 : ℝ)..t, Matrix.mulVec (freeE z (t - s))
        (Matrix.mulVec (rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) s) (f s) -
          Matrix.mulVec R (g s)))
  (∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
      MemLp (fun s : ℝ => g s i) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) →
  ∀ f : ℝ → (Fin 2 → ℂ),
    Sol f ↔ ∀ t : ℝ, 0 ≤ t →
      f t = Matrix.mulVec (∑' n : ℕ, potentialVolterraTerm38 φ z n t)
        (v0 - ∫ s in (0 : ℝ)..t,
          Matrix.mulVec ((∑' n : ℕ, potentialVolterraTerm38 φ z n s)⁻¹) (Matrix.mulVec R (g s)))
  : Prop)) := by
  intro φ z g v0 R Sol hg f
  exact G1011_main φ z g v0 hg f

end NlsGge.Atomic.G1011S2

