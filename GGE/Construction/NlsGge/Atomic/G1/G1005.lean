import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1003
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

namespace NlsGge.Atomic.G1005Aux

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

end NlsGge.Atomic.G1005Aux


end

section
                                                                                                  
                                                                                                    
                                                                                                         

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT NlsGge.Atomic.G1005Aux

namespace NlsGge.Atomic.G1005

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

end NlsGge.Atomic.G1005


end

