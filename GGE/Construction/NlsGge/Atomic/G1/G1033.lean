                                                                                                                                                               
-- removed (see dedup log); #check/#print lines stripped; no proof text changed.
import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterraProbe

                                                                                                                    
                                                                                                                           
                                                                                                                        
                                                                                                                                        
                                                                                                                  
                                                                                                                                         
                                                                                                                            

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.G1004GenT NlsGge.Pilot

/-! ### The potential pair of a continuous period-one pair -/

open NlsGge.Pilot

namespace NlsGge.Atomic.G1033S1.Aux

noncomputable section

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

/-- The continuous function on the circle of a continuous period-one function. -/
def liftMap (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc 0 1)) (hper : Function.Periodic u 1) :
    C(PhysicalCircle, ℂ) :=
  ⟨AddCircle.liftIoc 1 0 u,
    AddCircle.liftIoc_continuous (by simpa using (hper 0).symm) (by simpa using hu)⟩

/-- Its physical `L²` class. -/
def liftPD (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc 0 1)) (hper : Function.Periodic u 1) : PhysicalL2 :=
  ContinuousMap.toLp 2 spatialMeasure ℂ (liftMap u hu hper)

theorem liftPD_cover_ae (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc 0 1)) (hper : Function.Periodic u 1) :
    ∀ᵐ s : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 → coverRep38 (liftPD u hu hper) s = u s := by
  set F := liftMap u hu hper with hF
  have h1 := coverRep38_ae_phys (liftPD u hu hper)
  have h2 : (⇑(liftPD u hu hper) : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] (F : PhysicalCircle → ℂ) :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure F
  have hv : (⇑(liftPD u hu hper) : PhysicalCircle → ℂ) =ᵐ[(volume : Measure PhysicalCircle)]
      (F : PhysicalCircle → ℂ) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure h2 _
  have hr := (AddCircle.measurePreserving_mk (1 : ℝ) 0).quasiMeasurePreserving.ae_eq_comp hv
  have h01 : (0 : ℝ) + 1 = 1 := by norm_num
  rw [h01] at hr
  have hr' := (ae_restrict_iff' measurableSet_Ioc).1 hr
  filter_upwards [h1, hr'] with s hs1 hs2 hmem
  rw [hs1]
  refine (hs2 hmem).trans ?_
  show AddCircle.liftIoc 1 0 u (s : PhysicalCircle) = u s
  exact AddCircle.liftIoc_coe_apply (by simpa using hmem)


end

end NlsGge.Atomic.G1033S1.Aux

namespace NlsGge.Atomic.G1033S1

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

end

end NlsGge.Atomic.G1033S1

namespace NlsGge.Atomic.G1033S1

noncomputable section

theorem hT1 : (0 : ℝ) ≤ 1 := zero_le_one

theorem exists_u (w : ℂ) : ∃ u : ℝ → ℂ, ContinuousOn u (Set.Icc 0 1) ∧ Function.Periodic u 1 ∧
    ∫ s in (0 : ℝ)..1, u s * Complex.exp (2 * Complex.I * w * (s : ℂ)) ≠ 0 := by
  by_cases hw : ∃ m : ℤ, w = (m : ℂ) * (Real.pi : ℂ)
  · obtain ⟨m, rfl⟩ := hw
    refine ⟨fun s => Complex.exp (-(2 * Complex.I * ((m : ℂ) * (Real.pi : ℂ)) * (s : ℂ))), ?_, ?_, ?_⟩
    · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
    · intro s
      have e : -(2 * Complex.I * ((m : ℂ) * (Real.pi : ℂ)) * (((s + 1 : ℝ)) : ℂ)) =
          -(2 * Complex.I * ((m : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) +
            ((-m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      show Complex.exp (-(2 * Complex.I * ((m : ℂ) * (Real.pi : ℂ)) * (((s + 1 : ℝ)) : ℂ))) =
        Complex.exp (-(2 * Complex.I * ((m : ℂ) * (Real.pi : ℂ)) * (s : ℂ)))
      rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    · have h1 : ∀ s : ℝ, Complex.exp (-(2 * Complex.I * ((m : ℂ) * (Real.pi : ℂ)) * (s : ℂ))) *
          Complex.exp (2 * Complex.I * ((m : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) = 1 := by
        intro s; rw [← Complex.exp_add]; simp
      simp only [h1]
      simp
  · refine ⟨fun _ => 1, continuousOn_const, fun _ => rfl, ?_⟩
    have hw0 : w ≠ 0 := fun h => hw ⟨0, by simp [h]⟩
    have hc : 2 * Complex.I * w ≠ 0 := by
      have := Complex.I_ne_zero
      exact mul_ne_zero (mul_ne_zero two_ne_zero this) hw0
    simp only [one_mul]
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    refine div_ne_zero (sub_ne_zero.2 fun h => hw ?_) hc
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    refine ⟨n, ?_⟩
    have hI := Complex.I_ne_zero
    have hn' : 2 * Complex.I * w = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hI)
    rw [hn']; ring

/-- `ψ ↦ 𝒱_ψ` at fixed `z` as a continuous linear map (the construction of `volterraZeroLT` at general `z`). -/
def volterraLT (z : ℂ) {T : ℝ} (hT : 0 ≤ T) : PotPair →L[ℂ] (PairContT T →L[ℂ] PairContT T) :=
  LinearMap.mkContinuous
    { toFun := fun φ => volterraPT φ z hT
      map_add' := fun φ ψ => volterraPT_add φ ψ z hT
      map_smul' := fun c φ => by
        show volterraPT (c • φ) z hT = c • volterraPT φ z hT
        exact volterraPT_smul_potential c φ z hT }
    (Real.exp (|z.im| * T) * (2 * (Nat.ceil T : ℝ))) fun φ => by
      refine (norm_volterraPT_le φ z hT).trans ?_
      have h := potL1Norm38_le_two_mul φ
      have hc : (0 : ℝ) ≤ Nat.ceil T := Nat.cast_nonneg _
      have he := Real.exp_pos (|z.im| * T)
      calc Real.exp (|z.im| * T) * ((Nat.ceil T : ℝ) * potL1Norm38 φ)
          ≤ Real.exp (|z.im| * T) * ((Nat.ceil T : ℝ) * (2 * ‖φ‖)) := by gcongr
        _ = Real.exp (|z.im| * T) * (2 * (Nat.ceil T : ℝ)) * ‖φ‖ := by ring

theorem volterraLT_apply (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (φ : PotPair) :
    volterraLT z hT φ = volterraPT φ z hT := rfl


theorem fund_deriv_eq (φ h : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    DifferentiableAt ℂ (fun ψ : PotPair => fundContT ψ z hT) φ ∧
    (fderiv ℂ (fun ψ : PotPair => fundContT ψ z hT) φ) h =
      volterraPT φ z hT ((fderiv ℂ (fun ψ : PotPair => fundContT ψ z hT) φ) h) +
        volterraPT h z hT (fundContT φ z hT) := by
  have hF : DifferentiableAt ℂ (fun ψ : PotPair => fundContT ψ z hT) φ := by
    have h1 : AnalyticAt ℂ (fun ψ : PotPair => fundContT ψ z hT) φ :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => fundContT p.1 p.2 hT)
        (f := fun ψ : PotPair => (ψ, z))
        (analyticOnNhd_fundContT hT (φ, z) (Set.mem_univ _))
        (analyticAt_id.prod analyticAt_const)
    exact h1.differentiableAt
  refine ⟨hF, ?_⟩
  have hLd : HasFDerivAt (volterraLT z hT) (volterraLT z hT) φ := ContinuousLinearMap.hasFDerivAt (𝕜 := ℂ) (E := PotPair)
    (F := PairContT T →L[ℂ] PairContT T) (volterraLT z hT)
  have hFd : HasFDerivAt (fun ψ : PotPair => fundContT ψ z hT)
      (fderiv ℂ (fun ψ : PotPair => fundContT ψ z hT) φ) φ := hF.hasFDerivAt
  have hRHS := (hLd.clm_apply hFd).const_add (freeFundT T z)
  have hRHS' : HasFDerivAt (fun ψ : PotPair => fundContT ψ z hT) _ φ :=
    hRHS.congr_of_eventuallyEq (Eventually.of_forall fun ψ => by
      show fundContT ψ z hT = freeFundT T z + volterraPT ψ z hT (fundContT ψ z hT)
      exact fundContT_eq_add ψ z hT)
  have hU := hFd.unique hRHS'
  have := congrArg (fun L => L h) hU
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at this
  exact this


theorem entry_deriv (z : ℂ) (h : PotPair) (i j : Fin 2) :
    ((fderiv ℂ (fun φ : PotPair => fundContT φ z hT1) 0) h) ⟨1, hT1, le_rfl⟩ i j =
      freeKernelVolterraTerm38 (potRepFst38 h) (potRepSnd38 h) z 1 1 i j := by
  obtain ⟨-, heq⟩ := fund_deriv_eq 0 h z hT1
  have hV0 : volterraPT (0 : PotPair) z hT1 = 0 := volterra_zero z
  have hF0 : fundContT (0 : PotPair) z hT1 = freeFundT 1 z := by
    have := fundContT_eq_add (0 : PotPair) z hT1
    rw [hV0] at this
    simpa using this
  rw [hV0, hF0] at heq
  simp only [ContinuousLinearMap.zero_apply, zero_add] at heq
  rw [heq, volterraPT_apply, volterraFunT_apply, term1_apply]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
    have := Set.uIcc_subset_Icc (Set.left_mem_Icc.2 hT1) (⟨hT1, le_rfl⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1) hs
    exact this
  rw [ext38T_of_mem hT1 _ hs']
  rfl

theorem interior_empty (z : ℂ) (i j : Fin 2)
    (hne : ∃ h : PotPair, freeKernelVolterraTerm38 (potRepFst38 h) (potRepSnd38 h) z 1 1 i j ≠ 0) :
    interior {φ : PotPair | monodromyPair φ z i j = 0} = ∅ := by
  by_contra hcon
  obtain ⟨φ0, hφ0⟩ := Set.nonempty_iff_ne_empty.2 hcon
  set F : PotPair → PairContT 1 := fun φ => fundContT φ z hT1 with hF
  set f : PotPair → ℂ := fun φ => monodromyPair φ z i j with hf
  have hfe : ∀ φ : PotPair, f φ = F φ ⟨1, hT1, le_rfl⟩ i j := fun φ => rfl
  have hFa : AnalyticOnNhd ℂ F Set.univ := by
    intro φ _
    exact AnalyticAt.fun_comp (f := fun φ : PotPair => (φ, z))
      (analyticOnNhd_fundContT hT1 (φ, z) (Set.mem_univ _))
      (AnalyticAt.prod analyticAt_id analyticAt_const)
  have hfa : AnalyticOnNhd ℂ f Set.univ := by
    intro φ _
    have h2 := ((ContinuousLinearMap.analyticAt (fundEntryLT (T := 1) ⟨1, hT1, le_rfl⟩ i j) (F φ))).comp (hFa φ (Set.mem_univ _))
    exact h2
  have hev : f =ᶠ[nhds φ0] 0 := by
    have : {φ : PotPair | monodromyPair φ z i j = 0} ∈ nhds φ0 := mem_interior_iff_mem_nhds.1 hφ0
    filter_upwards [this] with φ hφ
    exact hφ
  have hzero := hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_univ (𝕜 := ℝ)).isPreconnected
    (Set.mem_univ φ0) hev
  have hf0 : f = 0 := funext fun φ => hzero (Set.mem_univ φ)
  obtain ⟨h, hh⟩ := hne
  have hFd : DifferentiableAt ℂ F 0 := by
    exact (hFa 0 (Set.mem_univ _)).differentiableAt
  have hg : HasFDerivAt f ((fundEntryLT (T := 1) ⟨1, hT1, le_rfl⟩ i j).comp (fderiv ℂ F 0)) 0 :=
    (ContinuousLinearMap.hasFDerivAt (fundEntryLT (T := 1) ⟨1, hT1, le_rfl⟩ i j)).comp 0 hFd.hasFDerivAt
  have hg0 : HasFDerivAt f (0 : PotPair →L[ℂ] ℂ) 0 := by
    rw [hf0]; exact hasFDerivAt_const (0 : ℂ) 0
  have hu := hg.unique hg0
  have := congrArg (fun L => L h) hu
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
  have hval : (fundEntryLT (T := 1) ⟨1, hT1, le_rfl⟩ i j) (fderiv ℂ F 0 h) = 
      freeKernelVolterraTerm38 (potRepFst38 h) (potRepSnd38 h) z 1 1 i j := entry_deriv z h i j
  rw [hval] at this
  exact hh this

theorem exists_h01 (z : ℂ) : ∃ h : PotPair,
    freeKernelVolterraTerm38 (potRepFst38 h) (potRepSnd38 h) z 1 1 0 1 ≠ 0 := by
  obtain ⟨u, hu, hper, hint⟩ := exists_u z
  refine ⟨(Aux.liftPD u hu hper, 0), ?_⟩
  rw [term1_entry01]
  have hI : Complex.I * Complex.exp (-(Complex.I * z * ((1 : ℝ) : ℂ))) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _)
  refine mul_ne_zero hI ?_
  have : ∫ s in (0 : ℝ)..1, potRepFst38 (Aux.liftPD u hu hper, (0 : PhysicalL2)) s *
      Complex.exp (2 * Complex.I * z * (s : ℂ)) =
      ∫ s in (0 : ℝ)..1, u s * Complex.exp (2 * Complex.I * z * (s : ℂ)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Aux.liftPD_cover_ae u hu hper] with s hs hmem
    have hmem' : s ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le zero_le_one] using hmem
    simp only [potRepFst38, hs hmem']
  rw [this]; exact hint

theorem exists_h10 (z : ℂ) : ∃ h : PotPair,
    freeKernelVolterraTerm38 (potRepFst38 h) (potRepSnd38 h) z 1 1 1 0 ≠ 0 := by
  obtain ⟨u, hu, hper, hint⟩ := exists_u (-z)
  refine ⟨(0, Aux.liftPD u hu hper), ?_⟩
  rw [term1_entry10]
  have hI : -Complex.I * Complex.exp (Complex.I * z * ((1 : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) (Complex.exp_ne_zero _)
  refine mul_ne_zero hI ?_
  have : ∫ s in (0 : ℝ)..1, potRepSnd38 ((0 : PhysicalL2), Aux.liftPD u hu hper) s *
      Complex.exp (2 * Complex.I * (-z) * (s : ℂ)) =
      ∫ s in (0 : ℝ)..1, u s * Complex.exp (2 * Complex.I * (-z) * (s : ℂ)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Aux.liftPD_cover_ae u hu hper] with s hs hmem
    have hmem' : s ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le zero_le_one] using hmem
    simp only [potRepSnd38, hs hmem']
  rw [this]; exact hint

theorem G1033_whole : ∀ z : ℂ,
    interior {φ : PotPair | monodromyPair φ z 0 1 = 0} = ∅ ∧
    interior {φ : PotPair | monodromyPair φ z 1 0 = 0} = ∅ ∧
    Dense {φ : PotPair | monodromyPair φ z 0 1 ≠ 0} ∧
    Dense {φ : PotPair | monodromyPair φ z 1 0 ≠ 0} := by
  intro z
  have h1 := interior_empty z 0 1 (exists_h01 z)
  have h2 := interior_empty z 1 0 (exists_h10 z)
  refine ⟨h1, h2, ?_, ?_⟩
  · have := interior_eq_empty_iff_dense_compl.1 h1
    simpa [Set.compl_setOf] using this
  · have := interior_eq_empty_iff_dense_compl.1 h2
    simpa [Set.compl_setOf] using this

end

end NlsGge.Atomic.G1033S1
