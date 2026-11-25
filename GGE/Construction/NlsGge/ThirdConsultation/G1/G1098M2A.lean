import NlsGge.GK38.GradFundamentalL2
import NlsGge.GK38.GradFundamentalPairing
import NlsGge.GK38.DirichletLabels
import NlsGge.Atomic.G1.G1062
import NlsGge.ThirdConsultation.G1.G1098Host

                                                                          
                                                                                       
                                                                                                   
                                                                                                 
                                                                                            
                                                                                         
                                                                                                   
                          
set_option autoImplicit false
open Filter Topology MeasureTheory Set NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G1098M2A
noncomputable section

/-- The Fourier basis vector of mode `n`, as a physical L2 class. -/
def vacBasis209 (n : ℤ) : PhysicalL2 := physicalFourierL2.symm (lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ))

/-- The reflected Fourier transform of the basis vector is the explicit lp vector `-e_{-n}`. -/
theorem reflectedFourierL2_vacBasis (n : ℤ) :
    reflectedFourierL2 (vacBasis209 n) = lp.single (E := fun _ : ℤ => ℂ) 2 (-n) (-1) := by
  have hF : physicalFourierL2 (vacBasis209 n) = lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) :=
    LinearIsometryEquiv.apply_symm_apply _ _
  apply lp.ext
  funext k
  rw [reflectedFourierL2_apply]
  unfold reflectedFourier
  rw [← physicalFourierL2_apply, hF]
  by_cases hk : k = -n
  · subst hk
    simp [lp.single_apply, Pi.single_apply]
  · have hk' : -k ≠ n := fun h => hk (by omega)
    simp [lp.single_apply, Pi.single_apply, hk, hk']

/-- The reflected Fourier transform of a single mode is a scalar multiple of the Fourier basis. -/
theorem reflectedFourierL2_symm_single (n : ℤ) (a : ℂ) :
    reflectedFourierL2.symm (lp.single (E := fun _ : ℤ => ℂ) 2 (-n) a) =
      (-a) • vacBasis209 n := by
  rw [LinearIsometryEquiv.symm_apply_eq, map_smul, reflectedFourierL2_vacBasis,
    ← lp.single_smul]
  congr 1
  ring

/-- Fourier coefficients of a kernel which is `c · fourier n` on `[0,1]`. -/
theorem fourierCoeff_liftIoc_eq_smul (f : ℝ → ℂ) (c : ℂ) (n : ℤ)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) 1, f s = c * fourier n (s : AddCircle (1 : ℝ))) (m : ℤ) :
    fourierCoeff (AddCircle.liftIoc 1 0 f) m = c * Pi.single (M := fun _ : ℤ => ℂ) n (1 : ℂ) m := by
  have hA : fourierCoeff (AddCircle.liftIoc 1 0 f) m =
      c * ∫ x in (0 : ℝ)..1, fourier (-m) (x : AddCircle (1 : ℝ)) •
        fourier n (x : AddCircle (1 : ℝ)) := by
    rw [fourierCoeff_eq_intervalIntegral _ m 0, zero_add, one_div, inv_one, one_smul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    simp only [smul_eq_mul]
    rw [AddCircle.liftIoc_zero_coe_apply hx, hf x ⟨hx.1.le, hx.2⟩]
    ring
  have hB : fourierCoeff (fourier n : AddCircle (1 : ℝ) → ℂ) m =
      ∫ x in (0 : ℝ)..1, fourier (-m) (x : AddCircle (1 : ℝ)) •
        fourier n (x : AddCircle (1 : ℝ)) := by
    rw [fourierCoeff_eq_intervalIntegral _ m 0, zero_add, one_div, inv_one, one_smul]
  have hC : fourierCoeff (fourier n : AddCircle (1 : ℝ) → ℂ) m = Pi.single (M := fun _ : ℤ => ℂ) n (1 : ℂ) m :=
    congrFun (fourierCoeff_fourier n) m
  rw [hA, ← hB, hC]

/-- The class of a pair kernel whose first coordinate is `c · fourier n` is `c` times the basis. -/
theorem pairKernel_fst_class_eq_smul (K : PairKernelCont38) (c : ℂ) (n : ℤ)
    (hK : ∀ s : ℝ, ∀ hs : s ∈ Set.Icc (0 : ℝ) 1,
      pairKernelExt38 K s 0 = c * fourier n (s : AddCircle (1 : ℝ))) :
    (pairKernelL2Class38 K).1 = c • vacBasis209 n := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext m
  have hF : physicalFourierL2 (vacBasis209 n) = lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) :=
    LinearIsometryEquiv.apply_symm_apply _ _
  have hXae : (pairKernelL2Class38 K).1 =ᵐ[spatialMeasure]
      AddCircle.liftIoc 1 0 (fun s => pairKernelExt38 K s 0) :=
    (memLp_intervalKernelLift38 _ (memLp_pairKernelExt38 K 0)).coeFn_toLp
  have hL : physicalFourierL2 (pairKernelL2Class38 K).1 m = c * Pi.single (M := fun _ : ℤ => ℂ) n (1 : ℂ) m := by
    rw [physicalFourierL2_apply]
    unfold physicalFourier
    rw [congrFun (fourierCoeff_congr_ae hXae) m]
    exact fourierCoeff_liftIoc_eq_smul _ c n (fun s hs => hK s hs) m
  have hR : physicalFourierL2 (c • vacBasis209 n) m =
      c * Pi.single (M := fun _ : ℤ => ℂ) n (1 : ℂ) m := by
    rw [map_smul, hF]
    simp [lp.single_apply, lp.coeFn_smul]
  rw [hL, hR]

/-- Pointwise value of the zero-potential fundamental solution on `[0,1]`. -/
theorem ext38_zero_eq_freeE (z : ℂ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ext38 (fundContP 0 z) s = freeE z s := by
  rw [ext38_of_mem _ hs]
  unfold fundContP
  rw [fundCont_zero]
  rfl

theorem state_zero_apply (z : ℂ) (a : PairVec38) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin 2) :
    state 0 z a ⟨s, hs⟩ i = a 0 * freeE z s i 0 + a 1 * freeE z s i 1 := by
  show (a 0 • fundColumn38 0 z s 0 + a 1 • fundColumn38 0 z s 1) i = _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, fundColumn38]
  rw [ext38_zero_eq_freeE z hs]

theorem mixedSquare_apply_fst (v w : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1) :
    mixedSquare v w t 0 = v t 1 * w t 1 := rfl

theorem pairKernelExt38_mixedSquare_fst (v w : PairKernelCont38) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    pairKernelExt38 (mixedSquare v w) s 0 = v ⟨s, hs⟩ 1 * w ⟨s, hs⟩ 1 := by
  rw [pairKernelExt38_of_mem _ hs]
  rfl

/-- `muSeq` at the zero potential is `n π`. -/
theorem muSeq_zero_eq (n : ℤ) : muSeq 0 n = (n : ℂ) * (Real.pi : ℂ) := by
  rw [muSeq_zero38]
  rfl

theorem complexDirState_zero_apply (n : ℤ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    complexDirState 0 n ⟨s, hs⟩ 1 =
      Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) := by
  unfold complexDirState
  rw [muSeq_zero_eq, state_zero_apply _ _ hs]
  simp [freeE]

theorem terminalSeed_zero_eq (z : ℂ) :
    terminalSeed 0 z = ![Complex.exp (Complex.I * z), -Complex.exp (-(Complex.I * z))] := by
  unfold terminalSeed
  rw [monodromyPair_zero_potential]
  ext i
  fin_cases i <;> simp [freeE]

theorem exp_I_nPi (n : ℤ) : Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ))) = parity n := by
  have h1 : Complex.I * ((n : ℂ) * (Real.pi : ℂ)) = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    ring
  rw [h1, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rfl

theorem exp_neg_I_nPi (n : ℤ) :
    Complex.exp (-(Complex.I * ((n : ℂ) * (Real.pi : ℂ)))) = parity n := by
  have h1 : -(Complex.I * ((n : ℂ) * (Real.pi : ℂ))) = (n : ℂ) * (-((Real.pi : ℂ) * Complex.I)) := by
    ring
  have h2 : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
    rw [Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  rw [h1, Complex.exp_int_mul, h2]
  rfl

theorem terminalSeed_zero_nPi (n : ℤ) :
    terminalSeed 0 ((n : ℂ) * (Real.pi : ℂ)) = ![parity n, -parity n] := by
  rw [terminalSeed_zero_eq, exp_I_nPi, exp_neg_I_nPi]

theorem complexTerminalState_zero_apply (n : ℤ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    complexTerminalState 0 n ⟨s, hs⟩ 1 = -parity n * Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) := by
  unfold complexTerminalState
  rw [muSeq_zero_eq, state_zero_apply _ _ hs, terminalSeed_zero_nPi]
  simp [freeE]

/-- The plus vacuum kernel has first coordinate `fourier n`. -/
theorem complexMixedKernel_zero_false_fst (n : ℤ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    pairKernelExt38 (complexMixedKernel 0 0 n false) s 0 =
      (1 : ℂ) * fourier n (s : AddCircle (1 : ℝ)) := by
  rw [show complexMixedKernel 0 0 n false =
      mixedSquare (complexDirState 0 n) (complexDirState 0 n) from rfl,
    pairKernelExt38_mixedSquare_fst _ _ hs, complexDirState_zero_apply, one_mul,
    fourier_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The minus vacuum kernel has first coordinate `-(2 i parity n) · fourier n`. -/
theorem complexMixedKernel_zero_true_fst (n : ℤ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    pairKernelExt38 (complexMixedKernel 0 0 n true) s 0 =
      (-(2 * Complex.I * parity n)) * fourier n (s : AddCircle (1 : ℝ)) := by
  rw [show complexMixedKernel 0 0 n true = Complex.I •
      (mixedSquare (complexDirState 0 n) (complexTerminalState 0 n) +
        mixedSquare (complexDirState 0 n) (complexTerminalState 0 n)) from rfl,
    pairKernelExt38_of_mem _ hs]
  simp only [ContinuousMap.smul_apply, ContinuousMap.add_apply, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul, mixedSquare_apply_fst]
  rw [complexDirState_zero_apply, complexTerminalState_zero_apply, fourier_coe_apply]
  have hE2 : Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) *
      Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * n * s) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [Complex.ofReal_one, div_one]
  linear_combination (-2 * Complex.I * parity n) * hE2

/-- The vacuum identity (Pro round 9 section 13): the complex mixed column at zero potentials is
the reference column `mixedReference n minus`. -/
theorem complexMixedColumn_vacuum (n : ℤ) (minus : Bool) :
    complexMixedColumn 0 0 n minus = mixedReference n minus := by
  cases minus with
  | false =>
    show (pairKernelL2Class38 (complexMixedKernel 0 0 n false)).1 =
      reflectedFourierL2.symm (lp.single 2 (-n) (-1))
    rw [pairKernel_fst_class_eq_smul _ 1 n (fun s hs => complexMixedKernel_zero_false_fst n hs),
      reflectedFourierL2_symm_single] <;> simp
  | true =>
    show (pairKernelL2Class38 (complexMixedKernel 0 0 n true)).1 =
      reflectedFourierL2.symm (lp.single 2 (-n) (2 * Complex.I * parity n))
    rw [pairKernel_fst_class_eq_smul _ _ n (fun s hs => complexMixedKernel_zero_true_fst n hs),
      reflectedFourierL2_symm_single] <;> simp

end
end NlsGge.ThirdConsultation.G1098M2A
