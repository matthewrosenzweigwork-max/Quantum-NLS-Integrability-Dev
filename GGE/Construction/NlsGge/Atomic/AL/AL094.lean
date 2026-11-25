import NlsGge.Spectral.ActualPhysicalUnitDiscriminantNonrealZeroFree32V1
import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4
import NlsGge.Spectral.ActualComplexZsFiniteDysonIteratesContinuousV9
import NlsGge.Spectral.ActualComplexZsDysonProductHasSumV2
import NlsGge.Analysis.NaturalCover

namespace NlsGge.Atomic.AL094


open NlsGge.SpectralFoundations

def alContinuumGenerator38 (U : ℝ → ℂ) (lam : ℝ) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I * (lam : ℂ), U x;
     star (U x), -Complex.I * (lam : ℂ)]

def alContinuumPhaseGauge38 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-Complex.I, 0; 0, 1]

def alContinuumPhaseGaugeInv38 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0; 0, 1]

theorem alContinuumGenerator_eq_zs38 (U : ℝ → ℂ) (lam x : ℝ) :
    alContinuumGenerator38 U lam x =
      zsCoefficientComplex (fun s => -Complex.I * U s) (-(lam : ℂ)) x := by
  unfold alContinuumGenerator38 zsCoefficientComplex
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, star_mul, Complex.star_def, Complex.conj_I,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    ring_nf <;> simp [Complex.ext_iff] <;> ring_nf <;> simp

theorem alContinuumPhaseGauge_mul_inv38 :
    alContinuumPhaseGauge38 * alContinuumPhaseGaugeInv38 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alContinuumPhaseGauge38, alContinuumPhaseGaugeInv38, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I, Matrix.one_apply]

theorem alContinuumPhaseGauge_inv_mul38 :
    alContinuumPhaseGaugeInv38 * alContinuumPhaseGauge38 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alContinuumPhaseGauge38, alContinuumPhaseGaugeInv38, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I, Matrix.one_apply]

theorem zsCoefficient_minusI_conjugate38
    (U : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    zsCoefficientComplex (fun s => -Complex.I * U s) z x =
      alContinuumPhaseGauge38 * zsCoefficientComplex U z x *
        alContinuumPhaseGaugeInv38 := by
  unfold zsCoefficientComplex alContinuumPhaseGauge38 alContinuumPhaseGaugeInv38
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, star_mul, Complex.star_def, Complex.conj_I,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    ring_nf <;> simp [Complex.ext_iff] <;> ring_nf <;> simp

theorem alContinuumPhaseGauge_sandwich_entry38 (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (alContinuumPhaseGauge38 * X * alContinuumPhaseGaugeInv38) i j =
      alContinuumPhaseGauge38 i i * alContinuumPhaseGaugeInv38 j j * X i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [alContinuumPhaseGauge38, alContinuumPhaseGaugeInv38] <;> (try ring_nf) <;>
    (try simp [Complex.I_sq]) <;> (try ring_nf)

theorem actualComplexZsDysonTerm_minusI38 (U : ℝ → ℂ) (z : ℂ) (n : ℕ) (t : ℝ) :
    actualComplexZsDysonTerm (fun s => -Complex.I * U s) z n t =
      alContinuumPhaseGauge38 * actualComplexZsDysonTerm U z n t *
        alContinuumPhaseGaugeInv38 := by
  have key : ∀ A T : Matrix (Fin 2) (Fin 2) ℂ,
      (alContinuumPhaseGauge38 * A * alContinuumPhaseGaugeInv38) *
        (alContinuumPhaseGauge38 * T * alContinuumPhaseGaugeInv38) =
      alContinuumPhaseGauge38 * (A * T) * alContinuumPhaseGaugeInv38 := by
    intro A T
    calc (alContinuumPhaseGauge38 * A * alContinuumPhaseGaugeInv38) *
          (alContinuumPhaseGauge38 * T * alContinuumPhaseGaugeInv38)
        = alContinuumPhaseGauge38 * A * (alContinuumPhaseGaugeInv38 * alContinuumPhaseGauge38) *
            T * alContinuumPhaseGaugeInv38 := by
          simp only [Matrix.mul_assoc]
      _ = alContinuumPhaseGauge38 * (A * T) * alContinuumPhaseGaugeInv38 := by
          rw [alContinuumPhaseGauge_inv_mul38]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
  induction n generalizing t with
  | zero =>
    simp [actualComplexZsDysonTerm, alContinuumPhaseGauge_mul_inv38]
  | succ n ih =>
    ext i j
    rw [alContinuumPhaseGauge_sandwich_entry38]
    simp only [actualComplexZsDysonTerm]
    simp_rw [zsCoefficient_minusI_conjugate38, ih, key, alContinuumPhaseGauge_sandwich_entry38]
    rw [intervalIntegral.integral_const_mul]


open NlsGge.SpectralFoundations NlsGge.Analysis NlsGge.Pilot NlsGge.Schur

noncomputable def alContinuumMonodromy38 (u : PhysicalL2) (lam : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  actualComplexZsDysonTsum
    (fun x => -Complex.I *
      (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
    (-(lam : ℂ)) 1

theorem actualComplexZsDysonTsum_minusI_physical38
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    actualComplexZsDysonTsum
      (fun s => -Complex.I *
        (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      z t =
      alContinuumPhaseGauge38 *
        actualComplexZsDysonTsum
          (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ)
            (s : SpectralCircle)) z t *
        alContinuumPhaseGaugeInv38 := by
  ext i j
  rw [alContinuumPhaseGauge_sandwich_entry38]
  unfold actualComplexZsDysonTsum
  simp only [actualComplexZsDysonTerm_minusI38, alContinuumPhaseGauge_sandwich_entry38]
  exact tsum_mul_left

theorem trace_conj_phase38 (T : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (alContinuumPhaseGauge38 * T * alContinuumPhaseGaugeInv38) =
      Matrix.trace T := by
  rw [Matrix.trace_mul_cycle, alContinuumPhaseGauge_inv_mul38, Matrix.one_mul]

theorem alContinuum_trace_reflection38
    (u : PhysicalL2) (lam : ℝ) :
    Matrix.trace (alContinuumMonodromy38 u lam) / 2 =
      actualPhysicalUnitHalfTrace32 u (-(lam : ℂ)) := by
  unfold alContinuumMonodromy38 actualPhysicalUnitHalfTrace32
  rw [actualComplexZsDysonTsum_minusI_physical38 u (-(lam : ℂ)) 1 ⟨zero_le_one, by norm_num⟩,
    trace_conj_phase38]

theorem alContinuumGenerator_eq_zs38_check (U : ℝ → ℂ) (lam x : ℝ) :
    alContinuumGenerator38 U lam x =
      zsCoefficientComplex (fun s => -Complex.I * U s) (-(lam : ℂ)) x :=
  alContinuumGenerator_eq_zs38 U lam x

end NlsGge.Atomic.AL094
