import NlsGge.Spectral.ActualPhysicalInteractionGaugeACVolterra32V3
import NlsGge.Spectral.ActualPhysicalUnitHalfTraceGeneralRescaling35V3
import NlsGge.Spectral.ActualInteractionPairKernel32V2
import NlsGge.Spectral.MatrixNormalFormUniformBox38V1

/-!
# Uniform box estimate, part 1: the normalized fundamental matrix

For the actual interaction state `D(t)` (period-one monodromy in the interaction
picture) put `Φ(t) := diag(1, e^{2itz}) · D(t)`.  Then, a.e. on `[0,1]`,
`Φ' = (Λ + V) Φ`, `Λ = diag(0, 2iz)`, `V = [[0, iU], [-iŪ, 0]]` with the ACTUAL
representative `U = naturalPhysicalCoverL2 u (· : SpectralCircle)`, `Φ(0) = 1`, and
`e^{iz} Δh(u,z) - (1 + e^{2iz})/2 = ((Φ(1)₀₀ - 1) + (Φ(1)₁₁ - e^{2iz}))/2`.
No exponential growth in `Im z` enters `Λ + V`; `e^{Λτ}` is a contraction for
`Im z ≥ 0`, `τ ≥ 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Row weights `w₀ = 1`, `w₁ = e^{2itz}`. -/
def uniformBoxRowWeight38 (z : ℂ) (t : ℝ) (i : Fin 2) : ℂ :=
  if i = 0 then 1 else Complex.exp (2 * (t : ℂ) * Complex.I * z)

/-- The actual rough potential representative. -/
def uniformBoxPotential38 (u : PhysicalL2) : ℝ → ℂ :=
  fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)

/-- The actual interaction state. -/
def uniformBoxInteractionState38 (u : PhysicalL2) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  actualZsInteractionState32 z
    (actualComplexZsDysonTsum (uniformBoxPotential38 u) z) t

/-- The normalized fundamental matrix `Φ(t) = diag(1, e^{2itz}) D(t)`. -/
def uniformBoxNormalizedState38 (u : PhysicalL2) (z : ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => uniformBoxRowWeight38 z t i * uniformBoxInteractionState38 u z t i j

/-- `Λ = diag(0, 2iz)`. -/
def uniformBoxLambda38 (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j ∧ i = 1 then 2 * Complex.I * z else 0

/-- `V(s) = [[0, iU(s)], [-iŪ(s), 0]]` for a potential function `U`. -/
def uniformBoxV38 (U : ℝ → ℂ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 0 else if i = 0 then Complex.I * U s else -Complex.I * star (U s)

theorem uniformBoxNormalizedState38_zero (u : PhysicalL2) (z : ℂ) :
    uniformBoxNormalizedState38 u z 0 = 1 := by
  have h : uniformBoxInteractionState38 u z 0 = 1 :=
    actualPhysicalInteractionState_initial32 u z
  ext i j
  simp only [uniformBoxNormalizedState38]
  rw [h]
  fin_cases i <;> simp [uniformBoxRowWeight38]

theorem uniformBoxExp38_contDiff (z : ℂ) :
    ContDiff ℝ 1 (fun t : ℝ => Complex.exp (2 * (t : ℂ) * Complex.I * z)) := by
  have h1 : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  exact (((contDiff_const.mul h1).mul contDiff_const).mul contDiff_const).cexp

theorem uniformBoxExp38_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.exp (2 * (r : ℂ) * Complex.I * z))
      (2 * Complex.I * z * Complex.exp (2 * (t : ℂ) * Complex.I * z)) t := by
  have h1 : HasDerivAt (fun r : ℝ => 2 * (r : ℂ) * Complex.I * z) (2 * Complex.I * z) t := by
    have := (((hasDerivAt_id (t : ℝ)).ofReal_comp).const_mul (2 : ℂ)).mul_const (Complex.I * z)
    convert this using 1
    · funext r; simp; ring
    · simp; ring
  have := h1.cexp
  convert this using 1
  ring

theorem uniformBoxRowWeight38_hasDerivAt (z : ℂ) (i : Fin 2) (t : ℝ) :
    HasDerivAt (fun r : ℝ => uniformBoxRowWeight38 z r i)
      (uniformBoxLambda38 z i i * uniformBoxRowWeight38 z t i) t := by
  fin_cases i
  · have : (fun r : ℝ => uniformBoxRowWeight38 z r 0) = fun _ => (1 : ℂ) := by
      funext r; simp [uniformBoxRowWeight38]
    show HasDerivAt (fun r : ℝ => uniformBoxRowWeight38 z r 0)
      (uniformBoxLambda38 z 0 0 * uniformBoxRowWeight38 z t 0) t
    rw [this]
    simpa [uniformBoxLambda38] using hasDerivAt_const t (1 : ℂ)
  · have : (fun r : ℝ => uniformBoxRowWeight38 z r 1) =
        fun r : ℝ => Complex.exp (2 * (r : ℂ) * Complex.I * z) := by
      funext r; simp [uniformBoxRowWeight38]
    show HasDerivAt (fun r : ℝ => uniformBoxRowWeight38 z r 1)
      (uniformBoxLambda38 z 1 1 * uniformBoxRowWeight38 z t 1) t
    rw [this]
    have hw : uniformBoxRowWeight38 z t 1 = Complex.exp (2 * (t : ℂ) * Complex.I * z) := by
      simp [uniformBoxRowWeight38]
    have hl : uniformBoxLambda38 z 1 1 = 2 * Complex.I * z := by
      simp [uniformBoxLambda38]
    rw [hw, hl]
    exact uniformBoxExp38_hasDerivAt z t

/-- Entrywise absolute continuity of `Φ` on `[0,1]`. -/
theorem uniformBoxNormalizedState38_ac (u : PhysicalL2) (z : ℂ) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval
      (fun t => uniformBoxNormalizedState38 u z t i j) 0 1 := by
  have hD : AbsolutelyContinuousOnInterval
      (fun t => uniformBoxInteractionState38 u z t i j) 0 1 := by
    have h := absolutelyContinuous_actualPhysicalInteractionState32 u z i j
    exact h.mono (by
      simp only [Set.uIcc_of_le (zero_le_one' ℝ), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
      exact Set.Icc_subset_Icc le_rfl (by norm_num))
  have hw : AbsolutelyContinuousOnInterval (fun t => uniformBoxRowWeight38 z t i) 0 1 := by
    have hc : ContDiff ℝ 1 (fun t : ℝ => uniformBoxRowWeight38 z t i) := by
      fin_cases i
      · have : (fun r : ℝ => uniformBoxRowWeight38 z r 0) = fun _ => (1 : ℂ) := by
          funext r; simp [uniformBoxRowWeight38]
        show ContDiff ℝ 1 (fun r : ℝ => uniformBoxRowWeight38 z r 0)
        rw [this]; exact contDiff_const
      · have : (fun r : ℝ => uniformBoxRowWeight38 z r 1) =
            fun r : ℝ => Complex.exp (2 * (r : ℂ) * Complex.I * z) := by
          funext r; simp [uniformBoxRowWeight38]
        show ContDiff ℝ 1 (fun r : ℝ => uniformBoxRowWeight38 z r 1)
        rw [this]; exact uniformBoxExp38_contDiff z
    exact hc.contDiffOn.absolutelyContinuousOnInterval
  simpa only [uniformBoxNormalizedState38, Pi.smul_apply, smul_eq_mul] using! hw.smul hD

/-- `Φ' = (Λ + V) Φ` a.e. on `[0,1]`. -/
theorem uniformBoxNormalizedState38_ae_hasDerivAt (u : PhysicalL2) (z : ℂ) :
    ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => uniformBoxNormalizedState38 u z r i j)
        (((uniformBoxLambda38 z + uniformBoxV38 (uniformBoxPotential38 u) s) *
          uniformBoxNormalizedState38 u z s) i j) s := by
  have hall : ∀ i j : Fin 2, ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt (fun s => uniformBoxInteractionState38 u z s i j)
        ((actualZsInteractionCoefficient32 (uniformBoxPotential38 u) z t *
          uniformBoxInteractionState38 u z t) i j) t :=
    fun i j => actualPhysicalZsInteractionState_ae_hasDerivAt32 u z i j
  have h00 := hall 0 0
  have h01 := hall 0 1
  have h10 := hall 1 0
  have h11 := hall 1 1
  filter_upwards [h00, h01, h10, h11] with s a00 a01 a10 a11 hs i j
  have hs2 : s ∈ Set.uIcc (0:ℝ) 2 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
    exact ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hD : ∀ a b : Fin 2, HasDerivAt (fun r => uniformBoxInteractionState38 u z r a b)
      ((actualZsInteractionCoefficient32 (uniformBoxPotential38 u) z s *
        uniformBoxInteractionState38 u z s) a b) s := by
    intro a b
    fin_cases a <;> fin_cases b
    · exact a00 hs2
    · exact a01 hs2
    · exact a10 hs2
    · exact a11 hs2
  have hprod := (uniformBoxRowWeight38_hasDerivAt z i s).mul (hD i j)
  refine hprod.congr_deriv ?_
  -- algebra: expand both sides
  obtain ⟨hc01, hc10⟩ := actualInteractionCoefficient_entries32 (uniformBoxPotential38 u) z s
  have hc00 : actualZsInteractionCoefficient32 (uniformBoxPotential38 u) z s 0 0 = 0 := by
    simp [actualZsInteractionCoefficient32]
  have hc11 : actualZsInteractionCoefficient32 (uniformBoxPotential38 u) z s 1 1 = 0 := by
    simp [actualZsInteractionCoefficient32]
  have hexp : Complex.exp (2 * (s : ℂ) * Complex.I * z) *
      Complex.exp (-2 * (s : ℂ) * Complex.I * z) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have hexp2 : Complex.exp (2 * (s : ℂ) * Complex.I * z) *
      Complex.exp (-(2 * (s : ℂ) * Complex.I * z)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hexp3 : Complex.exp (Complex.I * z * (s : ℂ) * 2) *
      Complex.exp (-(Complex.I * z * (s : ℂ) * 2)) = 1 := by
    rw [← Complex.exp_add]; simp
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, uniformBoxNormalizedState38,
      uniformBoxRowWeight38, uniformBoxLambda38, uniformBoxV38, hc00, hc11, hc01, hc10] <;>
    ring_nf <;>
    first
    | ring
    | linear_combination (-(Complex.I * (starRingEnd ℂ) (uniformBoxPotential38 u s) *
        uniformBoxInteractionState38 u z s 0 0)) * hexp3
    | linear_combination (-(Complex.I * (starRingEnd ℂ) (uniformBoxPotential38 u s) *
        uniformBoxInteractionState38 u z s 0 1)) * hexp3
    | linear_combination (-(Complex.I * (starRingEnd ℂ) (uniformBoxPotential38 u s) *
        uniformBoxInteractionState38 u z s 0 0)) * hexp2
    | linear_combination (-(Complex.I * (starRingEnd ℂ) (uniformBoxPotential38 u s) *
        uniformBoxInteractionState38 u z s 0 1)) * hexp2

/-- The normalized half-trace defect in terms of `Φ(1)`. -/
theorem uniformBox_normalizedHalfTrace_eq38 (u : PhysicalL2) (z : ℂ) :
    Complex.exp (Complex.I * z) * actualPhysicalUnitHalfTrace32 u z -
        (1 + Complex.exp (2 * Complex.I * z)) / 2 =
      ((uniformBoxNormalizedState38 u z 1 0 0 - 1) +
        (uniformBoxNormalizedState38 u z 1 1 1 - Complex.exp (2 * Complex.I * z))) / 2 := by
  rw [actualPhysicalUnitHalfTrace_generalRescaling35]
  simp only [uniformBoxNormalizedState38, uniformBoxRowWeight38, uniformBoxInteractionState38]
  unfold uniformBoxPotential38
  simp only [Fin.isValue, if_true, one_ne_zero, if_false, Complex.ofReal_one]
  have h : Complex.exp (2 * 1 * Complex.I * z) = Complex.exp (2 * Complex.I * z) := by
    ring_nf
  rw [h]
  ring

end NlsGge.SpectralFoundations
end
