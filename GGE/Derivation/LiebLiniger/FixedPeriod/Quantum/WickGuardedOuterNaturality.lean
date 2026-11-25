import LiebLiniger.FixedPeriod.Quantum.WickGuardedDerivativePairing

/-! Equality-only naturality of the actual guarded derivative contraction at
arbitrary outer input and output degrees. This extends the same private cast
argument already used in WickGuardedDerivativePairing; it assumes no Wick
product, mixed-factor identity or physical source theorem. SOURCE ONLY. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

private theorem outer_sectorCast_self_clm (n : ℕ) (h : n = n) :
    (symmetricSectorCast μ h).toLinearIsometry.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (SymmetricSector μ n) := by
  cases Subsingleton.elim h rfl
  rfl

private theorem outer_cast_polarized {a b c d : ℕ}
    (hin : a = b) (hout : c = d)
    (T : SymmetricSector μ b →L[ℂ] SymmetricSector μ c) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ
      ((symmetricSectorCast μ hout).toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        (symmetricSectorCast μ hin).toLinearIsometry.toContinuousLinearMap) v u =
      wickKernelPolarized μ T v u := by
  subst b
  subst d
  rfl

/-- Transport the same actual two input kernels across equality-only degree
casts. Both outer degrees are arbitrary and no source kernel is replaced. -/
private theorem outer_tensorContraction_cast {a R j b S q k : ℕ}
    (hr : R = a) (hs : S = b)
    (A : SymmetricSector μ (a + j) →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ k →L[ℂ] SymmetricSector μ (j + b)) :
    tensorDerivativeContraction (j := j) μ
        (A ∘L (symmetricSectorCast μ (congrArg (fun n => n + j) hr)).toLinearIsometry.toContinuousLinearMap)
        ((symmetricSectorCast μ (congrArg (fun n => j + n) hs.symm)).toLinearIsometry.toContinuousLinearMap ∘L B) =
      (symmetricSectorCast μ (congrArg (fun n => q + n) hs.symm)).toLinearIsometry.toContinuousLinearMap ∘L
        tensorDerivativeContraction (j := j) μ A B ∘L
        (symmetricSectorCast μ (congrArg (fun n => n + k) hr)).toLinearIsometry.toContinuousLinearMap := by
  cases hr
  cases hs
  simp only [outer_sectorCast_self_clm, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_id]

/-- The original-degree guarded source contraction has the same pure pairing
as its tensor contraction whenever the actual input/output degrees are
presented as a+j and j+b. All input/output sector degrees are retained. -/
theorem sourceDerivativeContractionKernel_available_outer_naturality
    (a j b q k : ℕ)
    (A : SymmetricSector μ (a + j) →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ k →L[ℂ] SymmetricSector μ (j + b))
    (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (sourceDerivativeContractionKernel μ A B j) v u =
      wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A B) v u := by
  have hj : j ≤ min (a + j) (j + b) := by omega
  let R : ℕ := (a + j) - j
  let S : ℕ := (j + b) - j
  have hr : R = a := by dsimp [R]; omega
  have hs : S = b := by dsimp [S]; omega
  rw [sourceDerivativeContractionKernel_available μ A B j hj]
  rw [outer_cast_polarized]
  change wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ
    (A ∘L (symmetricSectorCast μ (congrArg (fun n => n + j) hr)).toLinearIsometry.toContinuousLinearMap)
    ((symmetricSectorCast μ (congrArg (fun n => j + n) hs.symm)).toLinearIsometry.toContinuousLinearMap ∘L B)) v u = _
  calc
    _ = wickKernelPolarized μ
        ((symmetricSectorCast μ (congrArg (fun n => q + n) hs.symm)).toLinearIsometry.toContinuousLinearMap ∘L
          tensorDerivativeContraction (j := j) μ A B ∘L
          (symmetricSectorCast μ (congrArg (fun n => n + k) hr)).toLinearIsometry.toContinuousLinearMap) v u :=
      congrArg (fun T : SymmetricSector μ (R + k) →L[ℂ] SymmetricSector μ (q + S) =>
        wickKernelPolarized μ T v u) (outer_tensorContraction_cast μ hr hs A B)
    _ = wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A B) v u :=
      outer_cast_polarized μ (congrArg (fun n => n + k) hr)
        (congrArg (fun n => q + n) hs.symm) _ v u

end LiebLiniger.FixedPeriod.Quantum
end
