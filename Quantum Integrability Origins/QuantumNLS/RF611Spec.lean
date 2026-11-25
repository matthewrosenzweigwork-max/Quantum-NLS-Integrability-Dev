import QuantumNLS.HaarEigenbasis
/-! integrator-authored trusted spec for R-F611926F QG:prop:haar-kernel-factorization (QUANTUM_GAUGE_COMPONENTS.tex:293),
statements copied verbatim from the frozen HKF1/HKF2 theorems (Terra r130 ACCEPT on statement and argument):
exact factorization of the ACTUAL DEF-048 transfer kernel K_{r,z} on Sym^r as (1−q)/r!·S R_z^{⊗r} S (q = (−1)^{r−1}e^{izL} ≠ 1);
R_z^ρ = (D_ρ − iz)^{-1} on the twisted-boundary H¹ domain (R1); common z-independent orthonormal eigenbasis with eigenvalues
(1−q)/r!·∏ i/(z−ω(k_j+δ_r)) (R3); left side entire, right side's singularities removable, eigen-equation at every z (R2). -/
namespace RF611Spec
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators ComplexConjugate
open QuantumNLS QuantumNLS.BetheIntegralOperator QuantumNLS.PhysicalTensor QuantumNLS.HaarKernelFactorization
  QuantumNLS.HaarKernelFactorizationOp QuantumNLS.HaarResolvent QuantumNLS.HaarTwisted
  QuantumNLS.HaarKernelFactorizationSym QuantumNLS.HaarSlaterDensity QuantumNLS.HaarSlater
  QuantumNLS.HaarSlaterBasis QuantumNLS.BetheCompressedKernel QuantumNLS.KernelDefinition
  QuantumNLS.TensorCarrier QuantumNLS.BethePhysicalTransfer QuantumNLS.BetheWeakGradient QuantumNLS.HaarEigenbasis

theorem graphD_def (L : ℝ) [Fact (0 < L)] (ρ z : ℂ) (p : L2T L × L2T L) : p ∈ graphD L ρ z ↔
    ∃ (g h : ℝ → ℂ), ((∀ᵐ x ∂(volume : Measure (AddCircle L)), p.1 x = g (rep1 L x)) ∧
      MemLp h 2 (volume.restrict (Set.Ioc 0 L)) ∧ ∀ x ∈ Set.Icc 0 L, g x = g 0 + ∫ s in (0 : ℝ)..x, h s) ∧
      g L = ρ * g 0 ∧
      ∀ᵐ x ∂(volume : Measure (AddCircle L)), p.2 x = h (rep1 L x) - Complex.I * z * g (rep1 L x) := Iff.rfl

theorem qOf_def (L : ℝ) [Fact (0 < L)] (ρ z : ℂ) : qOf L ρ z = ρ * Complex.exp (Complex.I * z * L) := rfl

theorem physicalKernel_factorization_spec (L : ℝ) [Fact (0 < L)] (n : ℕ) (z : ℂ)
    (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1)
    (w : SymSector ℂ (L2T L) (n + 1)) :
    physUnitary ((physicalKernel L (n + 1) z w : SymSector ℂ (L2T L) (n + 1)) :
        HilbertTensorPower ℂ (L2T L) (n + 1)) =
      ((1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) / ((n + 1).factorial : ℂ)) •
        Sop L (n + 1) ((Rtens L (n + 1) ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z).operator
          (Sop L (n + 1) (physUnitary (w : HilbertTensorPower ℂ (L2T L) (n + 1)))))  := by
  apply QuantumNLS.HaarKernelFactorizationSym.physicalKernel_factorization <;> assumption

theorem resolvent_range_spec (L : ℝ) [Fact (0 < L)] {ρ z : ℂ} (hρ : ρ * ρ = 1) (hq : qOf L ρ z ≠ 1) (φ : L2T L) :
    (R1 L (qOf L ρ z) z φ, φ) ∈ graphD L ρ z  := by
  apply QuantumNLS.HaarResolvent.resolvent_range <;> assumption

theorem resolvent_left_inverse_spec (L : ℝ) [Fact (0 < L)] {ρ z : ℂ} (hρ : ρ * ρ = 1) (hq : qOf L ρ z ≠ 1) {f ψ : L2T L}
    (hfψ : (f, ψ) ∈ graphD L ρ z) : R1 L (qOf L ρ z) z ψ = f  := by
  apply QuantumNLS.HaarResolvent.resolvent_left_inverse <;> assumption

theorem physicalKernel_eigen_spec (L : ℝ) [Fact (0 < L)] (n : ℕ) (z : ℂ)
    (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1) (k : Idx (n + 1)) :
    physicalKernel L (n + 1) z (physBasis L n k) = Lam L n z k.1 • physBasis L n k  := by
  apply QuantumNLS.HaarEigenbasis.physicalKernel_eigen <;> assumption

set_option synthInstance.maxHeartbeats 400000 in
theorem entire_physicalKernel_spec (L : ℝ) [Fact (0 < L)] (n : ℕ) :
    Differentiable ℂ (fun z : ℂ => physicalKernel L (n + 1) z)  := by
  apply QuantumNLS.HaarEigenbasis.entire_physicalKernel <;> assumption

theorem removable_singularity_spec (L : ℝ) [Fact (0 < L)] (n : ℕ) (z0 : ℂ) (w : SymSector ℂ (L2T L) (n + 1)) :
    Tendsto (fun z : ℂ =>
      ((1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) / ((n + 1).factorial : ℂ)) •
        Sop L (n + 1) ((Rtens L (n + 1) ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z).operator
          (Sop L (n + 1) (physUnitary (L := L) (w : HilbertTensorPower ℂ (L2T L) (n + 1))))))
      (𝓝[≠] z0)
      (𝓝 (physUnitary (L := L) ((physicalKernel L (n + 1) z0 w : SymSector ℂ (L2T L) (n + 1)) :
        HilbertTensorPower ℂ (L2T L) (n + 1))))  := by
  apply QuantumNLS.HaarEigenbasis.removable_singularity <;> assumption

theorem eigen_all_spec (L : ℝ) [Fact (0 < L)] (n : ℕ) (z0 : ℂ) (k : Idx (n + 1)) :
    physicalKernel L (n + 1) z0 (physBasis L n k) = lamTilde L n k z0 • physBasis L n k  := by
  apply QuantumNLS.HaarEigenbasis.eigen_all <;> assumption

end RF611Spec
#print axioms RF611Spec.physicalKernel_factorization_spec
#print axioms RF611Spec.resolvent_range_spec
#print axioms RF611Spec.resolvent_left_inverse_spec
#print axioms RF611Spec.physicalKernel_eigen_spec
#print axioms RF611Spec.entire_physicalKernel_spec
#print axioms RF611Spec.removable_singularity_spec
#print axioms RF611Spec.eigen_all_spec
