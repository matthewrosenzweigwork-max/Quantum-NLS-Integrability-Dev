import QuantumNLS.R52CFMain
/-! integrator-authored trusted spec for R-52CF5DA1 prop:audit-finite-count-propagation (terra_review r221 PASS): headline statement(s) copied verbatim from R52CFMain (QuantumNLS.R52CFMain). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
open Set Filter Topology
namespace QuantumNLS.R52CSpec
open QuantumNLS.R52CFMain
open PhysicalTensor (L2T)
open RootMassInvolutionR8 (mass)
open QuantumNLS.ProductTorusGenerator (Linf)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.RF535Final (Tθ GlobalStatement)
open TensorCarrier TraceClass
variable (L : ℝ) [Fact (0 < L)] {κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem finite_count_propagation_spec (hκ : 0 < κ) (F : Finset ℤ) (R : ℝ) (k : ℕ) (α β : ℤ → ℝ) :
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N) (hk : k ≤ N), N₀ ≤ N →
      ∀ u ∈ R52CFCompact.profileClass L R, ∀ t : Linf, (∀ n ∉ F, t n = 0) →
        (∀ n ∈ F, α n ≤ t n ∧ t n ≤ β n) →
        traceNorm (PhysicalTensor.reducedDensityN N k hk
            (R52CFEvol.countEvol L hκ hN F t (HighMomentsOps.wvec N u) : HilbertTensorPower ℂ (L2T L) N) -
          Prop001.coherentProjector k (Tθ (L := L) hκ t u)) ≤ ENNReal.ofReal ε) ∧
    (∀ n : ℤ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ u ∈ R52CFCompact.profileClass L R,
        ‖(Prop010ContourBindingR11.B L hκ hN n - ((mass hκ n u : ℝ) : ℂ) •
          (1 : BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N))
          (HighMomentsOps.wvec N u)‖ ≤ ε) := by
  exact QuantumNLS.R52CFMain.finite_count_propagation L hκ F R k α β

set_option maxHeartbeats 8000000 in
theorem target_eq_chart_spec (hκ : 0 < κ) :
    ∃ (Φ : L2T L → K) (Ψ : K → L2T L), (∀ u, Ψ (Φ u) = u) ∧ (∀ z, Φ (Ψ z) = z) ∧
      (∀ u n, ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n) ∧ (∀ u, ‖Φ u‖ ^ 2 = ‖u‖ ^ 2) ∧
      ∀ (t : Linf) (u : L2T L),
        (∃ z : K, ∀ n, z n = Complex.exp (-(t n : ℂ) * Complex.I) * Φ u n) ∧
        ∀ z : K, (∀ n, z n = Complex.exp (-(t n : ℂ) * Complex.I) * Φ u n) → Tθ (L := L) hκ t u = Ψ z := by
  exact QuantumNLS.R52CFMain.target_eq_chart L hκ

end QuantumNLS.R52CSpec
#print axioms QuantumNLS.R52CSpec.finite_count_propagation_spec
#print axioms QuantumNLS.R52CSpec.target_eq_chart_spec
