import QuantumNLS.Local014Interval
/-! integrator-authored trusted spec for LOCAL-014 reset:analytic-egorov (review record r35 FULL ACCEPT; interval formulation): headline statement(s) copied verbatim from Local014Interval (QuantumNLS.Local014Interval). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators ENNReal Nat ComplexOrder
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.TraceClass QuantumNLS.Ext025B11TracePairing
  QuantumNLS.Ext025A12Trace QuantumNLS.Ext025A12Normal QuantumNLS.KernelDefinition
  QuantumNLS.KernelConvergence QuantumNLS.SymplecticBracket QuantumNLS.Local014Dyson
  QuantumNLS.Local014Heisenberg QuantumNLS.Local014IteratedSymbol
  QuantumNLS.Local014ClassicalSeries QuantumNLS.Local014RealSymbol QuantumNLS.Local014OneBody
  QuantumNLS.Local014StateLimits QuantumNLS.Local014ShortTime QuantumNLS.Local014Main
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.L014Spec
open QuantumNLS.Local014Interval
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 8000000 in
theorem local014_analytic_egorov_interval_spec {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (HN : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (hsa : ∀ N, IsSelfAdjoint (HN N))
    (hexp : ∀ N, RadiusBound.IsExpansion (HN N) (Hk N)) (hH : ConvergesOnRadius 8 Hk Hlim)
    (F : H → ℝ) (hFd : ∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ F u)
    (hF : ∀ u : H, ‖u‖ = 1 → (F u : ℂ) = symbol Hlim u)
    {v : H} (hv : ‖v‖ = 1) {I : Set ℝ} (hI : I.OrdConnected) (hI0 : (0 : ℝ) ∈ I)
    {phi : ℝ → H} (hphi0 : phi 0 = v)
    (hphi : ∀ s ∈ I, HasDerivWithinAt phi (hamField F (phi s)) I s)
    (hn : ∀ s ∈ I, ‖phi s‖ = 1)
    (ρ : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (hρ : ∀ N, IsNormalState (ρ N))
    (hcond : Tendsto (fun N => traceNorm (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v))
      atTop (𝓝 0)) :
    ((∀ u : H, ‖u‖ = 1 → (symbol Hlim u).im = 0) ∧
      (∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ (hReal Hlim) u ∧
        ((hReal Hlim u : ℝ) : ℂ) = symbol Hlim u)) ∧
    (∀ t ∈ I, ∀ (q : ℕ) (B : BoundedSymmetricKernel H q),
      Tendsto (fun N => if h : q ≤ N then
          tr (ρ N * (opExp ((Complex.I * (t : ℂ) * (N : ℂ)) • HN N) * RadiusBound.Q N q h B *
            opExp (-((Complex.I * (t : ℂ) * (N : ℂ)) • HN N)))) else 0) atTop
        (𝓝 (kernelProductSymbol B (phi t)))) ∧
    (∀ t ∈ I, Tendsto (fun N => traceNorm (oneBody N (evolve N (HN N) (ρ N) t) -
        InnerProductSpace.rankOne ℂ (phi t) (phi t))) atTop (𝓝 0)) := by
  exact QuantumNLS.Local014Interval.local014_analytic_egorov_interval HN hsa hexp hH F hFd hF hv hI hI0 hphi0 hphi hn ρ hρ hcond

end QuantumNLS.L014Spec
#print axioms QuantumNLS.L014Spec.local014_analytic_egorov_interval_spec
