import QuantumNLS.HaarNonlinearTail
/-! integrator-authored trusted spec for R-9C3CC17D QG:lem:haar-nonlinear-tail (Terra r150 ACCEPT):
headline copied verbatim from NT4 HaarNonlinearTail 8fad7820, with rfl defining equations of the free
root aF, F_w, the operators X_{N,n}(w), the energy mask, and the R_{N,I} eigenvalue rEig. -/
set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set
open scoped InnerProductSpace ComplexConjugate
namespace R9C3Spec
open QuantumNLS.HaarFreeTaylor QuantumNLS.HaarNonlinearAbstract QuantumNLS.HaarSpectralTail
  QuantumNLS.OffgridBessel QuantumNLS.HaarKernelFactorizationSym QuantumNLS.PeriodReconstruction
  QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.NormalizedTransfer
  QuantumNLS.KernelDefinition QuantumNLS.PeriodTwoTerm QuantumNLS.HaarNonlinearTail QuantumNLS

set_option maxHeartbeats 40000000 in
theorem haar_nonlinear_tail_spec (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : 0 < E)
    {k : ℕ} (hk : 1 ≤ k) :
    -- the free expansion `QG:eq:haar-free-taylor`
    (∃ σ M : ℝ, 0 < σ ∧ 0 ≤ M ∧ ∀ w ∈ Gamma0 L,
      DifferentiableOn ℂ (FW L w) (Metric.closedBall 0 σ) ∧
      ∃ f : ℕ → ℂ, f 0 = 0 ∧ f 1 = 1 / (1 - ew L w) ∧ (∀ d, ‖f d‖ ≤ M * σ⁻¹ ^ d) ∧
        ∀ X, ‖X‖ < σ → HasSum (fun d => f d * X ^ d) (FW L w X)) ∧
    ∃ R₀ CE : ℝ, 2 ≤ R₀ ∧ 0 ≤ CE ∧ ∀ (N : ℕ) (hkN : k ≤ N)
      (P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N),
      (∀ m, P (bas L hκ (hk.trans hkN) m) = mask L κ N E m • bas L hκ (hk.trans hkN) m) →
      -- `QG:eq:haar-small-spectral-tail`
      (∀ n : ℤ, R₀ < |(n : ℝ)| → ∀ w ∈ Gamma0 L, ∀ φ,
        ‖(Xop L κ N w n * P) φ‖ ≤ CE / |(n : ℝ)| * ‖φ‖) ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ I : Finset ℤ, (∀ n ∈ I, R < |(n : ℝ)|) → ∀ t : ℤ → ℝ,
        (∀ n, |t n| ≤ 1) →
        -- `R_{N,I}` exists by its joint spectral calculus
        (∃ RN : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
          ∀ m, RN (bas L hκ (hk.trans hkN) m) =
            rEig L hκ (hk.trans hkN) E I t m • bas L hκ (hk.trans hkN) m) ∧
        ∀ RN : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
          (∀ m, RN (bas L hκ (hk.trans hkN) m) =
            rEig L hκ (hk.trans hkN) E I t m • bas L hκ (hk.trans hkN) m) →
        ∀ (J : BoundedSymmetricKernel (L2T L) k) (ψ : SymSector ℂ (L2T L) N), P ψ = ψ → ‖ψ‖ = 1 →
          -- `QG:eq:haar-nonlinear-commutator`
          ‖⟪ψ, (RN * genericU_N_r N k hkN J - genericU_N_r N k hkN J * RN) ψ⟫_ℂ‖ ≤
            CE * ‖J‖ / Real.sqrt R ∧
          -- with `J_N` compressed by `P_{N,E}`
          ‖⟪ψ, (RN * (P * genericU_N_r N k hkN J * P) -
            (P * genericU_N_r N k hkN J * P) * RN) ψ⟫_ℂ‖ ≤ CE * ‖J‖ / Real.sqrt R ∧
          -- after conjugating the compression by a unitary commuting with the transfers and `P_{N,E}`
          ∀ V : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
            ContinuousLinearMap.adjoint V * V = 1 → V * ContinuousLinearMap.adjoint V = 1 →
            (∀ z, V * normalizedTransfer L κ N z = normalizedTransfer L κ N z * V) → V * P = P * V →
            ‖⟪ψ, (RN * (V * (P * genericU_N_r N k hkN J * P) * ContinuousLinearMap.adjoint V) -
              (V * (P * genericU_N_r N k hkN J * P) * ContinuousLinearMap.adjoint V) * RN) ψ⟫_ℂ‖ ≤
              CE * ‖J‖ / Real.sqrt R :=
  QuantumNLS.HaarNonlinearTail.haar_nonlinear_tail L hκ hE hk

theorem ew_def (L : ℝ) (w : ℂ) : ew L w = exp (I * L * w) := rfl
theorem uF_def (L : ℝ) (w X : ℂ) : uF L w X = (2 * (1 + ew L w) * X + X ^ 2) / (1 - ew L w) ^ 2 := rfl
theorem aF_def (L : ℝ) (w X : ℂ) : aF L w X =
  (1 + ew L w + X + (1 - ew L w) * (1 + uF L w X) ^ ((2 : ℂ)⁻¹)) / 2 := rfl
theorem FW_def (L : ℝ) (w X : ℂ) : FW L w X = log (aF L w X) := rfl
theorem Xop_def (L : ℝ) [Fact (0 < L)] (κ : ℝ) (N : ℕ) (w : ℂ) (n : ℤ) : Xop L κ N w n =
  normalizedTransfer L κ N (OffgridCommutator.zpt L w n) -
    (1 + ew L w) • (1 : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) := rfl
theorem adm_def (L : ℝ) [Fact (0 < L)] (κ : ℝ) (N : ℕ) (E : ℝ) : adm L κ N E =
  {m | EnergyProjection.energyEig L κ N (NormalityBridge.label m) ≤ N * E} := rfl
theorem Gfun_def (L : ℝ) (w y : ℂ) : Gfun L w y = FW L w y - y / (1 - ew L w) := rfl
theorem xEig_def (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (n : ℤ) (w : ℂ)
    (m : BetheLabels.MArr N) : xEig L hκ hN n w m =
  NormalityBridge.eigen (L := L) κ hκ hN m (OffgridCommutator.zpt L w n) - (1 + ew L w) := rfl
open Classical in
theorem rEig_def (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (E : ℝ) (I : Finset ℤ)
    (t : ℤ → ℝ) (m : BetheLabels.MArr N) : rEig L hκ hN E I t m =
  if m ∈ adm L κ N E then
    ((-(N / (2 * Real.pi * κ)) * (QuantumNLS.LabelExactPeriod.rectIntegral
      (fun w => ∑ n ∈ I, (t n : ℂ) * Gfun L w (xEig L hκ hN n w m))
        (-(omegaL L / 4)) (omegaL L / 4) (omegaL L / 4)).re : ℝ) : ℂ)
  else 0 := rfl
end R9C3Spec
#print axioms R9C3Spec.haar_nonlinear_tail_spec
