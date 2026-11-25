import Mathlib
import QuantumNLS.RB7Reg
import QuantumNLS.RB7Dir
import QuantumNLS.RB7Const
import QuantumNLS.RB7Zf
import QuantumNLS.RB7Exist
import QuantumNLS.RB7Uniq
import QuantumNLS.RB7HFlow

/-!
# R-7B122087 `thm:hierarchy`: uniqueness of the smooth Hamiltonian flow of `Re I_{r+1}` (RB7UniqF)

Printed: "For another smooth solution, ... All action moduli are therefore constant along that solution.  Its coordinate frequencies are the same constants, so each coordinate satisfies the same scalar linear
equation.  Injectivity proves uniqueness."

`coords_unique`: for ANY `HierarchyFlow.IsHamFlow` `Ψ'` of `hamiltonian L κ r` and smooth `u`, the chart coordinates of `Ψ'_t u` are `flow(t·1)(Φ u)`:
`RB7Const.moduli_const` (constant moduli, A9') and `RB7Const.coord_hasDerivAt` (coordinate ODE) feed `RB7Uniq.SeqData.unique_flow`.
`isHamFlow_eq`: hence `Ψ'_t u = physFlow (curveOf r) t u` (injectivity of `Φ`, `RB7H.eq_of_smoothL2_eq`), i.e. `Def024LowEquivariance.UniqueHamFlow`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology NNReal ContDiff
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.Reg015Setting QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.HierarchyFlow

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

theorem coords_unique (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (t : ℝ) (hs : SmoothPeriodic L (Ψ' t u)) :
    (fun n => C.Φ (smoothL2 hs) n) =
      (zflow hR C r _ le_rfl t (h02.ofMem (hinf_all hR C hu ((SOf r : ℝ≥0) : ℝ)))).val := by
  set S := sdata hR C r ((SOf r : ℝ≥0) : ℝ) le_rfl with hS
  have hsm : ∀ τ, SmoothPeriodic L (Ψ' τ u) := fun τ => ((hΨ u hu).2.2 τ).1
  let zS : h02 L ((SOf r : ℝ≥0) : ℝ) := h02.ofMem (hinf_all hR C hu ((SOf r : ℝ≥0) : ℝ))
  let y : ℝ → h02 L ((SOf r : ℝ≥0) : ℝ) := fun τ => h02.ofMem (hinf_smooth hR C (hsm τ) _ (NNReal.coe_nonneg _))
  obtain ⟨c, hcs, hcder⟩ := coord_hasDerivAt hR C r hΨ hu
  have hy0 : y 0 = zS := by
    apply WSeq.ext
    funext n
    show C.Φ (smoothL2 (hsm 0)) n = C.Φ (smoothL2 hu) n
    rw [smoothL2_congr (hΨ u hu).1 (hsm 0) hu]
  have hmod : ∀ τ j, ‖(y τ).val j‖ = ‖zS.val j‖ := by
    intro τ j
    have h := moduli_const hR C r hΨ hu j τ 0 (hsm τ) (hsm 0)
    have h0 : (zS.val j) = (y 0).val j := by rw [hy0]
    rw [h0]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  have hder : ∀ (j : ℤ) (τ : ℝ), HasDerivAt (fun τ => (y τ).val j)
      (-Complex.I * ∑ r', ((one1 r' : ℝ) : ℂ) * grad (fderiv ℝ (S.F r') (S.down r' (y τ))) j) τ := by
    intro j τ
    have h1 := hcder τ (hsm τ) j
    have e1 : (fun τ => (y τ).val j) = fun τ => (C.Φ (c τ) : ℤ → ℂ) j := by
      funext τ'
      show C.Φ (smoothL2 (hsm τ')) j = _
      rw [hcs τ' (hsm τ')]
    rw [e1]
    have e2 : (-Complex.I * ∑ r', ((one1 r' : ℝ) : ℂ) * grad (fderiv ℝ (S.F r') (S.down r' (y τ))) j) =
        -Complex.I * (Gcoord hR C r (hsm τ) : ℤ → ℂ) j := by
      simp only [Finset.univ_unique, Finset.sum_singleton, one1, Complex.ofReal_one, one_mul]
      congr 1
    rw [e2]
    exact h1
  have := SeqData.unique_flow S one1 zS y hy0 hmod hder t
  have e2 : (y t).val = fun n => C.Φ (smoothL2 hs) n := rfl
  rw [← e2, this]
  rfl

/-- **Uniqueness**: every smooth Hamiltonian flow of `Re I_{r+1}` is the chart flow. -/
theorem isHamFlow_eq (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    Ψ' s u = RB7H.physFlow (curveOf hR C r) s u := by
  have hs : SmoothPeriodic L (Ψ' s u) := ((hΨ u hu).2.2 s).1
  obtain ⟨hf, hfe⟩ := physFlow_slice hR C r hu s
  have h1 := coords_unique hR C r hΨ hu s hs
  have h2 : (fun n => C.Φ (smoothL2 hf) n) =
      (zflow hR C r _ le_rfl s (h02.ofMem (hinf_all hR C hu ((SOf r : ℝ≥0) : ℝ)))).val := by
    rw [hfe]
    funext n
    have := congrArg (fun z : lp (fun _ : ℤ => ℂ) 2 => (z : ℤ → ℂ) n) (Phi_curve hR C r u s)
    simp only at this
    rw [this, toBase_curve hR C r hu s]
    exact toBase_apply (L := L) _ (SOf r).2 _ n
  have h3 : C.Φ (smoothL2 hs) = C.Φ (smoothL2 hf) := lp.ext (h1.trans h2.symm)
  have h4 : smoothL2 hs = smoothL2 hf := by
    have := congrArg C.Ψ h3
    rwa [C.ΨΦ, C.ΨΦ] at this
  exact RB7H.eq_of_smoothL2_eq hs hf h4

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.coords_unique
#print axioms QuantumNLS.RB7.isHamFlow_eq
