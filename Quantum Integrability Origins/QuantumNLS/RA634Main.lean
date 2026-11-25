import Mathlib
import QuantumNLS.RootNlsInvariance
import QuantumNLS.F04Global

/-!
# R-A634027E `F04:cor-spectral` (F04.tex:352-367)

"Assume `κ > 0` and the spectral constructions and conclusions of Theorem thm:root-nls-invariance.
For every `u₀ ∈ H¹`, the quantum-derived discriminant, full-mass spectral measure, and each indexed
spectral mass of the global solution of (F04:eq-nls) are independent of time."

The global solution is the accepted R-169AABCC flow `umax (le_refl 1) κ u₀ : ℝ → h04 L 1`
(`F04Global.thm_global`: mild on ℝ, `C(ℝ;H¹) ∩ C¹(ℝ;H⁻¹)`, unique). The spectral objects are those
of the accepted R-BFCC01E8 (`RootNlsInvariance.SpectralDataConstant`): `L2SpatialTransfer.discriminant`,
the quantum product symbol, `FullMass.Mmeas`, `(RootIndexedMasses.masses hκ ·).1 n`, evaluated at
the `L²` vector `physical (m10 (u(t)))`.

Proof (source): on each `[-T,T]`, (F04:eq-approximation) supplies the regular solutions
`u_N = umax hs3 κ (P_N u₀) ∈ C(ℝ;H³) ∩ C¹(ℝ;H¹)` (R-3F6AA186 `lem_regular`, with the equation in `H¹`)
and their uniform `H¹` convergence (R-169AABCC); the second assertion of R-BFCC01E8 applies; `T` is
arbitrary.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull
  QuantumNLS.F04Regularity QuantumNLS.RootEnergyVariation

namespace QuantumNLS.RA634Main
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RootNlsInvariance

variable {L : ℝ} [Fact (0 < L)]

/-- The `H¹` time derivative of the regular solution from `H³` data. -/
def vel (κ : ℝ) (b : h04 L 3) (t : ℝ) : h04 L 1 := mL1 (Gder hs3 κ (umax hs3 κ b t))

/-- Every regular solution of R-3F6AA186 is a regular solution in the sense of R-BFCC01E8. -/
theorem regular_of_H3 {κ : ℝ} (hκ : 0 ≤ κ) (b : h04 L 3) (T : ℝ) :
    IsRegularNLSSolution κ T (umax hs3 κ b) (vel κ b) := by
  obtain ⟨_, _, hc, hcd, hd, _⟩ := lem_regular hκ b
  have hdv : deriv (fun t => m31 (umax hs3 κ b t)) = vel κ b := funext fun t => (hd t).deriv
  have hvc : Continuous (vel κ b) := by
    rw [← hdv]; exact hcd.continuous_deriv le_rfl
  refine ⟨hc.continuousOn, hvc.continuousOn, fun t _ => (hd t).hasDerivWithinAt, fun t _ => ?_⟩
  have he := I_smul_w κ (umax hs3 κ b t)
  have hl : m10 (mL1 (lapOp 3 (umax hs3 κ b t))) = lap (RootNlsInvDisc.m32 (umax hs3 κ b t)) := by
    rw [RootNlsInvDisc.lap_m32]
    apply WSeq.ext
    funext n
    change ((QuantumNLS.Fourier.freq L n ^ 2 : ℝ) : ℂ) * (umax hs3 κ b t).val n =
      -((Complex.I * (QuantumNLS.Fourier.freq L n : ℂ)) ^ 2 * (umax hs3 κ b t).val n)
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have h2 := congrArg (fun x : h04 L 1 => physical (m10 x)) he
  simp only [map_smul, map_add] at h2
  unfold vel uxx cub
  rw [h2, hl, neg_neg]

/-- **R-A634027E `F04:cor-spectral`.** -/
theorem F04_cor_spectral {κ : ℝ} (hκ : 0 < κ) (u0 : h04 L 1) :
    ∀ t s : ℝ,
      (∀ z : ℂ,
        L2SpatialTransfer.discriminant κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 t))) z =
          L2SpatialTransfer.discriminant κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 s))) z) ∧
      (∀ z : ℂ,
        NormalizedTransfer.productSymbol L κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 t))) z =
          NormalizedTransfer.productSymbol L κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 s))) z) ∧
      FullMass.Mmeas κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 t))) =
        FullMass.Mmeas κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 s))) ∧
      ∀ n : ℤ,
        (RootIndexedMasses.masses hκ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 t)))).1 n =
          (RootIndexedMasses.masses hκ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 s)))).1 n := by
  intro t s
  set T : ℝ := |t| + |s| with hT
  have ht : t ∈ Icc (-T) T := ⟨by linarith [neg_abs_le t, abs_nonneg s],
    by linarith [le_abs_self t, abs_nonneg s]⟩
  have hs : s ∈ Icc (-T) T := ⟨by linarith [neg_abs_le s, abs_nonneg t],
    by linarith [le_abs_self s, abs_nonneg t]⟩
  have hg := F04Global.thm_global hκ.le u0
  have hw : Continuous (umax (le_refl (1 : ℝ)) κ u0) := hg.2.1
  have hconv := hg.2.2.2.2.2.2.2.2.2.2.2.1 T
  exact (root_nls_invariance hκ T).2 (umax (le_refl (1 : ℝ)) κ u0)
    (fun N => umax hs3 κ (F04Global.PN N u0)) (fun N => vel κ (F04Global.PN N u0))
    hw.continuousOn (fun N => regular_of_H3 hκ.le (F04Global.PN N u0) T) hconv t ht s hs

end QuantumNLS.RA634Main

#print axioms QuantumNLS.RA634Main.regular_of_H3
#print axioms QuantumNLS.RA634Main.F04_cor_spectral
