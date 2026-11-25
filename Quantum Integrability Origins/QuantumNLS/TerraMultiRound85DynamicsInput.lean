import QuantumNLS.ActualGapR26
import QuantumNLS.L2Flow
import QuantumNLS.ActionTorus
import QuantumNLS.SobolevSpaces
import QuantumNLS.RootIndexedMasses
import QuantumNLS.StrongSymplectic

/-!
Statement interface for the as-yet unaccepted predecessor R-EF8C2837.
The source is physical_cubic.tex, theorem lines 28–89. No REF88 stage is
used as a substitute. This is a candidate transcription, not a proof of the
predecessor. In particular the H¹ actual-law clause is kept explicit.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ENNReal Topology BigOperators
open Filter MeasureTheory
namespace QuantumNLS.TerraMultiRound85DynamicsInput
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.L2Flow QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ActualGapDataR26 (Data)
open QuantumNLS.BornConvergence (TendstoInProbability)
open QuantumNLS.RootEnergyMomentLaws (law)
open QuantumNLS.BetheLabels (MArr)

abbrev K := lp (fun _ : ℤ => ℂ) 2
variable {L : ℝ} [Fact (0 < L)]

def seqToK {s : ℝ} (hs : 0 ≤ s) (w : h02 L s) : K :=
  toL2 (def002 L 0) (h02_mono L hs w)

def qEnergy (μ : Measure ℝ) : ℝ :=
  ∫ t, (QuantumNLS.QuantileTransport.qm μ t)^2 ∂QuantumNLS.QuantileForm.uI

def qT (D : QuantumNLS.BulkResponseForm.BulkResponseData)
    (W : QuantumNLS.BulkResponseForm.L2Unit) : ℝ :=
  2*qEnergy D.μ - 2*D.L*∫ t, QuantumNLS.QuantileTransport.qm D.μ t *
    (W : ℝ → ℝ) t ∂QuantumNLS.QuantileForm.uI

/-- Single intermediate input: full source statement, including quantum
normalization, zero coordinates, finite-action limits, the actual-law H¹
gap and all-order Sobolev and fixed-action torus clauses. The inverse is
chosen from the assumed strong symplectic diffeomorphism.
This declaration asserts nothing by itself. -/
def GlobalPhysicalDynamicsInput {κ : ℝ} (hκ : 0 < κ)
    (Φ : L2T L → K) (hΦ : QuantumNLS.StrongSymplectic.IsStronglySymplectic Φ) : Prop :=
  let Ψ := Classical.choose hΦ.exists_inverse
  ∃ ν : ℤ → QuantumNLS.ActionTorus.PosL1 → ℝ,
    (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n →
      Φ (flowMap hκ.le u t) n =
        Complex.exp (-Complex.I * ((t * ν n (QuantumNLS.RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ u n) ∧
    (∀ (u : L2T L) (t : ℝ) (n : ℤ), (QuantumNLS.RootIndexedMasses.masses hκ u).1 n = 0 →
      Φ (flowMap hκ.le u t) n = 0) ∧
    (∀ n : ℤ, ContinuousOn (ν n) {a : QuantumNLS.ActionTorus.PosL1 | 0 < a.1 n}) ∧
    (∀ (u : L2T L) (F : Finset ℤ), F.Nonempty →
      (∀ n, n ∈ F ↔ 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) →
      ∀ (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L), ‖v‖ = 1 →
      (∀ n, II hK v n = (QuantumNLS.RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) →
      Nonempty (Data hK v) ∧ ∀ D : Data hK v, ∀ n ∈ F,
      ν n (QuantumNLS.RootIndexedMasses.masses hκ u) =
        qEnergy (Mu hK v) + qT D.bd D.F + ∑ j ∈ F, II hK v j * D.omega n j) ∧
    (∀ (a : QuantumNLS.ActionTorus.PosL1) (n : ℤ), 0 < a.1 n →
      ∀ A : ℕ → QuantumNLS.ActionTorus.PosL1,
        (∀ j, ∃ F : Finset ℤ, ∀ k ∉ F, (A j).1 k = 0) →
        Tendsto A atTop (𝓝 a) → Tendsto (fun j => ν n (A j)) atTop (𝓝 (ν n a))) ∧
    (∀ (u : L2T L), QuantumNLS.ProductEnergyPreparation.OneH1 u → u ≠ 0 →
      ∀ (hK : 0 < κ * ‖u‖ ^ 2)
        (hv : ‖QuantumNLS.FullMass.unitDir u‖ = 1),
      ∃ D : Data hK (QuantumNLS.FullMass.unitDir u),
        ∀ a b : ℤ, a ≠ b → 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 a →
          0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 b →
          ν a (QuantumNLS.RootIndexedMasses.masses hκ u) -
            ν b (QuantumNLS.RootIndexedMasses.masses hκ u) = D.omega a b ∧
          ∀ default : ∀ N, MArr N → ℝ,
            TendstoInProbability (law hK (QuantumNLS.FullMass.unitDir u) hv)
              (fun _ => QuantumNLS.ActualGapR26.gapWithDefault L (κ * ‖u‖ ^ 2) a b default)
              (D.omega a b)) ∧
    (∀ (s : ℝ) (hs : 0 ≤ s), ∃ e : H02 L s ≃ₜ h02 L s,
      ∀ u : H02 L s, seqToK hs (e u) = Φ (H02.toL2 hs u)) ∧
    (∀ (s : ℝ) (hs : 0 ≤ s) (u : H02 L s) (t : ℝ),
      ∃ v : H02 L s, H02.toL2 hs v = flowMap hκ.le (H02.toL2 hs u) t) ∧
    (∀ a : QuantumNLS.ActionTorus.PosL1, ∀ z ∈ QuantumNLS.ActionTorus.actionTorus a,
      ∀ s t : ℝ,
        Φ (flowMap hκ.le (Ψ z) t) ∈ QuantumNLS.ActionTorus.actionTorus a ∧
        Φ (flowMap hκ.le (Ψ z) 0) = z ∧
        Φ (flowMap hκ.le (Ψ z) (s+t)) =
          Φ (flowMap hκ.le (Ψ (Φ (flowMap hκ.le (Ψ z) t))) s) ∧
        Continuous (fun t : ℝ => Φ (flowMap hκ.le (Ψ z) t)))

#print axioms GlobalPhysicalDynamicsInput
end QuantumNLS.TerraMultiRound85DynamicsInput
