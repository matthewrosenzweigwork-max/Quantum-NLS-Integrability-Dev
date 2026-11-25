import QuantumNLS.RB7HClauses45b
/-! integrator-authored trusted spec for R-7B122087 (terra_review r241 PASS): headline statement(s) copied verbatim from RB7HClauses45b (QuantumNLS.RB7HBridge). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section
open scoped ComplexConjugate Topology NNReal ContDiff
open Set Filter
namespace QuantumNLS.R7BSpec
open QuantumNLS.RB7HBridge
open QuantumNLS.RB7 QuantumNLS.RB7HSm2 QuantumNLS.Sobolev QuantumNLS.HierarchyFlow
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.PhysicalTensor
open MeasureTheory
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.Reg015Setting QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.HierarchyFlow QuantumNLS.LossSobolev QuantumNLS.Def024LowEquivariance
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem hierarchy_all_unconditional_spec (hκ : 0 < κ) (𝓡 : Finset ℕ) : HierarchyAll L κ hκ 𝓡 := by
  exact QuantumNLS.RB7HBridge.hierarchy_all_unconditional hκ 𝓡

theorem OrbitCompactInput_literal (L κ : ℝ) [Fact (0 < L)] (𝓡 : Finset ℕ) :
    QuantumNLS.RB7.OrbitCompactInput L κ 𝓡 ↔ (
  ∀ (F : HamFlows L κ 𝓡) (u : SmoothProf L),
    IsCompact (closure (Set.range fun t : ℕ → ℝ => (jetOf (jointClassicalFlow F t u.val) : ∀ k : ℕ, H02 L (k : ℝ))))) := Iff.rfl

theorem JointContInput_literal (L κ : ℝ) [Fact (0 < L)] (𝓡 : Finset ℕ) :
    QuantumNLS.RB7.JointContInput L κ 𝓡 ↔ (
  ∀ (F : HamFlows L κ 𝓡) (K : Set (SmoothProf L)) (B : Set (ℕ → ℝ)), IsCompact K → IsCompact B →
    ContinuousOn (fun p : (ℕ → ℝ) × SmoothProf L =>
      (jetOf (jointClassicalFlow F p.1 p.2.val) : ∀ k : ℕ, H02 L (k : ℝ))) (B ×ˢ K)) := Iff.rfl

theorem Clause1_literal (L κ : ℝ) [Fact (0 < L)] (𝓡 : Finset ℕ) :
    QuantumNLS.RB7.Clause1 L κ 𝓡 ↔ (
  (∀ r : ℕ, ∃ Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ), IsHamFlow L (hamiltonian L κ r) Φ ∧
    UniqueHamFlow L (hamiltonian L κ r) Φ ∧
    ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s a : ℝ, Φ s (Φ a u) = Φ (s + a) u) ∧
  (∃ F : HamFlows L κ 𝓡, ∀ r ∈ 𝓡, UniqueHamFlow L (hamiltonian L κ r) (F.Φ r)) ∧
  (∀ (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) (u : ℝ → ℂ), SmoothPeriodic L u →
    SmoothPeriodic L (jointClassicalFlow F t u))) := Iff.rfl

theorem Clause2_literal (L κ : ℝ) [Fact (0 < L)] (𝓡 : Finset ℕ) :
    QuantumNLS.RB7.Clause2 L κ 𝓡 ↔ (
  ∀ F : HamFlows L κ 𝓡,
    (∀ r ∈ 𝓡, ∀ r' ∈ 𝓡, ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s s' : ℝ,
      F.Φ r s (F.Φ r' s' u) = F.Φ r' s' (F.Φ r s u)) ∧
    (∀ (t : ℕ → ℝ) (l : List ℕ), l.Perm (𝓡.sort (· ≤ ·)) → ∀ u : ℝ → ℂ, SmoothPeriodic L u →
      ((l.map fun r => F.Φ r (t r)).foldr (· ∘ ·) id) u = jointClassicalFlow F t u)) := Iff.rfl

theorem Clause3_literal (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (𝓡 : Finset ℕ) :
    QuantumNLS.RB7.Clause3 L κ hκ 𝓡 ↔ (
  ∃ (C : ChartFacts (L := L) hκ) (Fr : ∀ r : ℕ, h02 L ((SOf r : ℝ≥0) : ℝ) → ℝ),
    (∀ r : ℕ, ContDiff ℝ 2 (Fr r) ∧ (∀ (c : ℤ → Circle) z, Fr r (rot c z) = Fr r z) ∧
      ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (z : h02 L ((SOf r : ℝ≥0) : ℝ)),
        z.val = (fun n => C.Φ (smoothL2 hf) n) → Fr r z = (charge L κ f (r + 1)).re) ∧
    (∀ (r : ℕ) (Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)), IsHamFlow L (hamiltonian L κ r) Ψ' →
      ∀ (u : ℝ → ℂ) (hu : SmoothPeriodic L u) (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)) (n : ℤ),
        (C.Φ (smoothL2 hs) : ℤ → ℂ) n =
          Complex.exp (((-(s * FreqSeq ((SOf r : ℝ≥0) : ℝ) (Fr r) (fun m => C.Φ (smoothL2 hu) m) n) : ℝ) : ℂ) *
            Complex.I) * (C.Φ (smoothL2 hu) : ℤ → ℂ) n ∧
        ‖(C.Φ (smoothL2 hs) : ℤ → ℂ) n‖ = ‖(C.Φ (smoothL2 hu) : ℤ → ℂ) n‖ ∧
        ∀ r' : ℕ, FreqSeq ((SOf r' : ℝ≥0) : ℝ) (Fr r') (fun m => C.Φ (smoothL2 hs) m) n =
          FreqSeq ((SOf r' : ℝ≥0) : ℝ) (Fr r') (fun m => C.Φ (smoothL2 hu) m) n) ∧
    (∀ (r' : ℕ) {u v : ℝ → ℂ} (hu : SmoothPeriodic L u) (hv : SmoothPeriodic L v) (c : ℤ → Circle),
      (∀ n, (C.Φ (smoothL2 hv) : ℤ → ℂ) n = (c n : ℂ) * (C.Φ (smoothL2 hu) : ℤ → ℂ) n) →
      ∀ n, FreqSeq ((SOf r' : ℝ≥0) : ℝ) (Fr r') (fun m => C.Φ (smoothL2 hv) m) n =
        FreqSeq ((SOf r' : ℝ≥0) : ℝ) (Fr r') (fun m => C.Φ (smoothL2 hu) m) n) ∧
    (∀ (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) (u : ℝ → ℂ) (hu : SmoothPeriodic L u)
      (hj : SmoothPeriodic L (jointClassicalFlow F t u)) (n : ℤ),
        (C.Φ (smoothL2 hj) : ℤ → ℂ) n =
          Complex.exp (((-(∑ r ∈ 𝓡, t r * FreqSeq ((SOf r : ℝ≥0) : ℝ) (Fr r)
            (fun m => C.Φ (smoothL2 hu) m) n) : ℝ) : ℂ) * Complex.I) * (C.Φ (smoothL2 hu) : ℤ → ℂ) n)) := Iff.rfl

theorem Clause6_literal (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (𝓡 : Finset ℕ) :
    QuantumNLS.RB7.Clause6 L κ hκ 𝓡 ↔ (
  (∀ (r : ℕ) (Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)), IsHamFlow L (hamiltonian L κ r) Ψ' →
    ∀ (u : ℝ → ℂ) (hu : SmoothPeriodic L u) (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)),
      (∀ j : ℕ, charge L κ (Ψ' s u) j = charge L κ u j) ∧
      ∀ n : ℤ, (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hs)).1 n =
        (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hu)).1 n) ∧
  (∀ (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) (u : ℝ → ℂ) (hu : SmoothPeriodic L u)
    (hj : SmoothPeriodic L (jointClassicalFlow F t u)),
      (∀ j : ℕ, charge L κ (jointClassicalFlow F t u) j = charge L κ u j) ∧
      ∀ n : ℤ, (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hj)).1 n =
        (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hu)).1 n)) := Iff.rfl

theorem HierarchyAll_literal (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (𝓡 : Finset ℕ) :
    QuantumNLS.RB7.HierarchyAll L κ hκ 𝓡 ↔ (
  Clause1 L κ 𝓡 ∧ Clause2 L κ 𝓡 ∧ Clause3 L κ hκ 𝓡 ∧ OrbitCompactInput L κ 𝓡 ∧ JointContInput L κ 𝓡 ∧
    Clause6 L κ hκ 𝓡) := Iff.rfl

end QuantumNLS.R7BSpec
#print axioms QuantumNLS.R7BSpec.hierarchy_all_unconditional_spec
