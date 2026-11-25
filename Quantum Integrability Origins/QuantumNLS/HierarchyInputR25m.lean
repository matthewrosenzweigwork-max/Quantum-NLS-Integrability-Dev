import QuantumNLS.Def033HierarchyR24m
import QuantumNLS.Reg015Setting
import QuantumNLS.RootScalarUniquenessR28
import QuantumNLS.R275Unconditional

/-! Statement interface only for R-7B122087 (thm:hierarchy).
No hierarchy flow theorem is proved here. The single Input below is the
printed conditional theorem, with its chart, Sobolev, scalar-uniqueness,
and scalar-moment antecedents explicit. The chart is the new exact-action
canonical chart in the accepted PrintedChart convention. Full orbits are
specified for every fixed finite family, with no growing-order uniformity.
The R24m candidate recorded only the conclusion at ambient antecedents;
we do not identify that candidate with this complete printed statement.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
namespace QuantumNLS.HierarchyInputR25m
open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow
open QuantumNLS.Def033HierarchyR24m
open QuantumNLS.Def024LowEquivariance QuantumNLS.Def033CoreR24m
variable {L κ : ℝ} [Fact (0 < L)]

/-- Sobolev restrictions of the same global chart, at every fixed real order.
Both sides have their established Sobolev norm topology. -/
def SobolevHomeomorphisms
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K) : Prop :=
  ∀ s : ℝ, 0 ≤ s →
    ∃ F : QuantumNLS.Sobolev.H02 L s ≃ₜ QuantumNLS.Sobolev.h02 L s,
      ∀ u n, (F u).val n = w u.val n

/-- Full accepted scalar-uniqueness theorem, including the unique continuous
law on the realized indexed-mass carrier. -/
def ScalarUniqueness (hκ : 0 < κ) : Prop :=
  (∀ u v : QuantumNLS.PhysicalTensor.L2T L,
    (∀ n : ℤ, (QuantumNLS.RootIndexedMasses.masses hκ u).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ v).1 n) →
    QuantumNLS.PhysicalQuantumMeasure.measure hκ u =
      QuantumNLS.PhysicalQuantumMeasure.measure hκ v) ∧
  (∃! F : QuantumNLS.RootScalarContinuityR28.realized (L := L) hκ → FiniteMeasure ℝ,
    (∀ u : QuantumNLS.PhysicalTensor.L2T L,
      (F (QuantumNLS.RootScalarContinuityR28.realizedPoint hκ u) : Measure ℝ) =
        QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ∧
    (∀ a : QuantumNLS.RootScalarContinuityR28.realized (L := L) hκ,
      Filter.Tendsto (fun b : QuantumNLS.RootScalarContinuityR28.realized (L := L) hκ =>
        QuantumNLS.TotalVariation.tvNorm (F b : Measure ℝ) (F a : Measure ℝ))
        (𝓝 a) (𝓝 0)))

/-- All smooth scalar moments, with charge reality and finite absolute moments.
This is the full accepted R-275B7656 statement, universally over smooth data. -/
def ScalarMomentIdentification (hκ : 0 < κ) : Prop :=
  ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f),
    (∀ j : ℕ, (charge L κ f j).im = 0) ∧
    ∀ r : ℕ, Integrable (fun t : ℝ => |t| ^ r)
      (QuantumNLS.FullMass.Mmeas κ (QuantumNLS.SmoothScalarMomentsPhysical.smoothL2 hf)) ∧
      ((∫ t : ℝ, t ^ r ∂(QuantumNLS.FullMass.Mmeas κ
        (QuantumNLS.SmoothScalarMomentsPhysical.smoothL2 hf)) : ℝ) : ℂ) =
        charge L κ f (r + 1)

/-- Every clause of the printed fixed-hierarchy conclusion, with one shared
family of actual physical Hamiltonian flows and the full smooth jet topology. -/
def HierarchyConclusion
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.QuantumFourierSpecification.Coordinates)
    (action : QuantumNLS.PhysicalTensor.L2T L → ℤ → ℝ) : Prop :=
  ∃ (Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
    (hΦ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ r)),
    (∀ r (hr : 2 ≤ r), UniqueHamFlow L (hamiltonian L κ r) (Φ r)) ∧
    (∀ r s, 2 ≤ r → 2 ≤ s → ∀ u : Smooth L, ∀ t τ,
      Φ r t (Φ s τ u.val) = Φ s τ (Φ r t u.val)) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L) n, ∃ freq : ℝ, ∀ t,
      w (physical ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n =
        phase t freq * w (physical u) n) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L), IsCompact (closure
      (Set.range fun t => (⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩ : Smooth L)))) ∧
    (∀ (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r),
      let F : HamFlows L κ R := ⟨Φ, fun r hr => hΦ r (hR r hr)⟩
      ∀ (K : Set (Smooth L)), IsCompact K → ∀ (T : ℕ → ℝ), (∀ r, 0 ≤ T r) →
        ContinuousOn (fun p : Smooth L × (ℕ → ℝ) => jointSmooth F p.2 p.1)
          (K ×ˢ (Set.pi Set.univ fun r => if r ∈ R then Set.Icc (-T r) (T r) else {0}))) ∧
    (∀ (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) (u : Smooth L),
      let F : HamFlows L κ R := ⟨Φ, fun r hr => hΦ r (hR r hr)⟩
      IsCompact (closure (Set.range fun t : ℕ → ℝ => jointSmooth F t u))) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L) (t : ℝ) j,
      charge L κ (Φ r t u.val) j = charge L κ u.val j) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L) (t : ℝ) n,
      action (physical ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n = action (physical u) n)

/-- The single missing predecessor is a conditional theorem, not an arbitrary
Prop token and not a frequency/existence hypothesis. There is no quantitative
uniformity as orders, label families or time boxes grow. -/
def HierarchyR7B122087Input (hκ : 0 < κ) : Prop :=
  ∀ w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K,
    QuantumNLS.REF88PrintedChart.PrintedChart hκ w →
    SobolevHomeomorphisms w → ScalarUniqueness (L := L) hκ →
    ScalarMomentIdentification (L := L) hκ →
    HierarchyConclusion (κ := κ) w (fun u n => (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)

/-- Accepted scalar theorem; no new predecessor premise. -/
theorem scalar_uniqueness (hκ : 0 < κ) : ScalarUniqueness (L := L) hκ :=
  QuantumNLS.RootScalarUniquenessR28.root_scalar_uniqueness hκ

theorem scalar_moments (hκ : 0 < κ) : ScalarMomentIdentification (L := L) hκ :=
  fun f hf => QuantumNLS.R275Unconditional.R_275B7656 κ hκ hf

/-- Forget only the additional finite-joint-orbit clause when invoking frozen
R24m proofs. The complete printed input remains in the new public theorem. -/
theorem conclusion_to_r24
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (action : QuantumNLS.PhysicalTensor.L2T L → ℤ → ℝ)
    (h : HierarchyConclusion (κ := κ) w action) :
    HierarchyPrintedInput (κ := κ) w action := by
  obtain ⟨Φ, hΦ, hu, hc, hr, hk, ht, hj, hq, ha⟩ := h
  exact ⟨Φ, hΦ, hu, hc, hr, hk, ht, hq, ha⟩

end QuantumNLS.HierarchyInputR25m
#print axioms QuantumNLS.HierarchyInputR25m.scalar_uniqueness
#print axioms QuantumNLS.HierarchyInputR25m.scalar_moments
#print axioms QuantumNLS.HierarchyInputR25m.conclusion_to_r24
