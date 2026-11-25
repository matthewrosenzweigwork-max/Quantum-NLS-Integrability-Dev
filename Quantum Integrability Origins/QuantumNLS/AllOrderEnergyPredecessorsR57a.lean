import QuantumNLS.AllOrderEnergyMarginalToolsR56a
import QuantumNLS.ValuesConcentration

/-! The printed window and weighted-occupation result types used by R-568BCDF8. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Filter Topology MeasureTheory

namespace QuantumNLS.AllOrderEnergyPredecessorsR57a
open PhysicalTensor Def033HierarchyR24m BetheCoefficientTransform HierarchyFlow
open ActualModelBindingR53a ActualModelTargetR53a AllOrderEnergyInputsR56a
open ClassicalCharges CommonBethePacket BetheLabels BulkResponseActual
open EmpiricalRapidity SmoothScalarMomentsPhysical AuditWeightedProbabilityR49a
open Prop025OInputs PROP017UniformN
variable {L κ : ℝ} [Fact (0 < L)]

def profileAt (r : ℕ) (u : Smooth L) : Sobolev.H02 L (Q07TailBindingR24.regularity r) :=
  Sobolev.WField.mk (physical u) (RB7.memHs_of_smooth u.property _)

/-- Uniform scalar differential estimates on the designated initial class. -/
def UniformScalarOn (hκ : 0 < κ) (R : Finset ℕ) (K : Set (Smooth L)) : Prop :=
  ∀ r ∈ R, 2 ≤ r → ∀ h : ℝ, 0 < h →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l₀ : ℕ, ∀ l ≥ l₀, ∀ u ∈ K,
      DifferentiableAt ℝ (Q07GradientRemovalR24.T hκ r h l) (profileAt r u) ∧
      ‖fderiv ℝ (Q07GradientRemovalR24.T hκ r h l) (profileAt r u)‖ ≤
        C * (cutSeq L l) ^ (-(1/2 : ℝ))

/-- The cutoff set is the physical set in the source's eq:Q07Bwindows.
Quantification is in the real cutoff with one threshold for the class and box. -/
def WindowRate {R : Finset ℕ} (F : HamFlows L κ R) (T : ℕ → ℝ)
    (K : Set (Smooth L)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℝ, ∀ a ∈ Set.range (cutSeq L), A ≤ a →
    ∀ u ∈ K, ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
    ∀ y, IsWindowTrajectory κ R t a (physical u) y →
      ‖y 1 - physical (jointSmooth F t u)‖ ≤ C * a ^ (-(1/4 : ℝ))

/-- The threshold in the real cutoff and the threshold in its printed index
are equivalent because the source cutoff sequence is increasing and cofinal. -/
theorem windowRate_iff_indexed {R : Finset ℕ} (F : HamFlows L κ R)
    (T : ℕ → ℝ) (K : Set (Smooth L)) :
    WindowRate F T K ↔ ∃ C : ℝ, 0 ≤ C ∧ ∃ l₀ : ℕ, ∀ l ≥ l₀,
      ∀ u ∈ K, ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      ∀ y, IsWindowTrajectory κ R t (cutSeq L l) (physical u) y →
        ‖y 1 - physical (jointSmooth F t u)‖ ≤ C * (cutSeq L l) ^ (-(1/4 : ℝ)) := by
  have hL : 0 < L := Fact.out
  have hp : 0 < Real.pi / L := div_pos Real.pi_pos hL
  have hm : StrictMono (cutSeq L) := by
    intro i j hij
    have hcast : (i : ℝ) < j := by exact_mod_cast hij
    have h' := mul_lt_mul_of_pos_right (show 2 * (i : ℝ) + 1 < 2 * j + 1 by linarith) hp
    simpa only [cutSeq, mul_div_assoc] using h'
  constructor
  · rintro ⟨C, hC, A, h⟩
    obtain ⟨l₀, hl₀⟩ := exists_nat_ge (A / (Real.pi / L))
    have ha : A ≤ cutSeq L l₀ := by
      have h' := (div_le_iff₀ hp).1 hl₀
      unfold cutSeq
      rw [mul_div_assoc]
      exact h'.trans (mul_le_mul_of_nonneg_right (by linarith only [Nat.cast_nonneg (α := ℝ) l₀]) hp.le)
    exact ⟨C, hC, l₀, fun l hl => h _ ⟨l, rfl⟩ (ha.trans (hm.monotone hl))⟩
  · rintro ⟨C, hC, l₀, h⟩
    refine ⟨C, hC, cutSeq L l₀, ?_⟩
    rintro a ⟨l, rfl⟩ ha
    exact h l (hm.le_iff_le.mp ha)

/-- R-E59628C9, with separate fixed-datum and uniform compact-class clauses.
The rate compares the unit auxiliary-time endpoint of the physical window
Hamiltonian in the preceding scalar contour setting. -/
def WindowRE59628C9Input (hκ : 0 < κ) : Prop :=
  ∀ w : L2T L → REF88Chart.K, REF88PrintedChart.PrintedChart hκ w →
    HierarchyInputR25m.SobolevHomeomorphisms w → GradientRemovalAntecedent (L := L) hκ →
    ∀ d : ℕ, 2 ≤ d → ∀ (R : Finset ℕ), (∀ r ∈ R, r ≤ d) →
    ∀ (F : HamFlows L κ R) (T : ℕ → ℝ), (∀ r, 0 ≤ T r) →
      (∀ u : Smooth L, WindowRate F T {u}) ∧
      (∀ K : Set (Smooth L), IsCompact K → UniformScalarOn hκ R K → WindowRate F T K)

theorem actual_window_rate (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (WindowRE59628C9Input : WindowRE59628C9Input (L := L) hκ)
    (d : ℕ) (hd : 2 ≤ d) (R : Finset ℕ) (hR : ∀ r ∈ R, r ≤ d)
    (T : ℕ → ℝ) (hT : ∀ r, 0 ≤ T r) :
    let F := hamFlows (flows hκ HierarchyR7B122087Input) R
    (∀ u : Smooth L, WindowRate F T {u}) ∧
      (∀ K : Set (Smooth L), IsCompact K → UniformScalarOn hκ R K → WindowRate F T K) :=
  WindowRE59628C9Input (chart (L := L) hκ).Φ (printed_chart hκ) (sobolev hκ)
    (gradient_removal hκ) d hd R hR _ T hT

/-- The bounded-transfer concentration and bias from R-0270D1F7 at the
fixed coupling, on the original Born law. -/
def ConcentrationAndBias (hκ : 0 < κ) : Prop :=
  ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 < C ∧
    ∀ (N : ℕ), 0 < N → ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f)
      (hu : ‖smoothL2 hf‖ = 1) (μ : ProbabilityMeasure ℝ),
      IsLimitingRapidityMeasure L κ hκ (smoothL2 hf) hu μ →
      ∀ z : ℂ, η₀ ≤ z.im →
        let g := CauchyUniqueness.cauchyTransform (μ : Measure ℝ) z
        let P := bornMeasure (physBasis L hκ N) (smoothL2 hf) hu
        (∫ m : MArr N, ‖CauchyUniqueness.cauchyTransform (empiricalProb L κ N m : Measure ℝ) z - g‖ ^ 2
          ∂P) ≤ C / (N * z.im ^ 2) ∧
        ‖(∫ m : MArr N, CauchyUniqueness.cauchyTransform (empiricalProb L κ N m : Measure ℝ) z
          ∂P) - g‖ ≤ C / (N * z.im ^ 2)

theorem concentrationAndBias (hκ : 0 < κ) : ConcentrationAndBias (L := L) hκ := by
  obtain ⟨hη₀, hC, h⟩ := ValuesConcentration.values_concentration (L := L) hκ (le_refl κ)
  exact ⟨_, _, hη₀, hC, fun N hN _ hf => h N hN (smoothL2 hf)⟩

/-- Conserved-value and weighted-occupation probability, and the same finite
packet sequence for all fixed orders in both support limits. -/
def WeightedConclusion (hκ : 0 < κ) : Prop :=
  ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (hu : ‖smoothL2 hf‖ = 1),
    (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu
        {m | ε < error hκ (smoothL2 hf) p N m}) atTop (𝓝 0)) ∧
    (∀ r : ℕ, BornConvergence.TendstoInProbability
      (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu)
      (fun N m => BetheSpectralCharges.eigenvalue L N (κ/N) r m / (N : ℝ))
      (charge L κ f (r+1)).re) ∧
    ∃ P : (N : ℕ) → Packet (physBasis L hκ N),
      Tendsto (fun N => ‖vector (P N) - productVec L N (smoothL2 hf)‖) atTop (𝓝 0) ∧
      (∀ r ε, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        |BetheSpectralCharges.eigenvalue L N (κ/N) r m / (N : ℝ) -
          (charge L κ f (r+1)).re| ≤ ε) ∧
      (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        error hκ (smoothL2 hf) p N m ≤ ε)

/-- The conditional structure of R-115CAA16. -/
def WeightedR115CAA16Input (hκ : 0 < κ) : Prop :=
  HierarchyInputR25m.ScalarMomentIdentification (L := L) hκ →
    ConcentrationAndBias (L := L) hκ → WeightedConclusion (L := L) hκ

/-- The R55a extra domain clause follows from finite support. The conditional
antecedents are supplied by the accepted scalar theorems. -/
theorem weighted_input_iff_r55 (hκ : 0 < κ) :
    WeightedR115CAA16Input (L := L) hκ ↔ AllOrderEnergyInputsR55a.WeightedR115CAA16Input (L := L) hκ := by
  constructor
  · intro h f hf hu
    obtain ⟨hp, hc, P, hP, hcharge, hweight⟩ :=
      h (HierarchyInputR25m.scalar_moments hκ) (concentrationAndBias hκ) f hf hu
    exact ⟨hp, hc, P, hP, hcharge, hweight,
      fun N ev => AuditWeightedPacketR49a.packet_mem_every_domain _ (P N) ev⟩
  · intro h _ _ f hf hu
    obtain ⟨hp, hc, P, hP, hcharge, hweight, _⟩ := h f hf hu
    exact ⟨hp, hc, P, hP, hcharge, hweight⟩

end QuantumNLS.AllOrderEnergyPredecessorsR57a
