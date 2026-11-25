import QuantumNLS.Def044InterfacesR51a
import QuantumNLS.R275Unconditional
import QuantumNLS.ValuesTail
import QuantumNLS.AuditWeightedTailR49a
import QuantumNLS.Q07UniformCutsR16

/-! R-E679E41D: indexed scalar measure at EVERY D1 regular cut.
All scalar objects are the actual full-mass quantum measures; unit profiles
are used only where probability normalization is required. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.ActualModelScalarR52a
open PhysicalTensor Def044InterfacesR51a Def044D1SpectralR51a
open IndexedScalarMeasure
variable {L κ : ℝ} [Fact (0 < L)]

/-- An exterior point is separated from the measure almost everywhere. -/
theorem exterior_away {μ : Measure ℝ} {x : ℝ} (hx : x ∉ μ.support) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ t ∂μ, δ ≤ |x-t| := by
  obtain ⟨U,hU,hzero⟩ := Measure.notMem_support_iff_exists.mp hx
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ,hδ,?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with t ht
  by_contra h
  apply ht
  apply hball
  simpa only [Metric.mem_ball,Real.dist_eq,abs_sub_comm] using (lt_of_not_ge h)

/-- The selected boundary phase equals the literal Cauchy phase at EVERY
exterior point. This extends the band-only convenience lemma without
changing the D1 definition or assuming separation. -/
theorem boundary_exterior (hκ : 0 < κ) (u : L2T L) {x : ℝ}
    (hx : x ∉ (PhysicalQuantumMeasure.measure hκ u).support) :
    PhysicalContinuousBoundary.boundary hκ u x =
      SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) (x : ℂ) := by
  obtain ⟨δ,hδ,haway⟩ := exterior_away hx
  have hd := PhysicalBandCauchy.hasDerivAt_cauchy_of_away
    (PhysicalQuantumMeasure.measure hκ u) hδ haway
  have hc : ContinuousAt
      (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u)) (x : ℂ) :=
    ((continuousAt_const.mul continuousAt_id).div_const 2).sub (hd.continuousAt.const_mul (κ : ℂ))
  have : NeBot (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) := ComplexCosineBoundary.upper_neBot x
  exact tendsto_nhds_unique (PhysicalContinuousBoundary.boundary_limit hκ u x)
    (hc.tendsto.mono_left nhdsWithin_le_nhds)

/-- Full physical D1 inhabitance; the proof does not take a cut set or a
separation hypothesis. Monotonicity and the integer-valued physical labels
supply both sides at every required cut. -/
def indexed (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) : D1Def043.D1ScalarMeasure L κ where
  hL := Fact.out
  hκ := hκ
  μ := PhysicalQuantumMeasure.measure hκ u
  isProb := ⟨by rw [PhysicalQuantumMeasure.measure_univ,hu]; norm_num⟩
  noAtoms := PhysicalUnconditionalTrace.atomless hκ u
  reG := Prop026Bound.reG hκ u
  boundary := Or.inr (Prop026Bound.boundary_bounded hκ u)
  integer_ae := Prop026Bound.integer_ae hκ (by intro h; rw [h,norm_zero] at hu; norm_num at hu)
  separation := by
    intro x hx a h1 h2
    have he : exteriorForce L κ (PhysicalQuantumMeasure.measure hκ u) x =
        2*(PhysicalContinuousBoundary.boundary hκ u x).re := by
      rw [exteriorForce_eq_two_re_phase,← boundary_exterior hκ u hx.1]
    rw [he] at h1 h2
    have hi := Prop026Bound.integer_ae hκ
      (show u ≠ 0 by intro h; rw [h,norm_zero] at hu; norm_num at hu)
    constructor
    · filter_upwards [hi] with t ht htx
      obtain ⟨n,hn⟩ := ht
      rw [hn]
      have hm := PhysicalContinuousBoundary.monotone_all hκ u htx.le
      have hl := Prop026Bound.label_eq hκ u t
      rw [hn] at hl
      have hp := Real.pi_pos
      have hv : (PhysicalContinuousBoundary.boundary hκ u t).re = n*Real.pi :=
        ((eq_div_iff hp.ne').mp hl).symm
      have hnlt : (n : ℝ) < a+1 := by nlinarith
      exact_mod_cast (show n ≤ a by exact Int.lt_add_one_iff.mp (by exact_mod_cast hnlt))
    · filter_upwards [hi] with t ht hxt
      obtain ⟨n,hn⟩ := ht
      rw [hn]
      have hm := PhysicalContinuousBoundary.monotone_all hκ u hxt.le
      have hl := Prop026Bound.label_eq hκ u t
      rw [hn] at hl
      have hp := Real.pi_pos
      have hv : (PhysicalContinuousBoundary.boundary hκ u t).re = n*Real.pi :=
        ((eq_div_iff hp.ne').mp hl).symm
      have hnlt : (a : ℝ) < n := by nlinarith
      exact_mod_cast (show a+1 ≤ n by exact Int.add_one_le_iff.mpr (by exact_mod_cast hnlt))

@[simp] theorem indexed_measure (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) :
    (indexed hκ u hu).μ = PhysicalQuantumMeasure.measure hκ u := rfl

/-- All smooth moments are the UNRESCALED physical Riccati charges. -/
theorem smooth_moments (hκ : 0 < κ) (u : Smooth L) :
    (∀ j : ℕ, (ClassicalCharges.charge L κ u.val j).im = 0) ∧
    ∀ r : ℕ, Integrable (fun t : ℝ => |t|^r) (PhysicalQuantumMeasure.measure hκ (physical u)) ∧
      ((∫ t : ℝ, t^r ∂PhysicalQuantumMeasure.measure hκ (physical u) : ℝ) : ℂ) =
        ClassicalCharges.charge L κ u.val (r+1) := by
  have he : SmoothScalarMomentsPhysical.smoothL2 u.property = physical u := rfl
  have hm := R275Unconditional.R_275B7656 κ hκ u.property
  rw [he] at hm
  simpa only [PhysicalL2Normalization.measure_eq_Mmeas] using hm

/-- Positive-tail estimate under the original full Born law; all scalar
moment and limiting-law premises of the accepted estimate are discharged. -/
theorem positive_tails (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) (p : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (N : ℕ) (_hN : 0 < N) (R : ℝ),
      Prop017Quantum.eta0 L κ ≤ R →
      (∫ m, RootEvent.tailFraction (Prop017Quantum.qAct L κ N) R m
        ∂EmpiricalRapidity.bornMeasure (BulkResponseActual.physBasis L hκ N) (physical u) hu) ≤
        C/R^(2*p) + D/((N : ℝ)*R) :=
  AuditWeightedTailR49a.smooth_born_tail hκ u.property hu p

/-- The mean-square Cauchy estimate uses the same actual limit measure and
complete original Born laws. Constants are independent of N,x,y. -/
theorem cauchy_mean_square (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (_hN : 0 < N) (x y : ℝ),
      Prop017Quantum.eta0 L κ ≤ y →
      (∫ m, ‖Extrapolation.Gfull (PhysicalQuantumMeasure.measure hκ u) (x+y*Complex.I) -
        Extrapolation.GN (Prop017Quantum.qAct L κ N m) (x+y*Complex.I)‖^2
        ∂EmpiricalRapidity.bornMeasure (BulkResponseActual.physBasis L hκ N) u hu) ≤
          C/((N : ℝ)*y^2) := by
  obtain ⟨μ,hμ⟩ := RootMeasureExistence.exists_limiting_measure hκ u hu
  have hm := Prop026Bound.physical_eq_limit hκ u hu hμ
  refine ⟨|RootMeasureConcentrationSharp.Csharp|,abs_nonneg _,?_⟩
  intro N hN x y hy
  have hb := Prop017Quantum.ms_actual hκ u hu hμ hN x y hy
  rw [← hm] at hb
  exact hb.trans (div_le_div_of_nonneg_right (le_abs_self _) (by positivity))

end QuantumNLS.ActualModelScalarR52a
#print axioms QuantumNLS.ActualModelScalarR52a.exterior_away
#print axioms QuantumNLS.ActualModelScalarR52a.boundary_exterior
#print axioms QuantumNLS.ActualModelScalarR52a.indexed
#print axioms QuantumNLS.ActualModelScalarR52a.smooth_moments
#print axioms QuantumNLS.ActualModelScalarR52a.positive_tails
#print axioms QuantumNLS.ActualModelScalarR52a.cauchy_mean_square

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelScalarR52a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelScalarR52a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round52 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
