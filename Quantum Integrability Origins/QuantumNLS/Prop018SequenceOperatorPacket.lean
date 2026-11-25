import QuantumNLS.Prop018SequenceWindowOperators

/-! PROP-018 for arbitrary positive parameter sequences with vanishing source error,
on arbitrary source-admissible designated moving cuts. Constants are uniform
in N, the label, and polynomial coefficients through their explicit l1 factor. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Prop018SequenceOperatorPacket
open PhysicalTensor BetheLabels BulkResponseActual EmpiricalRapidity RootEvent Prop017Quantum
open Prop017Physical PROP018Probability Prop018SequencePhase Prop018SequenceScalar Prop018SequenceWindowOperators
open Extrapolation PeriodReconstructionCore

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- Both source operator inequalities, bounded selfadjoint common-calculus
operators, full-charge commutation, and all charge domains on the literal event
projection. The vanishing error is the only rate assumption. -/
theorem prop018_operator_reconstruct (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (R ε a : ℕ → ℝ) (idx : ℕ → ℕ)
    (hR : ∀ N, 0 < R N) (hε : ∀ N, 0 < ε N)
    (hseq : Tendsto (fun N : ℕ => ε N + 1 / R N ^ b + 1 / (N : ℝ)) atTop (𝓝 0))
    (hcut : ∀ᶠ N : ℕ in atTop, l0 ≤ idx N ∧ a N = PROP017UniformN.cutSeq L (idx N) ∧ 2 * R N ≤ a N)
    (d : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∃ Cp Cs : ℝ, 0 ≤ Cp ∧ 0 ≤ Cs ∧ ∀ r0 : ℝ, 0 < r0 → ∀ (f : ℂ → ℂ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ),
        (∀ z w, ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < r0 → f z w = Prop018Phase.lam L κ (Gfull (μ : Measure ℝ)) z w) →
        (∀ z w v, ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < r0 →
          ‖v - deriv (sf L κ (Gfull (μ : Measure ℝ))) z‖ < r0 → qt z w v = Prop018Phase.qch L κ (Gfull (μ : Measure ℝ)) z w v) →
        ∀ᶠ N : ℕ in atTop, ∃ hN : 0 < N, ∀ p : ℕ → ℝ,
          (∀ z ∈ PeriodReconstruction.Gam (-(a N)) (a N) h,
            ∀ w, ContinuousAt (fun q : ℂ × ℂ => f q.1 q.2) (z, w)) →
          (∀ z ∈ PeriodReconstruction.Gam (-(a N)) (a N) h,
            ∀ w v, ContinuousAt (fun q : ℂ × (ℂ × ℂ) => qt q.1 q.2.1 q.2.2) (z, (w, v))) →
          WindowConclusion (L := L) hκ hN a h
            (EN (μ : Measure ℝ) (qAct L κ N) (R N) (a N) ρ h (eta0 L κ) (ε N) b)
            f qt p d
            (Cp * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a N) ^ (d + 1) / N)
            (Cs * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a N) ^ (d + 1) *
              (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)))
            (cscal L κ (μ : Measure ℝ) a h p d N) := by
  obtain ⟨ρ, hρ, Cp, Cs, hCp, hCs, hscalar⟩ :=
    prop018_reconstruct hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc R ε a idx hR hε hseq hcut d
  refine ⟨ρ, hρ, Cp, Cs, hCp, hCs, ?_⟩
  intro r0 hr0 f qt hfagree hqtagree
  filter_upwards [hscalar r0 hr0 f qt hfagree hqtagree, eventually_gt_atTop 0, hcut] with N hsc hN hc
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hRN : 0 < R N := hR N
  have hεN : 0 < ε N := hε N
  have ha : R N < a N := by linarith [hc.2.2]
  have ha0 : 0 < a N := hRN.trans ha
  have hh : 0 < h := (eta0_pos hκ).trans hηh
  refine ⟨hN, fun p hf hqt => ?_⟩
  apply event_operators (L := L) hκ hN a h (R N) hh hRN.le ha
    (EN (μ : Measure ℝ) (qAct L κ N) (R N) (a N) ρ h (eta0 L κ) (ε N) b)
    (fun m hm => hm.1) f qt hf hqt p d (by positivity) (by positivity)
  · intro m hm
    exact (hsc p m hm).1
  · intro m hm
    exact (hsc p m hm).2

end QuantumNLS.Prop018SequenceOperatorPacket

#print axioms QuantumNLS.Prop018SequenceOperatorPacket.prop018_operator_reconstruct

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop018SequenceOperatorPacket." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
