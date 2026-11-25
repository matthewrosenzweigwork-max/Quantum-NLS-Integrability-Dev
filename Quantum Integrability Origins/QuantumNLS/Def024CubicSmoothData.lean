import QuantumNLS.Def024CubicSmoothEmbedding

/-! Smooth periodic fields belong to every Fourier Sobolev space. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.ClassicalCharges QuantumNLS.ChargeEnergy QuantumNLS.WeakDerivatives
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
open QuantumNLS.Def024CubicSmoothEmbedding
namespace QuantumNLS.Def024CubicSmoothData
variable {L : ℝ} [Fact (0 < L)]

def field {u : ℝ → ℂ} (hu : SmoothPeriodic L u) : C(AddCircle L, ℂ) :=
  liftC hu.smooth.continuous hu.periodic

lemma smooth_deriv {u : ℝ → ℂ} (hu : SmoothPeriodic L u) : SmoothPeriodic L (deriv u) :=
  ⟨(contDiff_infty_iff_deriv.mp hu.smooth).2, periodic_deriv hu.periodic⟩

/-- Every integer order, obtained from the Fourier derivative identity and Parseval. -/
theorem mem_nat {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (m : ℕ) :
    Mem04 L (m : ℝ) (coeff L (field hu)) := by
  induction m generalizing u with
  | zero =>
    have h := (hasSum_sq_coeff (L := L) (memLp_of_continuous (field hu).continuous)).summable
    simpa only [Mem04, f04Weight, Nat.cast_zero, Real.rpow_zero, one_mul] using h
  | succ m ih =>
    have h := (ih hu).add (ih (smooth_deriv hu))
    apply h.congr
    intro n
    rw [show coeff L (field (smooth_deriv hu)) n = ikn L n * coeff L (field hu) n from coeff_deriv hu n]
    simp only [norm_ikn_mul_sq, f04Weight, Nat.cast_add, Nat.cast_one]
    rw [Real.rpow_add (by positivity), Real.rpow_one]
    ring

/-- Every real Sobolev order, with no smoothness premise hidden in the norm. -/
theorem mem_order {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    Mem04 L s (coeff L (field hu)) := by
  obtain ⟨m, hm⟩ := exists_nat_ge s
  exact mem04_mono hm (mem_nat hu m)

/-- The same physical datum at any Fourier Sobolev order. -/
def datum {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) : h04 L s :=
  h04.ofMem (mem_order hu s)

@[simp] lemma datum_val {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    (datum hu s).val = coeff L (field hu) := rfl

/-- Pointwise, rather than only almost everywhere, reconstruction of the input. -/
theorem series_datum {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s x : ℝ) :
    seriesRep L (datum hu s).val (x : AddCircle L) = u x := by
  have h1 := (smooth_h04 hu).2
  have he := (Continuous.ae_eq_iff_eq volume (field hu).continuous
    (continuous_seriesRep (summable_norm_of_mem04 le_rfl h1))).mp
      (ae_eq_seriesRep (memLp_of_continuous (field hu).continuous) h1)
  exact congrFun he.symm (x : AddCircle L)

/-- Global trajectories, all using the same coefficient sequence at time zero. -/
def trajectory {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {s : ℝ} (hs : 1 ≤ s)
    (κ : ℝ) : ℝ → h04 L s := umax hs κ (datum hu s)

lemma trajectory_mild {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {s : ℝ} (hs : 1 ≤ s)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    IsMild hs κ Set.univ (datum hu s) (trajectory hu hs κ) :=
  (QuantumNLS.Def024CubicPersistence.persist_global hs hκ (datum hu s)).1

/-- Projection of a mild solution to any lower algebra order. -/
lemma mild_mono {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hst : t ≤ s)
    {κ : ℝ} {I : Set ℝ} {u0 : h04 L s} {u : ℝ → h04 L s}
    (hu : IsMild hs κ I u0 u) :
    IsMild ht κ I (h04_mono L hst u0) (fun t => h04_mono L hst (u t)) := by
  let P := h04_mono L hst
  have hPS (r : ℝ) (a : h04 L s) : P (Sgrp s r a) = Sgrp t r (P a) :=
    WSeq.ext rfl
  have hPF (a : h04 L s) : P (Fh hs a) = Fh ht (P a) := WSeq.ext rfl
  refine ⟨hu.zero_mem, hu.ordConnected, P.continuous.comp_continuousOn hu.cont, fun r hr => ?_⟩
  rw [hu.duhamel_eq r hr]
  unfold duhamel
  have hi := integrable_duhamel hs hu.ordConnected hu.cont r 0 r hu.zero_mem hr
  rw [map_sub, map_smul, hPS, ← P.intervalIntegral_comp_comm hi]
  congr 2

/-- The global solutions constructed at different orders agree by proved uniqueness. -/
theorem trajectory_mono {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {s t : ℝ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hst : t ≤ s) {κ : ℝ} (hκ : 0 ≤ κ) (r : ℝ) :
    h04_mono L hst (trajectory hu hs κ r) = trajectory hu ht κ r := by
  have hp := mild_mono hs ht hst (trajectory_mild hu hs hκ)
  have he : h04_mono L hst (datum hu s) = datum hu t := WSeq.ext rfl
  rw [he] at hp
  exact mild_unique ht hκ hp (trajectory_mild hu ht hκ) r (Set.mem_univ r)

lemma trajectory_zero {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {s : ℝ} (hs : 1 ≤ s)
    {κ : ℝ} (hκ : 0 ≤ κ) : trajectory hu hs κ 0 = datum hu s :=
  (IsMild.toFrom (trajectory_mild hu hs hκ)).at_base

#print axioms mem_nat
#print axioms mem_order
#print axioms series_datum
#print axioms mild_mono
#print axioms trajectory_mono
#print axioms trajectory_zero
end QuantumNLS.Def024CubicSmoothData

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def024CubicSmoothData." ||
        n.toString.startsWith "_private.QuantumNLS.Def024CubicSmoothData." then
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
