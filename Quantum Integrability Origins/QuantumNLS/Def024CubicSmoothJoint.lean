import QuantumNLS.Def024CubicSmoothTime
import QuantumNLS.Def024CubicSmoothEvaluation

/-! DEF-024 r=2 D3 Joint: actual global Sobolev solution reconstruction. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
open QuantumNLS.ClassicalCharges QuantumNLS.ChargeEnergy
open QuantumNLS.Def024CubicSmoothData QuantumNLS.Def024CubicSmoothEmbedding
open QuantumNLS.Def024CubicSmoothNonlinearity QuantumNLS.Def024CubicSmoothTime
open QuantumNLS.Def024CubicSmoothEvaluation
namespace QuantumNLS.Def024CubicSmoothJoint
variable {L : ℝ} [Fact (0 < L)]

def profile {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (κ t x : ℝ) : ℂ :=
  seriesRep L (trajectory hu (le_refl (1:ℝ)) κ t).val (x : AddCircle L)

lemma profile_at_order {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {κ : ℝ} (hκ : 0 ≤ κ)
    {s : ℝ} (hs : 1 ≤ s) (t x : ℝ) :
    profile hu κ t x = seriesRep L (trajectory hu hs κ t).val (x : AddCircle L) := by
  have he := trajectory_mono hu hs (le_refl (1:ℝ)) hs hκ t
  have hv := congrArg WSeq.val he
  exact congrArg (fun a => seriesRep L a (x : AddCircle L)) hv.symm

/-- Joint regularity follows from smooth operator-valued evaluation, not from separate smoothness. -/
theorem joint_smooth {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {κ : ℝ} (hκ : 0 ≤ κ) :
    ContDiff ℝ ∞ (fun p : ℝ×ℝ => profile hu κ p.1 p.2) := by
  apply contDiff_infty.mpr
  intro k
  let s : ℝ := (k:ℝ)+2
  have hs : 1 ≤ s := by dsimp [s]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have he : ContDiff ℝ k (fun p : ℝ × ℝ => ev (L := L) hs p.2) :=
    (contDiff_ev (L := L) k (s := s) (by dsimp [s]; linarith)).comp contDiff_snd
  have ht : ContDiff ℝ k (fun p : ℝ × ℝ => trajectory hu hs κ p.1) :=
    (contDiff_trajectory hu hκ k hs).comp contDiff_fst
  have hf : (fun p : ℝ×ℝ => profile hu κ p.1 p.2) =
      (fun p : ℝ×ℝ => ev hs p.2 (trajectory hu hs κ p.1)) :=
    funext (fun p => profile_at_order hu hκ hs p.1 p.2)
  rw [hf]
  exact he.clm_apply ht

theorem smoothPeriodic_profile {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {κ : ℝ}
    (hκ : 0 ≤ κ) (t : ℝ) : SmoothPeriodic L (profile hu κ t) := by
  refine ⟨(joint_smooth hu hκ).comp (contDiff_const.prodMk contDiff_id), ?_⟩
  intro x
  change seriesRep L _ ((x+L : ℝ) : AddCircle L) = seriesRep L _ (x : AddCircle L)
  simp

lemma profile_zero {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {κ : ℝ} (hκ : 0 ≤ κ) :
    profile hu κ 0 = u := by
  funext x
  unfold profile
  rw [trajectory_zero hu _ hκ]
  exact series_datum hu 1 x


#print axioms profile_at_order
#print axioms joint_smooth
#print axioms smoothPeriodic_profile
#print axioms profile_zero
end QuantumNLS.Def024CubicSmoothJoint

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def024CubicSmoothJoint." ||
        n.toString.startsWith "_private.QuantumNLS.Def024CubicSmoothJoint." then
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
