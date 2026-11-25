import QuantumNLS.Def024CubicSmoothData
import QuantumNLS.Def024CubicSmoothNonlinearity

/-! Iterated strong time regularity of the compatible global Sobolev solutions. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Topology ContDiff
open Filter QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
open QuantumNLS.ClassicalCharges QuantumNLS.Def024CubicSmoothData QuantumNLS.Def024CubicSmoothNonlinearity
namespace QuantumNLS.Def024CubicSmoothTime
variable {L : ℝ} [Fact (0 < L)]

/-- Reindexing an equal Sobolev order is the identity on Fourier coefficients. -/
def transport {s t : ℝ} (h : s=t) : h04 L s →L[ℂ] h04 L t := by
  subst t
  exact ContinuousLinearMap.id ℂ _

@[simp] lemma transport_val {s t : ℝ} (h : s=t) (a : h04 L s) :
    (transport h a).val = a.val := by subst t; rfl

/-- The classical vector field with explicit two-derivative loss. -/
def rhs {s : ℝ} (hs : 1  ≤  s) (κ : ℝ) (a : h04 L (s+2)) : h04 L s :=
  transport (by ring : s+2-2=s) (Gder (by linarith : 1  ≤  s+2) κ a)

lemma contDiff_rhs {s : ℝ} (hs : 1  ≤  s) (κ : ℝ) :
    ContDiff ℝ ∞ (rhs (L := L) hs κ) :=
  ((transport (by ring : s+2-2=s)).restrictScalars ℝ).contDiff.comp
    (contDiff_Gder (by linarith : 1 ≤ s+2) κ)

lemma trajectory_hasDerivAt {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {s : ℝ}
    (hs : 1  ≤  s) {κ : ℝ} (hκ : 0  ≤  κ) (t : ℝ) :
    HasDerivAt (trajectory hu hs κ)
      (rhs hs κ (trajectory hu (by linarith : 1 ≤ s+2) κ t)) t := by
  have hd := (mild_C1 (trajectory_mild hu (by linarith : 1 ≤ s+2) hκ)).2.2.2.1 t
    (by simp)
  have hd' := ((transport (L := L) (by ring : s+2-2=s)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have he : (fun r => transport (L := L) (by ring : s+2-2=s)
      (ι2 (s+2) (trajectory hu (by linarith : 1 ≤ s+2) κ r))) = trajectory hu hs κ := by
    funext r
    have hproj : transport (L := L) (by ring : s+2-2=s)
        (ι2 (s+2) (trajectory hu (by linarith : 1 ≤ s+2) κ r)) =
        h04_mono L (by linarith : s ≤ s+2) (trajectory hu (by linarith : 1 ≤ s+2) κ r) :=
      WSeq.ext (by simp only [transport_val]; rfl)
    exact hproj.trans (trajectory_mono hu _ hs (by linarith) hκ r)
  change HasDerivAt (fun r => transport (L := L) (by ring : s+2-2=s)
    (ι2 (s+2) (trajectory hu (by linarith : 1 ≤ s+2) κ r)))
    (rhs hs κ (trajectory hu (by linarith : 1 ≤ s+2) κ t)) t at hd'
  rw [he] at hd'
  exact hd'

/-- Every finite time order, into every H^s algebra order, by iterating mild_C1. -/
theorem contDiff_trajectory {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {κ : ℝ}
    (hκ : 0  ≤  κ) (k : ℕ) {s : ℝ} (hs : 1  ≤  s) :
    ContDiff ℝ k (trajectory hu hs κ) := by
  induction k generalizing s with
  | zero => exact contDiff_zero.mpr (continuousOn_univ.mp (trajectory_mild hu hs hκ).cont)
  | succ k ih =>
    have hd := trajectory_hasDerivAt hu hs hκ
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun t => (hd t).differentiableAt, by simp, ?_⟩
    have he : deriv (trajectory hu hs κ) =
        fun t => rhs hs κ (trajectory hu (by linarith : 1 ≤ s+2) κ t) :=
      funext fun t => (hd t).deriv
    rw [he]
    exact ((contDiff_rhs hs κ).of_le (by simp)).comp (ih (by linarith : 1 ≤ s+2))

theorem smooth_trajectory {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {κ : ℝ}
    (hκ : 0  ≤  κ) {s : ℝ} (hs : 1  ≤  s) : ContDiff ℝ ∞ (trajectory hu hs κ) :=
  contDiff_infty.mpr (fun k => contDiff_trajectory hu hκ k hs)

/-- Strong time regularity at every real output order, including orders below 1. -/
theorem smooth_trajectory_lower {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {κ : ℝ}
    (hκ : 0  ≤  κ) (m : ℝ) : ContDiff ℝ ∞ (fun t =>
      h04_mono L (le_max_left m 1) (trajectory hu (le_max_right m 1) κ t)) :=
  ((h04_mono L (le_max_left m 1)).restrictScalars ℝ).contDiff.comp
    (smooth_trajectory hu hκ (le_max_right m 1))

#print axioms trajectory_hasDerivAt
#print axioms contDiff_trajectory
#print axioms smooth_trajectory
#print axioms smooth_trajectory_lower
end QuantumNLS.Def024CubicSmoothTime

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def024CubicSmoothTime." ||
        n.toString.startsWith "_private.QuantumNLS.Def024CubicSmoothTime." then
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
