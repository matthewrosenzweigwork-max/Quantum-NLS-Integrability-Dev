import QuantumNLS.RootH1RatioBounds
import QuantumNLS.RootH1RatioStrong

/-! The chosen nonlinear ratio for every sufficiently large real height. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioOperator
  QuantumNLS.RootH1RatioBounds QuantumNLS.RootH1RatioStrong
namespace QuantumNLS.RootH1RatioConvergence
variable {L : ℝ} [hLf : Fact (0 < L)]

def threshold (κ : ℝ) (u : L2T L) : ℝ :=
  max 1 (max (Real.log 3/L) (16*κ*‖u‖^2))

lemma height_spec {Y κ : ℝ} (u : L2T L) (h : threshold κ u ≤ Y) :
    0 < Y ∧ Real.log 3 ≤ Y*L ∧ 16*κ*‖u‖^2 ≤ Y := by
  have h1 : (1:ℝ) ≤ Y := (le_max_left _ _).trans h
  have h2 : Real.log 3/L ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans h)
  have h3 : 16*κ*‖u‖^2 ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans h)
  exact ⟨by linarith, (div_le_iff₀ hLf.out).mp h2,h3⟩

def ratioAt {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (Y : ℝ) : L2T L :=
  if h : threshold κ u ≤ Y then
    ratioL2 (height_spec u h).1 (height_spec u h).2.1 hκ u (height_spec u h).2.2 else 0

def ratioInfAt {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (Y : ℝ) : Linfty L :=
  if h : threshold κ u ≤ Y then
    ratio (height_spec u h).1 (height_spec u h).2.1 hκ u (height_spec u h).2.2 else 0

lemma ratioAt_eq {Y κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (h : threshold κ u ≤ Y) :
    ratioAt hκ u Y = ratioL2 (height_spec u h).1 (height_spec u h).2.1 hκ u (height_spec u h).2.2 := by
  rw [ratioAt,dite_eq_left h]

lemma ratioInfAt_eq {Y κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (h : threshold κ u ≤ Y) :
    ratioInfAt hκ u Y = ratio (height_spec u h).1 (height_spec u h).2.1 hκ u (height_spec u h).2.2 := by
  rw [ratioInfAt,dite_eq_left h]

/-- The nonlinear solution converges for the full real parameter Y→∞. -/
theorem nonlinear_strong {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) :
    Tendsto (fun Y : ℝ => (Y:ℂ) • ratioAt hκ u Y) atTop (nhds u) := by
  have hb : Tendsto (fun Y : ℝ => 4*κ*‖u‖^3/Y) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_id
  have he : ∀ᶠ Y : ℝ in atTop,
      ‖(Y:ℂ) • ratioAt hκ u Y-rescaled Y u‖ ≤ 4*κ*‖u‖^3/Y := by
    filter_upwards [eventually_ge_atTop (threshold κ u)] with Y hY
    rw [ratioAt_eq hκ u hY]
    have heq : (Y:ℂ) • ratioL2 (height_spec u hY).1 (height_spec u hY).2.1 hκ u (height_spec u hY).2.2 - rescaled Y u =
        (Y:ℂ) • (ratioL2 (height_spec u hY).1 (height_spec u hY).2.1 hκ u (height_spec u hY).2.2 -
          RootH1RatioOperator.resolvent Y u) := by
      simp only [rescaled,smul_apply,smul_sub]
    rw [heq]
    exact nonlinear_error (height_spec u hY).1 (height_spec u hY).2.1 hκ u (height_spec u hY).2.2
  have hz : Tendsto (fun Y : ℝ => (Y:ℂ) • ratioAt hκ u Y-rescaled Y u) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) he hb
  have ht := hz.add (resolvent_strong u)
  simp only [zero_add,sub_add_cancel] at ht
  exact ht

#print axioms height_spec
#print axioms ratioAt_eq
#print axioms ratioInfAt_eq
#print axioms nonlinear_strong
end QuantumNLS.RootH1RatioConvergence

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioConvergence." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioConvergence." then
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
