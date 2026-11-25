import QuantumNLS.RootMassFreeLimit
import QuantumNLS.RootMassPlane
import QuantumNLS.RootMassGalilean

/-! R-950BFB30, all printed clauses in one named theorem on the physical carrier. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootIndexedMassesFull
open PhysicalTensor (L2T)
open RootIndexedMasses (masses)
variable {L κ : ℝ} [Fact (0 < L)]
theorem root_indexed_masses (hκ : 0 < κ) (u : L2T L) :
    (∀ n : ℤ, (masses hκ u).1 n =
      (PhysicalQuantumMeasure.measure hκ u (Ioo
        (RootIndexedPhase.separator hκ u (n-1)) (RootIndexedPhase.separator hκ u n))).toReal) ∧
    (∀ n : ℤ, 0 ≤ (masses hκ u).1 n) ∧
    Summable (fun n => (masses hκ u).1 n) ∧
    (∑' n, (masses hκ u).1 n) = ‖u‖^2 ∧
    Continuous (fun p : DEF014Phase.Param L => masses p.1.2 p.2) ∧
    (∀ n : ℤ, PhysicalQuantumMeasure.measure hκ u (Ioo
      (RootIndexedPhase.separator hκ u (n-1)) (RootIndexedPhase.separator hκ u n)) = 0 →
      (masses hκ u).1 n = 0) ∧
    (∀ c : ℂ, ‖c‖ = 1 → masses hκ (c • u) = masses hκ u) ∧
    (∀ a : ℝ, masses hκ (BornTranslation.trans a u) = masses hκ u) ∧
    Tendsto (fun k : RootMassFree.Coupling => masses k.2 u) RootMassFree.zeroCoupling
      (𝓝 (RootMassFreeLimit.intensities u)) ∧
    (∀ (a : ℂ) (k n : ℤ),
      (masses hκ (((Real.sqrt L : ℂ)*a) • Fourier.modeLp L k)).1 n =
        if n=k then L*‖a‖^2 else 0) ∧
    (∀ (k n : ℤ), (masses hκ (RootMassBoostSymbol.boost k u)).1 n = (masses hκ u).1 (n-k)) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := RootIndexedMasses.root_indexed_masses_proved_clauses hκ u
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,RootMassFreeLimit.indexed_masses_free u,
    RootMassPlane.masses_plane_amplitude hκ,fun k n => RootMassGalilean.masses_boost hκ k n u⟩

end QuantumNLS.RootIndexedMassesFull
#print axioms QuantumNLS.RootIndexedMassesFull.root_indexed_masses

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootIndexedMassesFull." ||
        n.toString.startsWith "_private.QuantumNLS.RootIndexedMassesFull." then
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
  Lean.logInfo m!"RootIndexedMassesFull audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
