import QuantumNLS.GlobalCompatCovarianceR47a

/-! Global normalization rigidity and the zero-action strata. The competing
map is not assumed to agree locally with the given extension. Its norm
identity follows from its exact indexed actions and the accepted mass sum. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate Topology
open Set Metric Filter
namespace QuantumNLS.GlobalCompatR47a
open PhysicalTensor (L2T)
open D01LocalPrimitive (K)
open Local021 (Setting SymKind Mono)
open RF535Final (Local023Body)
open RootIndexedMasses (masses)
open ResetNormalizationUniqueness (Cphys)
variable {L κ d CL : ℝ} [Fact (0 < L)] {hκ : 0 < κ}
variable {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
variable {Φ : L2T L → K} {Ψ : K → L2T L}

theorem Extension.real_normalization (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl) (u : L2T L) :
    Φ (Cphys L u) = star (Φ u) := by
  have H := h.covariance hd hl SymKind.cjr u
  apply lp.ext
  funext n
  have Hn := congrArg (fun z : K => z n) H
  simpa [SymKind.phys, SymKind.mono, Mono.cj] using Hn

theorem Extension.unique (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl)
    (G : L2T L → K) (hG : StrongSymplectic.IsStronglySymplectic G)
    (ha : ∀ u, AnalyticAt ℝ G u)
    (hm : ∀ u n, ‖G u n‖^2 = (masses hκ u).1 n)
    (hD : ∀ v, fderiv ℝ G 0 v = QuantumNLS.Fourier.fourierL2 L v)
    (hc : ∀ u, G (Cphys L u) = star (G u)) : G = Φ := by
  have hnorm (u : L2T L) : ‖G u‖ = ‖u‖ := by
    have H := ActionTorus.tsum_sq_eq (G u)
    rw [show (∑' n, ‖G u n‖^2) = ∑' n, (masses hκ u).1 n from tsum_congr (hm u),
      (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.2.2.1] at H
    nlinarith [norm_nonneg (G u), norm_nonneg u]
  have hq0 (n : ℤ) : (masses hκ (0 : L2T L)).1 n = 0 := by
    rw [← h.moduli, h.zero]
    simp
  funext u
  exact ResetNormalizationUniqueness.reset_normalization_uniqueness_global L
    (fun n u => (masses hκ u).1 n) hq0 G Φ hG h.strong hnorm h.norm
    (fun u _ => ha u) (fun u _ => h.analytic u) hm h.moduli hD
    (fun v => by rw [h.fourier_derivative hd hl]; rfl) hc
    (h.real_normalization hd hl) u

theorem Extension.zero_action (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ) (u : L2T L) (n : ℤ) :
    (masses hκ u).1 n = 0 ↔ Φ u n = 0 := by
  rw [← h.moduli u n, sq_eq_zero_iff, norm_eq_zero]

theorem Extension.inverse_zero_action (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ) (z : K) (n : ℤ) :
    (masses hκ (Ψ z)).1 n = 0 ↔ z n = 0 := by
  simpa only [h.right_inv z] using h.zero_action (Ψ z) n

end QuantumNLS.GlobalCompatR47a

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.GlobalCompatR47a." ||
        n.toString.startsWith "_private.QuantumNLS.GlobalCompatR47a." then
      pending := pending.push n
      roots := roots + 1
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round47 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
