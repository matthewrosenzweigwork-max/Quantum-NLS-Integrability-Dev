import QuantumNLS.RF535Final

/-! DEF-021: select witnesses of the ACCEPTED global actual quantum chart,
using a single LOCAL-023 family at each period. Every field of these records
is proved from RF535Final.global_actual_chart; none is a supplied premise. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.Def021ChartR41b
open PhysicalTensor (L2T)
open D01LocalPrimitive (K)
open Metric Set

structure LocalChart (L : ℝ) [Fact (0 < L)] where
  d : ℝ
  CL : ℝ
  positive : 0 < d
  nonnegative : 0 ≤ CL
  Φ : ℝ → L2T L → K
  Ψ : ℝ → K → L2T L
  spec : RF535Final.Local023Body L d CL Φ Ψ

theorem local_exists (L : ℝ) [Fact (0 < L)] : Nonempty (LocalChart L) := by
  obtain ⟨d, CL, hd, hCL, Φ, Ψ, h⟩ := (RF535Final.global_actual_chart L).1
  exact ⟨⟨d, CL, hd, hCL, Φ, Ψ, h⟩⟩

def localChart (L : ℝ) [Fact (0 < L)] : LocalChart L := Classical.choice (local_exists L)

structure Chart (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) where
  Φ : L2T L → K
  Ψ : K → L2T L
  analytic : ∀ u, AnalyticAt ℝ Φ u
  inverse_analytic : ∀ z, AnalyticAt ℝ Ψ z
  left_inverse : ∀ u, Ψ (Φ u) = u
  right_inverse : ∀ z, Φ (Ψ z) = z
  actions : ∀ u n, ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n
  norm : ∀ u, ‖Φ u‖ ^ 2 = ‖u‖ ^ 2
  symplectic : ∀ u (h k : L2T L),
    2 * (inner ℂ (fderiv ℝ Φ u h) (fderiv ℝ Φ u k)).im = 2 * (inner ℂ h k).im
  differential : ∀ u, ∃ e : L2T L ≃L[ℝ] K,
    HasFDerivAt Φ (e : L2T L →L[ℝ] K) u ∧
    HasFDerivAt Ψ (e.symm : K →L[ℝ] L2T L) (Φ u)
  local_agreement : ∀ u ∈ ball (0 : L2T L) ((localChart L).d / Real.sqrt κ),
    Φ u = (localChart L).Φ κ u

theorem chart_exists (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Nonempty (Chart L κ hκ) := by
  let lc := localChart L
  have h := (RF535Final.global_actual_chart L).2 lc.d lc.CL lc.Φ lc.Ψ
    lc.positive lc.nonnegative lc.spec κ hκ
  rcases h.2 with ⟨Y, F, Φ, Ψ, _hY, _hYu, _hF0, _hFd, _hFu, _hform, _hiform,
    hΦ, hΨ, hΨΦ, hΦΨ, hm, hn, hs, he, hl, _rest⟩
  exact ⟨⟨Φ, Ψ, hΦ, hΨ, hΨΦ, hΦΨ, hm, hn, hs, he, hl⟩⟩

def chart (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Chart L κ hκ :=
  Classical.choice (chart_exists L κ hκ)

/-- Total family on the same carriers as DEF-020. Only positive couplings are
used; there it is the accepted actual quantum chart, not a candidate. -/
def Phi (L : ℝ) [Fact (0 < L)] (κ : ℝ) : L2T L → K :=
  if hκ : 0 < κ then (chart L κ hκ).Φ else fun _ => 0

theorem Phi_eq (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) :
    Phi L κ = (chart L κ hκ).Φ := dite_eq_left hκ

theorem analytic (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L) :
    AnalyticAt ℝ (Phi L κ) u := by
  rw [Phi_eq L κ hκ]
  exact (chart L κ hκ).analytic u

theorem local_agreement (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L)
    (hu : u ∈ ball (0 : L2T L) ((localChart L).d / Real.sqrt κ)) :
    Phi L κ u = (localChart L).Φ κ u := by
  rw [Phi_eq L κ hκ]
  exact (chart L κ hκ).local_agreement u hu

end QuantumNLS.Def021ChartR41b

#print axioms QuantumNLS.Def021ChartR41b.local_exists
#print axioms QuantumNLS.Def021ChartR41b.chart_exists
#print axioms QuantumNLS.Def021ChartR41b.Phi
#print axioms QuantumNLS.Def021ChartR41b.analytic
#print axioms QuantumNLS.Def021ChartR41b.local_agreement

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def021ChartR41b." ||
        n.toString.startsWith "_private.QuantumNLS.Def021ChartR41b." then
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
  Lean.logInfo m!"R41b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
