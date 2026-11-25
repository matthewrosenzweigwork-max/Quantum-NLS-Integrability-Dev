import QuantumNLS.GlobalCompatSettingR47a

/-! Analytic identity transport of all six indexed covariances, the Fourier
differential, and all complex plane amplitudes. No argument of a coordinate
is selected; every identity is an equality of full Hilbert-space maps. -/
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
open QuantumNLS.Fourier (fourierL2 modeLp)
variable {L κ d CL : ℝ} [Fact (0 < L)] {hκ : 0 < κ}
variable {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
variable {Φ : L2T L → K} {Ψ : K → L2T L}

theorem phys_analytic (s : SymKind) (u : L2T L) : AnalyticAt ℝ (s.phys L) u := by
  let e := ((Setting.Fcle L).trans (s.mono L).cle).trans (Setting.Fcle L).symm
  have he : s.phys L = (e : L2T L → L2T L) := by
    funext v
    change s.phys L v = (fourierL2 L).symm ((s.mono L).act (fourierL2 L v))
    rw [← s.fourier_phys v, LinearIsometryEquiv.symm_apply_apply]
  rw [he]
  exact e.analyticAt u

theorem local_cov (hκ : 0 < κ) (hl : Local023Body L d CL Φl Ψl) (s : SymKind)
    {u : L2T L} (hu : u ∈ ball (0 : L2T L) (d / Real.sqrt κ)) :
    Φl κ (s.phys L u) = (s.mono L).act (Φl κ u) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hc, -, -⟩ := hl.1 κ hκ
  apply lp.ext
  funext n
  have h := hc u hu n
  cases s with
  | phase a => simpa [SymKind.phys, SymKind.mono, Mono.cj] using h.2.2.2.2.1 a
  | trans y => simpa [SymKind.phys, SymKind.mono, Mono.cj] using h.1 y
  | boost k => simpa [SymKind.phys, SymKind.mono, Mono.cj, sub_eq_add_neg] using h.2.1 k
  | refl => simpa [SymKind.phys, SymKind.mono, Mono.cj] using h.2.2.1
  | cj => simpa [SymKind.phys, SymKind.mono, Mono.cj] using h.2.2.2.1
  | cjr => simpa [SymKind.phys, SymKind.mono, Mono.cj] using h.2.2.2.2.2

theorem Extension.covariance (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl) (s : SymKind) (u : L2T L) :
    Φ (s.phys L u) = (s.mono L).act (Φ u) := by
  have he := identity (fun v => (h.analytic _).comp (phys_analytic s v))
    (fun v => ((s.mono L).cle.analyticAt _).comp (h.analytic v))
    (div_pos hd (Real.sqrt_pos.2 hκ)) (fun v hv => ?_)
  · exact congrFun he u
  · change Φ (s.phys L v) = (s.mono L).act (Φ v)
    rw [h.local_eq _ (by simpa only [mem_ball_zero_iff, s.norm_phys] using hv), h.local_eq v hv]
    exact local_cov hκ hl s hv

theorem Extension.fourier_derivative (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl) :
    fderiv ℝ Φ 0 = Setting.Fcl L := by
  have he : Φ =ᶠ[𝓝 (0 : L2T L)] Φl κ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (div_pos hd (Real.sqrt_pos.2 hκ)))] with u hu
    exact h.local_eq u hu
  rw [he.fderiv_eq]
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hD, -⟩ := hl.1 κ hκ
  exact hD v

theorem Extension.plane (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl) (k : ℤ) (a : ℂ) :
    Φ (a • modeLp L k) = fourierL2 L (a • modeLp L k) := by
  have he := identity
    (f := fun a : ℂ => Φ (a • modeLp L k))
    (g := fun a : ℂ => fourierL2 L (a • modeLp L k))
    (fun a => (h.analytic _).comp (analyticAt_id.smul analyticAt_const))
    (fun a => ((Setting.Fcl L).analyticAt _).comp (analyticAt_id.smul analyticAt_const))
    (div_pos hd (Real.sqrt_pos.2 hκ)) (fun c hc => ?_)
  · exact congrFun he a
  · rw [mem_ball_zero_iff] at hc
    have hm : c • modeLp L k ∈ ball (0 : L2T L) (d / Real.sqrt κ) := by
      simpa [mem_ball_zero_iff, norm_smul, QuantumNLS.Local020Rr.norm_modeLp] using hc
    rw [h.local_eq _ hm]
    exact (hl.1 κ hκ).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k c hc
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
