import QuantumNLS.GlobalCompatCubicR47a

/-! Quantitative forward and inverse C1 estimates, uniform on the full balls.
All constants precede every field, coordinate and support quantifier. -/
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
open Local021 (Setting)
open RF535Final (Local023Body)
variable {L κ d CL : ℝ} [Fact (0 < L)] {hκ : 0 < κ}
variable {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
variable {Φ : L2T L → K} {Ψ : K → L2T L}

theorem Extension.derivative_bound (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hl : Local023Body L d CL Φl Ψl) {u : L2T L}
    (hu : u ∈ ball (0 : L2T L) (d / Real.sqrt κ)) :
    ‖fderiv ℝ Φ u - Setting.Fcl L‖ ≤ CL * κ * ‖u‖^2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := hl.1 κ hκ
  obtain ⟨e, -, -, hbd⟩ := hb u hu
  have hev : Φ =ᶠ[𝓝 u] Φl κ := by
    filter_upwards [isOpen_ball.mem_nhds hu] with v hv
    exact h.local_eq v hv
  rw [hev.fderiv_eq]
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans hbd

theorem Extension.inverse_derivative_bound (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hl : Local023Body L d CL Φl Ψl) {z : K}
    (hz : z ∈ ball (0 : K) (d / Real.sqrt κ)) :
    ‖fderiv ℝ Ψ z - ((Setting.Fcle L).symm : K →L[ℝ] L2T L)‖ ≤ CL * κ * ‖z‖^2 := by
  have hu : Ψ z ∈ ball (0 : L2T L) (d / Real.sqrt κ) := by
    simpa only [mem_ball_zero_iff, h.inverse_norm] using hz
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := hl.1 κ hκ
  obtain ⟨e, -, hi, hbd⟩ := hb (Ψ z) hu
  have he : Φl κ (Ψ z) = z := by rw [← h.local_eq _ hu, h.right_inv]
  rw [he] at hi
  have hev : Ψ =ᶠ[𝓝 z] Ψl κ := by
    filter_upwards [isOpen_ball.mem_nhds hz] with v hv
    exact h.inverse_local_eq hl v hv
  rw [hev.fderiv_eq, hi.fderiv]
  have H := (le_add_of_nonneg_left (norm_nonneg _)).trans hbd
  simpa only [h.inverse_norm] using H

theorem Extension.map_bound (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl) {u : L2T L}
    (hu : u ∈ ball (0 : L2T L) (d / Real.sqrt κ)) :
    ‖Φ u - Setting.Fcl L u‖ ≤ (CL / 3) * κ * ‖u‖^3 := by
  have H := cubic_bound Φ (Setting.Fcl L) (div_pos hd (Real.sqrt_pos.2 hκ))
    (fun v _ => (h.analytic v).differentiableAt) h.zero
    (fun v hv => h.derivative_bound hl hv) (mem_ball_zero_iff.mp hu)
  convert H using 1; ring

theorem Extension.inverse_map_bound (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl) {z : K}
    (hz : z ∈ ball (0 : K) (d / Real.sqrt κ)) :
    ‖Ψ z - (Setting.Fcle L).symm z‖ ≤ (CL / 3) * κ * ‖z‖^3 := by
  have H := cubic_bound Ψ ((Setting.Fcle L).symm : K →L[ℝ] L2T L)
    (div_pos hd (Real.sqrt_pos.2 hκ))
    (fun v _ => (h.inverse_analytic v).differentiableAt) h.inverse_zero
    (fun v hv => h.inverse_derivative_bound hl hv) (mem_ball_zero_iff.mp hz)
  calc ‖Ψ z - (Setting.Fcle L).symm z‖ ≤ ((CL*κ)/3)*‖z‖^3 := H
       _ = (CL/3)*κ*‖z‖^3 := by ring

theorem in_local_ball (hd : 0 < d) {R : ℝ} (hs : κ * R^2 < d^2)
    {E : Type*} [SeminormedAddCommGroup E] {u : E} (hu : ‖u‖ ≤ R) (hκ : 0 < κ) :
    u ∈ ball (0 : E) (d / Real.sqrt κ) := by
  have hR : 0 ≤ R := (norm_nonneg u).trans hu
  have hr : (Real.sqrt κ * R)^2 < d^2 := by simpa only [mul_pow, Real.sq_sqrt hκ.le] using hs
  have hr' : Real.sqrt κ * R < d := by nlinarith [mul_nonneg (Real.sqrt_nonneg κ) hR]
  rw [mem_ball_zero_iff, lt_div_iff₀ (Real.sqrt_pos.2 hκ)]
  exact (mul_le_mul_of_nonneg_right hu (Real.sqrt_nonneg κ)).trans_lt (by simpa [mul_comm] using hr')

theorem Extension.ball_estimates (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hd : 0 < d) (hCL : 0 ≤ CL) (hl : Local023Body L d CL Φl Ψl)
    {R : ℝ} (hsmall : κ * R^2 < d^2) :
    (∀ u : L2T L, ‖u‖ ≤ R →
      ‖fderiv ℝ Φ u - Setting.Fcl L‖ ≤ CL * κ * R^2 ∧
      ‖Φ u - Setting.Fcl L u‖ ≤ (CL / 3) * κ * R^3) ∧
    (∀ z : K, ‖z‖ ≤ R →
      ‖fderiv ℝ Ψ z - ((Setting.Fcle L).symm : K →L[ℝ] L2T L)‖ ≤ CL * κ * R^2 ∧
      ‖Ψ z - (Setting.Fcle L).symm z‖ ≤ (CL / 3) * κ * R^3) := by
  constructor
  · intro u hu
    have hm := in_local_ball hd hsmall hu hκ
    exact ⟨(h.derivative_bound hl hm).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg u) hu 2) (mul_nonneg hCL hκ.le)),
      (h.map_bound hd hl hm).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg u) hu 3) (mul_nonneg (by positivity) hκ.le))⟩
  · intro z hz
    have hm := in_local_ball hd hsmall hz hκ
    exact ⟨(h.inverse_derivative_bound hl hm).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg z) hz 2) (mul_nonneg hCL hκ.le)),
      (h.inverse_map_bound hd hl hm).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg z) hz 3) (mul_nonneg (by positivity) hκ.le))⟩
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
