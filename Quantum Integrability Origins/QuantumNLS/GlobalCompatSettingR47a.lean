import Mathlib
import QuantumNLS.RF535Final
import QuantumNLS.AnalyticIdentity
import QuantumNLS.ResetNormalizationUniquenessLOCAL022

/-! R-CA92819A: the printed premises, with the actual accepted local chart.
`Extension` contains only global analyticity, strong symplecticity, a genuine
analytic inverse, exact indexed moduli, and full local agreement. -/
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
open Local021 (Setting SymKind)
open RF535Final (Local023Body)
open RootIndexedMasses (masses)
variable {L : ℝ} [Fact (0 < L)]

structure Extension (κ : ℝ) (hκ : 0 < κ) (d : ℝ)
    (Φl : L2T L → K) (Ψl : K → L2T L) (Φ : L2T L → K) (Ψ : K → L2T L) : Prop where
  analytic : ∀ u, AnalyticAt ℝ Φ u
  inverse_analytic : ∀ z, AnalyticAt ℝ Ψ z
  left_inv : ∀ u, Ψ (Φ u) = u
  right_inv : ∀ z, Φ (Ψ z) = z
  strong : StrongSymplectic.IsStronglySymplectic Φ
  moduli : ∀ u n, ‖Φ u n‖^2 = (masses hκ u).1 n
  local_eq : ∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), Φ u = Φl u

variable {κ d CL : ℝ} {hκ : 0 < κ}
variable {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
variable {Φ : L2T L → K} {Ψ : K → L2T L}

theorem extension_exists (hd : 0 < d) (hlocal : Local023Body L d CL Φl Ψl) :
    ∃ Φ Ψ, Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ := by
  obtain ⟨-, Y, F, Φ, Ψ, -, -, -, -, -, -, -, ha, hb, hl, hr, hm, -, hs, he, hle, -, -⟩ :=
    RF535Final.global_of_localData hκ (RF535Final.localData hd hlocal hκ)
  refine ⟨Φ, Ψ, ha, hb, hl, hr, ?_, hm, hle⟩
  exact ⟨⟨Ψ, hl, hr, fun z => (hb z).differentiableAt⟩,
    fun u => (ha u).differentiableAt,
    fun u => by obtain ⟨e, h, -⟩ := he u; exact ⟨e, congrArg (fun A : L2T L →L[ℝ] K => (A : L2T L → K)) h.fderiv.symm⟩, hs⟩

theorem identity {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f g : E → F} (hf : ∀ u, AnalyticAt ℝ f u) (hg : ∀ u, AnalyticAt ℝ g u)
    {r : ℝ} (hr : 0 < r) (heq : ∀ u ∈ ball (0 : E) r, f u = g u) : f = g := by
  funext u
  exact sub_eq_zero.mp (AnalyticIdentity.identity_of_vanishing_ball (fun u => f u - g u)
    (fun u => (hf u).sub (hg u)) hr (fun u hu => sub_eq_zero.mpr (heq u hu)) u)

/-- Inverse local agreement is a consequence, not an extension premise. -/
theorem Extension.inverse_local_eq (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ)
    (hl : Local023Body L d CL Φl Ψl) (z : K) (hz : z ∈ ball (0 : K) (d / Real.sqrt κ)) :
    Ψ z = Ψl κ z := by
  obtain ⟨-, -, -, hi, -, hr, -⟩ := hl.1 κ hκ
  have H : Φ (Ψl κ z) = z := by rw [h.local_eq _ (hi hz), hr z hz]
  calc Ψ z = Ψ (Φ (Ψl κ z)) := congrArg Ψ H.symm
       _ = Ψl κ z := h.left_inv _

theorem Extension.norm (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ) (u : L2T L) :
    ‖Φ u‖ = ‖u‖ := by
  have hm := (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.2.2.1
  have hn := ActionTorus.tsum_sq_eq (Φ u)
  rw [show (∑' n, ‖Φ u n‖^2) = ∑' n, (masses hκ u).1 n from tsum_congr (h.moduli u), hm] at hn
  nlinarith [norm_nonneg (Φ u), norm_nonneg u]

theorem Extension.inverse_norm (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ) (z : K) :
    ‖Ψ z‖ = ‖z‖ := by
  simpa [h.right_inv z] using (h.norm (Ψ z)).symm

theorem Extension.zero (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ) : Φ 0 = 0 := by
  apply norm_eq_zero.mp
  rw [h.norm, norm_zero]

theorem Extension.inverse_zero (h : Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ) : Ψ 0 = 0 := by
  apply norm_eq_zero.mp
  rw [h.inverse_norm, norm_zero]
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
