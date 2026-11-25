import QuantumNLS.Ext025B3PhysicalSectors
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! PROP-021, Q7B:thm:main: signed-time comparison from a strong residual.
The energy argument applies to an unbounded maximal direct sum; no operator
norm bound or derivative of its full unitary group is required. This module
proves the comparison lemma, not the physical Weyl residual identity. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace Topology
open Set
namespace QuantumNLS.Prop021DuhamelR128

section RealEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Regularization at zeros removes any nonvanishing assumption on the error. -/
theorem norm_bound_of_energy {w v : ℝ → E} {s t C : ℝ}
    (hC : 0 ≤ C) (hzero : w s = 0)
    (hd : ∀ r ∈ uIcc s t, HasDerivAt w (v r) r)
    (he : ∀ r ∈ uIcc s t, |⟪w r, v r⟫_ℝ| ≤ C * ‖w r‖) :
    ‖w t‖ ≤ C * |t-s| := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let f : ℝ → ℝ := fun r => Real.sqrt (‖w r‖^2+ε^2)
  let f' : ℝ → ℝ := fun r => (2 * ⟪w r,v r⟫_ℝ) / (2 * f r)
  have hpos (r : ℝ) : 0 < ‖w r‖^2+ε^2 := by positivity
  have hfpos (r : ℝ) : 0 < f r := Real.sqrt_pos.2 (hpos r)
  have hnorm (r : ℝ) : ‖w r‖ ≤ f r := by
    dsimp [f]
    have h := Real.sqrt_le_sqrt (show ‖w r‖^2 ≤ ‖w r‖^2+ε^2 by nlinarith [sq_nonneg ε])
    simpa only [Real.sqrt_sq (norm_nonneg (w r))] using h
  have hfd : ∀ r ∈ uIcc s t, HasDerivAt f (f' r) r := by
    intro r hr
    exact ((hd r hr).norm_sq.add_const (ε^2)).sqrt (ne_of_gt (hpos r))
  have hfb : ∀ r ∈ uIcc s t, ‖f' r‖ ≤ C := by
    intro r hr
    dsimp [f']
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos (mul_pos (by norm_num) (hfpos r))]
    apply (div_le_iff₀ (mul_pos (by norm_num) (hfpos r))).2
    have h := mul_le_mul_of_nonneg_left (he r hr) (show (0:ℝ) ≤ 2 by norm_num)
    have h' := mul_le_mul_of_nonneg_left (hnorm r) hC
    nlinarith
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hfd r hr).hasDerivWithinAt) hfb (convex_uIcc s t)
    (left_mem_uIcc) (right_mem_uIcc)
  have hs : f s = ε := by simp [f,hzero,Real.sqrt_sq hε.le]
  have ht : f t-ε ≤ C * |t-s| := by
    calc
      f t-ε ≤ |f t-f s| := by rw [hs]; exact le_abs_self _
      _ ≤ C * |t-s| := by simpa only [Real.norm_eq_abs] using hm
  linarith [hnorm t]

/-- A skew energy term contributes zero; only the residual costs norm. -/
theorem residual_comparison {w g e : ℝ → E} {s t C : ℝ}
    (hC : 0 ≤ C) (hzero : w s = 0)
    (hd : ∀ r ∈ uIcc s t, HasDerivAt w (g r+e r) r)
    (hg : ∀ r ∈ uIcc s t, ⟪w r,g r⟫_ℝ = 0)
    (he : ∀ r ∈ uIcc s t, ‖e r‖ ≤ C) :
    ‖w t‖ ≤ C * |t-s| := by
  apply norm_bound_of_energy hC hzero hd
  intro r hr
  rw [inner_add_right,hg r hr,zero_add]
  exact (abs_real_inner_le_norm _ _).trans (by
    have h := mul_le_mul_of_nonneg_left (he r hr) (norm_nonneg (w r))
    nlinarith)
end RealEnergy

section PhysicalDirectSum
open Ext025B3PhysicalSectors BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]
local instance : NormedSpace ℝ (Fock L) := NormedSpace.restrictScalars ℝ ℂ (Fock L)
local instance : InnerProductSpace ℝ (Fock L) := InnerProductSpace.rclikeToReal ℂ (Fock L)

/-- Symmetry on the full maximal domain, with no uniform sector bound. -/
theorem block_symmetric (A : ∀ n, HN L n →L[ℂ] HN L n)
    (hA : ∀ n, (A n).adjoint = A n) (x y : (block A).domain) :
    ⟪block A x,y.val⟫_ℂ = ⟪x.val,block A y⟫_ℂ := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change ⟪A n (x.val n),y.val n⟫_ℂ = ⟪x.val n,A n (y.val n)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_right,hA n]

/-- The Schrodinger generator of the actual direct sum is energy-skew. -/
theorem block_skew (A : ∀ n, HN L n →L[ℂ] HN L n)
    (hA : ∀ n, (A n).adjoint = A n) (x : (block A).domain) :
    ⟪x.val,(-Complex.I) • block A x⟫_ℝ = 0 := by
  have h := block_symmetric A hA x x
  have hc : starRingEnd ℂ ⟪x.val,block A x⟫_ℂ = ⟪x.val,block A x⟫_ℂ := by
    rw [inner_conj_symm]; exact h
  have hi : (⟪x.val,block A x⟫_ℂ).im = 0 := by
    have := congrArg Complex.im hc
    change -(⟪x.val,block A x⟫_ℂ).im = (⟪x.val,block A x⟫_ℂ).im at this
    linarith
  change (⟪x.val,(-Complex.I) • block A x⟫_ℂ).re = 0
  simp [inner_smul_right,Complex.mul_re,hi]

/-- Strong residual comparison on physical Fock for arbitrary signed endpoints.
`w` is the error, `hw` its proved maximal-domain membership, and `e` its
actual residual. No conclusion about the physical approximate vector is input. -/
theorem physical_residual_comparison
    (A : ∀ n, HN L n →L[ℂ] HN L n) (hA : ∀ n, (A n).adjoint = A n)
    (w e : ℝ → Fock L) (hw : ∀ r, w r ∈ (block A).domain)
    {s t C : ℝ} (hC : 0 ≤ C) (hzero : w s = 0)
    (hd : ∀ r ∈ uIcc s t,
      HasDerivAt w ((-Complex.I) • block A ⟨w r,hw r⟩ + e r) r)
    (he : ∀ r ∈ uIcc s t, ‖e r‖ ≤ C) :
    ‖w t‖ ≤ C * |t-s| :=
  residual_comparison hC hzero hd (fun r _ => block_skew A hA ⟨w r,hw r⟩) he
end PhysicalDirectSum
end QuantumNLS.Prop021DuhamelR128

#print axioms QuantumNLS.Prop021DuhamelR128.norm_bound_of_energy
#print axioms QuantumNLS.Prop021DuhamelR128.physical_residual_comparison

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021DuhamelR128"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R128 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
