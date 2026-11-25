import QuantumNLS.BetheSmooth
import Mathlib.Analysis.Convex.Deriv

/-!
Literal strict-convexity repair for R-4C8D7C9E.
Source: foundations/periodic_basis.tex:143--162 and root_response/F02.tex:49--64.
The actual Yang--Yang second variation is the positive Gaudin quadratic form.
Critical points are global minima by convexity, and strict convexity gives uniqueness.
Frozen BetheSmooth, BetheRoots and BetheWavefunctions are imported/read only.
-/

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter

namespace QuantumNLS.BetheConvexity
open BetheAdmission BetheRoots

/-- First variation at every point of an affine line, obtained by translation
of the already proved literal Yang--Yang first variation. -/
theorem yangYang_line_derivative {N : ℕ} (L c : ℝ) (b q v : Fin N → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => yangYang L c b (q + s • v))
      (∑ i, (logMap L c (q + t • v) i - b i) * v i) t := by
  have h := (yangYang_line_hasDerivAt L c b (q + t • v) v).comp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  convert h using 1
  · ext s
    congr 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq]
    ring
  · simp

/-- Second variation is the actual Gaudin Hessian, with no supplied Hessian
or positivity hypothesis. -/
theorem yangYang_line_second {N : ℕ} (L : ℝ) {c : ℝ} (hc : 0 < c)
    (b q v : Fin N → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ i, (logMap L c (q + s • v) i - b i) * v i)
      (∑ i, v i * gaudin L c (q + t • v) v i) t := by
  have hl : HasDerivAt (fun s : ℝ => q + s • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v |>.const_add q
  have hg := (logMap_hasFDerivAt L hc (q + t • v)).comp_hasDerivAt t hl
  convert HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => ((hasDerivAt_pi.mp hg i).sub_const (b i)).mul_const (v i)) using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro i _
    simp [mul_comm]

/-- Positive Gaudin quadratic form implies strictly convex restriction to
every nonconstant affine line. -/
theorem yangYang_line_strictConvex {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b q : Fin N → ℝ) {v : Fin N → ℝ} (hv : v ≠ 0) :
    StrictConvexOn ℝ univ (fun t : ℝ => yangYang L c b (q + t • v)) := by
  have hm : StrictMono (fun t : ℝ => ∑ i, (logMap L c (q + t • v) i - b i) * v i) := by
    apply strictMono_of_deriv_pos
    intro t
    rw [(yangYang_line_second L hc b q v t).deriv]
    exact gaudin_pos hL hc _ hv
  apply StrictMono.strictConvexOn_univ_of_deriv
    (continuous_iff_continuousAt.mpr (fun t => (yangYang_line_derivative L c b q v t).continuousAt))
  have he : deriv (fun t : ℝ => yangYang L c b (q + t • v)) =
      (fun t => ∑ i, (logMap L c (q + t • v) i - b i) * v i) := by
    funext t
    exact (yangYang_line_derivative L c b q v t).deriv
  rw [he]
  exact hm

/-- Strict convexity of the source functional on all real configurations,
including collisions and the zero-particle sector. -/
theorem yangYang_strictConvex {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) : StrictConvexOn ℝ univ (yangYang L c b) := by
  refine ⟨convex_univ, ?_⟩
  intro q _ r _ hqr a d ha hd had
  have hv : r - q ≠ 0 := sub_ne_zero.mpr hqr.symm
  have h := (yangYang_line_strictConvex hL hc b q hv).2
    (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) (by norm_num) ha hd had
  have he : q + (a • (0 : ℝ) + d • (1 : ℝ)) • (r - q) = a • q + d • r := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_zero,
      mul_one, zero_add]
    linear_combination -q i * had
  simpa only [he, zero_smul, add_zero, one_smul, add_sub_cancel] using h

/-- Every solution of the critical-point equations is a global minimizer,
using the convex supporting-secant inequality on each affine line. -/
theorem solution_isMin {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {b q : Fin N → ℝ} (hq : logMap L c q = b) :
    ∀ r, yangYang L c b q ≤ yangYang L c b r := by
  intro r
  by_cases he : r = q
  · simp [he]
  have hv : r - q ≠ 0 := sub_ne_zero.mpr he
  have hd := yangYang_line_derivative L c b q (r - q) 0
  simp only [zero_smul, add_zero, hq, sub_self, zero_mul, Finset.sum_const_zero] at hd
  have hs := (yangYang_line_strictConvex hL hc b q hv).convexOn.le_slope_of_hasDerivAt
    (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) (by norm_num) hd
  simpa [slope_def_field, sub_nonneg] using hs

/-- Unique critical point by strict convexity and minimization, rather than
maximum-coordinate injectivity. -/
theorem solutions_eq {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {b q r : Fin N → ℝ} (hq : logMap L c q = b) (hr : logMap L c r = b) : q = r := by
  exact (yangYang_strictConvex hL hc b).eq_of_isMinOn
    (fun x _ => solution_isMin hL hc hq x)
    (fun x _ => solution_isMin hL hc hr x) (mem_univ _) (mem_univ _)

/-- Coercive minimization plus strict convexity yields exactly one real
solution, with no root-existence or uniqueness assumption. -/
theorem existsUnique_solution {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) : ∃! q, logMap L c q = b := by
  obtain ⟨q, hq⟩ := yangYang_exists_min hL hc b
  have hs := yangYang_min_solves L c b q hq
  exact ⟨q, hs, fun r hr => solutions_eq hL hc hr hs⟩

/-- Identify the frozen selected minimizer using convexity uniqueness. -/
theorem eq_root {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {b q : Fin N → ℝ} (hq : logMap L c q = b) : q = BetheSmooth.root L b c :=
  solutions_eq hL hc hq (BetheSmooth.root_solves hL hc b)

/-- The printed implicit-function step, identifying local branches by the
strict-convexity uniqueness theorem above. -/
theorem root_contDiffAt {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) : ContDiffAt ℝ ∞ (BetheSmooth.root L b) c := by
  let q := BetheSmooth.root L b c
  let f := fun p : ℝ × (Fin N → ℝ) => logMap L p.1 p.2
  have hs : ContDiffAt ℝ ∞ f (c, q) := BetheSmooth.logMap_contDiffAt L hc.ne' q
  have hi : (fderiv ℝ f (c, q) ∘L
      ContinuousLinearMap.inr ℝ ℝ (Fin N → ℝ)).IsInvertible := by
    rw [BetheSmooth.logMap_partial_q L hc q]
    exact BetheSmooth.gaudin_isInvertible hL hc q
  let ψ := hs.implicitFunction (by simp) hi
  have he : BetheSmooth.root L b =ᶠ[𝓝 c] ψ := by
    filter_upwards [hs.eventually_apply_implicitFunction (by simp) hi,
      isOpen_Ioi.mem_nhds hc] with d hd hdpos
    exact (eq_root hL hdpos (hd.trans (BetheSmooth.root_solves hL hc b))).symm
  exact (hs.contDiffAt_implicitFunction (by simp) hi).congr_of_eventuallyEq he

theorem root_contDiffOn {N : ℕ} {L : ℝ} (hL : 0 < L) (b : Fin N → ℝ) :
    ContDiffOn ℝ ∞ (BetheSmooth.root L b) (Ioi 0) :=
  fun _c hc => (root_contDiffAt hL hc b).contDiffWithinAt

/-- Full R-4C8D7C9E statement via coercive Yang--Yang minimization,
strict-convexity uniqueness and Gaudin implicit functions. The order and
radial norm bound reuse exactly the printed-route constituents.
The frozen root curve is unchanged; only its justification is repaired. -/
theorem source_roots_spec {N : ℕ} {L : ℝ} (hL : 0 < L)
    {n : Fin N → ℤ} (hn : Antitone n) :
    ContDiffOn ℝ ∞ (BetheSmooth.sourceRoots L n) (Ioi 0) ∧
    ∀ c : ℝ, 0 < c →
      logMap L c (BetheSmooth.sourceRoots L n c) =
        (fun i => 2 * Real.pi * BetheSmooth.sourceNumbers n i) ∧
      StrictAnti (BetheSmooth.sourceRoots L n c) ∧
      Real.sqrt (∑ i, (BetheSmooth.sourceRoots L n c i)^2) ≤
        2 * Real.pi * Real.sqrt (∑ i, (BetheSmooth.sourceNumbers n i)^2) / L ∧
      ∀ q, logMap L c q = (fun i => 2 * Real.pi * BetheSmooth.sourceNumbers n i) →
        q = BetheSmooth.sourceRoots L n c := by
  refine ⟨root_contDiffOn hL _, fun c hc =>
    ⟨BetheSmooth.sourceRoots_solves hL hc n, BetheSmooth.sourceRoots_strictAnti hL hc hn,
      BetheSmooth.sourceRoots_norm_bound hL hc n, ?_⟩⟩
  intro q hq
  exact eq_root hL hc hq

/-- Literal erased-diagonal equations, with the source's decreasing
zero-based correction displayed rather than hidden in a forcing variable. -/
theorem source_roots_printed {N : ℕ} {L : ℝ} (hL : 0 < L)
    {n : Fin N → ℤ} (hn : Antitone n) :
    ∃ Q : ℝ → (Fin N → ℝ), ContDiffOn ℝ ∞ Q (Ioi 0) ∧
      ∀ c : ℝ, 0 < c →
        (∀ i, L * Q c i + 2 * ∑ j ∈ Finset.univ.erase i,
          Real.arctan ((Q c i - Q c j) / c) =
          2 * Real.pi * ((n i : ℝ) + ((N : ℝ) - 1) / 2 - (i.val : ℝ))) ∧
        StrictAnti (Q c) ∧
        Real.sqrt (∑ i, (Q c i)^2) ≤
          2 * Real.pi * Real.sqrt (∑ i,
            ((n i : ℝ) + ((N : ℝ) - 1) / 2 - (i.val : ℝ))^2) / L ∧
        (∀ q : Fin N → ℝ,
          (∀ i, L * q i + 2 * ∑ j ∈ Finset.univ.erase i,
            Real.arctan ((q i - q j) / c) =
            2 * Real.pi * ((n i : ℝ) + ((N : ℝ) - 1) / 2 - (i.val : ℝ))) →
          q = Q c) := by
  obtain ⟨hs, hall⟩ := source_roots_spec hL hn
  refine ⟨BetheSmooth.sourceRoots L n, hs, fun c hc => ?_⟩
  obtain ⟨he, ho, hb, hu⟩ := hall c hc
  refine ⟨?_, ho, hb, ?_⟩
  · intro i
    simpa only [logMap_erase, BetheSmooth.sourceNumbers] using congrFun he i
  · intro q hq
    apply hu q
    funext i
    simpa only [logMap_erase, BetheSmooth.sourceNumbers] using hq i

end QuantumNLS.BetheConvexity

#print axioms QuantumNLS.BetheConvexity.yangYang_line_derivative
#print axioms QuantumNLS.BetheConvexity.yangYang_line_second
#print axioms QuantumNLS.BetheConvexity.yangYang_line_strictConvex
#print axioms QuantumNLS.BetheConvexity.yangYang_strictConvex
#print axioms QuantumNLS.BetheConvexity.solution_isMin
#print axioms QuantumNLS.BetheConvexity.solutions_eq
#print axioms QuantumNLS.BetheConvexity.existsUnique_solution
#print axioms QuantumNLS.BetheConvexity.eq_root
#print axioms QuantumNLS.BetheConvexity.root_contDiffAt
#print axioms QuantumNLS.BetheConvexity.root_contDiffOn
#print axioms QuantumNLS.BetheConvexity.source_roots_spec
#print axioms QuantumNLS.BetheConvexity.source_roots_printed

/- Compile-time proof-dependency audit: the literal package must reach
strict convexity/minimization and must not reach the old uniqueness route.
This command adds no mathematical assumption or declaration. -/
set_option maxHeartbeats 2000000 in
run_cmd do
  let env ← Lean.getEnv
  let forbidden : Array Lean.Name := #[
    ``QuantumNLS.BetheAdmission.logMap_injective,
    ``QuantumNLS.BetheSmooth.eq_root,
    ``QuantumNLS.BetheSmooth.root_contDiffAt,
    ``QuantumNLS.BetheSmooth.root_contDiffOn,
    ``QuantumNLS.BetheSmooth.source_roots_spec,
    ``QuantumNLS.BetheRoots.roots_existsUnique,
    ``QuantumNLS.BetheRoots.sorted_roots_existsUnique]
  let mut pending := #[``QuantumNLS.BetheConvexity.source_roots_printed,
    ``QuantumNLS.BetheConvexity.existsUnique_solution]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if forbidden.contains n then
        throwError "Convexity route reached forbidden alternate uniqueness declaration: {n}"
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheConvexity.yangYang_strictConvex,
      ``QuantumNLS.BetheConvexity.solutions_eq,
      ``QuantumNLS.BetheRoots.gaudin_pos,
      ``QuantumNLS.BetheRoots.yangYang_exists_min] do
    unless seen.contains n do
      throwError "Convexity route missed required declaration: {n}"
  Lean.logInfo m!"Convexity route audit passed: {seen.size} transitive constants; strict convexity, Gaudin positivity and minimization reached; seven alternate uniqueness declarations excluded."
