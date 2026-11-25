import QuantumNLS.R52CFLocal
import QuantumNLS.R52CFClause2

/-!
# R-52CF5DA1 `prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101)

> Let `F ⊂ ℤ` be finite. For every `R < ∞`, every fixed marginal rank `k` and every compact box of real times
> `t = (t_n)_{n∈F}`, the actual count evolution has the following limit, uniformly over smooth unit profiles with
> `H¹` norm at most `R`:
> `γ^{(k)}_{exp(-iΣ_{n∈F} t_n M_{N,n}) u^{⊗N}} → |(T_t u)^{⊗k}⟩⟨(T_t u)^{⊗k}|` in trace norm,
> `T_t u = Φ_κ^{-1}((e^{-it_n} Φ_κ(u)_n)_n)`, where `t_n = 0` outside `F`. On the same profile class each fixed
> intensive count has a strong scalar limit `I_n(u)`, uniformly.

**`finite_count_propagation`** states both printed clauses in one theorem, with no hypothesis beyond `L > 0`,
`κ > 0`:
* the realized objects: `M_{N,n} = N·B_{N,n}` (`R52CFEvol.countOp`, `B` the accepted PROP-010 normalized count),
  `exp(-iΣ t_n M_{N,n})` (`R52CFEvol.countEvol`), `u^{⊗N}` (`HighMomentsOps.wvec`), `γ^{(k)}` (DEF-030
  `PhysicalTensor.reducedDensityN`), the trace norm `TraceClass.traceNorm`, `|v^{⊗k}⟩⟨v^{⊗k}|`
  (`Prop001.coherentProjector`), `T_t` the time-one map of the complete flow of `X_{H_t}`, `H_t = Σ t_n I_n`
  (`RF535Final.Tθ`, accepted R-F5355ABD), `I_n = mass` (accepted), the profile class "smooth unit profiles with `H¹`
  norm at most `R`" (`R52CFCompact.profileClass`), the compact box `α_n ≤ t_n ≤ β_n` (`n ∈ F`) and `t_n = 0` off `F`;
* clause 1: for every `ε > 0` there is `N₀` such that the trace-norm distance is `≤ ε` for all `N ≥ N₀`, all
  profiles of the class and all admissible `t`;
* clause 2: for every `n` and `ε > 0` there is `N₀` with `‖(M_{N,n}/N - I_n(u)) u^{⊗N}‖ ≤ ε` uniformly.
The chart statement is supplied by the accepted `RF535Final.global_actual_chart`; the cut data are those of the
accepted PROP-010 `cutoff_probes` on `Prop026Bound.scalarCuts` inside the proofs (stage 10a); no cut-set notion and
no internal data hypothesis appears in the statement.

**`target_eq_chart`** identifies the target: for the global chart `Φ_κ` of the accepted R-F5355ABD (`Ψ = Φ_κ⁻¹`,
`|Φ_κ(u)_n|² = I_n`), the rotated sequence `(e^{-it_n} Φ_κ(u)_n)_n` lies in `ℓ²` and `T_t u = Φ_κ⁻¹` of it.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
open Set Filter Topology

namespace QuantumNLS.R52CFMain

open PhysicalTensor (L2T)
open RootMassInvolutionR8 (mass)
open QuantumNLS.ProductTorusGenerator (Linf)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.RF535Final (Tθ GlobalStatement)
open TensorCarrier TraceClass

variable (L : ℝ) [Fact (0 < L)] {κ : ℝ}

/-- **`prop:audit-finite-count-propagation`** (R-52CF5DA1): both printed clauses. -/
theorem finite_count_propagation (hκ : 0 < κ) (F : Finset ℤ) (R : ℝ) (k : ℕ) (α β : ℤ → ℝ) :
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N) (hk : k ≤ N), N₀ ≤ N →
      ∀ u ∈ R52CFCompact.profileClass L R, ∀ t : Linf, (∀ n ∉ F, t n = 0) →
        (∀ n ∈ F, α n ≤ t n ∧ t n ≤ β n) →
        traceNorm (PhysicalTensor.reducedDensityN N k hk
            (R52CFEvol.countEvol L hκ hN F t (HighMomentsOps.wvec N u) : HilbertTensorPower ℂ (L2T L) N) -
          Prop001.coherentProjector k (Tθ (L := L) hκ t u)) ≤ ENNReal.ofReal ε) ∧
    (∀ n : ℤ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ u ∈ R52CFCompact.profileClass L R,
        ‖(Prop010ContourBindingR11.B L hκ hN n - ((mass hκ n u : ℝ) : ℂ) •
          (1 : BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N))
          (HighMomentsOps.wvec N u)‖ ≤ ε) := by
  refine ⟨?_, fun n ε hε => R52CFClause2.clause2 L hκ R n ε hε⟩
  intro ε hε
  -- the accepted global chart statement at coupling `κ`
  obtain ⟨⟨d, CL, hd, hCL, Φloc, Ψloc, hloc⟩, hglob⟩ := RF535Final.global_actual_chart L
  have hG := hglob d CL Φloc Ψloc hd hCL hloc κ hκ
  -- the box as a bound on `|t_n|`
  set T : ℤ → ℝ := fun n => max |α n| |β n| with hT
  obtain ⟨hK, hunit⟩ := R52CFCompact.closure_compact (L := L) R
  let P : ℕ → L2T L → Prop := fun N v => ∀ (hN : 0 < N) (hk : k ≤ N), ‖v‖ = 1 →
    ∀ t : Linf, (∀ n ∉ F, t n = 0) → (∀ n ∈ F, |t n| ≤ T n) →
      traceNorm (PhysicalTensor.reducedDensityN N k hk
          (R52CFEvol.countEvol L hκ hN F t (HighMomentsOps.wvec N v) : HilbertTensorPower ℂ (L2T L) N) -
        Prop001.coherentProjector k (Tθ (L := L) hκ t v)) ≤ ENNReal.ofReal ε
  obtain ⟨N₀, hN₀⟩ := R52CFCompact.uniform_of_local hK P (fun x hx => by
    obtain ⟨U, hU, ρ, hρ, N₁, hloc'⟩ := R52CFLocal.local_rate hκ hG x (hunit x hx) F T k
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hρ.eventually (ge_mem_nhds hε))
    refine ⟨U, hU, max N₁ N₂, fun N hN v hv hN' hk hv1 t ht0 ht => ?_⟩
    exact (hloc' N hN' hk (le_trans (le_max_left _ _) hN) v hv hv1 t ht0 ht).trans
      (ENNReal.ofReal_le_ofReal (hN₂ N (le_trans (le_max_right _ _) hN))))
  refine ⟨N₀, fun N hN hk hNN u hu t ht0 ht => ?_⟩
  exact hN₀ N hNN u (subset_closure hu) hN hk hu.2.1 t ht0
    (fun n hn => abs_le_max_abs_abs (ht n hn).1 (ht n hn).2)

/-- **The target in the global chart**: `T_t u = Φ_κ⁻¹((e^{-it_n} Φ_κ(u)_n)_n)`. -/
theorem target_eq_chart (hκ : 0 < κ) :
    ∃ (Φ : L2T L → K) (Ψ : K → L2T L), (∀ u, Ψ (Φ u) = u) ∧ (∀ z, Φ (Ψ z) = z) ∧
      (∀ u n, ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n) ∧ (∀ u, ‖Φ u‖ ^ 2 = ‖u‖ ^ 2) ∧
      ∀ (t : Linf) (u : L2T L),
        (∃ z : K, ∀ n, z n = Complex.exp (-(t n : ℂ) * Complex.I) * Φ u n) ∧
        ∀ z : K, (∀ n, z n = Complex.exp (-(t n : ℂ) * Complex.I) * Φ u n) → Tθ (L := L) hκ t u = Ψ z := by
  obtain ⟨⟨d, CL, hd, hCL, Φloc, Ψloc, hloc⟩, hglob⟩ := RF535Final.global_actual_chart L
  have hG := hglob d CL Φloc Ψloc hd hCL hloc κ hκ
  obtain ⟨Y, Fl, Φ, Ψ, -, -, -, -, -, -, -, -, -, hΨΦ, hΦΨ, hact, hn, -, -, -, -, -, -, -, hrot, -, -⟩ := hG.2
  refine ⟨Φ, Ψ, hΨΦ, hΦΨ, hact, hn, fun t u => ⟨⟨Φ (Tθ (L := L) hκ t u), fun n => hrot t u n⟩, ?_⟩⟩
  intro z hz
  have hzΦ : z = Φ (Tθ (L := L) hκ t u) := lp.ext (funext fun n => (hz n).trans (hrot t u n).symm)
  rw [hzΦ, hΨΦ]

end QuantumNLS.R52CFMain

#print axioms QuantumNLS.R52CFMain.finite_count_propagation
#print axioms QuantumNLS.R52CFMain.target_eq_chart

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name :=
    #[`QuantumNLS.R52CFMain.finite_count_propagation, `QuantumNLS.R52CFMain.target_eq_chart]
  let mut seen : Std.HashSet Lean.Name := {}
  let mut mods : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
      if let some idx := env.getModuleIdxFor? n then
        mods := mods.insert env.header.moduleNames[idx.toNat]!
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
  let has (s p : String) : Bool := (s.splitOn p).length > 1
  let held := ((mods.toList.filter fun m =>
    let s := m.toString
    has s "Ext005" || has s "EXT005" || has s "Lns01" || has s "LNS01" || has s "Def035" || has s "DEF035" ||
      has s "Def044" || has s "DEF044" || has s "HeldGP").map toString).toArray.qsort (· < ·)
  let e25 := ((mods.toList.filter fun m => has m.toString "Ext025").map toString).toArray.qsort (· < ·)
  Lean.logInfo m!"R52CFMain audit PASS: {seen.size} transitive constants in {mods.size} modules; standard axioms only; no HeldGP14Tonelli."
  Lean.logInfo m!"Held-contract modules (EXT-005 / LNS-01 / DEF-035 / DEF-044 / HeldGP) in the closure ({held.size}): {held}"
  Lean.logInfo m!"EXT-025 modules in the closure ({e25.size}): {e25}"
