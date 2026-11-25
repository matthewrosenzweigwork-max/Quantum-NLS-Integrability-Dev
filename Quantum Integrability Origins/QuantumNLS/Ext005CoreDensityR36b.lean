import QuantumNLS.Ext005ResolventPerturbR35b
import QuantumNLS.Ext005ForwardEstimateR35b

/-! Source-derived density of the actual invariant B operator core.
The approximants are A-smoothed B resolvents; no Q(A) action of the B
resolvent and no energy bound are assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005CoreDensityR36b
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005SourceHypothesesR114
open Ext005PhysicalResolventR35b Ext005ResolventPerturbR35b
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005ComplexGramR34b
open Ext005CommutatorCoreR35b
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

omit [CompleteSpace H] in
/-- Commutation with a two-sided resolvent implies actual domain invariance
and intertwining of the unbounded operator. -/
lemma resolves_domain_commute (T : H →ₗ.[ℂ] H) (z : ℂ)
    (R M : H →L[ℂ] H) (hR : Resolves T z R)
    (hc : M.comp R = R.comp M) (x : T.domain) :
    ∃ hx : M (x : H) ∈ T.domain, T ⟨M (x : H), hx⟩ = M (T x) := by
  let y := T x - z • (x : H)
  have hy : R y = (x : H) := hR.2 x
  have he : R (M y) = M (x : H) := by
    rw [← hy]
    exact (congrArg (fun L : H →L[ℂ] H => L y) hc).symm
  obtain ⟨hm, ha⟩ := hR.1 (M y)
  have hx : M (x : H) ∈ T.domain := he ▸ hm
  refine ⟨hx, ?_⟩
  have ha' : T ⟨M (x : H), hx⟩ - z • M (x : H) = M y := by
    simpa only [he] using ha
  dsimp [y] at ha'
  rw [map_sub, map_smul] at ha'
  exact sub_left_inj.mp ha'

variable (A : PositiveOperator H) (B : NonnegativeOperator H)
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

/-- The bounded H-to-Q(A) map whose ambient realization is the physical cutoff. -/
def smoothing (r : ℝ) (hr : 0 < r) : H →L[ℂ] FormDomain A :=
  (inverseC (inclusion A) r hr).comp (inclusion A).adjoint

lemma smoothing_pair (r : ℝ) (hr : 0 < r) (x : H) :
    inclusion A (smoothing A r hr x) = physicalCutoffC A r hr x := rfl

lemma physical_embed (e : ℝ) (he : 0 < e) (u : FormDomain A) :
    physicalCutoffC A e he (inclusion A u) =
      inclusion A (cutoff ((inclusion A).restrictScalars ℝ) e he u) := by
  rw [physicalCutoffC_eq]
  exact physicalCutoff_embed _ e he u

lemma physical_tendsto (D : PositiveOperator H) (x : H) :
    Tendsto (fun n => physicalCutoffC D (epsilon n) (epsilon_pos n) x) atTop (𝓝 x) := by
  simp_rw [physicalCutoffC_eq]
  exact P_tendsto ((inclusion D).restrictScalars ℝ) (inclusion_injective D)
    (inclusion_dense D) x

/-- The A cutoff preserves D(B) and intertwines B, derived from the literal
source nonreal-resolvent convention. -/
lemma physical_B_commute (hc : StronglyCommute A.op B.op)
    (r : ℝ) (hr : 0 < r) (x : B.op.domain) :
    ∃ hx : physicalCutoffC A r hr (x : H) ∈ B.op.domain,
      B.op ⟨physicalCutoffC A r hr (x : H), hx⟩ = physicalCutoffC A r hr (B.op x) := by
  let f : ℝ := 1
  have hf : 0 < f := zero_lt_one
  have hR := resolves_unshift B.op 1 (-(f⁻¹:ℝ):ℂ)
    ((f:ℂ) • physicalCutoffC (plusOne B) f hf) (resolves_negative (plusOne B) f hf)
  apply resolves_domain_commute B.op _ _ (physicalCutoffC A r hr) hR _ x
  ext y
  have h := congrArg (fun L : H →L[ℂ] H => L y)
    (source_physical_cutoffs_commute A B hc r f hr hf)
  change physicalCutoffC A r hr ((f:ℂ) • physicalCutoffC (plusOne B) f hf y) =
    (f:ℂ) • physicalCutoffC (plusOne B) f hf (physicalCutoffC A r hr y)
  simpa only [map_smul, comp_apply] using congrArg (fun v : H => (f:ℂ) • v) h

/-- Every A-smoothed B-cutoff vector is in the invariant operator core for
EVERY epsilon, with the B action explicitly represented in Q(A). -/
lemma smoothing_in_core (hc : StronglyCommute A.op B.op)
    (e r f : ℝ) (he : 0 < e) (hr : 0 < r) (hf : 0 < f) (x : H) :
    smoothing A r hr (physicalCutoffC (plusOne B) f hf x) ∈
      cutoffOperatorCore A B e he := by
  let y := physicalCutoffC (plusOne B) f hf x
  obtain ⟨hy, _⟩ := physicalCutoffC_domain (plusOne B) f hf x
  change y ∈ B.op.domain at hy
  obtain ⟨hu, hBu⟩ := physical_B_commute A B hc r hr ⟨y, hy⟩
  let u := smoothing A r hr y
  let v := smoothing A r hr (B.op ⟨y, hy⟩)
  have hv : inclusion A v = B.op ⟨inclusion A u, hu⟩ := hBu.symm
  obtain ⟨hp, hBp⟩ := physical_B_commute A B hc e he ⟨inclusion A u, hu⟩
  have hp' : inclusion A (cutoff ((inclusion A).restrictScalars ℝ) e he u) ∈ B.op.domain := by
    rwa [physical_embed] at hp
  refine ⟨v, hu, hp', hv, ?_⟩
  rw [← physical_embed, hv]
  simpa only [physical_embed] using hBp.symm

/-- Density is an unconditional consequence of the source strong commutation.
First let the B cutoff tend to identity in H at fixed A smoothing, then let
the A cutoff tend to identity in Q(A). -/
theorem cutoffOperatorCore_dense (hc : StronglyCommute A.op B.op)
    (e : ℝ) (he : 0 < e) : Dense (cutoffOperatorCore A B e he) := by
  intro u
  have hsm (r : ℝ) (hr : 0 < r) (x : H) :
      smoothing A r hr x ∈ closure (cutoffOperatorCore A B e he) := by
    apply isClosed_closure.mem_of_tendsto
      ((smoothing A r hr).continuous.tendsto x |>.comp (physical_tendsto (plusOne B) x))
    exact Filter.Eventually.of_forall (fun n => subset_closure
      (smoothing_in_core A B hc e r (epsilon n) he hr (epsilon_pos n) x))
  have ht := C_tendsto ((inclusion A).restrictScalars ℝ) (inclusion_injective A) u
  apply isClosed_closure.mem_of_tendsto ht
  exact Filter.Eventually.of_forall (fun n => by
    have h := hsm (epsilon n) (epsilon_pos n) (inclusion A u)
    have heq : smoothing A (epsilon n) (epsilon_pos n) (inclusion A u) =
        C ((inclusion A).restrictScalars ℝ) n u := by
      apply inclusion_injective A
      exact physical_embed A (epsilon n) (epsilon_pos n) u
    rwa [heq] at h)

end QuantumNLS.Ext005CoreDensityR36b
#print axioms QuantumNLS.Ext005CoreDensityR36b.cutoffOperatorCore_dense

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005CoreDensityR36b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005CoreDensityR36b." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R36b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
