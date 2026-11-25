import QuantumNLS.Prop021ExcitationActionR131
import QuantumNLS.Prop024WWeylPhysical

/-! Excitation preservation by the actual Weyl displacement in the
condensate direction. The closed block graph is used to pass from the
analytic core to the maximal operator domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
open scoped InnerProductSpace Topology
open Filter
namespace QuantumNLS.Prop021ExcitationWeylR131

open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop021ExcitationR130 Prop021ExcitationActionR131 Prop024WWeylPhysical
open Prop022OQuadraticKet Prop022OWeakIdentity Prop022OFormIdentity Prop022OVacuum Occupation OccupationUnitary
open Ext006PhysFockCoord Ext006KernelHilbertSchmidt Ext005Moments Ext005FormCutoffR109
open Ext005MomentEnergyR108 Ext006PhysicalNormBridge.PairTensor
open Ext006StrongFieldR41a Ext006FieldClosureR42a Ext006FieldBoundsR42a
open Ext006BoundedExponentialR43a Ext006AnalyticFieldR42a Ext006EntireFieldR43a
variable {L : ℝ} [Fact (0 < L)]

local notation "OF" => Ext006VacuumRecurrence.Fock
local notation "OD" => Ext006SmoothOperatorsR34a.D
local notation "𝓓" => Prop021ExcitationFockR130.D

private lemma moment_of_occupation (x : OD) (j : ℕ) :
    (Phi (L := L)).symm x.val ∈ momentDomain (L := L) j :=
  Prop022OFormIdentity.smooth_mem x j

private lemma Qo_smooth (u : L2T L) (hu : ‖u‖ = 1) (x : OD) :
    Ext006ModeDomainR33a.Smooth (Qo (L := L) (q u) 0 x.val) := by
  let y := (Phi (L := L)).symm x.val
  have h := (mem_physSmooth_iff_moments (Qp (q u) 0 y)).mpr
    (fun j => by
      rw [← D_eq_Qp u y (moment_of_occupation x 2)]
      exact D_preserves_moments u hu y (moment_of_occupation x) j)
  exact h

private def Qd (u : L2T L) (hu : ‖u‖ = 1) : Module.End ℂ OD where
  toFun x := ⟨Qo (L := L) (q u) 0 x.val, Qo_smooth u hu x⟩
  map_add' x y := by
    apply Subtype.ext
    change Qo (L := L) (q u) 0 (x.val+y.val) = Qo (q u) 0 x.val+Qo (q u) 0 y.val
    unfold Qo
    rw [map_add, Qp_add _ _ _ _ (moment_of_occupation x 2) (moment_of_occupation y 2), map_add]
  map_smul' c x := by
    apply Subtype.ext
    change Qo (L := L) (q u) 0 (c • x.val) = c • Qo (q u) 0 x.val
    unfold Qo
    rw [map_smul, Qp_smul _ _ _ _ (moment_of_occupation x 2), map_smul]

private lemma Qd_physical (u : L2T L) (hu : ‖u‖ = 1) (x : OD) :
    (Phi (L := L)).symm (Qd u hu x).val =
      𝓓 u ⟨(Phi (L := L)).symm x.val, moment_mem_D u _ (moment_of_occupation x 2)⟩ := by
  change (Phi (L := L)).symm (Phi (Qp (q u) 0 ((Phi (L := L)).symm x.val))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact (D_eq_Qp u _ (moment_of_occupation x 2)).symm

private lemma coordinate_force_zero (u v : L2T L) (hu : ‖u‖ = 1) (c : ℂ) (hv : v = c • u) :
    LamH (L := L) (q u) 0 (weylVec v) = 0 := by
  have hzero : bOp (L := L) 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change Ext006PairDensityR40a.contract _ (twoIso (E := L2T L) 0) = 0
    rw [map_zero, map_zero]
  have ha : aOp (q u) ((-Complex.I) • v) = 0 := by
    rw [hv, smul_smul, map_smul, aOp_q_condensate u hu, smul_zero]
  rw [LamH, weylVec, LinearIsometryEquiv.symm_apply_apply, gen, hzero,
    zero_apply, sub_zero, ha, smul_zero, map_zero]

/-- The exact commutator on the smooth core, proved by the frozen form identity
for the literal quadratic coefficients. -/
private lemma field_commutes (u v : L2T L) (hu : ‖u‖ = 1) (c : ℂ) (hv : v = c • u) :
    Commute (Qd u hu) (field (weylVec v)) := by
  let h := weylVec v
  have hq : (q u).adjoint = q u := (q_projection u hu).isSelfAdjoint.adjoint_eq
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have he (z : OD) :
      ⟪z.val,(Qd u hu (field h w)).val⟫_ℂ =
        ⟪z.val,(field h (Qd u hu w)).val⟫_ℂ := by
    have hform := form_identity (q u) hq 0 h z w
    have hz : LamH (L := L) (q u) 0 h = 0 := coordinate_force_zero u v hu c hv
    rw [hz, show field (0 : Ext006BogoliubovAlg.H) = 0 by
        simp [field, Ext006IdentityCyclicR35a.A_zero, Ext006IdentityCyclicR35a.C_zero]] at hform
    have hs := Qo_symm (q u) hq 0 z (field h w)
    have hf := field_symmetric h z (Qd u hu w)
    change ⟪z.val, Qo (L := L) (q u) 0 (field h w).val⟫_ℂ =
      ⟪z.val,(field h (Qd u hu w)).val⟫_ℂ
    rw [← hs, hf]
    change ⟪Qo (L := L) (q u) 0 z.val,(field h w).val⟫_ℂ =
      ⟪(field h z).val,Qo (L := L) (q u) 0 w.val⟫_ℂ
    exact sub_eq_zero.mp (by simpa using hform)
  have hd (z : OF) :
      ⟪z,(Qd u hu (field h w)).val⟫_ℂ = ⟪z,(field h (Qd u hu w)).val⟫_ℂ := by
    refine core_dense.induction_on (p := fun z : OF =>
      ⟪z,(Qd u hu (field h w)).val⟫_ℂ = ⟪z,(field h (Qd u hu w)).val⟫_ℂ) z (isClosed_eq
      ((continuous_id.inner continuous_const) : Continuous (fun z : OF => ⟪z,(Qd u hu (field h w)).val⟫_ℂ))
      (continuous_id.inner continuous_const)) ?_
    intro y
    exact he y.val
  exact ext_inner_left ℂ hd

/-- A componentwise closed graph limit for the same maximal excitation operator. -/
private lemma graph_limit (u : L2T L) {x y : ℕ → Fock L} {x₀ y₀ : Fock L}
    (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto y atTop (𝓝 y₀))
    (hxy : ∀ j n, y j n = excitation u n (x j n)) :
    ∃ d : x₀ ∈ (𝓓 u).domain, 𝓓 u ⟨x₀,d⟩ = y₀ := by
  have he (n : ℕ) : y₀ n = excitation u n (x₀ n) := by
    let ev := lp.evalCLM ℂ (fun m => HN L m) 2 n
    have h1 := (ev.continuous.tendsto y₀).comp hy
    have h2 := ((excitation u n).continuous.tendsto (ev x₀)).comp
      ((ev.continuous.tendsto x₀).comp hx)
    exact tendsto_nhds_unique h1 (h2.congr fun j => (hxy j n).symm)
  have hm : x₀ ∈ (𝓓 u).domain := by
    change Memℓp (fun n => excitation u n (x₀ n)) 2
    simpa only [← he] using lp.memℓp y₀
  refine ⟨hm, ?_⟩
  apply lp.ext
  funext n
  exact (he n).symm

private lemma Qd_particles (u : L2T L) (hu : ‖u‖ = 1) (x : OD) (j : ℕ)
    (hx : ParticleBound j x.val) : ParticleBound j (Qd u hu x).val := by
  let X := (Phi (L := L)).symm x.val
  have hX (n : ℕ) (hn : j < n) : X n = 0 := by
    apply (physicalOccupation L n).injective
    apply lp.ext
    funext m
    rcases m with ⟨m, hm⟩
    subst n
    have he : (Phi (L := L) X) m = x.val m := by
      rw [LinearIsometryEquiv.apply_symm_apply]
    change occupationCoefficient (freeBasis L (total m)) (X (total m)) ⟨m,rfl⟩ = _ at he
    rw [occupationCoefficient_free, hx m hn] at he
    simpa only [map_zero, lp.coeFn_zero, Pi.zero_apply] using he
  intro m hm
  have he := congrArg (fun y : Fock L => Phi y m) (Qd_physical u hu x)
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  rw [he]
  change occupationCoefficient (freeBasis L (total m)) (excitation u (total m) (X (total m)))
    ⟨m,rfl⟩ = 0
  rw [hX _ hm, map_zero]
  simp

private lemma commute_core (u v : L2T L) (hu : ‖u‖ = 1) (c : ℂ) (hv : v = c • u)
    (x : OD) (j : ℕ) (hx : ParticleBound j x.val) :
    let X := (Phi (L := L)).symm x.val
    ∃ hd : printedWeyl v X ∈ (𝓓 u).domain,
      𝓓 u ⟨printedWeyl v X,hd⟩ =
        printedWeyl v (𝓓 u ⟨X,moment_mem_D u X (moment_of_occupation x 2)⟩) := by
  let h := weylVec v
  let A := Qd u hu
  let s := fun x : OD => fun k : ℕ => ∑ n ∈ Finset.range k,
    ((Complex.I * (1 : ℂ))^n/(n.factorial : ℂ)) • ((field h)^n) x
  have hs (w : OD) (k : ℕ) : (s w k).val = ∑ n ∈ Finset.range k, exponentialTerm h 1 w n := by
    simp [s, exponentialTerm]
  have ht (w : OD) {N : ℕ} (hw : ParticleBound N w.val) :
      Tendsto (fun k => (Phi (L := L)).symm (s w k).val) atTop
        (𝓝 (printedWeyl v ((Phi (L := L)).symm w.val))) := by
    rw [printedWeyl_eq_unitary, LinearIsometryEquiv.apply_symm_apply]
    have hu₁ : unitary (weylVec v) 1 w.val = Ext006ExponentialInnerR43a.exponential h 1 w :=
      unitary_core h 1 ⟨w,⟨N,hw⟩⟩
    rw [hu₁]
    have he := ((entire_summable h 1 w hw).hasSum.tendsto_sum_nat)
    simpa only [Function.comp_def, hs, Ext006ExponentialInnerR43a.exponential] using
      ((Phi (L := L)).symm.continuous.tendsto _).comp he
  have hcomm : Commute A (field h) := field_commutes u v hu c hv
  have hp (k : ℕ) : A (s x k) = s (A x) k := by
    simp only [s, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    exact LinearMap.congr_fun (hcomm.pow_right n).eq x
  have hgraph (k n : ℕ) :
      (Phi (L := L)).symm (s (A x) k).val n =
        excitation u n ((Phi (L := L)).symm (s x k).val n) := by
    rw [← hp]
    exact congrArg (fun y : Fock L => y n) (Qd_physical u hu (s x k))
  have hh := graph_limit u (ht x hx) (ht (A x) (Qd_particles u hu x j hx)) hgraph
  simpa only [A, Qd_physical] using hh

/-- Strong commutation on the whole maximal excitation-operator domain. -/
theorem D_weyl_commutes (u v : L2T L) (hu : ‖u‖ = 1) (c : ℂ) (hv : v = c • u)
    (x : (𝓓 u).domain) :
    ∃ hd : printedWeyl v x.val ∈ (𝓓 u).domain,
      𝓓 u ⟨printedWeyl v x.val,hd⟩ = printedWeyl v (𝓓 u x) := by
  have hcut (j : ℕ) :
      ∃ hd : printedWeyl v (cutoff j x.val) ∈ (𝓓 u).domain,
        𝓓 u ⟨printedWeyl v (cutoff j x.val),hd⟩ = printedWeyl v (cutoff j (𝓓 u x)) := by
    let y : physSmooth L := ⟨cutoff j x.val, (mem_physSmooth_iff_moments _).mpr
      (fun p => cutoff_mem p j x.val)⟩
    let z := physToD y
    have hp : ParticleBound j z.val := by
      intro m hm
      change occupationCoefficient (freeBasis L (total m)) (cutoff j x.val (total m)) ⟨m,rfl⟩ = 0
      simp [cutoff_apply, show ¬total m<j by omega]
    have he : (Phi (L := L)).symm z.val = cutoff j x.val :=
      (Phi (L := L)).symm_apply_apply y.val
    obtain ⟨hd,hc⟩ := commute_core u v hu c hv z j hp
    have hd' : printedWeyl v (cutoff j x.val) ∈ (𝓓 u).domain := by
      rw [← he]
      exact hd
    refine ⟨hd', ?_⟩
    have hcc : 𝓓 u ⟨(Phi (L := L)).symm z.val,
        moment_mem_D u _ (moment_of_occupation z 2)⟩ = cutoff j (𝓓 u x) := by
      apply lp.ext
      funext n
      change excitation u n (((Phi (L := L)).symm z.val) n) = _
      rw [he, cutoff_apply, cutoff_apply]
      split_ifs
      · rfl
      · exact map_zero _
    have harg : (⟨printedWeyl v (cutoff j x.val),hd'⟩ : (𝓓 u).domain) =
        ⟨printedWeyl v ((Phi (L := L)).symm z.val),hd⟩ :=
      Subtype.ext (congrArg (fun y : Fock L => printedWeyl v y) he.symm)
    rw [harg, hc, hcc]
  have hl (j n : ℕ) : printedWeyl v (cutoff j (𝓓 u x)) n =
      excitation u n (printedWeyl v (cutoff j x.val) n) := by
    obtain ⟨hd,h⟩ := hcut j
    exact congrArg (fun y : Fock L => y n) h.symm
  exact graph_limit u (((printedWeyl v).continuous.tendsto _).comp (cutoff_tendsto x.val))
    (((printedWeyl v).continuous.tendsto _).comp (cutoff_tendsto (𝓓 u x))) hl

/-- The literal Weyl map is a bijection of the maximal excitation domain. -/
theorem D_weyl_domain_iff (u v : L2T L) (hu : ‖u‖ = 1) (c : ℂ) (hv : v = c • u)
    (x : Fock L) :
    printedWeyl v x ∈ (𝓓 u).domain ↔ x ∈ (𝓓 u).domain := by
  constructor
  · intro hx
    have h := (D_weyl_commutes u (-v) hu (-c) (by rw [hv, neg_smul])
      ⟨printedWeyl v x,hx⟩).choose
    rwa [printedWeyl_neg_apply] at h
  · intro hx
    exact (D_weyl_commutes u v hu c hv ⟨x,hx⟩).choose

/-- Exact excitation-root norm preservation on the second-moment domain.
This is the form identity used in the exact-number extraction. -/
theorem root_weyl_norm (u v : L2T L) (hu : ‖u‖ = 1) (c : ℂ) (hv : v = c • u)
    (x : Fock L) (hx : x ∈ momentDomain (L := L) 2) :
    ∃ (h₁ : x ∈ (Prop021ExcitationFockR130.root u).domain)
      (h₂ : printedWeyl v x ∈ (Prop021ExcitationFockR130.root u).domain),
      ‖Prop021ExcitationFockR130.root u ⟨printedWeyl v x,h₂⟩‖ =
        ‖Prop021ExcitationFockR130.root u ⟨x,h₁⟩‖ := by
  have h₁ := Prop021ExcitationFockR130.moment_mem_root u hu x (domain_mono (by omega) hx)
  have h₂ := Prop021ExcitationFockR130.moment_mem_root u hu (printedWeyl v x)
    (weyl_mem_momentDomain v 1 x (domain_mono (by omega) hx))
  refine ⟨h₁,h₂,?_⟩
  let X : (𝓓 u).domain := ⟨x,moment_mem_D u x hx⟩
  obtain ⟨hw, he⟩ := D_weyl_commutes u v hu c hv X
  have hr := root_inner_eq u hu (printedWeyl v x) hw h₂
  rw [he, LinearIsometryEquiv.inner_map_map, root_inner_eq u hu x X.property h₁] at hr
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact_mod_cast hr.symm

end QuantumNLS.Prop021ExcitationWeylR131

#print axioms QuantumNLS.Prop021ExcitationWeylR131.D_weyl_commutes
#print axioms QuantumNLS.Prop021ExcitationWeylR131.root_weyl_norm

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021ExcitationWeylR131"].any
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
  Lean.logInfo m!"R131 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
