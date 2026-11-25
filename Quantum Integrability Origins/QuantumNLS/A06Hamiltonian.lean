import QuantumNLS.A06Domains

/-! R-66C3BDD2, A06.tex:217. The contact realization's self-adjointness
and accepted Bethe eigenrelation are exactly the printed hypotheses.
Equality is equality of partial linear maps, hence includes both domains. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace BigOperators LinearPMap
namespace QuantumNLS.A06Hamiltonian
open BetheSpectralCharges BetheCoefficientTransform PhysicalTensor BetheLabels
open BoundedBetheTransfer Ext025B6GraphCore
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- Parseval and the eigenrelation force the contact operator into the
maximal multiplier, without assuming an operator-domain characterization. -/
theorem contact_le (b : BetheBasis L N) (a : MArr N → ℝ)
    (H : HN L N →ₗ.[ℂ] HN L N) (hH : IsSelfAdjoint H)
    (hm : ∀ m, b m ∈ H.domain)
    (he : ∀ m, H ⟨b m,hm m⟩ = (a m : ℂ) • b m) : H ≤ multiplier b a := by
  have hs : H.IsFormalAdjoint H := by
    have h := LinearPMap.adjoint_isFormalAdjoint hH.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hH] at h
  have hc (x : H.domain) (m : MArr N) :
      ⟪b m,H x⟫_ℂ = (a m : ℂ)*⟪b m,(x : HN L N)⟫_ℂ := by
    rw [← hs ⟨b m,hm m⟩ x,he,inner_smul_left]
    simp only [Complex.conj_ofReal]
  have hd : H.domain ≤ (multiplier b a).domain := by
    intro x hx
    change Memℓp (fun m => (a m : ℂ)*b.repr x m) 2
    have hh : (fun m => (a m : ℂ)*b.repr x m) = fun m => b.repr (H ⟨x,hx⟩) m := by
      funext m
      simpa only [HilbertBasis.repr_apply_apply] using (hc ⟨x,hx⟩ m).symm
    rw [hh]
    exact lp.memℓp _
  refine ⟨hd,?_⟩
  intro x y hxy
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply]
  rw [hc,multiplier_coord,hxy]

/-- Self-adjoint maximality supplies the reverse inclusion. This is
independent of any supplied closure or domain equality. -/
theorem identification (b : BetheBasis L N) (a : MArr N → ℝ)
    (H : HN L N →ₗ.[ℂ] HN L N) (hH : IsSelfAdjoint H)
    (hm : ∀ m, b m ∈ H.domain)
    (he : ∀ m, H ⟨b m,hm m⟩ = (a m : ℂ) • b m) : H = multiplier b a := by
  have hle := contact_le b a H hH hm he
  have hf : H.IsFormalAdjoint (multiplier b a) := by
    intro x y
    have hh := hle.2 (x := x) (y := ⟨x.val,hle.1 x.property⟩) rfl
    rw [hh]
    exact BetheChargeResolution.multiplier_formalAdjoint b a _ y
  have hr := LinearPMap.IsFormalAdjoint.le_adjoint hH.dense_domain hf
  rw [LinearPMap.isSelfAdjoint_def.mp hH] at hr
  exact le_antisymm hle hr

/-- Literal proposition, including the printed squared power-sum domain
and finite Bethe combinations as an operator core. -/
structure Statement (b : BetheBasis L N) (c : ℝ)
    (H : HN L N →ₗ.[ℂ] HN L N) : Prop where
  operator_eq : H = charge b c 2
  domain_eq : H.domain = (charge b c 2).domain
  domain_exact : ∀ x, x ∈ H.domain ↔ Summable (fun m =>
    (∑ j, rapidity L N c m j ^ 2)^2 * ‖⟪b m,x⟫_ℂ‖^2)
  truncation_mem : ∀ (F : Finset (MArr N)) x, projection b (F : Set (MArr N)) x ∈ H.domain
  core : ∀ x (hx : x ∈ H.domain), ∃ hF : ∀ F : Finset (MArr N),
      projection b (F : Set (MArr N)) x ∈ H.domain,
    (∀ F : Finset (MArr N), projection b (F : Set (MArr N)) x ∈ Submodule.span ℂ (Set.range b)) ∧
    Tendsto (fun F : Finset (MArr N) => (projection b (F : Set (MArr N)) x,
      H ⟨projection b (F : Set (MArr N)) x,hF F⟩)) atTop (𝓝 (x,H ⟨x,hx⟩))

/-- Full printed consumer proposition at the unconditional physical basis.
The self-adjoint contact realization and its accepted eigenrelation remain
visible, as in the source; no additional spectral assumption is introduced. -/
theorem R_66C3BDD2 (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N)
    (c : ℝ) (hc : 0 < c) (H : HN L N →ₗ.[ℂ] HN L N)
    (hH : IsSelfAdjoint H)
    (hm : ∀ m, A06Domains.bethe L N hN c hc m ∈ H.domain)
    (he : ∀ m, H ⟨A06Domains.bethe L N hN c hc m,hm m⟩ =
      (eigenvalue L N c 2 m : ℂ) • A06Domains.bethe L N hN c hc m) :
    Statement (A06Domains.bethe L N hN c hc) c H := by
  let b := A06Domains.bethe L N hN c hc
  have heq := identification b (eigenvalue L N c 2) H hH hm he
  change H = charge b c 2 at heq
  subst H
  have hfinite (F : Finset (MArr N)) (x : HN L N) :
      projection b (F : Set (MArr N)) x ∈ (charge b c 2).domain := by
    have hs : Submodule.span ℂ (Set.range b) ≤ (charge b c 2).domain := by
      apply Submodule.span_le.mpr
      rintro _ ⟨m,rfl⟩
      exact basis_mem_domain b _ m
    exact hs (A06Domains.finite_projection_mem b F x)
  change Statement b c (charge b c 2)
  refine ⟨rfl,rfl,?_,hfinite,?_⟩
  · intro x
    simpa only [charge,multiplier,eigenvalue,sq_abs] using mem_domain b (eigenvalue L N c 2) x
  · intro x hx
    refine ⟨fun F => hfinite F x,fun F => A06Domains.finite_projection_mem b F x,?_⟩
    exact A06Domains.individual_core b (eigenvalue L N c 2) x hx
end QuantumNLS.A06Hamiltonian

#print axioms QuantumNLS.A06Hamiltonian.R_66C3BDD2
#print axioms QuantumNLS.A06Hamiltonian.identification
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.A06Hamiltonian" then
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
  Lean.logInfo m!"A06Hamiltonian audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
