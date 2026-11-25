import QuantumNLS.BetheFreeFamily
import QuantumNLS.ContactFormFamily

/-!
Concrete prerequisites of R-9BF8373D for R-8E4D05E7.
Source: periodic_basis.tex:70–85, 301–310; Emsiz 1009.4487v1,
Theorem 2, printed p.4, accepted applicability instance FIN-CORE-E-01.

This module proves the free endpoint eigenrelation by passing to the limit
in the actual resolvent equation. It constructs the same eigenfamily on the
closed half-line in the fixed physical symmetric Hilbert space. The abstract
Dorlas completeness theorem is not an available proved import and is not
asserted here. No positive-coupling dense-span conclusion is introduced.
-/
noncomputable section
open scoped BigOperators Topology InnerProductSpace NNReal
open Filter Set
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.BetheFreeFamily QuantumNLS.BetheWaveContinuity
  QuantumNLS.BetheH1 QuantumNLS.BetheEigen QuantumNLS.ContactOperator

namespace QuantumNLS.BetheContinuityInputs
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The actual continued wave stays in the original symmetric subspace. -/
theorem continuedWave_mem_sym (n : Label (N+1)) (c : ℝ) :
    continuedWave (L := L) n.val n.property c ∈ SymL2 L (N+1) := by
  by_cases hc : 0 < c
  · rw [continuedWave_pos n.property hc]
    exact (valSym (waveH1Sym (L := L) hc n.property)).property
  · simp only [continuedWave, dite_eq_right hc]
    exact freeVector_mem_sym n.val

/-- Fixed-label family in the fixed physical Hilbert space, for all c ≥ 0. -/
def wave (c : ℝ≥0) (n : Label (N+1)) : SymL2 L (N+1) :=
  ⟨continuedWave (L := L) n.val n.property c, continuedWave_mem_sym n c⟩

theorem wave_pos {c : ℝ≥0} (hc : 0 < (c : ℝ)) (n : Label (N+1)) :
    wave (L := L) c n = valSym (waveH1Sym (L := L) hc n.property) := by
  apply Subtype.ext
  exact continuedWave_pos n.property hc

theorem wave_zero (n : Label (N+1)) :
    wave (L := L) 0 n = freeSym (L := L) n := by
  apply Subtype.ext
  exact continuedWave_zero n.property

/-- Norm continuity in the symmetric Hilbert norm, including the endpoint. -/
theorem continuous_wave (n : Label (N+1)) : Continuous (fun c => wave (L := L) c n) := by
  have h : Continuous (fun c : ℝ≥0 => continuedWave (L := L) n.val n.property c) :=
    (continuedWave_continuousOn n.property).comp_continuous NNReal.continuous_coe
      (fun c => c.property)
  exact h.subtype_mk _

theorem wave_ne_zero (c : ℝ≥0) (n : Label (N+1)) : wave (L := L) c n ≠ 0 := by
  by_cases hc : 0 < (c : ℝ)
  · rw [wave_pos hc]
    exact BetheVandermonde.valSym_ne_zero hc n.property
  · have hc0 : c = 0 := NNReal.coe_eq_zero.1 (le_antisymm (not_lt.1 hc) c.property)
    rw [hc0, wave_zero]
    exact freeSym_ne_zero n

/-- Independence holds also at c=0, without an energy simplicity premise. -/
theorem wave_independent (c : ℝ≥0) :
    LinearIndependent ℂ (wave (L := L) c : Label (N+1) → SymL2 L (N+1)) := by
  by_cases hc : 0 < (c : ℝ)
  · have h := BetheVandermonde.waves_independent (L := L) (N := N) hc
    apply LinearIndependent.of_comp ((SymL2 L (N+1)).subtype :
      SymL2 L (N+1) →ₗ[ℂ] L2TN L (N+1))
    convert h using 1
    funext n
    exact continuedWave_pos n.property hc
  · have hc0 : c = 0 := NNReal.coe_eq_zero.1 (le_antisymm (not_lt.1 hc) c.property)
    subst c
    exact linearIndependent_of_ne_zero_of_inner_eq_zero
      (wave_ne_zero 0) (fun n m hne => by
        change ⟪wave (L := L) 0 n, wave (L := L) 0 m⟫_ℂ = 0
        rw [wave_zero, wave_zero]
        exact freeSym_orthogonal hne)

/-- Source free energy, retaining the volume and momentum normalization. -/
def freeEnergy (n : Label (N+1)) : ℝ := ∑ j, (freeRoots L n.val j) ^ 2

omit [Fact (0 < L)] in
theorem freeEnergy_nonneg (n : Label (N+1)) : 0 ≤ freeEnergy (L := L) n :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem energy_zero_limit (n : Label (N+1)) :
    Tendsto (fun c : ℝ => energy L c n.val) (𝓝[>] 0) (𝓝 (freeEnergy (L := L) n)) := by
  have hq := BetheZeroLimitLiteral.first_limit_literal (Fact.out : 0 < L) n.property
  exact tendsto_finsetSum Finset.univ (fun j _ => ((tendsto_pi_nhds.1 hq) j).pow 2)

/-- The actual resolvent, viewed as an operator-valued map on the half-line. -/
def resolvent (c : ℝ≥0) : SymL2 L (N+1) →L[ℂ] SymL2 L (N+1) := Rop c c.property

theorem lipschitz_resolvent :
    LipschitzWith (⟨ContactFormFamily.lipConst L (N+1), ContactFormFamily.lipConst_nonneg⟩ : ℝ≥0)
      (resolvent (L := L) (N := N)) := by
  apply LipschitzWith.of_dist_le_mul
  intro c b
  rw [dist_eq_norm, NNReal.dist_eq]
  exact ContactFormFamily.Rop_lipschitz c.property b.property

theorem continuous_resolvent : Continuous (resolvent (L := L) (N := N)) :=
  lipschitz_resolvent.continuous

/-- The positive-coupling eigenrelation in bounded resolvent form. -/
theorem positive_resolvent_equation {c : ℝ} (hc : 0 < c) (n : Label (N+1)) :
    Rop c hc.le (((energy L c n.val : ℂ) + 1) •
      valSym (waveH1Sym (L := L) hc n.property)) =
      valSym (waveH1Sym (L := L) hc n.property) := by
  obtain ⟨h, he⟩ := BetheEigenGlobal.Hop_eigen (L := L) hc n.property
  have hh := ContactFormTheorem.Rop_Hop_add hc.le
    (⟨valSym (waveH1Sym (L := L) hc n.property), h⟩ : (Hop c hc.le).domain)
  rw [he] at hh
  simpa only [add_smul, one_smul] using hh

/-- The right-hand endpoint limit occurs in the same symmetric Hilbert space. -/
theorem positive_wave_zero_limit (n : Label (N+1)) :
    Tendsto (fun c : Ioi (0 : ℝ) => valSym (waveH1Sym (L := L) c.property n.property))
      (comap (fun c : Ioi (0 : ℝ) => (c : ℝ)) (𝓝[>] 0))
      (𝓝 (freeSym (L := L) n)) := by
  apply tendsto_subtype_rng.2
  have h := (continuedWave_zero_limit (L := L) n.property).comp
    (Filter.tendsto_comap : Tendsto (fun c : Ioi (0 : ℝ) => (c : ℝ))
      (comap (fun c : Ioi (0 : ℝ) => (c : ℝ)) (𝓝[>] 0)) (𝓝[>] 0))
  have he : (fun c : Ioi (0 : ℝ) => continuedWave (L := L) n.val n.property c.val) =
      (fun c : Ioi (0 : ℝ) => (valSym (waveH1Sym (L := L) c.property n.property) :
        L2TN L (N+1))) := by
    funext c
    exact continuedWave_pos n.property c.property
  change Tendsto _ _ (𝓝 (freeVector L n.val))
  rw [← he]
  exact h

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
/-- Endpoint eigenrelation obtained from the positive-coupling resolvent
equations, using operator-norm continuity and the literal free limit. -/
theorem free_resolvent_equation (n : Label (N+1)) :
    Rop 0 le_rfl (((freeEnergy (L := L) n : ℂ) + 1) • freeSym (L := L) n) =
      freeSym (L := L) n := by
  have ht : Tendsto (fun c : ℝ => c.toNNReal) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_real_toNNReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hr := (continuous_resolvent (L := L) (N := N)).continuousAt.tendsto.comp ht
  have hv := (continuous_wave (L := L) n).continuousAt.tendsto.comp ht
  have he := ((Complex.continuous_ofReal.tendsto _).comp (energy_zero_limit (L := L) n)).add_const 1
  have hleft := (isBoundedBilinearMap_apply (𝕜 := ℂ)
    (E := SymL2 L (N+1)) (F := SymL2 L (N+1))).continuous.continuousAt.tendsto.comp
      (hr.prodMk_nhds (he.smul hv))
  have heq : (fun c : ℝ => resolvent (L := L) c.toNNReal
        (((energy L c n.val : ℂ) + 1) • wave (L := L) c.toNNReal n)) =ᶠ[𝓝[>] 0]
      (fun c : ℝ => wave (L := L) c.toNNReal n) := by
    apply eventually_nhdsWithin_of_forall
    intro c hc
    change 0 < c at hc
    have hcoe : (c.toNNReal : ℝ) = c := Real.coe_toNNReal c hc.le
    have hc' : 0 < (c.toNNReal : ℝ) := by simpa only [hcoe] using hc
    change resolvent (L := L) c.toNNReal
      (((energy L c n.val : ℂ) + 1) • wave (L := L) c.toNNReal n) = wave c.toNNReal n
    rw [wave_pos hc']
    simpa only [resolvent, hcoe] using positive_resolvent_equation (L := L) hc n
  have hright := hv.congr' heq.symm
  simpa only [resolvent, wave_zero, NNReal.coe_zero] using tendsto_nhds_unique hleft hright

/-- Literal contact-operator eigenvector at the free endpoint. -/
theorem free_Hop_eigen (n : Label (N+1)) :
    ∃ h : freeSym (L := L) n ∈ (Hop (L := L) (N := N+1) 0 le_rfl).domain,
      Hop 0 le_rfl ⟨freeSym (L := L) n, h⟩ =
        (freeEnergy (L := L) n : ℂ) • freeSym (L := L) n := by
  let g := (((freeEnergy (L := L) n : ℂ) + 1) • freeSym (L := L) n)
  obtain ⟨h, hh⟩ := Hop_Rop (c := 0) le_rfl g
  have he : Rop 0 le_rfl g = freeSym (L := L) n := free_resolvent_equation n
  have hmem : freeSym (L := L) n ∈ (Hop (L := L) (N := N+1) 0 le_rfl).domain := he ▸ h
  have he' : (⟨Rop 0 le_rfl g, h⟩ : (Hop (L := L) (N := N+1) 0 le_rfl).domain) =
      ⟨freeSym (L := L) n, hmem⟩ := Subtype.ext he
  rw [he', he] at hh
  refine ⟨hmem, ?_⟩
  apply add_right_cancel (b := freeSym (L := L) n)
  simpa only [g, add_smul, one_smul] using hh

/-- The source eigenvalue on the closed parameter half-line. -/
def parameterEnergy (c : ℝ≥0) (n : Label (N+1)) : ℝ :=
  if 0 < (c : ℝ) then energy L c n.val else freeEnergy (L := L) n

omit [Fact (0 < L)] in
theorem parameterEnergy_nonneg (c : ℝ≥0) (n : Label (N+1)) :
    0 ≤ parameterEnergy (L := L) c n := by
  unfold parameterEnergy
  split_ifs
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · exact freeEnergy_nonneg n

/-- Every vector is an eigenvector, including at c=0. No completeness input. -/
theorem wave_Hop_eigen (c : ℝ≥0) (n : Label (N+1)) :
    ∃ h : wave (L := L) c n ∈ (Hop (L := L) (N := N+1) c c.property).domain,
      Hop c c.property ⟨wave (L := L) c n, h⟩ =
        (parameterEnergy (L := L) c n : ℂ) • wave (L := L) c n := by
  by_cases hc : 0 < (c : ℝ)
  · simp only [wave_pos hc, parameterEnergy, ite_eq_left hc]
    exact BetheEigenGlobal.Hop_eigen hc n.property
  · have hc0 : c = 0 := NNReal.coe_eq_zero.1 (le_antisymm (not_lt.1 hc) c.property)
    subst c
    simpa only [wave_zero, parameterEnergy, NNReal.coe_zero, lt_self_iff_false, ite_false]
      using free_Hop_eigen (L := L) n

/-- The initial span is dense in the exact same Hilbert space. -/
theorem initial_dense :
    (Submodule.span ℂ (Set.range (wave (L := L) 0 : Label (N+1) →
      SymL2 L (N+1)))).topologicalClosure = ⊤ := by
  have he : (wave (L := L) 0 : Label (N+1) → SymL2 L (N+1)) = freeSym :=
    funext wave_zero
  rw [he]
  exact free_family_complete

/-- The strict-positive convention uses the actual operator H(c)+1,
whose existing implementation is Tinv, with unchanged eigenvectors. -/
theorem shifted_wave_eigen (c : ℝ≥0) (n : Label (N+1)) :
    ∃ h : wave (L := L) c n ∈ (Tinv (L := L) (N := N+1) c c.property).domain,
      Tinv c c.property ⟨wave (L := L) c n, h⟩ =
        ((parameterEnergy (L := L) c n : ℂ) + 1) • wave (L := L) c n := by
  obtain ⟨h, he⟩ := wave_Hop_eigen (L := L) c n
  refine ⟨h, ?_⟩
  change Tinv c c.property ⟨wave (L := L) c n, h⟩ - wave (L := L) c n =
    (parameterEnergy (L := L) c n : ℂ) • wave (L := L) c n at he
  simpa only [add_smul, one_smul] using sub_eq_iff_eq_add.1 he

theorem shifted_positive (c : ℝ≥0)
    (ψ : (Tinv (L := L) (N := N+1) c c.property).domain) :
    ‖(ψ : SymL2 L (N+1))‖ ^ 2 ≤
      (⟪(ψ : SymL2 L (N+1)), Tinv c c.property ψ⟫_ℂ).re := by
  have h := ContactFormTheorem.Hop_domain_nonneg c.property
    (⟨ψ.val, ψ.property⟩ : (Hop (L := L) (N := N+1) c c.property).domain)
  change 0 ≤ (⟪(ψ : SymL2 L (N+1)), Tinv c c.property ψ - ψ.val⟫_ℂ).re at h
  rw [inner_sub_right, Complex.sub_re] at h
  have hself : (⟪(ψ : SymL2 L (N+1)), (ψ : SymL2 L (N+1))⟫_ℂ).re =
      ‖(ψ : SymL2 L (N+1))‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (ψ : SymL2 L (N+1)))
  linarith

/-- Strong right continuity of the inverse shifted operator, obtained from
the proved operator-norm Lipschitz estimate. -/
theorem resolvent_right_strong (c : ℝ≥0) (f : SymL2 L (N+1)) :
    Tendsto (fun d : ℝ≥0 => resolvent (L := L) d f) (𝓝[≥] c)
      (𝓝 (resolvent (L := L) c f)) := by
  have h : Continuous (fun d : ℝ≥0 => resolvent (L := L) d f) :=
    (continuous_resolvent (L := L) (N := N)).clm_apply continuous_const
  exact (h.tendsto c).mono_left nhdsWithin_le_nhds

/-- Normalization is well-defined before a complete orthogonal family has
been established. This declaration makes no basis claim. -/
def unitWave (c : ℝ≥0) (n : Label (N+1)) : SymL2 L (N+1) :=
  (‖wave (L := L) c n‖⁻¹ : ℂ) • wave (L := L) c n

theorem norm_unitWave (c : ℝ≥0) (n : Label (N+1)) : ‖unitWave (L := L) c n‖ = 1 :=
  norm_smul_inv_norm (wave_ne_zero c n)

theorem continuous_unitWave (n : Label (N+1)) :
    Continuous (fun c => unitWave (L := L) c n) := by
  have h : Continuous (fun c : ℝ≥0 => (‖wave (L := L) c n‖ : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_wave (L := L) n).norm
  have hi := h.inv₀ (fun c => Complex.ofReal_ne_zero.2
    (norm_ne_zero_iff.2 (wave_ne_zero (L := L) c n)))
  exact hi.smul (continuous_wave (L := L) n)

/-- All concrete analytic and eigenfamily inputs on the source route.
There is deliberately no positive-parameter dense-span conclusion. -/
theorem continuity_inputs :
    (∀ c : ℝ≥0, IsSelfAdjoint (Tinv (L := L) (N := N+1) c c.property)) ∧
    (∀ c : ℝ≥0, ∀ ψ : (Tinv (L := L) (N := N+1) c c.property).domain,
      ‖(ψ : SymL2 L (N+1))‖ ^ 2 ≤
        (⟪(ψ : SymL2 L (N+1)), Tinv c c.property ψ⟫_ℂ).re) ∧
    (∀ c b : ℝ≥0, c ≤ b → ∀ ψ : VSym L (N+1),
      (Bform c ψ ψ).re ≤ (Bform b ψ ψ).re) ∧
    Continuous (resolvent (L := L) (N := N)) ∧
    IsCompactOperator (resolvent (L := L) (N := N) 0) ∧
    (∀ n : Label (N+1), Continuous (fun c => wave (L := L) c n)) ∧
    (∀ c : ℝ≥0, ∀ n : Label (N+1), wave (L := L) c n ≠ 0) ∧
    (∀ c : ℝ≥0, LinearIndependent ℂ (wave (L := L) (N := N) c)) ∧
    (∀ c : ℝ≥0, ∀ n : Label (N+1),
      ∃ h : wave (L := L) c n ∈ (Tinv (L := L) (N := N+1) c c.property).domain,
        Tinv c c.property ⟨wave (L := L) c n, h⟩ =
          ((parameterEnergy (L := L) c n : ℂ) + 1) • wave (L := L) c n) ∧
    (Submodule.span ℂ (Set.range (wave (L := L) 0 : Label (N+1) →
      SymL2 L (N+1)))).topologicalClosure = ⊤ := by
  exact ⟨fun c => Tinv_isSelfAdjoint c.property, shifted_positive,
    fun c b h ψ => ContactFormFamily.Bform_mono h ψ, continuous_resolvent,
    Hop_compact_resolvent le_rfl, continuous_wave, wave_ne_zero, wave_independent,
    shifted_wave_eigen, initial_dense⟩

end QuantumNLS.BetheContinuityInputs

#print axioms QuantumNLS.BetheContinuityInputs.continuedWave_mem_sym
#print axioms QuantumNLS.BetheContinuityInputs.wave
#print axioms QuantumNLS.BetheContinuityInputs.wave_pos
#print axioms QuantumNLS.BetheContinuityInputs.wave_zero
#print axioms QuantumNLS.BetheContinuityInputs.continuous_wave
#print axioms QuantumNLS.BetheContinuityInputs.wave_ne_zero
#print axioms QuantumNLS.BetheContinuityInputs.wave_independent
#print axioms QuantumNLS.BetheContinuityInputs.freeEnergy
#print axioms QuantumNLS.BetheContinuityInputs.freeEnergy_nonneg
#print axioms QuantumNLS.BetheContinuityInputs.energy_zero_limit
#print axioms QuantumNLS.BetheContinuityInputs.resolvent
#print axioms QuantumNLS.BetheContinuityInputs.lipschitz_resolvent
#print axioms QuantumNLS.BetheContinuityInputs.continuous_resolvent
#print axioms QuantumNLS.BetheContinuityInputs.positive_resolvent_equation
#print axioms QuantumNLS.BetheContinuityInputs.positive_wave_zero_limit
#print axioms QuantumNLS.BetheContinuityInputs.free_resolvent_equation
#print axioms QuantumNLS.BetheContinuityInputs.free_Hop_eigen
#print axioms QuantumNLS.BetheContinuityInputs.parameterEnergy
#print axioms QuantumNLS.BetheContinuityInputs.parameterEnergy_nonneg
#print axioms QuantumNLS.BetheContinuityInputs.wave_Hop_eigen
#print axioms QuantumNLS.BetheContinuityInputs.initial_dense
#print axioms QuantumNLS.BetheContinuityInputs.shifted_wave_eigen
#print axioms QuantumNLS.BetheContinuityInputs.shifted_positive
#print axioms QuantumNLS.BetheContinuityInputs.resolvent_right_strong
#print axioms QuantumNLS.BetheContinuityInputs.unitWave
#print axioms QuantumNLS.BetheContinuityInputs.norm_unitWave
#print axioms QuantumNLS.BetheContinuityInputs.continuous_unitWave
#print axioms QuantumNLS.BetheContinuityInputs.continuity_inputs

/- Proof provenance check for the concrete prerequisites. -/
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let forbidden : Array Lean.Name := #[
    ``QuantumNLS.BetheEigenGlobal.planeCharacter,
    ``QuantumNLS.BetheEigenGlobal.planeCharacters_independent,
    ``QuantumNLS.BetheEigenGlobal.analyticAt_coordinateAnsatz,
    ``QuantumNLS.BetheEigenGlobal.coordinateAnsatz_chamber_nonzero,
    ``QuantumNLS.BetheEigenGlobal.wave_ne_zero,
    ``QuantumNLS.BetheEigenGlobal.chamber_ansatz_independent,
    ``QuantumNLS.BetheEigenGlobal.waves_independent,
    ``linearIndependent_monoidHom]
  let mut pending := #[``QuantumNLS.BetheContinuityInputs.continuity_inputs,
    ``QuantumNLS.BetheContinuityInputs.norm_unitWave,
    ``QuantumNLS.BetheContinuityInputs.continuous_unitWave,
    ``QuantumNLS.BetheContinuityInputs.resolvent_right_strong]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if forbidden.contains n then
        throwError "Continuity inputs reached alternate independence proof: {n}"
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheContinuityInputs.free_resolvent_equation,
      ``QuantumNLS.BetheContinuityInputs.free_Hop_eigen,
      ``QuantumNLS.BetheEigenGlobal.Hop_eigen,
      ``QuantumNLS.BetheEigenGlobal.weak_eigen,
      ``QuantumNLS.BetheVandermonde.waves_independent,
      ``QuantumNLS.BetheVandermonde.valSym_ne_zero,
      ``QuantumNLS.BetheZeroLimitLiteral.first_limit_literal,
      ``QuantumNLS.ContactFormFamily.Rop_lipschitz,
      ``QuantumNLS.ContactFormFamily.Bform_mono,
      ``QuantumNLS.ContactOperator.Tinv_isSelfAdjoint,
      ``QuantumNLS.ContactOperator.Hop_compact_resolvent,
      ``QuantumNLS.BetheFreeFamily.free_family_complete] do
    unless seen.contains n do
      throwError "Concrete continuity route missed required step: {n}"
  Lean.logInfo m!"Continuity-input route PASS: {seen.size} transitive constants; actual positive and free endpoint operator eigenrelations, printed Vandermonde, zero-root limit, form order, norm resolvent continuity and initial free dense span reached; eight alternate independence declarations excluded."
