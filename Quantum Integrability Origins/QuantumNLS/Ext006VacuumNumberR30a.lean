import QuantumNLS.Ext006OneParticleR30a
import QuantumNLS.Ext006Blocks

/-! EXT-006 / PROP-022, fluctuations.tex:110-111,186-188.
The number expectation of the implemented physical vacuum is Tr β*β.
The proof uses the physical Heisenberg annihilation relation and Parseval;
no number moment, determinant, product distribution or domain assertion is
assumed. Implementer construction remains a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.Ext006VacuumNumberR30a
open Occupation OccupationHilbert Ext006BogoliubovAlg Ext006PhysFockCoord
  Ext006PhysQuasifree Ext006OneParticleR30a Ext006PhysicalVacuum Ext006NumberPhase
open scoped ComplexConjugate InnerProductSpace ENNReal
variable {L : ℝ} [Fact (0 < L)]

abbrev Phys := Ext025B3PhysicalSectors.Fock L

def modeBasis : HilbertBasis ℤ ℂ H := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ H)

@[simp] lemma modeBasis_apply (d : ℤ) : modeBasis d = lp.single 2 d (1 : ℂ) := by
  exact modeBasis.repr_self d

variable (V : Phys (L := L) ≃ₗᵢ[ℂ] Phys (L := L))

lemma uvec_zero (n : Occ) : uvec V n 0 = 0 := by
  apply lp.ext; funext c
  rw [uvec_apply, Ann_ket]
  simp

lemma wvec_zero_inner (h : H) (n : Occ) :
    inner ℂ h (wvec V n 0) = inner ℂ (zvec V n) (oneParticle (star h)) := by
  rw [inner_oneParticle_right, lp.inner_eq_tsum]
  apply tsum_congr
  intro c
  rw [wvec_apply, inner_Cre_core, ME_conj]
  simp [lp.star_apply, RCLike.inner_apply, zvec]

/-- The annihilation of VΩ is an actual Fock vector, constructed from a row of β. -/
def annImage (B : H →L[ℂ] H) (d : ℤ) : Phys (L := L) :=
  V ((Phi (L := L)).symm (oneParticle (star (B.adjoint (modeBasis d)))))

lemma annImage_norm (B : H →L[ℂ] H) (d : ℤ) :
    ‖annImage V B d‖ = ‖B.adjoint (modeBasis d)‖ := by
  simp only [annImage, LinearIsometryEquiv.norm_map, norm_oneParticle, norm_star]

lemma annImage_coefficient {A B : H →L[ℂ] H} (hA : HeisAnn V A B) (d : ℤ) (n : Occ) :
    coefficient (annImage V B d) n =
      (Real.sqrt ((n d : ℝ) + 1) : ℂ) * coefficient (V (vac (L := L))) (n + e d) := by
  have he := hA d n 0 (uvec V n 0) (wvec V n 0) (uvec_apply V n 0) (wvec_apply V n 0)
  rw [uvec_zero, map_zero, lp.coeFn_zero, Pi.zero_apply, zero_add, inner_physCore_Cre] at he
  change coefficient (annImage V B d) n =
    (Real.sqrt ((n d : ℝ) + 1) : ℂ) * coefficient (V (physCore (L := L) (ket 0))) (n + e d)
  rw [he]
  have hb : (B (wvec V n 0)) d = inner ℂ (B.adjoint (modeBasis d)) (wvec V n 0) := by
    rw [ContinuousLinearMap.adjoint_inner_left, modeBasis_apply, lp.inner_single_left]
    simp
  rw [hb, wvec_zero_inner]
  rw [← inner_physCore_ket]
  change inner ℂ (physCore (L := L) (ket n))
      (V ((Phi (L := L)).symm (oneParticle (star (B.adjoint (modeBasis d)))))) = _
  have hv := V.inner_map_map (V.symm (physCore (L := L) (ket n)))
    ((Phi (L := L)).symm (oneParticle (star (B.adjoint (modeBasis d)))))
  rw [LinearIsometryEquiv.apply_symm_apply] at hv
  rw [hv]
  have hp := (Phi (L := L)).inner_map_map (V.symm (physCore (L := L) (ket n)))
    ((Phi (L := L)).symm (oneParticle (star (B.adjoint (modeBasis d)))))
  rw [LinearIsometryEquiv.apply_symm_apply] at hp
  exact hp.symm

/-- Per-mode occupation expectation, allowing the value infinity. -/
def modeExpectation (x : Phys (L := L)) (d : ℤ) : ℝ≥0∞ :=
  ∑' m : Occ, (m d : ℝ≥0∞) * Prop023FiniteModeLimit.mass x m

lemma shift_sum (x : Phys (L := L)) (d : ℤ) : modeExpectation x d =
    ∑' n : Occ, ((n d : ℝ≥0∞) + 1) * Prop023FiniteModeLimit.mass x (n + e d) := by
  have hi : Function.Injective (fun n : Occ => n + e d) := add_left_injective _
  have hs : Function.support (fun m : Occ => (m d : ℝ≥0∞) * Prop023FiniteModeLimit.mass x m) ⊆
      Set.range (fun n : Occ => n + e d) := by
    intro m hm
    have hd : m d ≠ 0 := by
      intro h; apply hm; simp [h]
    exact ⟨m - e d, shift_sub_add (Nat.one_le_iff_ne_zero.mpr hd)⟩
  rw [modeExpectation, ← hi.tsum_eq hs]
  simp

lemma modeExpectation_eq_norm {A B : H →L[ℂ] H} (hA : HeisAnn V A B) (d : ℤ) :
    modeExpectation (V (vac (L := L))) d = ENNReal.ofReal (‖B.adjoint (modeBasis d)‖ ^ 2) := by
  rw [shift_sum]
  have he : ∀ n : Occ,
      ((n d : ℝ≥0∞) + 1) * Prop023FiniteModeLimit.mass (V (vac (L := L))) (n + e d) =
        ENNReal.ofReal (‖coefficient (annImage V B d) n‖ ^ 2) := by
    intro n
    rw [annImage_coefficient V hA, Ext006QuasifreeWeak.norm_sq_sqrt_mul _ (by positivity),
      Prop023FiniteModeLimit.mass, ENNReal.ofReal_mul (by positivity)]
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  simp_rw [he]
  have hs := Prop023Number.summable_normSq (annImage V B d)
  have hs' : Summable (fun m => ‖coefficient (annImage V B d) m‖ ^ 2) :=
    hs.congr fun m => by rw [Complex.sq_norm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs',
    sum_sq_eq, annImage_norm]

lemma total_eq_tsum (m : Occ) : (total m : ℝ≥0∞) = ∑' d : ℤ, (m d : ℝ≥0∞) := by
  classical
  rw [tsum_eq_sum (s := m.support) (fun d hd => by
    rw [Finsupp.notMem_support_iff.mp hd]; simp)]
  simp only [total, Finsupp.degree_apply, Nat.cast_sum]

/-- The total physical number expectation is the sum of mode occupations,
with no moment-domain or finiteness hypothesis. -/
lemma numberExpectation_eq_modes (x : Phys (L := L)) :
    numberExpectation (fun n => (n : ℝ≥0∞)) x = ∑' d : ℤ, modeExpectation x d := by
  rw [Prop023FiniteModeLimit.numberExpectation_eq_occupation]
  simp_rw [total_eq_tsum, ← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_comm

/-- The source's two-point identity. The Heisenberg relation supplies the
annihilated vacuum vectors, so no assumed finite-number condition occurs. -/
theorem vacuum_number {A B : H →L[ℂ] H} (hA : HeisAnn V A B) :
    numberExpectation (fun n => (n : ℝ≥0∞)) (V (vac (L := L))) = TraceClass.hsSq modeBasis B := by
  rw [numberExpectation_eq_modes]
  simp_rw [modeExpectation_eq_norm V hA]
  exact (TraceClass.hsSq_eq_hsSq_adjoint modeBasis modeBasis B).symm

/-- Literal positive-trace form of the same identity. -/
theorem vacuum_number_trace {A B : H →L[ℂ] H} (hA : HeisAnn V A B) :
    numberExpectation (fun n => (n : ℝ≥0∞)) (V (vac (L := L))) =
      TraceClass.posTrace (B.adjoint ∘L B) := by
  rw [vacuum_number V hA,
    TraceClass.posTrace_eq modeBasis (ContinuousLinearMap.isPositive_adjoint_comp_self B),
    TraceClass.traceIn_adjoint_comp_self]

/-- Finiteness is a conclusion of the original HS block hypothesis. -/
theorem vacuum_number_finite {A B : H →L[ℂ] H} (hA : HeisAnn V A B)
    (hB : TraceClass.hsSq modeBasis B ≠ ⊤) :
    numberExpectation (fun n => (n : ℝ≥0∞)) (V (vac (L := L))) ≠ ⊤ := by
  rw [vacuum_number V hA]
  exact hB

/-- The two terminal PROP-022 assertions for an implementing physical unitary.
The time-dependent propagator and its implementation are separate inputs;
this theorem does not claim to construct them. -/
theorem implemented_vacuum {A B : H →L[ℂ] H} (hs : Ext006PhysSymplectic.PhysSymplectic A B)
    (hA : HeisAnn V A B) (hC : HeisCre V A B) :
    PhysicalQuasifreeSource (V (vac (L := L))) ∧
    numberExpectation (fun n => (n : ℝ≥0∞)) (V (vac (L := L))) = TraceClass.hsSq modeBasis B :=
  ⟨⟨V, A, B, hs, hA, hC, rfl⟩, vacuum_number V hA⟩

lemma vac_norm : ‖vac (L := L)‖ = 1 := by
  rw [vac, physCore_ket, LinearIsometryEquiv.norm_map, lp.norm_single (by norm_num)]
  exact norm_one

/-- All terminal vacuum claims, including normalization and finite mean, from
the physical symplectic implementation and its original HS block condition. -/
theorem implemented_vacuum_hs {A B : H →L[ℂ] H} (hs : Ext006PhysSymplectic.PhysSymplectic A B)
    (hA : HeisAnn V A B) (hC : HeisCre V A B) (hB : TraceClass.hsSq modeBasis B ≠ ⊤) :
    ‖V (vac (L := L))‖ = 1 ∧ PhysicalQuasifreeSource (V (vac (L := L))) ∧
    numberExpectation (fun n => (n : ℝ≥0∞)) (V (vac (L := L))) =
      TraceClass.posTrace (B.adjoint ∘L B) ∧
    numberExpectation (fun n => (n : ℝ≥0∞)) (V (vac (L := L))) ≠ ⊤ ∧
    TraceClass.IsTraceClass (B.adjoint ∘L B) := by
  refine ⟨?_, (implemented_vacuum V hs hA hC).1, vacuum_number_trace V hA,
    vacuum_number_finite V hA hB, (Ext006Blocks.beta_adjoint_beta_traceClass modeBasis B hB).1⟩
  rw [LinearIsometryEquiv.norm_map, vac_norm]

section OriginalOneParticleSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Matrix of the original physical operator in its fixed orthonormal modes.
This is unitary coordinate transport, with the original complex structure. -/
def coordinateOperator (b : HilbertBasis ℤ ℂ E) (T : E →L[ℂ] E) : H →L[ℂ] H :=
  b.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
    b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace E] in
lemma coordinateOperator_hsSq (b : HilbertBasis ℤ ℂ E) (T : E →L[ℂ] E) :
    TraceClass.hsSq modeBasis (coordinateOperator b T) = TraceClass.hsSq b T := by
  unfold TraceClass.hsSq
  apply tsum_congr
  intro d
  change ENNReal.ofReal (‖b.repr (T (b.repr.symm (modeBasis d)))‖ ^ 2) = _
  rw [modeBasis_apply, HilbertBasis.repr_symm_single, LinearIsometryEquiv.norm_map]

/-- The two-point identity for the original physical beta, rather than its
coordinate matrix. Its HS norm and positive trace are unchanged by transport. -/
theorem vacuum_number_original (b : HilbertBasis ℤ ℂ E) (a beta : E →L[ℂ] E)
    (hA : HeisAnn V (coordinateOperator b a) (coordinateOperator b beta)) :
    numberExpectation (fun n => (n : ℝ≥0∞)) (V (vac (L := L))) =
      TraceClass.posTrace (beta.adjoint ∘L beta) := by
  rw [vacuum_number V hA, coordinateOperator_hsSq,
    TraceClass.posTrace_eq b (ContinuousLinearMap.isPositive_adjoint_comp_self beta),
    TraceClass.traceIn_adjoint_comp_self]

end OriginalOneParticleSpace

end QuantumNLS.Ext006VacuumNumberR30a
#print axioms QuantumNLS.Ext006VacuumNumberR30a.annImage_coefficient
#print axioms QuantumNLS.Ext006VacuumNumberR30a.modeExpectation_eq_norm
#print axioms QuantumNLS.Ext006VacuumNumberR30a.numberExpectation_eq_modes
#print axioms QuantumNLS.Ext006VacuumNumberR30a.vacuum_number
#print axioms QuantumNLS.Ext006VacuumNumberR30a.vacuum_number_trace
#print axioms QuantumNLS.Ext006VacuumNumberR30a.vacuum_number_finite
#print axioms QuantumNLS.Ext006VacuumNumberR30a.implemented_vacuum
#print axioms QuantumNLS.Ext006VacuumNumberR30a.implemented_vacuum_hs

#print axioms QuantumNLS.Ext006VacuumNumberR30a.coordinateOperator_hsSq
#print axioms QuantumNLS.Ext006VacuumNumberR30a.vacuum_number_original

-- Audit every own declaration, including generated constants, and their full
-- proof dependencies. This is an author check, not independent acceptance.
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006VacuumNumberR30a." then
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
  Lean.logInfo m!"Round30a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
