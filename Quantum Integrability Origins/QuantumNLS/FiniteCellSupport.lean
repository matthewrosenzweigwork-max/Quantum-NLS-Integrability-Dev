import QuantumNLS.FullOccupationAffinity

/-! R-D8BB052C, group A: complete-array support geometry and scalar polar completion.
Every coordinate is a complete Arr N. No selected exterior cutoff is imposed.
All constructions here are independent of any vector, target, and EXT-001. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate ENNReal Classical
namespace QuantumNLS.FiniteCellSupport
open Occupation OccupationHilbert FullOccupationAffinity
variable {N : ℕ}

/-- The actual complete-array donor bijection, including its inverse support. -/
def donorEquiv (a b : ℤ) (hab : a ≠ b) : Donor N a ≃ Donor N b where
  toFun m := ⟨destination N a b m, donorOK_shift_receiver hab⟩
  invFun m := ⟨destination N b a m, donorOK_shift_receiver hab.symm⟩
  left_inv m := by
    apply Subtype.ext; apply Subtype.ext
    exact shift_shift_reverse m.2
  right_inv m := by
    apply Subtype.ext; apply Subtype.ext
    exact shift_shift_reverse m.2

theorem destination_reverse (a b : ℤ) (hab : a ≠ b) (m : Donor N a) :
    destination N b a (donorEquiv a b hab m) = m.1 :=
  congrArg Subtype.val ((donorEquiv a b hab).left_inv m)

theorem destination_exterior (a b c : ℤ) (hca : c ≠ a) (hcb : c ≠ b)
    (m : Donor N a) : (destination N a b m).1 c = m.1.1 c :=
  shift_apply_exterior m.1.1 hca hcb

theorem destination_range (a b : ℤ) (hab : a ≠ b) (m : Arr N) :
    (∃ d : Donor N a, destination N a b d = m) ↔ DonorOK b m.1 := by
  constructor
  · rintro ⟨d, rfl⟩; exact donorOK_shift_receiver hab
  · intro hd
    exact ⟨(donorEquiv a b hab).symm ⟨m, hd⟩,
      congrArg Subtype.val ((donorEquiv a b hab).apply_symm_apply ⟨m, hd⟩)⟩

/-- Equality on all elementary vectors determines a bounded map on an arbitrary ℓ². -/
theorem l2_ext_single {I : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : L2 I →L[ℂ] E} (h : ∀ i z, A (lp.single 2 i z) = B (lp.single 2 i z)) : A = B := by
  apply ContinuousLinearMap.ext
  intro v
  exact ((lp.hasSum_single (by norm_num) v).mapL A).unique
    (by simpa only [h] using (lp.hasSum_single (by norm_num) v).mapL B)

theorem inject_at_image {I J : Type*} (f : I → J) (hf : Function.Injective f)
    (v : L2 I) (i : I) : injectL2 f hf v (f i) = v i := by
  have h := (injectL2 f hf).inner_map_map (lp.single 2 i 1) v
  simpa only [injectL2_single, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using h

theorem inject_off_image {I J : Type*} (f : I → J) (hf : Function.Injective f)
    (v : L2 I) (j : J) (hj : ∀ i, f i ≠ j) : injectL2 f hf v j = 0 := by
  classical
  have h : (lp.evalCLM ℂ (fun _ : J => ℂ) 2 j).comp (injectL2 f hf).toContinuousLinearMap = 0 := by
    apply l2_ext_single
    intro i z
    simp [injectL2_single, lp.evalCLM, lp.single_apply, Pi.single_eq_of_ne (hj i).symm]
  exact congrArg (fun A : L2 I →L[ℂ] ℂ => A v) h

theorem restrict_inject {I J : Type*} (f : I → J) (hf : Function.Injective f) (v : L2 I) :
    restrictL2 f hf (injectL2 f hf v) = v := by
  apply lp.ext; funext i
  rw [restrictL2_apply]
  exact inject_at_image f hf v i

/-- Orthogonal support projection, constructed by restriction and extension by zero. -/
def support (a : ℤ) : H N →L[ℂ] H N :=
  (injectL2 (Subtype.val : Donor N a → Arr N) Subtype.val_injective).toContinuousLinearMap ∘L
    restrictL2 (Subtype.val : Donor N a → Arr N) Subtype.val_injective

theorem support_apply (a : ℤ) (v : H N) (m : Arr N) :
    support a v m = if DonorOK a m.1 then v m else 0 := by
  classical
  by_cases hd : DonorOK a m.1
  · rw [ite_eq_left hd]
    exact (inject_at_image _ Subtype.val_injective _ (⟨m, hd⟩ : Donor N a)).trans
      (restrictL2_apply _ _ _ _)
  · rw [ite_eq_right hd]
    exact inject_off_image (Subtype.val : Donor N a → Arr N) Subtype.val_injective _ m
      (fun i hi => hd (hi ▸ i.2))

theorem support_idempotent (a : ℤ) : support (N := N) a ∘L support a = support a := by
  ext v m
  simp only [ContinuousLinearMap.comp_apply, support_apply]
  split_ifs <;> rfl

theorem support_adjoint (a : ℤ) : (support (N := N) a).adjoint = support a := by
  simp only [support, restrictL2, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- Actual initial and final supports of the complete-array injection. -/
theorem destination_projection (a b : ℤ) (hab : a ≠ b) :
    (injectL2 (destination N a b) (destination_injective N a b)).toContinuousLinearMap ∘L
      restrictL2 (destination N a b) (destination_injective N a b) = support b := by
  ext v m
  by_cases hd : DonorOK b m.1
  · let d := (donorEquiv a b hab).symm ⟨m, hd⟩
    have he : destination N a b d = m := congrArg Subtype.val
      ((donorEquiv a b hab).apply_symm_apply ⟨m, hd⟩)
    change injectL2 (destination N a b) (destination_injective N a b) _ m = _
    have h := inject_at_image (destination N a b) (destination_injective N a b)
      (restrictL2 (destination N a b) (destination_injective N a b) v) d
    rw [restrictL2_apply, he] at h
    exact h.trans (by rw [support_apply, ite_eq_left hd])
  · rw [support_apply, ite_eq_right hd]
    exact inject_off_image (destination N a b) (destination_injective N a b) _ m
      (fun i hi => hd ((destination_range a b hab m).mp ⟨i, hi⟩))

/-- Unit scalar completion; zero polar coefficients are assigned exactly 1. -/
def completePhase (z : ℂ) : Phase :=
  ⟨if z = 0 then 1 else z / (‖z‖ : ℂ), by
    split_ifs with hz
    · exact norm_one
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hz)]⟩

theorem completePhase_zero : (completePhase 0).1 = 1 := by simp [completePhase]

theorem completePhase_nonzero (z : ℂ) (hz : z ≠ 0) :
    (completePhase z).1 = z / (‖z‖ : ℂ) := by simp [completePhase, hz]

theorem completePhase_polar (z : ℂ) : (completePhase z).1 * (‖z‖ : ℂ) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [completePhase_nonzero z hz, div_mul_cancel₀]
    exact_mod_cast norm_ne_zero_iff.mpr hz

/-- One chosen forward seed; the reverse will be imposed from this choice. -/
def completedSeed (a b : ℤ) (c : Donor N a → ℂ) : H N →L[ℂ] H N :=
  transfer a b (fun m => completePhase (c m))

/-- Reverse coefficients are conjugates at the inverse full-array edge. -/
def reversePhase (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase) (d : Donor N b) : Phase :=
  ⟨conj (α ((donorEquiv a b hab).symm d)).1, by
    rw [Complex.norm_conj, (α _).2]⟩

/-- Exact forward edge coefficient, valid for every ℓ² vector. -/
theorem transfer_at_destination (a b : ℤ) (α : Donor N a → Phase) (v : H N) (m : Donor N a) :
    transfer a b α v (destination N a b m) = (α m).1 * v m.1 := by
  change injectL2 (destination N a b) (destination_injective N a b)
    (diagonal (fun m => (α m).1) 1 zero_le_one (fun m => (α m).2.le)
      (sourceCoefficients a v)) (destination N a b m) = _
  rw [inject_at_image, diagonal_apply, sourceCoefficients, restrictL2_apply]

theorem transfer_off_receiver (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase)
    (v : H N) (m : Arr N) (hd : ¬ DonorOK b m.1) : transfer a b α v m = 0 := by
  exact inject_off_image (destination N a b) (destination_injective N a b) _ m
    (fun i hi => hd ((destination_range a b hab m).mp ⟨i, hi⟩))

/-- Unit multiplication preserves the actual donor restriction norm. -/
theorem transfer_norm (a b : ℤ) (α : Donor N a → Phase) (v : H N) :
    ‖transfer a b α v‖ = ‖sourceCoefficients a v‖ := by
  change ‖injectL2 (destination N a b) (destination_injective N a b)
    (diagonal (fun m => (α m).1) 1 zero_le_one (fun m => (α m).2.le)
      (sourceCoefficients a v))‖ = _
  rw [LinearIsometry.norm_map]
  apply le_antisymm
  · exact lp.norm_mono (by norm_num) (fun i => by
      simp only [diagonal_apply, norm_mul, (α i).2, one_mul]; rfl)
  · exact lp.norm_mono (by norm_num) (fun i => by
      simp only [diagonal_apply, norm_mul, (α i).2, one_mul]; rfl)

/-- The actual Hilbert adjoint coefficient, including zero on empty donors. -/
theorem transfer_adjoint_apply (a b : ℤ) (α : Donor N a → Phase) (v : H N) (m : Arr N) :
    (transfer a b α).adjoint v m =
      if hd : DonorOK a m.1 then
        conj (α ⟨m, hd⟩).1 * v (shiftArr a b m hd) else 0 := by
  have h := (transfer a b α).adjoint_inner_right (lp.single 2 m 1) v
  rw [transfer_basis] at h
  split_ifs with hd
  · simp only [dite_eq_left hd] at h
    simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one,
      inner_smul_left] using h
  · simp only [dite_eq_right hd] at h
    simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, inner_zero_left] using h

/-- The reverse is imposed as the adjoint of the single chosen forward seed. -/
theorem transfer_adjoint (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase) :
    (transfer a b α).adjoint = transfer b a (reversePhase a b hab α) := by
  ext v m
  rw [transfer_adjoint_apply]
  split_ifs with hd
  · have h := transfer_at_destination b a (reversePhase a b hab α) v
      (donorEquiv a b hab ⟨m, hd⟩)
    rw [destination_reverse] at h
    simp only [reversePhase, Equiv.symm_apply_apply] at h
    exact h.symm
  · exact (transfer_off_receiver b a hab.symm (reversePhase a b hab α) v m hd).symm

theorem phase_conj_mul (z : Phase) : conj z.1 * z.1 = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, z.2]
  norm_num

theorem transfer_initial_projection (a b : ℤ) (α : Donor N a → Phase) :
    (transfer a b α).adjoint ∘L transfer a b α = support a := by
  ext v m
  rw [ContinuousLinearMap.comp_apply, transfer_adjoint_apply, support_apply]
  split_ifs with hd
  · rw [show shiftArr a b m hd = destination N a b ⟨m, hd⟩ from rfl,
      transfer_at_destination, ← mul_assoc, phase_conj_mul, one_mul]
  · rfl

theorem transfer_final_projection (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase) :
    transfer a b α ∘L (transfer a b α).adjoint = support b := by
  have h := transfer_initial_projection b a (reversePhase a b hab α)
  rw [← transfer_adjoint a b hab α, ContinuousLinearMap.adjoint_adjoint] at h
  exact h

theorem transfer_support_norm (a b : ℤ) (α : Donor N a → Phase) (v : H N) :
    ‖transfer a b α v‖ = ‖support a v‖ := by
  rw [transfer_norm]
  exact ((injectL2 (Subtype.val : Donor N a → Arr N) Subtype.val_injective).norm_map _).symm

theorem transfer_adjoint_support_norm (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase)
    (v : H N) : ‖(transfer a b α).adjoint v‖ = ‖support b v‖ := by
  rw [transfer_adjoint a b hab α, transfer_support_norm]

/-- The completed forward and imposed reverse are both literal FOA1 instances. -/
theorem completedSeed_adjoint (a b : ℤ) (hab : a ≠ b) (c : Donor N a → ℂ) :
    (completedSeed a b c).adjoint =
      transfer b a (reversePhase a b hab (fun m => completePhase (c m))) :=
  transfer_adjoint a b hab _

theorem completePhase_unit (z : ℂ) (hz : ‖z‖ = 1) : (completePhase z).1 = z := by
  have hn : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  rw [completePhase_nonzero z hn, hz]
  simp

theorem donorEquiv_symm (a b : ℤ) (hab : a ≠ b) :
    (donorEquiv (N := N) a b hab).symm = donorEquiv b a hab.symm := rfl

theorem reversePhase_reverse (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase) :
    reversePhase b a hab.symm (reversePhase a b hab α) = α := by
  funext m; apply Subtype.ext
  simp only [reversePhase, ← donorEquiv_symm a b hab, Equiv.symm_symm,
    Equiv.symm_apply_apply, starRingEnd_self_apply]

/-- One seed for each unordered pair, represented by its increasing orientation. -/
abbrev OrderedSeeds (N : ℕ) := ∀ (a b : ℤ), a < b → Donor N a → ℂ

/-- Completion is chosen once in the increasing direction; the other is its reverse. -/
def seedPhase (c : OrderedSeeds N) (a b : ℤ) (hab : a ≠ b) : Donor N a → Phase :=
  if h : a < b then fun m => completePhase (c a b h m)
  else reversePhase b a hab.symm (fun m => completePhase (c b a (by omega) m))

theorem seedPhase_reverse (c : OrderedSeeds N) (a b : ℤ) (hab : a ≠ b) :
    seedPhase c b a hab.symm = reversePhase a b hab (seedPhase c a b hab) := by
  by_cases h : a < b
  · simp only [seedPhase, dite_eq_left h, dite_eq_right (not_lt_of_gt h)]
  · have h' : b < a := by omega
    simp only [seedPhase, dite_eq_left h', dite_eq_right h, reversePhase_reverse]

def seedTransfer (c : OrderedSeeds N) (a b : ℤ) (hab : a ≠ b) : H N →L[ℂ] H N :=
  transfer a b (seedPhase c a b hab)

theorem seedTransfer_adjoint (c : OrderedSeeds N) (a b : ℤ) (hab : a ≠ b) :
    (seedTransfer c a b hab).adjoint = seedTransfer c b a hab.symm := by
  change (transfer a b (seedPhase c a b hab)).adjoint = transfer b a (seedPhase c b a hab.symm)
  rw [transfer_adjoint a b hab, seedPhase_reverse c a b hab]

end QuantumNLS.FiniteCellSupport

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellSupport.donorEquiv
#print axioms QuantumNLS.FiniteCellSupport.destination_reverse
#print axioms QuantumNLS.FiniteCellSupport.destination_exterior
#print axioms QuantumNLS.FiniteCellSupport.destination_range
#print axioms QuantumNLS.FiniteCellSupport.l2_ext_single
#print axioms QuantumNLS.FiniteCellSupport.inject_at_image
#print axioms QuantumNLS.FiniteCellSupport.inject_off_image
#print axioms QuantumNLS.FiniteCellSupport.restrict_inject
#print axioms QuantumNLS.FiniteCellSupport.support
#print axioms QuantumNLS.FiniteCellSupport.support_apply
#print axioms QuantumNLS.FiniteCellSupport.support_idempotent
#print axioms QuantumNLS.FiniteCellSupport.support_adjoint
#print axioms QuantumNLS.FiniteCellSupport.destination_projection
#print axioms QuantumNLS.FiniteCellSupport.completePhase
#print axioms QuantumNLS.FiniteCellSupport.completePhase_zero
#print axioms QuantumNLS.FiniteCellSupport.completePhase_nonzero
#print axioms QuantumNLS.FiniteCellSupport.completePhase_polar
#print axioms QuantumNLS.FiniteCellSupport.completedSeed
#print axioms QuantumNLS.FiniteCellSupport.reversePhase
#print axioms QuantumNLS.FiniteCellSupport.transfer_at_destination
#print axioms QuantumNLS.FiniteCellSupport.transfer_off_receiver
#print axioms QuantumNLS.FiniteCellSupport.transfer_norm
#print axioms QuantumNLS.FiniteCellSupport.transfer_adjoint_apply
#print axioms QuantumNLS.FiniteCellSupport.transfer_adjoint
#print axioms QuantumNLS.FiniteCellSupport.phase_conj_mul
#print axioms QuantumNLS.FiniteCellSupport.transfer_initial_projection
#print axioms QuantumNLS.FiniteCellSupport.transfer_final_projection
#print axioms QuantumNLS.FiniteCellSupport.transfer_support_norm
#print axioms QuantumNLS.FiniteCellSupport.transfer_adjoint_support_norm
#print axioms QuantumNLS.FiniteCellSupport.completedSeed_adjoint
#print axioms QuantumNLS.FiniteCellSupport.completePhase_unit
#print axioms QuantumNLS.FiniteCellSupport.donorEquiv_symm
#print axioms QuantumNLS.FiniteCellSupport.reversePhase_reverse
#print axioms QuantumNLS.FiniteCellSupport.OrderedSeeds
#print axioms QuantumNLS.FiniteCellSupport.seedPhase
#print axioms QuantumNLS.FiniteCellSupport.seedPhase_reverse
#print axioms QuantumNLS.FiniteCellSupport.seedTransfer
#print axioms QuantumNLS.FiniteCellSupport.seedTransfer_adjoint

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellSupport.donorEquiv,
    ``QuantumNLS.FiniteCellSupport.destination_reverse,
    ``QuantumNLS.FiniteCellSupport.destination_exterior,
    ``QuantumNLS.FiniteCellSupport.destination_range,
    ``QuantumNLS.FiniteCellSupport.l2_ext_single,
    ``QuantumNLS.FiniteCellSupport.inject_at_image,
    ``QuantumNLS.FiniteCellSupport.inject_off_image,
    ``QuantumNLS.FiniteCellSupport.restrict_inject,
    ``QuantumNLS.FiniteCellSupport.support,
    ``QuantumNLS.FiniteCellSupport.support_apply,
    ``QuantumNLS.FiniteCellSupport.support_idempotent,
    ``QuantumNLS.FiniteCellSupport.support_adjoint,
    ``QuantumNLS.FiniteCellSupport.destination_projection,
    ``QuantumNLS.FiniteCellSupport.completePhase,
    ``QuantumNLS.FiniteCellSupport.completePhase_zero,
    ``QuantumNLS.FiniteCellSupport.completePhase_nonzero,
    ``QuantumNLS.FiniteCellSupport.completePhase_polar,
    ``QuantumNLS.FiniteCellSupport.completedSeed,
    ``QuantumNLS.FiniteCellSupport.reversePhase,
    ``QuantumNLS.FiniteCellSupport.transfer_at_destination,
    ``QuantumNLS.FiniteCellSupport.transfer_off_receiver,
    ``QuantumNLS.FiniteCellSupport.transfer_norm,
    ``QuantumNLS.FiniteCellSupport.transfer_adjoint_apply,
    ``QuantumNLS.FiniteCellSupport.transfer_adjoint,
    ``QuantumNLS.FiniteCellSupport.phase_conj_mul,
    ``QuantumNLS.FiniteCellSupport.transfer_initial_projection,
    ``QuantumNLS.FiniteCellSupport.transfer_final_projection,
    ``QuantumNLS.FiniteCellSupport.transfer_support_norm,
    ``QuantumNLS.FiniteCellSupport.transfer_adjoint_support_norm,
    ``QuantumNLS.FiniteCellSupport.completedSeed_adjoint,
    ``QuantumNLS.FiniteCellSupport.completePhase_unit,
    ``QuantumNLS.FiniteCellSupport.donorEquiv_symm,
    ``QuantumNLS.FiniteCellSupport.reversePhase_reverse,
    ``QuantumNLS.FiniteCellSupport.OrderedSeeds,
    ``QuantumNLS.FiniteCellSupport.seedPhase,
    ``QuantumNLS.FiniteCellSupport.seedPhase_reverse,
    ``QuantumNLS.FiniteCellSupport.seedTransfer,
    ``QuantumNLS.FiniteCellSupport.seedTransfer_adjoint]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Abstract finite-cell proof reached EXT-001: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"FiniteCellSupport aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
