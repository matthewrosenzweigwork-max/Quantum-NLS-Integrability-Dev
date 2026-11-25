import QuantumNLS.Ext006SmearedDomainR33a

/-! The constructed source-HS state satisfies a strong squeezed-annihilation
identity for every ℓ² test vector, on the actual completed carrier. The source
conjugation K=bar(Q P^{-1}) remains explicit. This is not an implementation or
cyclicity assertion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006StrongVacuumR33a
open Occupation Ext006VacuumRecurrence Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006BogoliubovAlg

lemma smooth_add {v w : Occ → ℂ} (hv : Smooth v) (hw : Smooth w) : Smooth (v+w) := by
  intro p
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (pow_nonneg (by positivity) p) (sq_nonneg _))
    (fun m => ?_) (((hv p).add (hw p)).mul_left 2)
  have hn : ‖v m+w m‖^2 ≤ 2*(‖v m‖^2+‖w m‖^2) := by
    have ht := norm_add_le (v m) (w m)
    have hp := pow_le_pow_left₀ (norm_nonneg _) ht 2
    nlinarith [sq_nonneg (‖v m‖-‖w m‖)]
  calc
    _ ≤ ((total m : ℝ)+1)^p*(2*(‖v m‖^2+‖w m‖^2)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by ring

/-- A smooth vector with its already proved domain membership. -/
abbrev SmoothState := {w : Fock // Smooth w}

/-- A general transformed field is constructed for arbitrary two ℓ² rows.
The coefficient pair may come from the actual source blocks. -/
def field (h k : H) (w : SmoothState) : SmoothState :=
  ⟨smearedAnn h w.1 w.2 + smearedCre k w.1 w.2,
    smooth_add (smearedAnn_smooth h w.1 w.2) (smearedCre_smooth k w.1 w.2)⟩

/-- Every finite ordered word of general smeared transformed fields acts
on this common domain; neither intermediate domains nor convergence of the
individual smearings are hypotheses. -/
def fieldWord : List (H × H) → SmoothState → SmoothState
  | [], w => w
  | hk::ops, w => field hk.1 hk.2 (fieldWord ops w)


lemma weak_vector (K : H →L[ℂ] H) (w : Fock)
    (hw : WeakVacuum (fun a b => K (lp.single 2 b 1) a) w) (m : Occ) :
    xvec w m + K (yvec w m) = 0 := by
  apply lp.ext
  funext a
  have hy : (K (yvec w m)) a =
      ∑ b ∈ m.support, K (lp.single 2 b 1) a * (Real.sqrt (m b : ℝ) : ℂ)*w (m-e b) := by
    rw [yvec_eq_sum, map_sum]
    simp only [map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, ycoord]
    apply Finset.sum_congr rfl
    intro b _
    ring
  change xcoord w m a + (K (yvec w m)) a = 0
  rw [hy, xcoord, hw a m, neg_add_cancel]

lemma inner_K_y (K : H →L[ℂ] H) (h : H) (w : Fock) (m : Occ) :
    inner ℂ h (K (yvec w m)) =
      smearedCreCoeff (star (K.adjoint h)) w m := by
  rw [← ContinuousLinearMap.adjoint_inner_left, yvec_eq_sum, inner_sum]
  simp only [inner_smul_right, lp.inner_single_right, RCLike.inner_apply,
    smearedCreCoeff, lp.star_apply, creCoeff, ycoord, Complex.star_def]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Strong annihilation for every test vector, with no supplied domain or
implementation relation. -/
theorem strong_squeeze (K : H →L[ℂ] H) (w : Fock) (hw : Smooth w)
    (hv : WeakVacuum (fun a b => K (lp.single 2 b 1) a) w) (h : H) :
    smearedAnn h w hw + smearedCre (star (K.adjoint h)) w hw = 0 := by
  apply lp.ext
  funext m
  have he := congrArg (fun z : H => inner ℂ h z) (weak_vector K w hv m)
  rw [inner_add_right, inner_zero_right, inner_K_y] at he
  exact he

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The actual bounded operator in the fixed occupation coordinates. -/
def coordinateOp (b : HilbertBasis ℤ ℂ E) (K : E →L[ℂ] E) : H →L[ℂ] H :=
  b.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L K ∘L
    b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace E] in
lemma coordinateOp_entry (b : HilbertBasis ℤ ℂ E) (K : E →L[ℂ] E) (a c : ℤ) :
    coordinateOp b K (lp.single 2 c 1) a = Ext006CompressionR32a.coordinates b K a c := by
  change b.repr (K (b.repr.symm (lp.single 2 c 1))) a = _
  rw [b.repr_symm_single, b.repr_apply_apply]
  rfl

/-- Symmetry of the actual matrix gives the full bounded-operator transpose
identity; the extension uses the norm-convergent single-coordinate series. -/
lemma symmetric_star_adjoint (K : H →L[ℂ] H)
    (hSym : ∀ a b : ℤ, K (lp.single 2 b 1) a = K (lp.single 2 a 1) b) (h : H) :
    star (K.adjoint h) = K (star h) := by
  have hunit (a : ℤ) : tp K (lp.single 2 a 1) = K (lp.single 2 a 1) := by
    apply lp.ext
    funext c
    rw [tp_entry]
    exact hSym a c
  have heq (z : H) : tp K z = K z := by
    have ht := (tp K).hasSum (lp.hasSum_single ENNReal.ofNat_ne_top z)
    have hk := K.hasSum (lp.hasSum_single ENNReal.ofNat_ne_top z)
    have he (a : ℤ) : tp K (lp.single 2 a (z a)) = K (lp.single 2 a (z a)) := by
      have hs : (lp.single 2 a (z a) : H) = z a • lp.single 2 a 1 := by
        rw [← lp.single_smul]
        simp only [smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, hunit]
    simp only [he] at ht
    exact ht.unique hk
  simpa only [tp_apply, star_star] using heq (star h)


/-- Apply the strong identity to the canonical vacuum constructed in R32a. -/
theorem normalized_strong (b : HilbertBasis ℤ ℂ E) (K : E →L[ℂ] E)
    (hSym : ∀ i j, Ext006CompressionR32a.coordinates b K i j = Ext006CompressionR32a.coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : TraceClass.hsSq b K ≠ ⊤) (h : H) :
    smearedAnn h (Ext006HSVacuumR32a.normalized b K hSym hn hHS)
        (normalized_smooth b K hSym hn hHS) +
      smearedCre (star ((coordinateOp b K).adjoint h))
        (Ext006HSVacuumR32a.normalized b K hSym hn hHS)
        (normalized_smooth b K hSym hn hHS) = 0 := by
  apply strong_squeeze
  simpa only [coordinateOp_entry] using Ext006HSVacuumR32a.normalized_weak b K hSym hn hHS

section Physical
variable {L : ℝ} [Fact (0 < L)]
open Ext006KernelHilbertSchmidt Ext006CompressionR32a

/-- Physical mode-smearing uses the fixed Fourier occupation isometry. -/
def physicalAnn (h : H) (x : Ext025B3PhysicalSectors.Fock L)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) : Ext025B3PhysicalSectors.Fock L :=
  Ext006PhysFockCoord.Phi.symm (smearedAnn h (Ext006PhysFockCoord.Phi x) hx)

def physicalCre (h : H) (x : Ext025B3PhysicalSectors.Fock L)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) : Ext025B3PhysicalSectors.Fock L :=
  Ext006PhysFockCoord.Phi.symm (smearedCre h (Ext006PhysFockCoord.Phi x) hx)

/-- Agreement with the frozen physical core annihilation matrix elements. -/
theorem physicalAnn_mode_pairing (a : ℤ) (m : Occ)
    (x : Ext025B3PhysicalSectors.Fock L)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) :
    inner ℂ (Ext006PhysFockCoord.physCore (ket m))
        (physicalAnn (lp.single 2 a 1) x hx) =
      inner ℂ (Ext006PhysFockCoord.physCore (Cre a (ket m))) x := by
  rw [Ext006PhysFockCoord.inner_physCore_ket,
    Ext006PhysFockCoord.inner_physCore_Cre]
  change Ext006PhysFockCoord.Phi (Ext006PhysFockCoord.Phi.symm _) m = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change inner ℂ (lp.single 2 a (1 : ℂ)) (xvec (Ext006PhysFockCoord.Phi x) m) = _
  rw [lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]
  rfl

lemma smearedCre_single (a : ℤ) (w : Fock) (m : Occ) :
    smearedCreCoeff (lp.single 2 a 1) w m = creCoeff a w m := by
  rw [smearedCreCoeff, Finset.sum_eq_single a]
  · simp only [lp.single_apply_self, one_mul]
  · intro b _ hba
    rw [lp.single_apply_ne _ _ _ hba, zero_mul]
  · intro ha
    have hz : m a = 0 := by simpa using ha
    simp [creCoeff, hz]

/-- Agreement with the frozen physical core creation matrix elements. -/
theorem physicalCre_mode_pairing (a : ℤ) (m : Occ)
    (x : Ext025B3PhysicalSectors.Fock L)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) :
    inner ℂ (Ext006PhysFockCoord.physCore (ket m))
        (physicalCre (lp.single 2 a 1) x hx) =
      inner ℂ (Ext006PhysFockCoord.physCore (Ann a (ket m))) x := by
  rw [Ext006PhysFockCoord.inner_physCore_ket,
    Ext006PhysFockCoord.inner_physCore_Ann]
  change Ext006PhysFockCoord.Phi (Ext006PhysFockCoord.Phi.symm _) m = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact smearedCre_single a (Ext006PhysFockCoord.Phi x) m


local instance physicalRealNormedSpace : NormedSpace ℝ (PhysicalTensor.L2T L) :=
  (InnerProductSpace.complexToReal : InnerProductSpace ℝ (PhysicalTensor.L2T L)).toNormedSpace

/-- Source symplectic and original HS assumptions alone give a normalized
physical state with all polynomial domains and all smeared strong squeeze
identities. No physical unitary or transformed-field covariance is assumed. -/
theorem source_physical_strong
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ x : Ext025B3PhysicalSectors.Fock L, ‖x‖ = 1 ∧
      ∃ hx : Smooth (Ext006PhysicalVacuum.coefficient x),
        ∀ h : H, physicalAnn h x hx +
          physicalCre (star ((coordinateOp (physicalBasis L)
            (operatorConjugate (physicalBasis L) (sourceQ (physicalBasis L) S ∘L sourcePInv S hS))).adjoint h)) x hx = 0 := by
  obtain ⟨hSym, hn, hHS, _, _⟩ := «FIN-CORE-BD-02-kernel» (physicalBasis L) S hS hβ
  let K := squeeze (physicalBasis L) S hS
  let w := Ext006HSVacuumR32a.normalized (physicalBasis L) K hSym hn hHS
  have hw : Smooth w := normalized_smooth (physicalBasis L) K hSym hn hHS
  let x : Ext025B3PhysicalSectors.Fock L := Ext006PhysFockCoord.Phi.symm w
  have hxw : Ext006PhysFockCoord.Phi x = w := LinearIsometryEquiv.apply_symm_apply _ _
  have hx : Smooth (Ext006PhysicalVacuum.coefficient x) := by
    change Smooth (Ext006PhysFockCoord.Phi x : Occ → ℂ)
    rw [hxw]
    exact hw
  refine ⟨x, ?_, hx, ?_⟩
  · change ‖Ext006PhysFockCoord.Phi.symm w‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact Ext006HSVacuumR32a.normalized_norm (physicalBasis L) K hSym hn hHS
  · intro h
    have he := normalized_strong (physicalBasis L) K hSym hn hHS h
    have he' := congrArg (Ext006PhysFockCoord.Phi (L := L)).symm he
    rw [map_add, map_zero] at he'
    simp only [physicalAnn, physicalCre, hxw]
    rw [← sourceK_formula (physicalBasis L) S hS]
    exact he'

/-- The strong identity expressed in the original source P and Q blocks.
This constructs the transformed annihilator's vacuum action, without assuming
an implementer or either Heisenberg relation. -/
theorem source_physical_blocks
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ x : Ext025B3PhysicalSectors.Fock L, ‖x‖ = 1 ∧
      ∃ hx : Smooth (Ext006PhysicalVacuum.coefficient x),
        ∀ f : PhysicalTensor.L2T L,
          physicalAnn ((physicalBasis L).repr (sourceP S f)) x hx +
            physicalCre ((physicalBasis L).repr
              (conjugation (physicalBasis L) (sourceQ (physicalBasis L) S f))) x hx = 0 := by
  let b := physicalBasis L
  let K := squeeze b S hS
  have hs := squeeze_matrix_symmetric b S hS
  have hc (z : PhysicalTensor.L2T L) : b.repr (conjugation b z) = star (b.repr z) := by
    change b.repr (b.repr.symm (star (b.repr z))) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  have hp (f : PhysicalTensor.L2T L) : K (conjugation b (sourceP S f)) =
      conjugation b (sourceQ b S f) := by
    change Ext006SymplecticKernel.kernel S hS
      (conjugation b (conjugation b (sourceP S f))) = _
    rw [conjugation_sq]
    change Ext006Blocks.antilinearPart S.toContinuousLinearMap
      ((Ext006SymplecticKernel.linearBlock S hS).symm (sourceP S f)) = _
    have hi : (Ext006SymplecticKernel.linearBlock S hS).symm (sourceP S f) = f :=
      (Ext006SymplecticKernel.linearBlock S hS).symm_apply_apply f
    rw [hi]
    change Ext006Blocks.antilinearPart S.toContinuousLinearMap f =
      conjugation b (conjugation b (Ext006Blocks.antilinearPart S.toContinuousLinearMap f))
    rw [conjugation_sq]
  have hk (f : PhysicalTensor.L2T L) :
      star ((coordinateOp b K).adjoint (b.repr (sourceP S f))) =
        b.repr (conjugation b (sourceQ b S f)) := by
    rw [symmetric_star_adjoint]
    · rw [← hc]
      change b.repr (K (b.repr.symm (b.repr (conjugation b (sourceP S f))))) = _
      rw [LinearIsometryEquiv.symm_apply_apply, hp]
    · intro a c
      rw [coordinateOp_entry, coordinateOp_entry]
      exact hs a c
  obtain ⟨x, hxn, hx, hstrong⟩ := source_physical_strong S hS hβ
  refine ⟨x, hxn, hx, fun f => ?_⟩
  have he := hstrong (b.repr (sourceP S f))
  rw [← sourceK_formula b S hS] at he
  rw [hk] at he
  exact he


end Physical
end QuantumNLS.Ext006StrongVacuumR33a

#print axioms QuantumNLS.Ext006StrongVacuumR33a.fieldWord

#print axioms QuantumNLS.Ext006StrongVacuumR33a.weak_vector

#print axioms QuantumNLS.Ext006StrongVacuumR33a.inner_K_y

#print axioms QuantumNLS.Ext006StrongVacuumR33a.strong_squeeze

#print axioms QuantumNLS.Ext006StrongVacuumR33a.normalized_strong

#print axioms QuantumNLS.Ext006StrongVacuumR33a.physicalAnn_mode_pairing

#print axioms QuantumNLS.Ext006StrongVacuumR33a.physicalCre_mode_pairing

#print axioms QuantumNLS.Ext006StrongVacuumR33a.symmetric_star_adjoint

#print axioms QuantumNLS.Ext006StrongVacuumR33a.source_physical_blocks

#print axioms QuantumNLS.Ext006StrongVacuumR33a.source_physical_strong

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006StrongVacuumR33a." then
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
  Lean.logInfo m!"Round33a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
