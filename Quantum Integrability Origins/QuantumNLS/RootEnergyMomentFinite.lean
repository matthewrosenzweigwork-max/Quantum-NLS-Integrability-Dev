import QuantumNLS.RootEnergyMomentForm
import QuantumNLS.ContactProductExact
import QuantumNLS.RootMeasureTransfer

/-! The finite Born energy is derived from the accepted contact form and
its complete physical Bethe eigenbasis. No finite expectation is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy QuantumNLS.BetheLabels
open QuantumNLS.ContactOperator QuantumNLS.ContactForm QuantumNLS.ContactFormTheorem
open QuantumNLS.BetheCoefficientTransform QuantumNLS.BulkResponseActual
namespace QuantumNLS.RootEnergyMomentFinite
variable {L κ : ℝ} [hL : Fact (0 < L)] {N : ℕ}

/-- Complete coordinate basis of the accepted normalized physical waves. -/
def coordBasis (hN : 0 < N) (hκ : 0 < κ) : HilbertBasis (MArr N) ℂ (SymL2 L N) :=
  reindexBasis (QuantumNLS.BetheConditionalBasis.labelArr N)
    (QuantumNLS.BetheConditionalBasis.coordinateBasis
      QuantumNLS.AbstractContinuityProof.abstractContinuity L N hN (κ/N)
      (div_pos hκ (Nat.cast_pos.mpr hN)))

lemma coordBasis_apply (hN : 0 < N) (hκ : 0 < κ) (m : MArr N) :
    coordBasis (L := L) hN hκ m =
      QuantumNLS.BetheConditionalBasis.normalizedWave L N
        ⟨κ/N, (div_pos hκ (Nat.cast_pos.mpr hN)).le⟩
        ((QuantumNLS.BetheConditionalBasis.labelArr N).symm m) := by
  rw [coordBasis, reindexBasis_apply]
  exact QuantumNLS.BetheConditionalBasis.coordinateBasis_apply _ L N hN _ _ _

lemma source_energy (hN : 0 < N) (hκ : 0 < κ) (m : MArr N) :
    (∑ j, QuantumNLS.BetheSmooth.sourceRoots L
      ((QuantumNLS.BetheConditionalBasis.labelArr N).symm m).val (κ/N) j ^ 2) =
      ∑ j, (arrRoots L (κ/N) m j)^2 := by
  have hr (j : Fin N) : QuantumNLS.BetheSmooth.sourceRoots L
      ((QuantumNLS.BetheConditionalBasis.labelArr N).symm m).val (κ/N) j =
      arrRoots L (κ/N) m (Fin.rev j) := by
    change QuantumNLS.BetheSmooth.sourceRoots L (QuantumNLS.NormalityBridge.label m).val
      (κ/N) j = _
    rw [QuantumNLS.RootMeasureTransfer.label_val]
    exact sourceRoots_eq_roots_rev hL.out (div_pos hκ (Nat.cast_pos.mpr hN)) _ j
  simp only [hr]
  exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N))
    (fun j : Fin N => (arrRoots L (κ/N) m j)^2)

lemma basis_form_lift (hN : 0 < N) (hκ : 0 < κ) (m : MArr N) :
    ∃ v : VSym L N, valSym v = coordBasis hN hκ m ∧
      ∀ x : VSym L N,
        Bform (κ/N) x v = ((1 + ∑ j, (arrRoots L (κ/N) m j)^2 : ℝ) : ℂ) *
          ⟪valSym x, coordBasis hN hκ m⟫_ℂ := by
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (Nat.cast_pos.mpr hN)
  obtain ⟨_, _, _, _, _, _, _, heig⟩ :=
    QuantumNLS.UnconditionalBetheBasis.basis L N hN (κ/N) hc
  let n := (QuantumNLS.BetheConditionalBasis.labelArr N).symm m
  have hcb := coordBasis_apply (L := L) hN hκ m
  have hg : ∃ h : coordBasis hN hκ m ∈ (Hop (L := L) (N := N) (κ/N) hc.le).domain,
      Hop (κ/N) hc.le ⟨coordBasis hN hκ m,h⟩ =
        ((∑ j, (arrRoots L (κ/N) m j)^2 : ℝ) : ℂ) • coordBasis hN hκ m := by
    rw [hcb]
    obtain ⟨hm,hem⟩ := heig n
    refine ⟨hm,?_⟩
    have hem' : Hop (κ/N) hc.le
        ⟨QuantumNLS.BetheConditionalBasis.normalizedWave L N ⟨κ/N,hc.le⟩ n,hm⟩ =
          ((∑ j,QuantumNLS.BetheSmooth.sourceRoots L
            ((QuantumNLS.BetheConditionalBasis.labelArr N).symm m).val (κ/N) j^2 : ℝ) : ℂ) •
            QuantumNLS.BetheConditionalBasis.normalizedWave L N ⟨κ/N,hc.le⟩ n := hem
    rw [source_energy (L := L) hN hκ m] at hem'
    exact hem' 
  obtain ⟨v,hv,hq⟩ := (Hop_isAssociated hc.le _ _).mp hg
  refine ⟨v,hv,fun x => ?_⟩
  unfold Bform
  rw [hq]
  change ⟪valSym x, ((∑ j, (arrRoots L (κ/N) m j)^2 : ℝ) : ℂ) •
    coordBasis hN hκ m⟫_ℂ + ⟪valSym x,valSym v⟫_ℂ = _
  have hmul : ⟪valSym x, ((∑ j, (arrRoots L (κ/N) m j)^2 : ℝ) : ℂ) •
      coordBasis hN hκ m⟫_ℂ =
      ((∑ j, (arrRoots L (κ/N) m j)^2 : ℝ) : ℂ) * ⟪valSym x,coordBasis hN hκ m⟫_ℂ :=
    inner_smul_right (𝕜 := ℂ) (valSym x) (coordBasis hN hκ m)
      (((∑ j, (arrRoots L (κ/N) m j)^2 : ℝ) : ℂ))
  rw [hmul,hv]
  push_cast
  ring

/-- Contact-form Parseval in the original physical normalization. -/
theorem contact_energy_hasSum (hN : 0 < N) (hκ : 0 < κ) (x : VSym L N) :
    HasSum (fun m => (∑ j, (arrRoots L (κ/N) m j)^2) *
      ‖⟪coordBasis hN hκ m, valSym x⟫_ℂ‖^2) (q (κ/N) x.1 x.1).re := by
  classical
  let v : MArr N → VSym L N := fun m => (basis_form_lift hN hκ m).choose
  have hv (m : MArr N) : valSym (v m) = coordBasis hN hκ m :=
    (basis_form_lift hN hκ m).choose_spec.1
  have hp (z : VSym L N) (m : MArr N) :
      BformCLM (κ/N) (div_pos hκ (Nat.cast_pos.mpr hN)).le z (v m) =
        ((1 + ∑ j, (arrRoots L (κ/N) m j)^2 : ℝ) : ℂ) *
          ⟪valSym z,coordBasis hN hκ m⟫_ℂ :=
    (basis_form_lift hN hκ m).choose_spec.2 z
  have hinj : Function.Injective (valSym (L := L) (N := N)) := by
    intro z z' hz
    apply Subtype.ext
    apply PhysH1.val_injective
    exact congrArg (fun t : SymL2 L N => (t : L2TN L N)) hz
  have hh := QuantumNLS.RootEnergyMomentForm.form_parseval
    (BformCLM (κ/N) (div_pos hκ (Nat.cast_pos.mpr hN)).le)
    valSym (coordBasis hN hκ) v (fun m => 1 + ∑ j, (arrRoots L (κ/N) m j)^2)
    hv hp hinj (Bform_conj_symm (κ/N))
    (fun z => by
      change ‖z‖^2 ≤ (Bform (κ/N) z z).re
      rw [← inner_Mop_right (div_pos hκ (Nat.cast_pos.mpr hN)).le]
      exact coercive_Mop (div_pos hκ (Nat.cast_pos.mpr hN)).le z)
    (fun m => by positivity) x
  have hmass := QuantumNLS.RootMeasureTransfer.hasSum_norm_sq (coordBasis hN hκ) (valSym x)
  have hout := hh.sub hmass
  convert hout using 1
  · funext m
    rw [HilbertBasis.repr_apply_apply]
    ring
  · change (q (κ/N) x.1 x.1).re = (Bform (κ/N) x x).re - ‖valSym x‖^2
    unfold Bform
    rw [Complex.add_re]
    have hnorm : (⟪x.1.val,x.1.val⟫_ℂ).re = ‖valSym x‖^2 := by
      exact inner_self_eq_norm_sq (𝕜 := ℂ) x.1.val
    rw [hnorm]
    ring

#print axioms contact_energy_hasSum
end QuantumNLS.RootEnergyMomentFinite

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentFinite." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentFinite." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
