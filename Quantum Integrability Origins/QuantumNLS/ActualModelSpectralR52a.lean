import QuantumNLS.ActualModelQuantumR52a
import QuantumNLS.ActualModelScalarR52a
import QuantumNLS.AuditWeightedValuesR50a
import QuantumNLS.RootCoreH1

/-! R-E679E41D: bind the scalar estimates and high-cut geometry to the
actual maximal-charge enumeration and the original Born law of R51a. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter Topology MeasureTheory Complex
namespace QuantumNLS.ActualModelSpectralR52a
open PhysicalTensor BetheLabels BetheCoefficientTransform
open Def044D1SpectralR51a Def044InterfacesR51a ActualModelScalarR52a
variable {L κ : ℝ} [Fact (0 < L)]

lemma originalLaw_eq (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) :
    originalLaw hκ u hu N = EmpiricalRapidity.bornMeasure
      (BulkResponseActual.physBasis L hκ (N+1)) u hu := by
  rw [RootMeasureExistence.physBasis_eq hκ (by omega : 1 ≤ N+1)]
  rfl

lemma root_eq_rev (hκ : 0 < κ) (N : ℕ) (m : MArr (N+1)) (j : Fin (N+1)) :
    root (L := L) (κ := κ) N m j = arrRoots L (κ/((N+1 : ℕ) : ℝ)) m (Fin.rev j) := by
  simpa only [Def044D1SpectralR51a.root,Nat.cast_add,Nat.cast_one] using
    AuditWeightedValuesR50a.rapidity_eq_arrRoots_rev hκ (by omega : 0 < N+1) m j

lemma tail_eq (hκ : 0 < κ) (N : ℕ) (R : ℝ) (m : MArr (N+1)) :
    Def044D1SpectralR51a.tailFraction (L := L) (κ := κ) N R m =
      RootEvent.tailFraction (Prop017Quantum.qAct L κ (N+1)) R m := by
  unfold Def044D1SpectralR51a.tailFraction RootEvent.tailFraction
  simp only [Set.indicator_apply,Set.mem_ofPred_eq,Prop017Quantum.qAct]
  simp_rw [root_eq_rev hκ]
  have hs := Equiv.sum_comp Fin.revPerm
    (fun j : Fin (N+1) => if R < |arrRoots L (κ/((N+1 : ℕ) : ℝ)) m j| then (1 : ℝ) else 0)
  change (∑ j, if R < |arrRoots L (κ/((N+1 : ℕ) : ℝ)) m (Fin.rev j)| then (1 : ℝ) else 0) = _ at hs
  rw [hs]
  simp only [Nat.cast_add,Nat.cast_one]
  ring

lemma empiricalG_eq (hκ : 0 < κ) (N : ℕ) (m : MArr (N+1)) (z : ℂ) :
    empiricalG (L := L) (κ := κ) N m z =
      Extrapolation.GN (Prop017Quantum.qAct L κ (N+1) m) z := by
  unfold empiricalG Extrapolation.GN
  simp_rw [root_eq_rev hκ]
  have hs := Equiv.sum_comp Fin.revPerm
    (fun j : Fin (N+1) => (z-(arrRoots L (κ/((N+1 : ℕ) : ℝ)) m j : ℂ))⁻¹)
  change (∑ j, (z-(arrRoots L (κ/((N+1 : ℕ) : ℝ)) m (Fin.rev j) : ℂ))⁻¹) = _ at hs
  rw [hs]
  simp only [Prop017Quantum.qAct,one_div,Nat.cast_add,Nat.cast_one]

/-- Every physical open-band cut is regular in the exact D1 sense. -/
lemma band_regular (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0) (x : ℝ)
    (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    D1Def043.regularCut L κ (PhysicalQuantumMeasure.measure hκ u) x := by
  refine ⟨Prop026Bound.cuts_sub hκ hu hx,?_⟩
  intro a ha
  have hf := Prop026Bound.force_eq hκ hu hx
  have ht : (PhysicalContinuousBoundary.boundary hκ u x).re = (a : ℝ)*Real.pi := by
    have he := (div_eq_iff (by positivity : (2*Real.pi : ℝ) ≠ 0)).mp ha
    change IndexedScalarMeasure.exteriorForce L κ (PhysicalQuantumMeasure.measure hκ u) x = _ at he
    rw [hf] at he
    nlinarith
  have hs := RootCauchyJointR9.sine_regular hκ (u,(x : ℂ)) (Or.inr hx)
  rw [DEF014UpperAnalytic.selected_real_eq hκ u hx] at hs
  change sin (((PhysicalContinuousBoundary.boundary hκ u x).re : ℝ) : ℂ) ≠ 0 at hs
  rw [ht,Complex.ofReal_mul] at hs
  apply hs
  simpa only [Complex.ofReal_intCast] using (Complex.sin_int_mul_pi a)

/-- High windows have a common positive support gap and multiplier lower
bound. Regularity at BOTH cuts uses D1, rather than a supplied cut set. -/
theorem high_geometry (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    {h : ℝ} (hh : 0 < h) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∃ l0 : ℕ,
      ∀ l : ℕ, l0 ≤ l →
        D1Def043.regularCut L κ (PhysicalQuantumMeasure.measure hκ (physical u)) (highCut (L := L) l) ∧
        D1Def043.regularCut L κ (PhysicalQuantumMeasure.measure hκ (physical u)) (-highCut (L := L) l) ∧
        (∀ q ∈ (PhysicalQuantumMeasure.measure hκ (physical u)).support,
          delta ≤ |q-highCut (L := L) l| ∧ delta ≤ |q+highCut (L := L) l|) ∧
        (∀ z ∈ rectangle (highCut (L := L) l) h,
          c ≤ ‖discriminant (L := L) (κ := κ) (PhysicalQuantumMeasure.measure hκ (physical u)) z‖) := by
  obtain ⟨uf,hrep⟩ := RootCoreH1.periodicRep_of_oneH1 (physical u)
    (PhysicalProductPreparation.oneH1_smooth u.property)
  obtain ⟨μ,hμ⟩ := RootMeasureExistence.exists_limiting_measure hκ (physical u) hu
  have hmeas := Prop026Bound.physical_eq_limit hκ (physical u) hu hμ
  obtain ⟨l0,hgap,hlower⟩ := RootSpectralInputsDischarge.rootSpectralInputs_geometry hκ hu hrep hμ hh
  obtain ⟨l1,hsmall⟩ := RootSpectralInputsDischarge.disc_small (L := L) hκ hrep.1
  have hu0 : physical u ≠ 0 := by intro he; rw [he,norm_zero] at hu; norm_num at hu
  refine ⟨1/L,RootSpectralInputsDischarge.dlow L κ (1/L) h,
    one_div_pos.mpr (Fact.out : 0 < L),
    RootSpectralInputsDischarge.dlow_pos hκ (Fact.out : 0 < L) (one_div_pos.mpr (Fact.out : 0 < L)) hh,
    max l0 l1,?_⟩
  intro l hl
  have hl0 := (le_max_left l0 l1).trans hl
  have hl1 := (le_max_right l0 l1).trans hl
  have hband : ∀ a : ℝ, (a = highCut (L := L) l ∨ a = -highCut (L := L) l) →
      |(L2SpatialTransfer.discriminant κ (physical u) (a : ℂ)).re| < 2 := by
    intro a ha
    have hb := (hsmall l hl1 a ha).2
    rw [RootDensityIdentification.disc_eq_rep hrep κ,
      RootDiscriminant.discriminant_eq_discReal L κ hrep.1]
    simpa only [Complex.ofReal_re] using (lt_of_le_of_lt hb (by norm_num : (1/2 : ℝ) < 2))
  refine ⟨band_regular hκ (physical u) hu0 _ (hband _ (Or.inl rfl)),
    band_regular hκ (physical u) hu0 _ (hband _ (Or.inr rfl)),?_,?_⟩
  · have hg := hgap l hl0
    rw [← hmeas] at hg
    exact Measure.support_subset_of_isClosed
      ((isClosed_le continuous_const (continuous_id.sub continuous_const).abs).inter
        (isClosed_le continuous_const (continuous_id.add continuous_const).abs)) hg
  · intro z hz
    have hz' : z ∈ ResolventNeighborhood.GammaN (PROP017UniformN.cutSeq L l) h := by
      simpa only [rectangle,ResolventNeighborhood.GammaN,highCut,PROP017UniformN.cutSeq,
        abs_le,or_comm] using hz
    have hb := hlower l hl0 z hz'
    rw [← hmeas,NonvanishingD.Dsrc,RootSpectralInputsDischarge.Gfull_eq] at hb
    exact hb

end QuantumNLS.ActualModelSpectralR52a
#print axioms QuantumNLS.ActualModelSpectralR52a.originalLaw_eq
#print axioms QuantumNLS.ActualModelSpectralR52a.root_eq_rev
#print axioms QuantumNLS.ActualModelSpectralR52a.tail_eq
#print axioms QuantumNLS.ActualModelSpectralR52a.empiricalG_eq
#print axioms QuantumNLS.ActualModelSpectralR52a.band_regular
#print axioms QuantumNLS.ActualModelSpectralR52a.high_geometry

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelSpectralR52a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelSpectralR52a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"Round52 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
