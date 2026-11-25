import QuantumNLS.AllOrderEnergyDomainR56a
import QuantumNLS.ActualModelQuantumR52a
import QuantumNLS.Ext025GP08R27m
import QuantumNLS.TerraMultiRound89EigenForm

/-! The exact joint spectral unitary acts on the closed physical contact
form domain. The identification uses the actual common Bethe basis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open MeasureTheory
open scoped InnerProductSpace LinearPMap
namespace QuantumNLS.AllOrderEnergyQuantumR56a
open PhysicalTensor BetheLabels BetheCoefficientTransform BetheSpectralCharges
open ContactOperator ContactFormTheorem BethePhysicalTransfer EnergyPreparationDef
open Def044D1SpectralR51a ActualModelQuantumR52a
variable {L κ : ℝ} [Fact (0 < L)]

/-- The same spectral unitary in position space. -/
def positionChargeUnitary (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (N : ℕ) :
    SymL2 L (N + 1) ≃ₗᵢ[ℂ] SymL2 L (N + 1) :=
  (symmetricPosition L (N + 1)).symm.trans
    ((chargeUnitary hκ R t N).trans (symmetricPosition L (N + 1)))

private theorem evolution_basis {N : ℕ} (b : BetheBasis L N) (ev : MArr N → ℝ) (m : MArr N) :
    evolution b ev 1 (b m) = DiagonalMultiplier.phase ev 1 m • b m := by
  classical
  apply b.repr.injective
  ext j
  rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  conv_lhs => rw [HilbertBasis.repr_apply_apply, evolution_coord, ← HilbertBasis.repr_apply_apply]
  by_cases h : j = m
  · subst j; rw [b.repr_self]
  · rw [b.repr_self, lp.single_apply_ne _ _ _ h, mul_zero, mul_zero]

/-- With the position unitary, `H_N` is diagonal on the very basis used
in `chargeUnitary`, and its eigenvalue is `Λ_{N,2}`. -/
theorem contact_Hamiltonian_basis (hκ : 0 < κ) (N : ℕ) (m : MArr (N + 1)) :
    let c : ℝ := κ / (N + 1 : ℕ)
    let hc : 0 ≤ c := div_nonneg hκ.le (Nat.cast_nonneg _)
    let b : SymL2 L (N + 1) := symmetricPosition L (N + 1) (basis hκ N m)
    ∃ hm : b ∈ (Hop (L := L) (N := N + 1) c hc).domain,
      Hop c hc ⟨b, hm⟩ = (eigenvalue L (N + 1) c 2 m : ℂ) • b := by
  dsimp only
  let c : ℝ := κ / (N + 1 : ℕ)
  have hc : 0 < c := div_pos hκ (by positivity)
  let n := (BetheConditionalBasis.labelArr (N + 1)).symm m
  have hb : symmetricPosition L (N + 1) (basis hκ N m) =
      BetheConditionalBasis.normalizedWave L (N + 1) ⟨c, hc.le⟩ n :=
    UnconditionalBetheBasis.physicalBasis_position L (N + 1) (by omega) c hc m
  obtain ⟨-, -, -, -, -, -, -, H⟩ := UnconditionalBetheBasis.basis L (N + 1) (by omega) c hc
  obtain ⟨hm, heig⟩ := H n
  have liftEq : ∀ (x : SymL2 L (N + 1)), x = BetheConditionalBasis.normalizedWave L (N + 1) ⟨c, hc.le⟩ n →
      ∃ hx : x ∈ (Hop (L := L) (N := N + 1) c hc.le).domain,
        Hop c hc.le ⟨x, hx⟩ = (eigenvalue L (N + 1) c 2 m : ℂ) • x := by
    intro x hx
    subst x
    exact ⟨hm, heig⟩
  exact liftEq _ hb

/-- Two bounded diagonal operators are instances of the repaired GP-08
calculus on one common atomic resolution. Encoding the countable labels
preserves all multiplicities of the Hamiltonian energies. -/
private theorem bounded_common_commute {ι E : Type*} [Countable ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (A B : E →L[ℂ] E) (a d : ι → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hd : ∀ i, ‖d i‖ ≤ 1)
    (hA : ∀ i, A (b i) = a i • b i) (hB : ∀ i, B (b i) = d i • b i) : A * B = B * A := by
  classical
  obtain ⟨encode, hinj⟩ := Countable.exists_injective_nat ι
  let label := fun i => (encode i : ℝ)
  have hlabel : Function.Injective label := fun i j h => hinj (Nat.cast_inj.mp h)
  let symbol (v : ι → ℂ) (t : ℝ) := if h : t ∈ Set.range label then v (Classical.choose h) else 0
  have hvalue (v : ι → ℂ) (i : ι) : symbol v (label i) = v i := by
    have h : label i ∈ Set.range label := ⟨i, rfl⟩
    simpa only [symbol, dite_eq_left h] using (congrArg v (hlabel (Classical.choose_spec h)))
  have hmeas (v : ι → ℂ) : Measurable (symbol v) := by
    apply (measurable_const (a := (0 : ℂ))).measurable_of_countable_ne
    apply (Set.countable_range label).mono
    intro t ht
    by_contra h
    exact ht (by simp only [symbol, dite_eq_right h])
  have hbound (v : ι → ℂ) (hv : ∀ i, ‖v i‖ ≤ 1) (t : ℝ) : ‖symbol v t‖ ≤ 1 := by
    by_cases ht : t ∈ Set.range label
    · simpa only [symbol, dite_eq_left ht] using hv (Classical.choose ht)
    · simp only [symbol, dite_eq_right ht, norm_zero, zero_le_one]
  let P := Ext025B10Atomic.resolution b label
  have hidentify (S : E →L[ℂ] E) (v : ι → ℂ) (hv : ∀ i, ‖v i‖ ≤ 1)
      (hs : ∀ i, S (b i) = v i • b i) :
      S = Ext025B8BorelCalculus.bounded P (symbol v) (hmeas v) 1 zero_le_one (hbound v hv) := by
    apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
    rintro _ ⟨i, rfl⟩
    rw [hs i]
    exact (Ext025B10Atomic.bounded_basis b label (symbol v) (hmeas v) 1 zero_le_one (hbound v hv) i).trans
      (congrArg (fun c : ℂ => c • b i) (hvalue v i)) |>.symm
  obtain ⟨_, _, _, _, _, _, _, _, hcomm, _, _⟩ := (Ext025GP08R27m.contract_GP08_fixed.{_, 0} P).2.2
  rw [hidentify A a ha hA, hidentify B d hd hB]
  exact hcomm (symbol a) (symbol d) (hmeas a) (hmeas d) 1 1 zero_le_one zero_le_one
    (hbound a ha) (hbound d hd)

/-- The actual joint unitary and the resolvent of H are bounded functions of
one common resolution. GP-08 supplies the commutation on the entire sector. -/
theorem chargeUnitary_commutes_resolvent (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (N : ℕ) :
    let c : ℝ := κ / (N + 1 : ℕ)
    let hc : 0 ≤ c := div_nonneg hκ.le (Nat.cast_nonneg _)
    let U := positionChargeUnitary (L := L) hκ R t N
    ∀ g, Rop c hc (U g) = U (Rop c hc g) := by
  classical
  dsimp only
  let c : ℝ := κ / (N + 1 : ℕ)
  have hc : 0 ≤ c := div_nonneg hκ.le (Nat.cast_nonneg _)
  let pos := symmetricPosition L (N + 1)
  let B := HilbertBasis.ofRepr (pos.symm.trans (basis (L := L) hκ N).repr)
  have hB (m : MArr (N + 1)) : B m = pos (basis hκ N m) := rfl
  let U := positionChargeUnitary (L := L) hκ R t N
  let Uop := U.toContinuousLinearEquiv.toContinuousLinearMap
  let ev := eigenvalue L (N + 1) c 2
  let inv := fun m => (((ev m + 1)⁻¹ : ℝ) : ℂ)
  let phase := DiagonalMultiplier.phase (chargeSymbol (L := L) (κ := κ) R t N) 1
  have huv (m : MArr (N + 1)) : Uop (B m) = phase m • B m := by
    change U (B m) = _
    simp only [U, hB, pos, positionChargeUnitary, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.symm_apply_apply, chargeUnitary, evolution_basis, map_smul, phase]
  have hnonneg (m : MArr (N + 1)) : 0 ≤ ev m := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrv (m : MArr (N + 1)) : Rop c hc (B m) = inv m • B m := by
    obtain ⟨hm, he⟩ := contact_Hamiltonian_basis (L := L) hκ N m
    have hpos : 0 < ev m + 1 := by linarith [hnonneg m]
    have he' : Rop c hc (((ev m + 1 : ℝ) : ℂ) • B m) = B m := by
      rw [hB, Rop_eq_valSym_psi]
      exact (TerraMultiRound89EigenForm.eigen_resolvent_form hc _ hm (ev m) he).1
    have hi : inv m * (((ev m + 1 : ℝ) : ℂ)) = 1 := by
      dsimp [inv]
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
    calc
      Rop c hc (B m) = Rop c hc (inv m • (((ev m + 1 : ℝ) : ℂ) • B m)) := by
        rw [smul_smul, hi, one_smul]
      _ = inv m • B m := by rw [map_smul, he']
  have hinv (m : MArr (N + 1)) : ‖inv m‖ ≤ 1 := by
    have hp : (1 : ℝ) ≤ ev m + 1 := by linarith [hnonneg m]
    change ‖(((ev m + 1)⁻¹ : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
    exact inv_le_one_of_one_le₀ hp
  have h := bounded_common_commute B (Rop c hc) Uop inv phase hinv
    (fun m => (DiagonalMultiplier.norm_phase _ _ m).le) hrv huv
  intro g
  exact congrArg (fun S : SymL2 L (N+1) →L[ℂ] SymL2 L (N+1) => S g) h

/-- The exact joint charge evolution preserves the physical form, starting
from any symmetric H¹ wave function. -/
theorem chargeUnitary_form (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (N : ℕ)
    (x : VSym L (N + 1)) :
    ∃ y : VSym L (N + 1),
      valSym y = positionChargeUnitary hκ R t N (valSym x) ∧
      hN κ (N + 1) y.1 = hN κ (N + 1) x.1 :=
  AllOrderEnergyDomainR56a.form_evolution_of_commuting_resolvent
    (div_nonneg hκ.le (Nat.cast_nonneg _)) (positionChargeUnitary hκ R t N)
    (chargeUnitary_commutes_resolvent hκ R t N) x

end QuantumNLS.AllOrderEnergyQuantumR56a
set_option maxHeartbeats 15000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := env.constants.toList.filterMap fun (n, _) =>
    if n.toString.startsWith "QuantumNLS.AllOrderEnergyQuantumR56a." ||
        n.toString.startsWith "_private.QuantumNLS.AllOrderEnergyQuantumR56a." then some n else none
  let roots := pending.length
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := ci.type.getUsedConstants.toList ++ pending
        if let some v := ci.value? (allowOpaque := true) then
          pending := v.getUsedConstants.toList ++ pending
      else throwError "Missing dependency: {n}"
  Lean.logInfo m!"R56a audit PASS: {roots} namespace constants; {seen.size} transitive constants."
