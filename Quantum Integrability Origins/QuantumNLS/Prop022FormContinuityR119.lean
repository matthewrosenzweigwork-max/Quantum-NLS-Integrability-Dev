import QuantumNLS.Prop022CutoffHamiltonianR115
import QuantumNLS.Prop022HessianR118
import QuantumNLS.Prop022CoefficientTimeR117

/-! Coefficient continuity for the literal R115 cutoffs, and specialization
of the full Hessian identity to the actual unit Hartree trajectory. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022FormContinuityR119
open TensorCarrier PhysicalTensor BetheCoefficientTransform TensorPlacements
open Ext025B3PhysicalSectors Ext005PhysicalNumberFormR114 Ext005PhysicalPairFormR114
open Ext005PhysicalHalfPairR114 Ext005PhysicalSymmetryR114 Ext005ComplexRieszR113
open Ext005AlgebraicFormR114 Ext005QuadraticEnergyR108 Ext005PairSector
open Ext005FormCutoffR109
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022CutoffHamiltonianR115
variable {L : ℝ} [Fact (0 < L)]
local instance (priority := 1200) opNormed : NormedAddCommGroup (HN L 1 →L[ℂ] HN L 1) :=
  inferInstance
local instance (priority := 1200) fockOpNormed : NormedAddCommGroup (Fock L →L[ℂ] Fock L) :=
  inferInstance

lemma firstPlacement_sub {p q : ℕ} (a c : HN L p →L[ℂ] HN L p) :
    firstPlacement (q := q) (a-c) = firstPlacement (q := q) a - firstPlacement (q := q) c := by
  have he : extendSymKernel (a-c) = extendSymKernel a - extendSymKernel c := by
    ext x
    simp [extendSymKernel]
  have hm := map_sub (ampliate ℂ (HilbertTensorPower ℂ (L2T L) p)
    (HilbertTensorPower ℂ (L2T L) q)) (extendSymKernel a) (extendSymKernel c)
  simp only [ampliate_apply] at hm
  simp only [firstPlacement, he, hm, sub_comp, comp_sub]

lemma Q_sub {p q : ℕ} (a c : HN L p →L[ℂ] HN L p) :
    Q_N_p (q := q) (a-c) = Q_N_p (q := q) a - Q_N_p (q := q) c := by
  have h (σ : Equiv.Perm (Fin (p+q))) :
      permutedPlacement σ (a-c) = permutedPlacement σ a - permutedPlacement σ c := by
    simp only [permutedPlacement, firstPlacement_sub, comp_sub, sub_comp]
  have hs : symmetrizedPlacement (q := q) (a-c) =
      symmetrizedPlacement (q := q) a - symmetrizedPlacement (q := q) c := by
    simp only [symmetrizedPlacement, h, Finset.sum_sub_distrib, smul_sub]
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change symmetrizedPlacement (a-c) x.val =
    symmetrizedPlacement a x.val - symmetrizedPlacement c x.val
  rw [hs, sub_apply]

lemma physicalQ_sub (n p : ℕ) (hp : p ≤ n) (a c : HN L p →L[ℂ] HN L p) :
    PhysicalPlacements.physicalQ_N_p L n p hp (a-c) =
      PhysicalPlacements.physicalQ_N_p L n p hp a - PhysicalPlacements.physicalQ_N_p L n p hp c := by
  have hc {m n : ℕ} (h : m = n) (a c : HN L m →L[ℂ] HN L m) :
      PhysicalPlacements.castSymSectorOperator L h (a-c) =
        PhysicalPlacements.castSymSectorOperator L h a - PhysicalPlacements.castSymSectorOperator L h c := by
    cases h
    rfl
  simp only [PhysicalPlacements.physicalQ_N_p, Q_sub, hc]

lemma numberBlock_sub (a c : HN L 1 →L[ℂ] HN L 1) (n : ℕ) :
    numberBlock (a-c) n = numberBlock a n - numberBlock c n := by
  unfold numberBlock
  split_ifs <;> simp only [physicalQ_sub, smul_sub, sub_self]

lemma numberContinuous_sub (a c : HN L 1 →L[ℂ] HN L 1) :
    numberContinuous (a-c) = numberContinuous a - numberContinuous c := by
  have hn : numberCoordinates (a-c) = numberCoordinates a - numberCoordinates c := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    funext n
    change normalizedBlock (a-c) n (u n) = normalizedBlock a n (u n) - normalizedBlock c n (u n)
    simp only [normalizedBlock, numberBlock_sub, sub_apply, smul_apply, smul_sub]
  ext u v
  change ⟪v, numberCoordinates (a-c) u⟫_ℂ =
    ⟪v, numberCoordinates a u⟫_ℂ - ⟪v, numberCoordinates c u⟫_ℂ
  rw [hn, sub_apply, inner_sub_right]

lemma annihilation_sub (b d : HN L 2) (n : ℕ) :
    annihilation (b-d) n = annihilation b n - annihilation d n := by
  have hh : IntrinsicContact.htmulR (F := HilbertTensorPower ℂ (L2T L) n)
      ((b-d : HN L 2) : HilbertTensorPower ℂ (L2T L) 2) =
      IntrinsicContact.htmulR (b : HilbertTensorPower ℂ (L2T L) 2) - IntrinsicContact.htmulR (d : HilbertTensorPower ℂ (L2T L) 2) := by
    ext x
    change htmul (b.val-d.val) x = htmul b.val x - htmul d.val x
    simp [htmul, TensorProduct.sub_tmul, UniformSpace.Completion.coe_sub]
  simp only [annihilation, contraction, IntrinsicContact.contractL, hh, map_sub,
    comp_sub, sub_comp, smul_sub]

lemma pairContinuous_sub (b d : HN L 2) :
    pairContinuous (b-d) = pairContinuous b - pairContinuous d := by
  have hs (u v : Fock L) : annihilationForm (b-d) u v =
      annihilationForm b u v - annihilationForm d u v := by
    change (∑' n, sectorTerm (b-d) u v n) = (∑' n, sectorTerm b u v n) - ∑' n, sectorTerm d u v n
    have he : sectorTerm (b-d) u v = fun n => sectorTerm b u v n - sectorTerm d u v n := by
      funext n
      simp only [sectorTerm, annihilation_sub, sub_apply, inner_sub_right]
    rw [he, (sectorTerm_summable b u v).tsum_sub (sectorTerm_summable d u v)]
  ext u v
  change annihilationForm (b-d) u v + starRingEnd ℂ (annihilationForm (b-d) v u) =
    (annihilationForm b u v + starRingEnd ℂ (annihilationForm b v u)) -
      (annihilationForm d u v + starRingEnd ℂ (annihilationForm d v u))
  rw [hs, hs, map_sub]
  ring

lemma quadraticContinuous_sub (a c : HN L 1 →L[ℂ] HN L 1) (b d : HN L 2) :
    quadraticContinuous (a-c) (b-d) = quadraticContinuous a b - quadraticContinuous c d := by
  ext u v
  change numberContinuous (a-c) u v + (1/2 : ℂ) * pairContinuous (b-d) u v =
    (numberContinuous a u v + (1/2 : ℂ) * pairContinuous b u v) -
      (numberContinuous c u v + (1/2 : ℂ) * pairContinuous d u v)
  rw [numberContinuous_sub, pairContinuous_sub]
  simp only [sub_apply]
  ring

/-- A proved operator-norm modulus, with no regularity of H(t) as an input. -/
lemma cutoff_sub_bound (a c : HN L 1 →L[ℂ] HN L 1)
    (ha : a.adjoint = a) (hc : c.adjoint = c) (b d : HN L 2) (N : ℕ) :
    ‖cutoffHamiltonian a b N - cutoffHamiltonian c d N‖ ≤
      (3 * ‖rootCutoff 1 N (L := L)‖ ^ 2) * (‖a-c‖ + ‖b-d‖) := by
  have hs : (a-c).adjoint = a-c := by rw [map_sub, ha, hc]
  have hb (u v : Fock L) : ‖quadraticContinuous (a-c) (b-d) u v‖ ≤
      (3 * (‖a-c‖ + ‖b-d‖)) * ‖u‖ * ‖v‖ := by
    let raw : RawForm (Fock L) :=
      { toFun u := (quadraticContinuous (a-c) (b-d) u).toLinearMap
        map_add' u v := by ext w; simp
        map_smul' c u := by ext w; simp }
    exact raw_bound raw _ (by positivity)
      (quadraticContinuous_symmetric (a-c) hs (b-d))
      (fun u => (Complex.abs_re_le_norm _).trans
        (quadraticContinuous_diagonal_bound (a-c) (b-d) u)) u v
  apply opNorm_le_of_re_inner_le (by positivity)
  intro x y hx hy
  have he : ⟪(cutoffHamiltonian a b N - cutoffHamiltonian c d N) x, y⟫_ℂ =
      starRingEnd ℂ (quadraticContinuous (a-c) (b-d) (rootCutoff 1 N x) (rootCutoff 1 N y)) := by
    rw [← inner_conj_symm, sub_apply, inner_sub_right, cutoff_pair, cutoff_pair,
      quadraticContinuous_sub]
    rfl
  rw [he]
  calc
    _ ≤ ‖quadraticContinuous (a-c) (b-d) (rootCutoff 1 N x) (rootCutoff 1 N y)‖ :=
      (Complex.re_le_norm _).trans_eq (RCLike.norm_conj _)
    _ ≤ (3 * (‖a-c‖ + ‖b-d‖)) * ‖rootCutoff 1 N x‖ * ‖rootCutoff 1 N y‖ := hb _ _
    _ ≤ (3 * (‖a-c‖ + ‖b-d‖)) * (‖rootCutoff 1 N (L := L)‖ * 1) *
        (‖rootCutoff 1 N (L := L)‖ * 1) := by
      gcongr
      · exact (le_opNorm _ _).trans_eq (by rw [hx])
      · exact (le_opNorm _ _).trans_eq (by rw [hy])
    _ = _ := by ring

lemma cutoff_continuous (a : ℝ → HN L 1 →L[ℂ] HN L 1) (b : ℝ → HN L 2)
    (ha : Continuous a) (hb : Continuous b) (hs : ∀ t, (a t).adjoint = a t) (N : ℕ) :
    Continuous (fun t => cutoffHamiltonian (a t) (b t) N) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hz : Filter.Tendsto (fun s => (3 * ‖rootCutoff 1 N (L := L)‖ ^ 2) *
      (‖a s-a t‖ + ‖b s-b t‖)) (𝓝 t) (𝓝 0) := by
    simpa only [Pi.sub_apply, Pi.add_apply, sub_self, norm_zero, zero_add, mul_zero] using
      ((((ha.continuousAt (x := t)).sub (continuousAt_const (y := a t))).norm.add
        ((hb.continuousAt (x := t)).sub (continuousAt_const (y := b t))).norm).const_mul
        (3 * ‖rootCutoff 1 N (L := L)‖ ^ 2)).tendsto
  change Filter.Tendsto (fun s => cutoffHamiltonian (a s) (b s) N) (𝓝 t)
    (𝓝 (cutoffHamiltonian (a t) (b t) N))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact (squeeze_zero (fun _ => norm_nonneg _)
      (fun s => cutoff_sub_bound (a s) (a t) (hs s) (hs t) (b s) (b t) N) hz)

/-- The 'unit profile' restriction includes every time on the actual
PROP-022 Hartree trajectory, by the proved global sphere preservation. -/
theorem actual_hessian_identity (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L))
    (t : ℝ) (h k : L2T L) :
    let u := profile B M A hA hB hs u₀ t
    2 * Prop022HessianR118.seriesHessian B u h k =
      Prop022HessianR118.coefficientDiagonal B u (h+k) -
        Prop022HessianR118.coefficientDiagonal B u h -
          Prop022HessianR118.coefficientDiagonal B u k := by
  dsimp only
  exact Prop022HessianR118.seriesHessian_eq_coefficients B hs M A hA hB _ h k
    ((profile_spec B M A hA hB hs u₀).2.2.1 t)

end QuantumNLS.Prop022FormContinuityR119

#print axioms QuantumNLS.Prop022FormContinuityR119.cutoff_sub_bound

#print axioms QuantumNLS.Prop022FormContinuityR119.cutoff_continuous

#print axioms QuantumNLS.Prop022FormContinuityR119.actual_hessian_identity

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022FormContinuityR119." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022FormContinuityR119." then
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
  Lean.logInfo m!"R119 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
