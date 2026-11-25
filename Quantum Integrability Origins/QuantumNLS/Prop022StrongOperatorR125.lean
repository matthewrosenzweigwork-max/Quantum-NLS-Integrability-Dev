import QuantumNLS.Prop022DomainR122
import QuantumNLS.Prop022FormContinuityR119

/-! The literal physical quadratic Hamiltonian as a bounded map from
D(Num+1), in second-moment coordinates, to physical Fock space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap Set Filter
namespace QuantumNLS.Prop022StrongOperatorR125
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005FormScaleR109 Ext005FormCutoffR109 Ext005MomentEnergyR108
open Ext005PhysicalNumberFormR114 Ext005PhysicalPairFormR114 Ext005PhysicalHalfPairR114
open Ext005ComplexRieszR113 Ext005PairSector Ext005QuadraticEnergyR108
variable {L : ℝ} [Fact (0 < L)]
local instance (priority := 1200) opNormed : NormedAddCommGroup (HN L 1 →L[ℂ] HN L 1) := inferInstance
local instance (priority := 1200) fockOpNormed : NormedAddCommGroup (Fock L →L[ℂ] Fock L) := inferInstance

/-- Shift of the actual sector sequence; its norm is a tail of the Fock norm. -/
def tail (x : Fock L) : lp (fun n => HN L (2+n)) 2 :=
  ⟨fun n => x (2+n), by
    apply memℓp_gen
    have hs := (summable_nat_add_iff 2).mpr ((lp.memℓp x).summable (by norm_num))
    convert hs using 1
    funext n
    rw [Nat.add_comm 2 n]⟩

lemma tail_norm (x : Fock L) : ‖tail x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x)
  have h := tsum_comp_le_tsum_of_inj
    ((lp.memℓp x).summable (by norm_num)) (fun n => by positivity)
    (show Function.Injective (fun n : ℕ => 2+n) from fun _ _ h => Nat.add_left_cancel h)
  rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x]
  exact h

/-- Normalized lowering block. j=3 weights its input; j=1 weights its output. -/
def lowerBlock (j : ℕ) (b : HN L 2) (n : ℕ) : HN L (2+n) →L[ℂ] HN L n :=
  ((((n : ℝ)+(j : ℝ))⁻¹ : ℝ) : ℂ) • annihilation b n

lemma lowerBlock_bound (j : ℕ) (hj : 1 ≤ j) (b : HN L 2) (n : ℕ)
    (x : HN L (2+n)) : ‖lowerBlock j b n x‖ ≤ (2*‖b‖)*‖x‖ := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hn : 0 < (n : ℝ)+(j : ℝ) := by positivity
  have hs : Real.sqrt (((n : ℝ)+1)*((n : ℝ)+2)) ≤ 2*((n : ℝ)+(j : ℝ)) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  simp only [lowerBlock, smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ ((n : ℝ)+(j : ℝ))⁻¹ *
        (‖b‖*Real.sqrt (((n : ℝ)+1)*((n : ℝ)+2))*‖x‖) :=
      mul_le_mul_of_nonneg_left (annihilation_bound b n x) (by positivity)
    _ ≤ ((n : ℝ)+(j : ℝ))⁻¹ * (‖b‖*(2*((n : ℝ)+(j : ℝ)))*‖x‖) := by gcongr
    _ = _ := by field_simp [hn.ne']

lemma lower_mem (j : ℕ) (hj : 1 ≤ j) (b : HN L 2) (x : Fock L) :
    Memℓp (fun n => lowerBlock j b n (x (2+n))) 2 := by
  apply ((lp.memℓp (tail x)).const_smul ((2*‖b‖ : ℝ) : ℂ)).mono'
  intro n
  change ‖lowerBlock j b n (x (2+n))‖ ≤ ‖((2*‖b‖ : ℝ) : ℂ) • x (2+n)‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact lowerBlock_bound j hj b n _

def lower (j : ℕ) (hj : 1 ≤ j) (b : HN L 2) : Fock L →L[ℂ] Fock L :=
  LinearMap.mkContinuous
    { toFun x := ⟨fun n => lowerBlock j b n (x (2+n)), lower_mem j hj b x⟩
      map_add' x y := by
        apply Subtype.ext
        funext n
        exact map_add (lowerBlock j b n) _ _
      map_smul' c x := by
        apply Subtype.ext
        funext n
        exact map_smul (lowerBlock j b n) c _ }
    (2*‖b‖) (by
      intro x
      calc
        _ ≤ ‖((2*‖b‖ : ℝ) : ℂ) • tail x‖ := by
          apply lp.norm_mono (by norm_num)
          intro n
          change ‖lowerBlock j b n (x (2+n))‖ ≤ ‖((2*‖b‖ : ℝ) : ℂ) • x (2+n)‖
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact lowerBlock_bound j hj b n _
        _ = (2*‖b‖)*‖tail x‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ (2*‖b‖)*‖x‖ := mul_le_mul_of_nonneg_left (tail_norm x) (by positivity))

lemma lower_norm (j : ℕ) (hj : 1 ≤ j) (b : HN L 2) : ‖lower j hj b‖ ≤ 2*‖b‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

lemma embedding_two_apply (x : Fock L) (n : ℕ) :
    embedding 2 x n = ((((n : ℝ)+1)⁻¹ : ℝ) : ℂ) • x n := by
  simp only [embedding_apply, momentWeight, Real.sqrt_sq (by positivity : 0 ≤ (n : ℝ)+1)]

lemma embedding_one_two (x : Fock L) : embedding 1 (embedding 1 x) = embedding 2 x := by
  apply Subtype.ext
  funext n
  simp only [embedding_apply, smul_smul, ← Complex.ofReal_mul]
  congr 2
  rw [← sq, inv_pow, Real.sq_sqrt (momentWeight_nonneg 1 n)]
  simp only [momentWeight, pow_one, Real.sqrt_sq (by positivity : 0 ≤ (n : ℝ)+1)]

/-- Exact annihilation after dividing by Num+1 on its input. -/
lemma lower_three_apply (b : HN L 2) (x : Fock L) (n : ℕ) :
    lower 3 (by omega) b x n = annihilation b n (embedding 2 x (2+n)) := by
  change ((((n : ℝ)+3)⁻¹ : ℝ) : ℂ) • annihilation b n (x (2+n)) = _
  rw [embedding_two_apply, map_smul]
  congr 2
  push_cast
  ring

/-- The physical dGamma(a)+1/2(a*(b)+a(b)), on second-moment coordinates. -/
def strongCoordinates (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) : Fock L →L[ℂ] Fock L :=
  numberCoordinates a + (1/2 : ℂ) • (lower 3 (by omega) b + (lower 1 (by omega) b).adjoint)

lemma numberCoordinates_two (a : HN L 1 →L[ℂ] HN L 1) (x : Fock L) (n : ℕ) :
    numberCoordinates a x n = numberBlock a n (embedding 2 x n) := by
  change normalizedBlock a n (x n) = _
  rw [normalizedBlock, smul_apply, embedding_two_apply, map_smul]

lemma number_pair (a : HN L 1 →L[ℂ] HN L 1) (x v : Fock L) :
    ⟪embedding 1 v, numberCoordinates a x⟫_ℂ = numberContinuous a (embedding 1 x) v := by
  rw [lp.inner_eq_tsum, numberContinuous_offDiagonal]
  apply tsum_congr
  intro n
  rw [numberCoordinates_two, embedding_one_two]

lemma annihilation_pair (b : HN L 2) (x v : Fock L) :
    ⟪embedding 1 v, lower 3 (by omega) b x⟫_ℂ = annihilationForm b (embedding 1 x) v := by
  rw [lp.inner_eq_tsum]
  change (∑' n, _) = ∑' n, sectorTerm b (embedding 1 x) v n
  apply tsum_congr
  intro n
  rw [lower_three_apply]
  simp only [sectorTerm, embedding_one_two]

lemma creation_pair (b : HN L 2) (x v : Fock L) :
    ⟪embedding 1 v, (lower 1 (by omega) b).adjoint x⟫_ℂ =
      starRingEnd ℂ (annihilationForm b v (embedding 1 x)) := by
  rw [adjoint_inner_right, ← inner_conj_symm, lp.inner_eq_tsum]
  congr 1
  change (∑' n, _) = ∑' n, sectorTerm b v (embedding 1 x) n
  apply tsum_congr
  intro n
  change ⟪x n, lowerBlock 1 b n (embedding 1 v (2+n))⟫_ℂ = _
  simp only [lowerBlock, smul_apply, sectorTerm, embedding_one_two,
    embedding_two_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal, Nat.cast_one]

/-- Exact representation of the existing quadratic form, retaining its
physical pair coefficients and its original one-half factor. -/
theorem strongCoordinates_pair (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (x v : Fock L) :
    ⟪embedding 1 v, strongCoordinates a b x⟫_ℂ =
      quadraticContinuous a b (embedding 1 x) v := by
  simp only [strongCoordinates, add_apply, smul_apply, inner_add_right, inner_smul_right,
    number_pair, annihilation_pair, creation_pair]
  rfl

lemma strongCoordinates_embedding (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (x : Fock L) :
    embedding 1 (strongCoordinates a b x) =
      formOperator (quadraticContinuous a b) (embedding 1 x) := by
  apply ext_inner_left ℂ
  intro v
  rw [← embedding_symmetric, strongCoordinates_pair, form_pair]

lemma numberCoordinates_norm (a : HN L 1 →L[ℂ] HN L 1) : ‖numberCoordinates a‖ ≤ ‖a‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _

/-- A dimension-independent operator bound on D(Num+1). -/
theorem strongCoordinates_norm (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) :
    ‖strongCoordinates a b‖ ≤ ‖a‖+2*‖b‖ := by
  apply opNorm_le_bound _ (by positivity)
  intro x
  have hn : ‖numberCoordinates a x‖ ≤ ‖a‖*‖x‖ :=
    (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (numberCoordinates_norm a) (norm_nonneg x))
  have hl : ‖lower 3 (by omega) b x‖ ≤ (2*‖b‖)*‖x‖ :=
    (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (lower_norm 3 (by omega) b) (norm_nonneg x))
  have hr : ‖(lower 1 (by omega) b).adjoint x‖ ≤ (2*‖b‖)*‖x‖ := by
    apply (le_opNorm _ _).trans
    rw [adjoint.norm_map]
    exact mul_le_mul_of_nonneg_right (lower_norm 1 (by omega) b) (norm_nonneg x)
  change ‖numberCoordinates a x + (1/2 : ℂ) •
    (lower 3 (by omega) b x + (lower 1 (by omega) b).adjoint x)‖ ≤ _
  have he := norm_add_le (numberCoordinates a x) ((1/2 : ℂ) •
    (lower 3 (by omega) b x + (lower 1 (by omega) b).adjoint x))
  rw [norm_smul, show ‖(1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num] at he
  have ha := norm_add_le (lower 3 (by omega) b x) ((lower 1 (by omega) b).adjoint x)
  nlinarith

lemma lower_sub (j : ℕ) (hj : 1 ≤ j) (b d : HN L 2) :
    lower j hj (b-d) = lower j hj b - lower j hj d := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change lowerBlock j (b-d) n (x (2+n)) =
    lowerBlock j b n (x (2+n)) - lowerBlock j d n (x (2+n))
  simp only [lowerBlock, Prop022FormContinuityR119.annihilation_sub,
    smul_sub, sub_apply]

lemma strongCoordinates_sub (a c : HN L 1 →L[ℂ] HN L 1) (b d : HN L 2) :
    strongCoordinates (a-c) (b-d) = strongCoordinates a b - strongCoordinates c d := by
  have hn : numberCoordinates (a-c) = numberCoordinates a - numberCoordinates c := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    change normalizedBlock (a-c) n (x n) = normalizedBlock a n (x n) - normalizedBlock c n (x n)
    simp only [normalizedBlock, Prop022FormContinuityR119.numberBlock_sub, smul_sub, sub_apply]
  simp only [strongCoordinates, hn, lower_sub, map_sub, smul_sub, smul_add]
  abel

/-- Coefficient continuity in the operator norm D(Num+1) -> Fock. -/
theorem strongCoordinates_continuous (a : ℝ → HN L 1 →L[ℂ] HN L 1)
    (b : ℝ → HN L 2) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun t => strongCoordinates (a t) (b t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  change Tendsto (fun s => strongCoordinates (a s) (b s)) (𝓝 t) (𝓝 (strongCoordinates (a t) (b t)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz : Tendsto (fun s => ‖a s-a t‖+2*‖b s-b t‖) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero, zero_add] using
      (((ha.tendsto t).sub_const (a t)).norm.add
        (((hb.tendsto t).sub_const (b t)).norm.const_mul 2))
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro s
  rw [← strongCoordinates_sub]
  exact strongCoordinates_norm _ _

lemma root_one_of_two (x : momentDomain (L := L) 2) :
    rootLift 1 x.val = embedding 1 (momentRoot 2 x) := by
  apply embedding_injective 1
  have h1 : embedding 1 (rootLift 1 x.val) = x.val :=
    (congrArg (embedding 1) (rootLift_eq 1 _ (domain_mono (by omega) x.property))).trans
      (embedding_root 1 ⟨x.val, domain_mono (by omega) x.property⟩)
  exact h1.trans ((embedding_one_two (momentRoot 2 x)).trans (embedding_root 2 x)).symm

/-- The maximal second-moment-domain action; its domain is D(Num+1). -/
def quadraticAction (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (x : momentDomain (L := L) 2) : Fock L := strongCoordinates a b (momentRoot 2 x)

theorem quadraticAction_bound (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (x : momentDomain (L := L) 2) :
    ‖quadraticAction a b x‖ ≤ (‖a‖+2*‖b‖)*‖momentRoot 2 x‖ :=
  (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (strongCoordinates_norm a b) (norm_nonneg _))

theorem quadraticAction_form (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (x : momentDomain (L := L) 2) (v : Fock L) :
    ⟪embedding 1 v, quadraticAction a b x⟫_ℂ =
      quadraticContinuous a b (rootLift 1 x.val) v := by
  rw [quadraticAction, strongCoordinates_pair, root_one_of_two]


end QuantumNLS.Prop022StrongOperatorR125

#print axioms QuantumNLS.Prop022StrongOperatorR125.lower_three_apply
set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022StrongOperatorR125." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022StrongOperatorR125." then
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
  Lean.logInfo m!"R125 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
