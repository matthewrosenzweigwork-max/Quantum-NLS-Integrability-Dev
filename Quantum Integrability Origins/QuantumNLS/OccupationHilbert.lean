import QuantumNLS.Occupation
import QuantumNLS.Gelfand
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finsupp.Encodable

/-!
# The complete occupation coefficient Hilbert space

PR11 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f, DEF-006/007/026 and
`chapters/core/occupation_transfers.tex:2–9`. The carrier is the unweighted
countable ℓ² of ALL complete occupation arrays of total N. The operators below
are constructed on this carrier, rather than postulated as an interface.
Identifying this carrier with the symmetric tensor sector or the complete Bethe
basis, and selecting the report's universal gauge, are separate obligations.
-/

noncomputable section
open scoped InnerProductSpace ComplexConjugate Classical ENNReal

namespace QuantumNLS.OccupationHilbert

open Occupation

/-- The report's full occupation coefficient carrier, with no finite-label truncation. -/
abbrev H (N : ℕ) := lp (fun _ : Arr N => ℂ) 2

example (N : ℕ) : Countable (Arr N) := inferInstance
example (N : ℕ) : CompleteSpace (H N) := inferInstance
example (N : ℕ) : InnerProductSpace ℂ (H N) := inferInstance

abbrev L2 (I : Type*) := lp (fun _ : I => ℂ) 2

section GeneralL2
variable {I J : Type*}

/-- Each coordinate inclusion is an isometry. -/
def singleIsometry (i : I) : ℂ →ₗᵢ[ℂ] L2 I where
  __ := lp.lsingle (E := fun _ : I => ℂ) (𝕜 := ℂ) 2 i
  norm_map' z := lp.norm_single (E := fun _ : I => ℂ) (p := 2) (by norm_num) i z

lemma single_orthogonal : OrthogonalFamily ℂ (fun _ : I => ℂ)
    (singleIsometry : I → ℂ →ₗᵢ[ℂ] L2 I) := by
  classical
  intro i j hij z w
  change inner ℂ (lp.single 2 i z : L2 I) (lp.single 2 j w : L2 I) = 0
  rw [lp.inner_single_left]
  simp [lp.single_apply, Pi.single_eq_of_ne hij]

/-- Extension by zero along any injection of coordinate sets. -/
def injectL2 (f : I → J) (hf : Function.Injective f) : L2 I →ₗᵢ[ℂ] L2 J :=
  ((single_orthogonal (I := J)).comp hf).linearIsometry

@[simp] lemma injectL2_single (f : I → J) (hf : Function.Injective f) (i : I) (z : ℂ) :
    injectL2 f hf (lp.single 2 i z) = lp.single 2 (f i) z := by
  classical
  exact OrthogonalFamily.linearIsometry_apply_single
    ((single_orthogonal (I := J)).comp hf) (i := i) z

/-- Restriction to the injected coordinates, constructed as an adjoint. -/
def restrictL2 (f : I → J) (hf : Function.Injective f) : L2 J →L[ℂ] L2 I :=
  (injectL2 f hf).toContinuousLinearMap.adjoint

@[simp] lemma restrictL2_apply (f : I → J) (hf : Function.Injective f) (v : L2 J) (i : I) :
    restrictL2 f hf v i = v (f i) := by
  classical
  have h := (injectL2 f hf).toContinuousLinearMap.adjoint_inner_right (lp.single 2 i 1) v
  simpa only [restrictL2, lp.inner_single_left, LinearIsometry.coe_toContinuousLinearMap,
    injectL2_single, RCLike.inner_apply, map_one, one_mul, mul_one] using h

lemma restrictL2_norm_le (f : I → J) (hf : Function.Injective f) (v : L2 J) :
    ‖restrictL2 f hf v‖ ≤ ‖v‖ := by
  apply le_trans ((restrictL2 f hf).le_opNorm v)
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [restrictL2, ContinuousLinearMap.adjoint.norm_map]
  exact (injectL2 f hf).toContinuousLinearMap.opNorm_le_bound zero_le_one
    (by intro x; simp)

/-- Pointwise multiplication by a bounded coefficient. -/
def diagonalLinear (c : I → ℂ) (C : ℝ) (hc : ∀ i, ‖c i‖ ≤ C) :
    L2 I →ₗ[ℂ] L2 I where
      toFun := fun v => ⟨fun i => c i * v i,
        ((lp.memℓp v).norm.const_mul C).mono (by
          intro i
          simpa only [Pi.mul_apply, Pi.smul_apply, norm_mul] using
            mul_le_mul_of_nonneg_right (hc i) (norm_nonneg (v i)))⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        funext i
        change c i * (x i + y i) = c i * x i + c i * y i
        exact mul_add _ _ _
      map_smul' := by intros; apply Subtype.ext; funext i; simp [mul_left_comm]

/-- A bounded diagonal multiplier on ℓ², constructed by pointwise multiplication. -/
def diagonal (c : I → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) :
    L2 I →L[ℂ] L2 I :=
  (diagonalLinear c C hc).mkContinuous C (by
      intro v
      have h := lp.norm_mono (p := 2) (by norm_num)
        (x := diagonalLinear c C hc v)
        (y := (C : ℂ) • v) (fun i => by
          change ‖c i * v i‖ ≤ ‖((C : ℂ) • v) i‖
          simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, norm_mul]
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
          exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg (v i)))
      simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using h)

@[simp] lemma diagonal_apply (c : I → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C)
    (v : L2 I) (i : I) : diagonal c C hC hc v i = c i * v i := rfl

lemma diagonal_norm_le (c : I → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) :
    ‖diagonal c C hC hc‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

end GeneralL2

/-- The canonical normalized complete basis of the coefficient carrier. -/
def basis (N : ℕ) : HilbertBasis (Arr N) ℂ (H N) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] lemma basis_apply (N : ℕ) (m : Arr N) : basis N m = lp.single 2 m 1 := by
  convert! ((basis N).repr_symm_single m).symm using 1

/-- The algebraic finite-support core embeds with its actual coordinate values. -/
def core (N : ℕ) : Sector N →ₗ[ℂ] H N :=
  Finsupp.linearCombination ℂ (fun m => lp.single 2 m (1 : ℂ))

@[simp] lemma core_single (N : ℕ) (m : Arr N) (z : ℂ) :
    core N (Finsupp.single m z) = lp.single 2 m z := by
  simp only [core, Finsupp.linearCombination_single, ← lp.single_smul, smul_eq_mul, mul_one]

@[simp] lemma core_apply (N : ℕ) (v : Sector N) (m : Arr N) : core N v m = v m := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single n z => simp [lp.single_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]

lemma core_injective (N : ℕ) : Function.Injective (core N) := by
  intro u v h
  ext m
  simpa using congrArg (fun x : H N => x m) h

/-- Finite occupation vectors are dense in the complete, untruncated ℓ² carrier. -/
lemma core_dense (N : ℕ) : DenseRange (core N) := by
  intro v
  refine mem_closure_of_tendsto (lp.hasSum_single (by norm_num) v)
    (Filter.Eventually.of_forall fun s => ?_)
  exact ⟨∑ m ∈ s, Finsupp.single m (v m), by simp⟩

lemma inner_core (N : ℕ) (u v : Sector N) :
    inner ℂ (core N u) (core N v) = ipS N u v := by
  rw [ipS_eq]
  convert! (basis N).orthonormal.inner_finsupp_eq_sum_left u v using 1
  have hb : (fun m : Arr N => lp.single 2 m (1 : ℂ)) = ⇑(basis N) :=
    funext fun m => (basis_apply N m).symm
  simp only [core, hb]

/-- The occupied-donor domain of a transfer in a fixed complete sector. -/
abbrev Donor (N : ℕ) (a : ℤ) := {m : Arr N // DonorOK a m.1}

def destination (N : ℕ) (a b : ℤ) (m : Donor N a) : Arr N :=
  shiftArr a b m.1 m.2

lemma destination_injective (N : ℕ) (a b : ℤ) :
    Function.Injective (destination N a b) := by
  intro m n h
  apply Subtype.ext
  apply Subtype.ext
  exact shift_injOn m.2 n.2 (congrArg Subtype.val h)

lemma restrict_donor_single (N : ℕ) (a : ℤ) (m : Arr N) (z : ℂ) :
    restrictL2 (Subtype.val : Donor N a → Arr N) Subtype.val_injective (lp.single 2 m z) =
      if h : DonorOK a m.1 then lp.single 2 (⟨m, h⟩ : Donor N a) z else 0 := by
  apply lp.ext
  funext d
  rw [restrictL2_apply]
  split_ifs with h
  · simp [lp.single_apply, Pi.single_apply, Subtype.ext_iff]
  · have hd : d.1 ≠ m := by intro he; exact h (he ▸ d.2)
    simp [lp.single_apply, Pi.single_eq_of_ne hd]

/-- A concrete weighted partial shift: restriction, bounded multiplication, then
extension by zero along the injective destination map. -/
def transferOp (N : ℕ) (a b : ℤ) (c : Donor N a → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1) :
    H N →L[ℂ] H N :=
  (injectL2 (destination N a b) (destination_injective N a b)).toContinuousLinearMap ∘L
    diagonal c 1 zero_le_one hc ∘L
    restrictL2 (Subtype.val : Donor N a → Arr N) Subtype.val_injective

lemma transferOp_norm_le (N : ℕ) (a b : ℤ) (c : Donor N a → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1) :
    ‖transferOp N a b c hc‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖injectL2 (destination N a b) (destination_injective N a b)
    (diagonal c 1 zero_le_one hc
      (restrictL2 (Subtype.val : Donor N a → Arr N) Subtype.val_injective v))‖ ≤ 1 * ‖v‖
  rw [LinearIsometry.norm_map, one_mul]
  calc
    ‖diagonal c 1 zero_le_one hc (restrictL2 _ _ v)‖ ≤
        ‖diagonal c 1 zero_le_one hc‖ * ‖restrictL2 _ _ v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖restrictL2 _ _ v‖ :=
      mul_le_mul_of_nonneg_right (diagonal_norm_le c 1 zero_le_one hc) (norm_nonneg _)
    _ ≤ ‖v‖ := by simpa using restrictL2_norm_le _ _ v

lemma transferOp_single (N : ℕ) (a b : ℤ) (c : Donor N a → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1)
    (m : Arr N) (z : ℂ) :
    transferOp N a b c hc (lp.single 2 m z) =
      if h : DonorOK a m.1 then
        lp.single 2 (shiftArr a b m h) (c ⟨m, h⟩ * z) else 0 := by
  simp only [transferOp, ContinuousLinearMap.comp_apply, restrict_donor_single]
  split_ifs with h
  · have hd : diagonal c 1 zero_le_one hc (lp.single 2 (⟨m, h⟩ : Donor N a) z) =
        lp.single 2 (⟨m, h⟩ : Donor N a) (c ⟨m, h⟩ * z) := by
      apply lp.ext
      funext d
      by_cases he : d = ⟨m, h⟩ <;> simp [lp.single_apply, he]
    rw [hd]
    convert! injectL2_single (destination N a b) (destination_injective N a b)
      ⟨m, h⟩ (c ⟨m, h⟩ * z) using 1
    · simp only [LinearIsometry.coe_toContinuousLinearMap]
      congr 1
      apply lp.ext
      funext d
      simp [lp.single_apply, Pi.single_apply]
    · apply lp.ext
      funext d
      simp [lp.single_apply, Pi.single_apply, destination]
  · simp

/-- Ungauged partial occupation transfer (the coefficient-space version of `W`). -/
def W (N : ℕ) (a b : ℤ) : H N →L[ℂ] H N :=
  transferOp N a b (fun _ => 1) (by intro m; simp)

lemma W_norm_le (N : ℕ) (a b : ℤ) : ‖W N a b‖ ≤ 1 :=
  transferOp_norm_le _ _ _ _ _

lemma coefficient_bound (N : ℕ) (a b : ℤ) (m : Arr N) : ‖(coef N a b m.1 : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coef_nonneg N a b m.1)]
  by_cases hN : N = 0
  · subst N; simp [coef]
  · exact coef_le_one (Nat.pos_of_ne_zero hN) m.2 a b

/-- The normalized weighted transfer `E_{N,ab}` as a bounded operator on ℓ²(𝓜_N).
The coefficient and destination are the report's concrete formulas. -/
def E (N : ℕ) (a b : ℤ) : H N →L[ℂ] H N :=
  transferOp N a b (fun m => (coef N a b m.1.1 : ℂ))
    (fun m => coefficient_bound N a b m.1)

lemma E_norm_le (N : ℕ) (a b : ℤ) : ‖E N a b‖ ≤ 1 := transferOp_norm_le _ _ _ _ _

lemma E_single (N : ℕ) (a b : ℤ) (m : Arr N) (z : ℂ) :
    E N a b (lp.single 2 m z) = if h : DonorOK a m.1 then
      lp.single 2 (shiftArr a b m h) ((coef N a b m.1 : ℂ) * z) else 0 :=
  transferOp_single _ _ _ _ _ _ _

/-- The bounded realization really extends the previously proved algebraic map. -/
lemma E_core (N : ℕ) (a b : ℤ) (v : Sector N) :
    E N a b (core N v) = core N (EN N a b v) := by
  have h : (E N a b).toLinearMap.comp (core N) = (core N).comp (EN N a b) := by
    apply Finsupp.lhom_ext
    intro m z
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, core_single, E_single,
      EN, LinearMap.smul_apply, TN, Finsupp.linearCombination_single]
    split_ifs with hd
    · simp only [map_smul, core_single, smul_smul, ← lp.single_smul, smul_eq_mul, mul_one]
      congr 1
      rw [coef_eq_w]
      push_cast
      ring
    · simp
  exact LinearMap.congr_fun h v

/-- Bounded operators are determined by the dense finite occupation core. -/
lemma ext_core (N : ℕ) {A B : H N →L[ℂ] H N}
    (h : ∀ v : Sector N, A (core N v) = B (core N v)) : A = B := by
  apply DFunLike.coe_injective
  exact (core_dense N).equalizer A.continuous B.continuous (funext h)

/-- Exact CCR on the complete coefficient Hilbert space, with the source signs
and every diagonal/index coincidence retained (`wick_calculus.tex:131–134`). -/
theorem E_comm {N : ℕ} (hN : 0 < N) (a b c d : ℤ) :
    E N a b * E N c d - E N c d * E N a b =
      ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • E N c b
        - (if b = c then (1 : ℂ) else 0) • E N a d) := by
  apply ext_core N
  intro v
  have h := congrArg (core N) (LinearMap.congr_fun (EN_comm hN a b c d) v)
  simpa only [sub_apply, mul_apply_eq_comp,
    smul_apply, E_core, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, map_sub, map_smul] using h

/-- Adjointness extends by density in BOTH variables, using the actual core pairing. -/
theorem E_inner_adjoint (N : ℕ) (a b : ℤ) (u v : H N) :
    inner ℂ u (E N a b v) = inner ℂ (E N b a u) v := by
  apply (core_dense N).induction_on₂
    (p := fun u v => inner ℂ u (E N a b v) = inner ℂ (E N b a u) v)
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_ u v
  intro x y
  simpa only [E_core, inner_core] using EN_adjoint N a b x y

theorem E_adjoint (N : ℕ) (a b : ℤ) : (E N a b).adjoint = E N b a := by
  apply ContinuousLinearMap.ext
  intro v
  exact ext_inner_left ℂ fun u => by
    rw [ContinuousLinearMap.adjoint_inner_right, E_inner_adjoint]

/-- The source minor identity on the complete coefficient carrier
(`wick_calculus.tex:146–150`), obtained from the algebraic sector identity. -/
theorem E_minors (N : ℕ) (a b c d : ℤ) :
    E N a b * E N c d - E N a d * E N c b =
      ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • E N c b
        - (if a = b then (1 : ℂ) else 0) • E N c d) := by
  have hsector : EN N a b * EN N c d - EN N a d * EN N c b =
      ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • EN N c b
        - (if a = b then (1 : ℂ) else 0) • EN N c d) := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun x : Sector N => ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) • x)
      (LinearMap.congr_fun (TN_minors N a b c d) v)
    simpa only [EN, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      map_smul, smul_sub, smul_smul, mul_assoc, mul_left_comm, mul_comm] using h
  apply ext_core N
  intro v
  have h := congrArg (core N) (LinearMap.congr_fun hsector v)
  simpa only [sub_apply, mul_apply_eq_comp, smul_apply, E_core,
    LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul] using h

lemma unitGauge_norm {q : Occ → ℂ} (hq : UnitGauge q) (m : Occ) : ‖q m‖ = 1 := by
  have h := hq m
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (q m)]

/-- The actual bounded diagonal rephasing for any given unit-modulus function.
This constructs an operator for a supplied gauge; it does not select the Bethe gauge. -/
def gauge (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) : H N →L[ℂ] H N :=
  diagonal (fun m : Arr N => q m.1) 1 zero_le_one
    (fun m => (unitGauge_norm hq m.1).le)

@[simp] lemma gauge_apply (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (v : H N) (m : Arr N) :
    gauge N q hq v m = q m.1 * v m := rfl

lemma unitGauge_conj {q : Occ → ℂ} (hq : UnitGauge q) :
    UnitGauge (fun m => (starRingEnd ℂ) (q m)) := by
  intro m
  simpa using hq m

lemma gauge_norm_le (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) : ‖gauge N q hq‖ ≤ 1 :=
  diagonal_norm_le _ _ _ _

lemma gauge_core (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (v : Sector N) :
    gauge N q hq (core N v) = core N (DgN N q v) := by
  have h : (gauge N q hq).toLinearMap.comp (core N) = (core N).comp (DgN N q) := by
    apply Finsupp.lhom_ext
    intro m z
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, core_single,
      DgN, Finsupp.linearCombination_single, map_smul, core_single]
    apply lp.ext
    funext n
    by_cases hn : n = m <;> simp [lp.single_apply, hn, mul_comm]
  exact LinearMap.congr_fun h v

/-- Gauged normalized transfer, by concrete diagonal conjugation. -/
def Eq (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (a b : ℤ) : H N →L[ℂ] H N :=
  gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) * E N a b * gauge N q hq

lemma Eq_core (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (a b : ℤ) (v : Sector N) :
    Eq N q hq a b (core N v) = core N (EqN N q a b v) := by
  simp only [Eq, mul_apply_eq_comp, gauge_core, E_core, EqN, TqN,
    EN, LinearMap.smul_apply, Module.End.mul_apply, map_smul]

lemma Eq_norm_le (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (a b : ℤ) :
    ‖Eq N q hq a b‖ ≤ 1 := by
  calc
    ‖Eq N q hq a b‖ ≤ ‖gauge N _ (unitGauge_conj hq) * E N a b‖ * ‖gauge N q hq‖ :=
      norm_mul_le _ _
    _ ≤ (1 * 1) * 1 := mul_le_mul
      (le_trans (norm_mul_le _ _) (mul_le_mul (gauge_norm_le _ _ _) (E_norm_le _ _ _)
        (norm_nonneg _) zero_le_one))
      (gauge_norm_le _ _ _) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem Eq_comm (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (a b c d : ℤ) :
    Eq N q hq a b * Eq N q hq c d - Eq N q hq c d * Eq N q hq a b =
      ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • Eq N q hq c b
        - (if b = c then (1 : ℂ) else 0) • Eq N q hq a d) := by
  apply ext_core N
  intro v
  have h := congrArg (core N) (LinearMap.congr_fun (EqN_comm hq N a b c d) v)
  simpa only [sub_apply, mul_apply_eq_comp, smul_apply, Eq_core,
    LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul] using h

theorem Eq_inner_adjoint (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (a b : ℤ) (u v : H N) :
    inner ℂ u (Eq N q hq a b v) = inner ℂ (Eq N q hq b a u) v := by
  apply (core_dense N).induction_on₂
    (p := fun u v => inner ℂ u (Eq N q hq a b v) = inner ℂ (Eq N q hq b a u) v)
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_ u v
  intro x y
  simpa only [Eq_core, inner_core] using EqN_adjoint N q a b x y

theorem Eq_adjoint (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (a b : ℤ) :
    (Eq N q hq a b).adjoint = Eq N q hq b a := by
  apply ContinuousLinearMap.ext
  intro v
  exact ext_inner_left ℂ fun u => by
    rw [ContinuousLinearMap.adjoint_inner_right, Eq_inner_adjoint]

theorem Eq_minors (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (a b c d : ℤ) :
    Eq N q hq a b * Eq N q hq c d - Eq N q hq a d * Eq N q hq c b =
      ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • Eq N q hq c b
        - (if a = b then (1 : ℂ) else 0) • Eq N q hq c d) := by
  have hsector : EqN N q a b * EqN N q c d - EqN N q a d * EqN N q c b =
      ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • EqN N q c b
        - (if a = b then (1 : ℂ) else 0) • EqN N q c d) := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun x : Sector N => ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) • x)
      (LinearMap.congr_fun (TqN_minors hq N a b c d) v)
    simpa only [EqN, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      map_smul, smul_sub, smul_smul, mul_assoc, mul_left_comm, mul_comm] using h
  apply ext_core N
  intro v
  have h := congrArg (core N) (LinearMap.congr_fun hsector v)
  simpa only [sub_apply, mul_apply_eq_comp, smul_apply, Eq_core,
    LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul] using h

lemma gauge_single (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (m : Arr N) (z : ℂ) :
    gauge N q hq (lp.single 2 m z) = lp.single 2 m (q m.1 * z) := by
  apply lp.ext
  funext n
  by_cases hn : n = m <;> simp [lp.single_apply, hn]

/-- Exact phase and coefficient from source equations W/E on the full Hilbert carrier. -/
theorem Eq_single (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (a b : ℤ) (m : Arr N) (z : ℂ) :
    Eq N q hq a b (lp.single 2 m z) = if h : DonorOK a m.1 then
      lp.single 2 (shiftArr a b m h)
        ((q m.1 * (starRingEnd ℂ) (q (shift a b m.1)) * (coef N a b m.1 : ℂ)) * z)
      else 0 := by
  simp only [Eq, mul_apply_eq_comp, gauge_single, E_single]
  split_ifs with hd
  · rw [gauge_single]
    congr 1
    change (starRingEnd ℂ) (q (shift a b m.1)) *
      ((coef N a b m.1 : ℂ) * (q m.1 * z)) = _
    ring
  · simp

theorem Eq_diag (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (a : ℤ) : Eq N q hq a a = E N a a := by
  apply ext_core N
  intro v
  rw [Eq_core, E_core, EqN_diag hq]

/-- The coefficient Hilbert sector is nonzero, including N=0. -/
instance (N : ℕ) : Nontrivial (H N) := by
  let m : Arr N := ⟨Finsupp.single 0 N, by simp [IsArray, total]⟩
  refine ⟨⟨lp.single 2 m 1, 0, ?_⟩⟩
  intro h
  have he := congrArg (fun v : H N => v m) h
  simp at he

/-- A genuinely bounded sequence of operators on varying complete occupation sectors.
The N=0 component is the explicit inverse-zero convention for E and causes no tail change. -/
def ESequence (a b : ℤ) : lp (fun N : ℕ => H N →L[ℂ] H N) ∞ :=
  ⟨fun N => E N a b, memℓp_infty ⟨1, by rintro _ ⟨N, rfl⟩; exact E_norm_le N a b⟩⟩

def EqSequence (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (a b : ℤ) :
    lp (fun N : ℕ => H N →L[ℂ] H N) ∞ :=
  ⟨fun N => Eq N (q N) (hq N) a b,
    memℓp_infty ⟨1, by rintro _ ⟨N, rfl⟩; exact Eq_norm_le N (q N) (hq N) a b⟩⟩

lemma ESequence_star (a b : ℤ) : star (ESequence a b) = ESequence b a := by
  apply lp.ext
  funext N
  exact (ContinuousLinearMap.star_eq_adjoint _).trans (E_adjoint N a b)

lemma EqSequence_star (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (a b : ℤ) :
    star (EqSequence q hq a b) = EqSequence q hq b a := by
  apply lp.ext
  funext N
  exact (ContinuousLinearMap.star_eq_adjoint _).trans (Eq_adjoint N (q N) (hq N) a b)

/-- Exact diagonal action on every vector, derived on the finite core and extended
by continuity of coordinate evaluation. -/
lemma E_diag_apply (N : ℕ) (a : ℤ) (v : H N) (m : Arr N) :
    E N a a v m = (coef N a a m.1 : ℂ) * v m := by
  have h : (fun v : H N => E N a a v m) =
      (fun v : H N => (coef N a a m.1 : ℂ) * v m) := by
    apply (core_dense N).equalizer
    · exact (lp.evalCLM ℂ (fun _ : Arr N => ℂ) 2 m).continuous.comp (E N a a).continuous
    · exact continuous_const.mul (lp.evalCLM ℂ (fun _ : Arr N => ℂ) 2 m).continuous
    · funext u
      change E N a a (core N u) m = (coef N a a m.1 : ℂ) * core N u m
      induction u using Finsupp.induction_linear with
      | zero => simp
      | add u w hu hw => simp [hu, hw, mul_add]
      | single n z =>
        simp only [core_single, E_single]
        by_cases hd : DonorOK a n.1
        · have hs : shiftArr a a n hd = n := Subtype.ext (shift_self hd)
          simp only [hd, ↓reduceDIte, hs]
          by_cases hm : m = n <;> simp [lp.single_apply, hm]
        · have hz : coef N a a n.1 = 0 := coef_empty_donor (by unfold DonorOK at hd; omega)
          simp only [hd, ↓reduceDIte, lp.coeFn_zero, Pi.zero_apply]
          by_cases hm : m = n <;> simp [lp.single_apply, hm, hz]
  exact congrFun h v

lemma sum_E_diag_apply (N : ℕ) (S : Finset ℤ) (v : H N) (m : Arr N) :
    (∑ a ∈ S, E N a a) v m = ((∑ a ∈ S, coef N a a m.1 : ℝ) : ℂ) * v m := by
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply, E_diag_apply]
  rw [← Finset.sum_mul, Complex.ofReal_sum]

/-- The finite-label diagonal sum is a contraction. No restriction of the
occupation carrier to that label set is made. -/
theorem sum_E_diag_norm_le {N : ℕ} (hN : 0 < N) (S : Finset ℤ) :
    ‖∑ a ∈ S, E N a a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply lp.norm_mono (p := 2) (by norm_num)
  intro m
  rw [sum_E_diag_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun a _ => coef_nonneg N a a m.1)]
  exact mul_le_of_le_one_left (norm_nonneg _) (sum_diag_coef_le_one m.2 hN S)

/-- The source finite-label trace bound as a quadratic-form inequality. -/
theorem sum_E_diag_inner_le {N : ℕ} (hN : 0 < N) (S : Finset ℤ) (v : H N) :
    (inner ℂ v ((∑ a ∈ S, E N a a) v)).re ≤ ‖v‖ ^ 2 := by
  calc
    (inner ℂ v ((∑ a ∈ S, E N a a) v)).re ≤ ‖inner ℂ v ((∑ a ∈ S, E N a a) v)‖ :=
      Complex.re_le_norm _
    _ ≤ ‖v‖ * ‖(∑ a ∈ S, E N a a) v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖∑ a ∈ S, E N a a‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖v‖ * (1 * ‖v‖) := by gcongr; exact sum_E_diag_norm_le hN S
    _ = ‖v‖ ^ 2 := by ring

theorem sum_Eq_diag_inner_le {N : ℕ} (hN : 0 < N) (q : Occ → ℂ) (hq : UnitGauge q)
    (S : Finset ℤ) (v : H N) :
    (inner ℂ v ((∑ a ∈ S, Eq N q hq a a) v)).re ≤ ‖v‖ ^ 2 := by
  simpa only [Eq_diag] using sum_E_diag_inner_le hN S v

/-- Finite matrix quadratic combination, with precisely the source's donor/receiver convention. -/
def matrixOp (N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) : H N →L[ℂ] H N :=
  ∑ a ∈ S, ∑ b ∈ S, ((starRingEnd ℂ) (v a) * v b) • E N a b

private lemma ip_finset_sum_right {I : Type*} (S : Finset I) (f : I → FS) (u : FS) :
    ip u (∑ i ∈ S, f i) = ∑ i ∈ S, ip u (f i) := by
  induction S using Finset.induction_on with
  | empty => simp [ip_zero_right]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add_right, ih]

/-- The actual finite-support annihilation vector used in the positivity proof. -/
def annihilationSum (S : Finset ℤ) (v : ℤ → ℂ) (u : FS) : FS :=
  ∑ a ∈ S, (starRingEnd ℂ) (v a) • Ann a u

lemma fs_matrix_identity (S : Finset ℤ) (v : ℤ → ℂ) (u : FS) :
    (∑ a ∈ S, ∑ b ∈ S, ((starRingEnd ℂ) (v a) * v b) * ip u (Top a b u)) =
      ip (annihilationSum S v u) (annihilationSum S v u) := by
  simp_rw [Top_eq_Cre_Ann, Module.End.mul_apply, Cre_adjoint]
  symm
  unfold annihilationSum
  rw [ip_sum_left]
  simp only [ip_smul_left, ip_finset_sum_right,
    ip_smul_right, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Positivity is a sum-of-squares identity on the dense core, not an assumed
matrix-positivity field. -/
lemma matrixOp_inner_core (N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (u : Sector N) :
    inner ℂ (core N u) (matrixOp N S v (core N u)) =
      ((N : ℂ)⁻¹) * ip (annihilationSum S v (emb N u)) (annihilationSum S v (emb N u)) := by
  simp only [matrixOp, sum_apply, smul_apply, inner_sum, inner_smul_right, E_core,
    inner_core, ipS, emb_EN, EOp, LinearMap.smul_apply, ip_smul_right]
  rw [← fs_matrix_identity S v (emb N u)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma matrixOp_inner_nonneg (N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (u : H N) :
    0 ≤ (inner ℂ u (matrixOp N S v u)).re := by
  refine (core_dense N).induction_on
    (p := fun u => 0 ≤ (inner ℂ u (matrixOp N S v u)).re)
    u (isClosed_le continuous_const (by fun_prop)) ?_
  intro x
  rw [matrixOp_inner_core]
  have hr : 0 ≤ ((N : ℂ)⁻¹).re := by
    rw [Complex.inv_re]
    exact div_nonneg (by simp) (Complex.normSq_nonneg _)
  have hi : ((N : ℂ)⁻¹).im = 0 := by simp [Complex.inv_im]
  rw [Complex.mul_re, hi, zero_mul, sub_zero, ip_self_re]
  exact mul_nonneg hr
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

lemma matrixOp_selfAdjoint (N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) :
    IsSelfAdjoint (matrixOp N S v) := by
  change (matrixOp N S v).adjoint = matrixOp N S v
  simp only [matrixOp, map_sum, map_smulₛₗ, E_adjoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  simp [mul_comm]

/-- The source matrix combination is a positive bounded operator. -/
theorem matrixOp_positive (N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) :
    (matrixOp N S v).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨matrixOp_selfAdjoint N S v, ?_⟩
  intro u
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
  exact matrixOp_inner_nonneg N S v u

lemma gauge_adjoint (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) :
    (gauge N q hq).adjoint = gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro m
  simp only [gauge_apply, RCLike.inner_apply, map_mul]
  ring

def matrixOpq (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (S : Finset ℤ) (v : ℤ → ℂ) :
    H N →L[ℂ] H N :=
  ∑ a ∈ S, ∑ b ∈ S, ((starRingEnd ℂ) (v a) * v b) • Eq N q hq a b

lemma matrixOpq_conjugation (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q)
    (S : Finset ℤ) (v : ℤ → ℂ) :
    matrixOpq N q hq S v = (gauge N q hq).adjoint * matrixOp N S v * gauge N q hq := by
  simp only [matrixOpq, matrixOp, gauge_adjoint, Eq, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc]

theorem matrixOpq_positive (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q)
    (S : Finset ℤ) (v : ℤ → ℂ) : (matrixOpq N q hq S v).IsPositive := by
  rw [matrixOpq_conjugation]
  have h := (matrixOp_positive N S v).conj_adjoint (gauge N q hq).adjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc] using h

/-- The source finite-label inequality `∑ B_a ≤ Id`, in positive-operator form. -/
theorem one_sub_sum_diag_positive {N : ℕ} (hN : 0 < N) (S : Finset ℤ) :
    (1 - ∑ a ∈ S, E N a a).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  constructor
  · change (1 - ∑ a ∈ S, E N a a).adjoint = 1 - ∑ a ∈ S, E N a a
    simp only [map_sub, ContinuousLinearMap.adjoint_one, map_sum, E_adjoint]
  · intro u
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
    simp only [sub_apply, one_apply_eq_self, inner_sub_right, map_sub, inner_self_eq_norm_sq_to_K,
      RCLike.re_ofReal_pow]
    exact sub_nonneg.mpr (sum_E_diag_inner_le hN S u)

theorem one_sub_sum_diagq_positive {N : ℕ} (hN : 0 < N) (q : Occ → ℂ) (hq : UnitGauge q)
    (S : Finset ℤ) : (1 - ∑ a ∈ S, Eq N q hq a a).IsPositive := by
  simpa only [Eq_diag] using one_sub_sum_diag_positive hN S

/-- The concrete fiber algebras for the coefficient-space quotient. -/
abbrev Fiber (N : ℕ) := H N →L[ℂ] H N

abbrev OccupationQuotient := Gelfand.SequenceQuotient Fiber

/-- The report's sequence-quotient generators, now instantiated with actual
bounded occupation operators rather than assumed finite-N identities. -/
def quotientGenerator (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (a b : ℤ) :
    OccupationQuotient := Gelfand.sequenceQuotientMk Fiber (EqSequence q hq a b)

private lemma indicator_smul (N : ℕ) (p : Prop) [Decidable p] (T : Fiber N) :
    (if p then (1 : ℂ) else 0) • T = if p then T else 0 := by
  split_ifs
  · exact one_smul ℂ T
  · exact zero_smul ℂ T

lemma quotientGenerator_star (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (a b : ℤ) :
    star (quotientGenerator q hq a b) = quotientGenerator q hq b a := by
  simp only [quotientGenerator, ← map_star, EqSequence_star]

theorem quotientGenerator_commute (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (a b c d : ℤ) :
    Commute (quotientGenerator q hq a b) (quotientGenerator q hq c d) := by
  apply Gelfand.sequenceQuotient_commute_of_CCR Fiber (EqSequence q hq)
  intro i j k l
  exact Filter.Eventually.of_forall fun N => by
    change Eq N (q N) (hq N) i j * Eq N (q N) (hq N) k l -
        Eq N (q N) (hq N) k l * Eq N (q N) (hq N) i j =
      (N : ℂ)⁻¹ • ((if i = l then Eq N (q N) (hq N) k j else 0) -
        (if j = k then Eq N (q N) (hq N) i l else 0))
    simpa only [indicator_smul] using Eq_comm N (q N) (hq N) i j k l

theorem quotientGenerator_minors (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (a b c d : ℤ) :
    quotientGenerator q hq a b * quotientGenerator q hq c d =
      quotientGenerator q hq a d * quotientGenerator q hq c b := by
  apply Gelfand.sequenceQuotient_minors_of_identity Fiber (EqSequence q hq)
  intro i j k l
  exact Filter.Eventually.of_forall fun N => by
    change Eq N (q N) (hq N) i j * Eq N (q N) (hq N) k l -
        Eq N (q N) (hq N) i l * Eq N (q N) (hq N) k j =
      (N : ℂ)⁻¹ • ((if i = l then Eq N (q N) (hq N) k j else 0) -
        (if i = j then Eq N (q N) (hq N) k l else 0))
    simpa only [indicator_smul] using Eq_minors N (q N) (hq N) i j k l

/-- The closed unital star algebra for any fixed finite label set. -/
abbrev quotientAlgebra (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ) :=
  Gelfand.generatedAlgebra (fun a b : I => quotientGenerator q hq a.1 b.1)

theorem quotientAlgebra_commutative (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N))
    (I : Finset ℤ) : IsMulCommutative (quotientAlgebra q hq I) :=
  Gelfand.generatedAlgebra_isMulCommutative _
    (fun a b => quotientGenerator_star q hq a.1 b.1)
    (fun a b c d => quotientGenerator_commute q hq a.1 b.1 c.1 d.1)

/-- Concrete coefficient-space application of the admitted Gelfand theorem.
Physical U4/U5 transport and character positivity/trace transfer remain separate. -/
def quotientGelfand (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ) :
    quotientAlgebra q hq I ≃⋆ₐ[ℂ]
      C(WeakDual.characterSpace ℂ (quotientAlgebra q hq I), ℂ) :=
  Gelfand.generatedGelfand _
    (fun a b => quotientGenerator_star q hq a.1 b.1)
    (fun a b c d => quotientGenerator_commute q hq a.1 b.1 c.1 d.1)

theorem quotientGelfand_isometry (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ) :
    Isometry (quotientGelfand q hq I) :=
  Gelfand.generatedGelfand_isometry _ _ _

/-- A gauge supplied on exactly the report's sector extends by phase one outside
it. Thus the all-array algebraic interface adds no hypothesis to a sector gauge. -/
def extendSectorGauge (N : ℕ) (q : Arr N → ℂ) (m : Occ) : ℂ :=
  if h : IsArray N m then q ⟨m, h⟩ else 1

@[simp] lemma extendSectorGauge_apply (N : ℕ) (q : Arr N → ℂ) (m : Arr N) :
    extendSectorGauge N q m.1 = q m := by simp [extendSectorGauge, m.2]

lemma extendSectorGauge_unit (N : ℕ) (q : Arr N → ℂ)
    (hq : ∀ m, Complex.normSq (q m) = 1) : UnitGauge (extendSectorGauge N q) := by
  intro m
  unfold extendSectorGauge
  split_ifs with h
  · exact hq ⟨m, h⟩
  · simp

/-- Source-domain version: no phase data outside 𝓜_N is requested. -/
def sectorEq (N : ℕ) (q : Arr N → ℂ) (hq : ∀ m, Complex.normSq (q m) = 1) (a b : ℤ) :
    H N →L[ℂ] H N := Eq N (extendSectorGauge N q) (extendSectorGauge_unit N q hq) a b

lemma sectorEq_single (N : ℕ) (q : Arr N → ℂ) (hq : ∀ m, Complex.normSq (q m) = 1)
    (a b : ℤ) (m : Arr N) (z : ℂ) :
    sectorEq N q hq a b (lp.single 2 m z) = if h : DonorOK a m.1 then
      lp.single 2 (shiftArr a b m h)
        ((q m * (starRingEnd ℂ) (q (shiftArr a b m h)) * (coef N a b m.1 : ℂ)) * z)
      else 0 := by
  rw [sectorEq, Eq_single]
  split_ifs with h
  · rw [extendSectorGauge_apply]
    have hs := extendSectorGauge_apply N q (shiftArr a b m h)
    change extendSectorGauge N q (shift a b m.1) = q (shiftArr a b m h) at hs
    rw [hs]
  · rfl

lemma sectorEq_norm_le (N : ℕ) (q : Arr N → ℂ) (hq : ∀ m, Complex.normSq (q m) = 1) (a b : ℤ) :
    ‖sectorEq N q hq a b‖ ≤ 1 := Eq_norm_le _ _ _ _ _

#print axioms E_core
#print axioms E_comm
#print axioms E_inner_adjoint
#print axioms E_adjoint
#print axioms E_minors
#print axioms Eq_core
#print axioms Eq_norm_le
#print axioms Eq_comm
#print axioms Eq_adjoint
#print axioms Eq_minors
#print axioms Eq_single
#print axioms Eq_diag
#print axioms ESequence_star
#print axioms EqSequence_star
#print axioms E_diag_apply
#print axioms sum_E_diag_norm_le
#print axioms sum_E_diag_inner_le
#print axioms sum_Eq_diag_inner_le
#print axioms fs_matrix_identity
#print axioms matrixOp_inner_core
#print axioms matrixOp_positive
#print axioms matrixOpq_positive
#print axioms one_sub_sum_diag_positive
#print axioms one_sub_sum_diagq_positive
#print axioms quotientGenerator_star
#print axioms quotientGenerator_commute
#print axioms quotientGenerator_minors
#print axioms quotientAlgebra_commutative
#print axioms quotientGelfand_isometry
#print axioms extendSectorGauge_unit
#print axioms sectorEq_single
#print axioms sectorEq_norm_le

#print axioms core_dense
#print axioms inner_core
#print axioms transferOp_norm_le
#print axioms transferOp_single
#print axioms E_norm_le
#print axioms E_single

end QuantumNLS.OccupationHilbert
