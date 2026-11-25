import Mathlib
import QuantumNLS.Ext002MonoLift
import QuantumNLS.BethePhysicalTransfer

/-!
# EXT-002 / V-01 full monodromy (owner decision D4), stage M2b: weak normal-ordered field monomials

Source conventions (no silent choice):
* Normalized annihilation field on a symmetric `N`-particle wave function:
  `Φ(y)G = √N G(y,·)`, and `r` applications give `√((N)_r) G(y₁,…,y_r,·)`
  (`source/chapters/foundations/A04.tex:72-76`; Vlaar thesis eq. (2.2.1), printed p. 16,
  `(Φ(y)F)(x) = √(N+1) F(x,y)` for `F ∈ D_{N+1}`, which coincides on symmetric functions).
  This is `annihilate`.
* The normal-ordered integral `∫ a(x;y) Φ*(x₁)⋯Φ*(x_r) Φ(y₁)⋯Φ(y_s)` is understood through its
  weak matrix elements (A04.tex:67-70); creation fields are the adjoints of annihilation fields
  (A04.tex:77-85), so for `F ∈ H_{r+q}`, `G ∈ H_{s+q}`
  `⟨F, W G⟩ = ∫_w ∫_x ∫_y conj((Φ^r F)(x,w)) a(x;y) (Φ^s G)(y,w)`
  (`inner_monomial`). For `r = s` this is literally A04.tex:80-82 with the factor `(N)_r`.
* Fixed-sector domains: `H_n = SymSector ℂ (L2T L) n`, realized in position space by the
  frozen `BethePhysicalTransfer.positionInclusion` (the space of the DEF-048 transfer).
The operator is constructed (not postulated) as `liftOut† ∘ (multiplication by a) ∘ liftIn`;
the adjoint is Mathlib's Riesz-representation adjoint, and the Cauchy–Schwarz bound of
A04.tex:86-91 is `norm_sliceOp_apply_le`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace ENNReal

namespace QuantumNLS.Ext002MonoFields
open PhysicalTensor TensorCarrier BethePhysicalTransfer Ext002MonoLift

variable (L : ℝ) [Fact (0 < L)]

/-- A bounded measurable kernel `a(x;y)`, `x ∈ 𝕋_L^r` creation and `y ∈ 𝕋_L^s` annihilation
variables. -/
structure MonoKernel (r s : ℕ) where
  fn : (Fin r → AddCircle L) × (Fin s → AddCircle L) → ℂ
  measurable : Measurable fn
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ p, ‖fn p‖ ≤ bound

variable {L}

namespace MonoKernel
variable {r s : ℕ}

/-- The kernel as a multiplier on the triple space, `((x,w),y) ↦ a(x;y)`. -/
def tripFn (a : MonoKernel L r s) (q : ℕ) (p : Trip L r s q) : ℂ := a.fn (p.1.1, p.2)

theorem measurable_tripFn (a : MonoKernel L r s) (q : ℕ) : Measurable (a.tripFn q) :=
  a.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

theorem norm_tripFn_le (a : MonoKernel L r s) (q : ℕ) (p : Trip L r s q) :
    ‖a.tripFn q p‖ ≤ a.bound :=
  a.norm_le _

/-- Sum of kernels. -/
def add (a b : MonoKernel L r s) : MonoKernel L r s where
  fn p := a.fn p + b.fn p
  measurable := a.measurable.add b.measurable
  bound := a.bound + b.bound
  bound_nonneg := add_nonneg a.bound_nonneg b.bound_nonneg
  norm_le p := (norm_add_le _ _).trans (add_le_add (a.norm_le p) (b.norm_le p))

/-- Scalar multiple of a kernel. -/
def smul (c : ℂ) (a : MonoKernel L r s) : MonoKernel L r s where
  fn p := c * a.fn p
  measurable := measurable_const.mul a.measurable
  bound := ‖c‖ * a.bound
  bound_nonneg := mul_nonneg (norm_nonneg _) a.bound_nonneg
  norm_le p := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (a.norm_le p) (norm_nonneg _)

end MonoKernel

variable (L)

/-- The constant kernel `c` with no field variables (the zero-field term). -/
def constKernel (c : ℂ) : MonoKernel L 0 0 where
  fn _ := c
  measurable := measurable_const
  bound := ‖c‖
  bound_nonneg := norm_nonneg _
  norm_le _ := le_rfl

/-- The `L²`-level weak monomial with `q` spectators:
`⟨F, sliceOp a G⟩ = ∫ conj F(x,w) a(x;y) G(y,w)`. -/
def sliceOp {r s : ℕ} (q : ℕ) (a : MonoKernel L r s) : L2TN L (s+q) →L[ℂ] L2TN L (r+q) :=
  (liftOut L r s q).adjoint ∘L
    (mulOp (μ := tripMeasure L r s q) (a.tripFn q) (a.measurable_tripFn q) a.bound
      (a.norm_tripFn_le q) ∘L liftIn L r s q)

theorem inner_sliceOp {r s : ℕ} (q : ℕ) (a : MonoKernel L r s) (F : L2TN L (r+q))
    (G : L2TN L (s+q)) :
    ⟪F, sliceOp L q a G⟫_ℂ =
      ∫ p, conj (F (outPt L p)) * a.fn (p.1.1, p.2) * G (inPt L p) ∂tripMeasure L r s q := by
  rw [sliceOp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_liftOut L r s q F,
    coeFn_mulOp (μ := tripMeasure L r s q) (a.tripFn q) (a.measurable_tripFn q) a.bound
      (a.norm_tripFn_le q) (liftIn L r s q G), coeFn_liftIn L r s q G] with p h1 h2 h3
  rw [RCLike.inner_apply', h1, h2, h3]
  simp only [MonoKernel.tripFn]
  ring

theorem torus_univ_toReal (n : ℕ) : (torusPiMeasure L n Set.univ).toReal = L ^ n := by
  rw [Measure.pi_univ]
  simp only [AddCircle.measure_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (Fact.out : 0 < L).le]

theorem norm_liftOut_le (r s q : ℕ) :
    ‖liftOut L r s q‖ ≤ (L ^ s) ^ ((1 : ℝ≥0∞) / 2).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (Real.rpow_nonneg (pow_nonneg (Fact.out : (0:ℝ) < L).le s) _)
  intro F
  exact le_of_eq (by rw [liftOut, norm_pull, torus_univ_toReal])

theorem norm_liftIn_apply (r s q : ℕ) (G : L2TN L (s+q)) :
    ‖liftIn L r s q G‖ = (L ^ r) ^ ((1 : ℝ≥0∞) / 2).toReal * ‖G‖ := by
  rw [liftIn, norm_pull, torus_univ_toReal]

/-- Cauchy–Schwarz bound (A04.tex:86-91): `‖W‖ ≤ L^{s/2} ‖a‖_∞ L^{r/2}` before the
falling-factorial normalization. -/
theorem norm_sliceOp_apply_le {r s : ℕ} (q : ℕ) (a : MonoKernel L r s) (G : L2TN L (s+q)) :
    ‖sliceOp L q a G‖ ≤
      (L ^ s) ^ ((1 : ℝ≥0∞) / 2).toReal * a.bound *
        ((L ^ r) ^ ((1 : ℝ≥0∞) / 2).toReal * ‖G‖) := by
  have hadj : ‖(liftOut L r s q).adjoint‖ = ‖liftOut L r s q‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  have hm : ‖mulOp (μ := tripMeasure L r s q) (a.tripFn q) (a.measurable_tripFn q) a.bound
      (a.norm_tripFn_le q) (liftIn L r s q G)‖ ≤ a.bound * ‖liftIn L r s q G‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [coeFn_mulOp (μ := tripMeasure L r s q) (a.tripFn q) (a.measurable_tripFn q)
      a.bound (a.norm_tripFn_le q) (liftIn L r s q G)] with p hp
    rw [hp, norm_mul]
    exact mul_le_mul_of_nonneg_right (a.norm_tripFn_le q p) (norm_nonneg _)
  rw [sliceOp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  calc _ ≤ ‖(liftOut L r s q).adjoint‖ * ‖mulOp (μ := tripMeasure L r s q) (a.tripFn q)
          (a.measurable_tripFn q) a.bound (a.norm_tripFn_le q) (liftIn L r s q G)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (L ^ s) ^ ((1 : ℝ≥0∞) / 2).toReal * (a.bound * ‖liftIn L r s q G‖) := by
        rw [hadj]
        exact mul_le_mul (norm_liftOut_le L r s q) hm (norm_nonneg _)
          (Real.rpow_nonneg (pow_nonneg (Fact.out : (0:ℝ) < L).le s) _)
    _ = _ := by rw [norm_liftIn_apply]; ring

/-- `r`-fold normalized annihilation field `Φ(y₁)⋯Φ(y_r)G = √((N)_r) G(y,·)` on an
`N = r+q` particle wave function (A04.tex:72-76). -/
def annihilate (r q : ℕ) (G : (Fin (r+q) → AddCircle L) → ℂ) (y : Fin r → AddCircle L)
    (w : Fin q → AddCircle L) : ℂ :=
  (Real.sqrt ((r+q).descFactorial r) : ℂ) * G (Fin.append y w)

/-- The fixed-sector space `H_n` (the space of the DEF-048 transfer). -/
abbrev H (n : ℕ) : Type := SymSector ℂ (L2T L) n

/-- The weak normal-ordered monomial `∫ a(x;y) Φ*(x₁)⋯Φ*(x_r) Φ(y₁)⋯Φ(y_s)` from the fixed
sector `H_{s+q}` to `H_{r+q}`. -/
def monomial {r s : ℕ} (q : ℕ) (a : MonoKernel L r s) : H L (s+q) →L[ℂ] H L (r+q) :=
  ((Real.sqrt (((r+q).descFactorial r * (s+q).descFactorial s : ℕ) : ℝ) : ℝ) : ℂ) •
    ((positionInclusion L (r+q)).adjoint ∘L sliceOp L q a ∘L positionInclusion L (s+q))

/-- **Weak matrix elements with normalized fields** (A04.tex:77-85). -/
theorem inner_monomial {r s : ℕ} (q : ℕ) (a : MonoKernel L r s) (F : H L (r+q))
    (G : H L (s+q)) :
    ⟪F, monomial L q a G⟫_ℂ =
      ∫ p, conj (annihilate L r q (positionInclusion L (r+q) F) p.1.1 p.1.2) *
        a.fn (p.1.1, p.2) * annihilate L s q (positionInclusion L (s+q) G) p.2 p.1.2
          ∂tripMeasure L r s q := by
  have hc : ((Real.sqrt (((r+q).descFactorial r * (s+q).descFactorial s : ℕ) : ℝ) : ℝ) : ℂ) =
      (Real.sqrt ((r+q).descFactorial r) : ℂ) * (Real.sqrt ((s+q).descFactorial s) : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  rw [monomial, ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply, inner_sliceOp, hc,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  simp only [annihilate, outPt, inPt, map_mul, Complex.conj_ofReal]
  ring

theorem sliceOp_congr {r s : ℕ} (q : ℕ) (a b : MonoKernel L r s) (h : a.fn = b.fn) :
    sliceOp L q a = sliceOp L q b := by
  have h' : a.tripFn q = b.tripFn q := by
    funext p
    simp only [MonoKernel.tripFn, h]
  unfold sliceOp
  rw [mulOp_congr (a.tripFn q) (b.tripFn q) (a.measurable_tripFn q) (b.measurable_tripFn q)
    a.bound b.bound (a.norm_tripFn_le q) (b.norm_tripFn_le q) h']

theorem sliceOp_add {r s : ℕ} (q : ℕ) (a b : MonoKernel L r s) :
    sliceOp L q (a.add b) = sliceOp L q a + sliceOp L q b := by
  have hs : Measurable (a.tripFn q + b.tripFn q) :=
    (a.measurable_tripFn q).add (b.measurable_tripFn q)
  have hsb : ∀ p, ‖(a.tripFn q + b.tripFn q) p‖ ≤ a.bound + b.bound := fun p =>
    (norm_add_le _ _).trans (add_le_add (a.norm_tripFn_le q p) (b.norm_tripFn_le q p))
  unfold sliceOp
  rw [mulOp_congr (μ := tripMeasure L r s q) ((a.add b).tripFn q) (a.tripFn q + b.tripFn q)
      ((a.add b).measurable_tripFn q) hs (a.add b).bound (a.bound + b.bound)
      ((a.add b).norm_tripFn_le q) hsb rfl,
    mulOp_add (a.tripFn q) (b.tripFn q) (a.measurable_tripFn q) (b.measurable_tripFn q)
      a.bound b.bound (a.norm_tripFn_le q) (b.norm_tripFn_le q) hs hsb,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

theorem sliceOp_smul {r s : ℕ} (q : ℕ) (c : ℂ) (a : MonoKernel L r s) :
    sliceOp L q (a.smul c) = c • sliceOp L q a := by
  have hs : Measurable (c • a.tripFn q) := (a.measurable_tripFn q).const_smul c
  have hsb : ∀ p, ‖(c • a.tripFn q) p‖ ≤ ‖c‖ * a.bound := fun p => by
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (a.norm_tripFn_le q p) (norm_nonneg _)
  unfold sliceOp
  rw [mulOp_congr (μ := tripMeasure L r s q) ((a.smul c).tripFn q) (c • a.tripFn q)
      ((a.smul c).measurable_tripFn q) hs (a.smul c).bound (‖c‖ * a.bound)
      ((a.smul c).norm_tripFn_le q) hsb rfl,
    mulOp_smul c (a.tripFn q) (a.measurable_tripFn q) a.bound (‖c‖ * a.bound)
      (a.norm_tripFn_le q) hs hsb,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

theorem monomial_congr {r s : ℕ} (q : ℕ) (a b : MonoKernel L r s) (h : a.fn = b.fn) :
    monomial L q a = monomial L q b := by
  rw [monomial, monomial, sliceOp_congr L q a b h]

theorem monomial_add {r s : ℕ} (q : ℕ) (a b : MonoKernel L r s) :
    monomial L q (a.add b) = monomial L q a + monomial L q b := by
  rw [monomial, monomial, monomial, sliceOp_add, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add, smul_add]

theorem monomial_smul {r s : ℕ} (q : ℕ) (c : ℂ) (a : MonoKernel L r s) :
    monomial L q (a.smul c) = c • monomial L q a := by
  rw [monomial, monomial, sliceOp_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_comm]

/-- The position realization is isometric. -/
theorem inner_positionInclusion (n : ℕ) (F G : H L n) :
    ⟪positionInclusion L n F, positionInclusion L n G⟫_ℂ = ⟪F, G⟫_ℂ := by
  change ⟪physUnitary (F : HilbertTensorPower ℂ (L2T L) n),
    physUnitary (G : HilbertTensorPower ℂ (L2T L) n)⟫_ℂ = _
  rw [LinearIsometryEquiv.inner_map_map]
  rfl

/-- **Zero-field term**: with no field variables the monomial is multiplication by the
constant (the `n = 0` terms of Vlaar (2.4.1)/(2.4.4)). -/
theorem monomial_const (q : ℕ) (c : ℂ) :
    monomial L q (constKernel L c) = c • ContinuousLinearMap.id ℂ (H L (0+q)) := by
  apply ContinuousLinearMap.ext
  intro G
  apply ext_inner_left ℂ
  intro F
  rw [inner_monomial, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_right, ← inner_positionInclusion, L2.inner_def]
  have step : ∀ p : Trip L 0 0 q,
      conj (annihilate L 0 q (positionInclusion L (0+q) F) p.1.1 p.1.2) *
        (constKernel L c).fn (p.1.1, p.2) *
          annihilate L 0 q (positionInclusion L (0+q) G) p.2 p.1.2 =
      conj ((positionInclusion L (0+q) F) (Fin.append p.1.1 p.1.2)) * c *
        (positionInclusion L (0+q) G) (Fin.append p.1.1 p.1.2) := by
    intro p
    rw [Subsingleton.elim p.2 p.1.1]
    simp only [annihilate, Nat.descFactorial_zero, Nat.cast_one, Real.sqrt_one,
      Complex.ofReal_one, one_mul, constKernel]
  simp only [step]
  have hfst := integral_fun_fst (μ := (torusPiMeasure L 0).prod (torusPiMeasure L q))
    (ν := torusPiMeasure L 0)
    (fun x : (Fin 0 → AddCircle L) × (Fin q → AddCircle L) =>
      conj ((positionInclusion L (0+q) F) (Fin.append x.1 x.2)) * c *
        (positionInclusion L (0+q) G) (Fin.append x.1 x.2))
  try simp only at hfst
  have h0 : (torusPiMeasure L 0).real Set.univ = 1 := by
    simp [Measure.real, Measure.pi_univ]
  rw [hfst, h0, one_smul]
  have e : ∀ p : (Fin 0 → AddCircle L) × (Fin q → AddCircle L),
      (BetheBlockTensor.splitCoordinates L 0 q).symm p = Fin.append p.1 p.2 :=
    fun p => splitCoordinates_symm_apply L 0 q p.1 p.2
  have hmp := ((BetheBlockTensor.measurePreserving_splitCoordinates L 0 q).symm
    (BetheBlockTensor.splitCoordinates L 0 q)).integral_comp'
    (fun u => conj ((positionInclusion L (0+q) F) u) * c * (positionInclusion L (0+q) G) u)
  simp only [e] at hmp
  rw [hmp, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [RCLike.inner_apply']
  ring

end QuantumNLS.Ext002MonoFields

#print axioms QuantumNLS.Ext002MonoFields.sliceOp
#print axioms QuantumNLS.Ext002MonoFields.inner_sliceOp
#print axioms QuantumNLS.Ext002MonoFields.norm_sliceOp_apply_le
#print axioms QuantumNLS.Ext002MonoFields.monomial
#print axioms QuantumNLS.Ext002MonoFields.inner_monomial
#print axioms QuantumNLS.Ext002MonoFields.monomial_congr
#print axioms QuantumNLS.Ext002MonoFields.monomial_add
#print axioms QuantumNLS.Ext002MonoFields.monomial_smul
#print axioms QuantumNLS.Ext002MonoFields.inner_positionInclusion
#print axioms QuantumNLS.Ext002MonoFields.monomial_const
