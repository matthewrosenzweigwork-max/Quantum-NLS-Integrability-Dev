import QuantumNLS.LocalWellPosednessFull
import QuantumNLS.ChargeEnergy

/-!
# F04:lem-regular (R-3F6AA186): global regular solutions and conservation

Source: `source/chapters/foundations/F04.tex`, Lemma `F04:lem-regular` (lines 224-241) and its proof
(lines 243-276).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators Topology ComplexConjugate InnerProductSpace
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull

namespace QuantumNLS.F04Regularity

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. Auxiliary maps and Parseval -/

lemma f04W_zero (n : ℤ) : (f04W L 0).w n = 1 := by
  show f04Weight L 0 n = 1
  simp [f04Weight]

/-- The inner product of `h^0` is the `ℓ²` pairing of coefficients. -/
lemma inner_h0 (a b : h04 L 0) : ⟪a, b⟫_ℂ = ∑' n, conj (a.val n) * b.val n := by
  rw [inner_def, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [toL2_apply, toL2_apply, f04W_zero, Real.sqrt_one]
  simp [mul_comm]

/-- `H^1 ↪ H^0`. -/
abbrev m10 : h04 L 1 →L[ℂ] h04 L 0 := h04_mono L zero_le_one
/-- `H^3 ↪ H^1`. -/
abbrev m31 : h04 L 3 →L[ℂ] h04 L 1 := h04_mono L (by norm_num)
/-- `H^{3−2} ↪ H^1` (identity on sequences, `3 − 2 = 1`). -/
abbrev mL1 : h04 L (3 - 2) →L[ℂ] h04 L 1 := h04_mono L (by norm_num)

/-- `−i∂_x` on Fourier coefficients: `(Da)_n = p_n a_n`, `H^1 → H^0`. -/
def D : h04 L 1 →L[ℂ] h04 L 0 :=
  LinearMap.mkContinuous
    { toFun := fun a => WSeq.mk _ (fun n => ((freq L n : ℝ) : ℂ) * a.val n) (by
        refine Summable.of_nonneg_of_le (fun n => mul_nonneg ((f04W L 0).pos n).le (sq_nonneg _))
          (fun n => ?_) a.summable
        exact D_le n (a.val n))
      map_add' := fun a b => WSeq.ext (by funext n; simp [mul_add])
      map_smul' := fun c a => WSeq.ext (by funext n; simp; ring) }
    1 (fun a => by
      rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_tsum, norm_sq_eq_tsum]
      exact Summable.tsum_le_tsum (fun n => D_le n (a.val n)) (WSeq.summable _) a.summable)
where
  D_le (n : ℤ) (z : ℂ) : (f04W L 0).w n * ‖((freq L n : ℝ) : ℂ) * z‖ ^ 2 ≤ (f04W L 1).w n * ‖z‖ ^ 2 := by
    rw [f04W_zero, one_mul, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
    show freq L n ^ 2 * ‖z‖ ^ 2 ≤ f04Weight L 1 n * ‖z‖ ^ 2
    rw [f04Weight_one]
    nlinarith [sq_nonneg ‖z‖]

@[simp] lemma D_val (a : h04 L 1) (n : ℤ) : (D a).val n = ((freq L n : ℝ) : ℂ) * a.val n := rfl

lemma summable_norm_h1 (a : h04 L 1) : Summable fun n => ‖a.val n‖ :=
  (tsum_norm_le_cL Fact.out (h04_mem L 1 a)).1

/-- The continuous representative `Σ a_n e_n` as a bounded map `H^1 → C(𝕋_L)`. -/
def S1 : h04 L 1 →L[ℂ] C(AddCircle L, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨seriesRep L a.val, continuous_seriesRep (summable_norm_h1 a)⟩
      map_add' := fun a b => by
        ext x
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, WSeq.val_add]
        exact seriesRep_add' (summable_norm_h1 a) (summable_norm_h1 b) x
      map_smul' := fun c a => by
        ext x
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, WSeq.val_smul, smul_eq_mul,
          RingHom.id_apply]
        exact seriesRep_smul' c a.val x }
    (cL L) (fun a => by
      refine (ContinuousMap.norm_le _ (by have := cL_nonneg L; positivity)).mpr fun x => ?_
      show ‖seriesRep L a.val x‖ ≤ cL L * ‖a‖
      have hL : 0 < L := Fact.out
      have h1 := norm_seriesRep_le (L := L) (summable_norm_h1 a) x
      have h2 := (tsum_norm_le_cL hL (h04_mem L 1 a)).2
      rw [← norm_eq_sqrt] at h2
      have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
      calc ‖seriesRep L a.val x‖ ≤ (Real.sqrt L)⁻¹ * ∑' n, ‖a.val n‖ := h1
        _ ≤ (Real.sqrt L)⁻¹ * (Real.sqrt L * cL L * ‖a‖) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = cL L * ‖a‖ := by field_simp)

@[simp] lemma S1_apply (a : h04 L 1) (x : AddCircle L) : S1 a x = seriesRep L a.val x := rfl

lemma coeff_S1 (a : h04 L 1) (n : ℤ) : coeff L (S1 a) n = a.val n :=
  coeff_seriesRep (summable_norm_h1 a) n

/-- **Parseval for the mass-`L` inner product** of continuous functions. -/
lemma parseval {f g : AddCircle L → ℂ} (hf : Continuous f) (hg : Continuous g) :
    ∫ x, conj (f x) * g x = ∑' n, conj (coeff L f n) * coeff L g n := by
  have hfm := memLp_of_continuous (L := L) hf
  have hgm := memLp_of_continuous (L := L) hg
  have h1 : ⟪hfm.toLp f, hgm.toLp g⟫_ℂ = ∫ x, conj (f x) * g x := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hfm.coeFn_toLp, hgm.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply, mul_comm]
  have h2 : ⟪hfm.toLp f, hgm.toLp g⟫_ℂ =
      ⟪fourierL2 L (hfm.toLp f), fourierL2 L (hgm.toLp g)⟫_ℂ :=
    ((fourierL2 L).inner_map_map _ _).symm
  rw [← h1, h2, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [fourierL2_toLp hfm, fourierL2_toLp hgm, RCLike.inner_apply, mul_comm]

/-! ## 2. Mass, kinetic and quartic functionals on `H^1` -/

/-- The quartic functional `∫ |u|⁴` of the continuous representative. -/
def quart (a : h04 L 1) : ℝ := ∫ x, ‖S1 a x‖ ^ 4

/-- `Σ conj(a_n) \widehat{F(a)}(n) = ∫ |u|⁴`. -/
lemma inner_F_eq_quart (a : h04 L 1) :
    ⟪m10 a, m10 (Fh (le_refl (1 : ℝ)) a)⟫_ℂ = ((quart a : ℝ) : ℂ) := by
  rw [inner_h0]
  have hS := (S1 a).continuous
  have hN := continuous_nlRep (L := L) (summable_norm_h1 a)
  have hp := parseval (L := L) hS hN
  simp only [coeff_S1] at hp
  have e : ∀ n, (m10 a).val n = a.val n := fun n => rfl
  have e2 : ∀ n, (m10 (Fh (le_refl (1 : ℝ)) a)).val n = coeff L (nlRep L a.val) n := fun n => rfl
  simp only [e, e2]
  rw [← hp, quart, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [S1_apply, nlRep]
  have := Complex.mul_conj (seriesRep L a.val x)
  rw [Complex.normSq_eq_norm_sq] at this
  push_cast
  calc conj (seriesRep L a.val x) * (↑‖seriesRep L a.val x‖ ^ 2 * seriesRep L a.val x)
      = ↑‖seriesRep L a.val x‖ ^ 2 * (seriesRep L a.val x * conj (seriesRep L a.val x)) := by ring
    _ = _ := by rw [this]; push_cast; ring

#print axioms inner_h0
#print axioms parseval
#print axioms inner_F_eq_quart

/-! ## 3. Derivatives along differentiable curves in `H^1` -/

lemma hasDerivAt_normSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {x : ℝ → E}
    {x' : E} {t : ℝ} (h : HasDerivAt x x' t) :
    HasDerivAt (fun s => ‖x s‖ ^ 2) (2 * (⟪x t, x'⟫_ℂ).re) t := by
  have h1 := h.inner ℂ h
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
  convert h2 using 1
  · funext s
    simp only [Function.comp_apply, Complex.reCLM_apply]
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  · simp only [Complex.reCLM_apply, Complex.add_re]
    have := inner_re_symm (𝕜 := ℂ) x' (x t)
    simp only [RCLike.re_to_complex] at this
    linarith

/-- The integral on `C(𝕋_L, ℂ)` as a real-linear bounded functional. -/
def intCLM : C(AddCircle L, ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (f.continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
          (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
    (volume (Set.univ : Set (AddCircle L))).toReal (fun f => by
      show ‖∫ x, f x‖ ≤ _
      have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (AddCircle L)))
        (C := ‖f‖) (Eventually.of_forall fun x => f.norm_coe_le_norm x)
      rw [measureReal_def] at this
      linarith [mul_comm (volume (Set.univ : Set (AddCircle L))).toReal ‖f‖])

@[simp] lemma intCLM_apply (f : C(AddCircle L, ℂ)) : intCLM f = ∫ x, f x := rfl

lemma integrable_cont {f : AddCircle L → ℂ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma intCLM_P (a : h04 L 1) :
    intCLM (S1 a * star (S1 a) * S1 a * star (S1 a)) = ((quart a : ℝ) : ℂ) := by
  rw [intCLM_apply, quart, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, Complex.star_def]
  have := Complex.mul_conj (S1 a x)
  rw [Complex.normSq_eq_norm_sq] at this
  rw [show S1 a x * conj (S1 a x) * S1 a x * conj (S1 a x) =
    (S1 a x * conj (S1 a x)) * (S1 a x * conj (S1 a x)) by ring, this]
  push_cast; ring

/-- The integral of the derivative of `|u|⁴` along direction `b`. -/
lemma intCLM_dP (a b : h04 L 1) :
    intCLM (((S1 b * star (S1 a) + S1 a * star (S1 b)) * S1 a + S1 a * star (S1 a) * S1 b) *
        star (S1 a) + S1 a * star (S1 a) * S1 a * star (S1 b)) =
      2 * ⟪m10 (Fh (le_refl (1 : ℝ)) a), m10 b⟫_ℂ +
        2 * conj ⟪m10 (Fh (le_refl (1 : ℝ)) a), m10 b⟫_ℂ := by
  set Y : AddCircle L → ℂ := fun x => conj (nlRep L a.val x) * S1 b x
  have hYc : Continuous Y := (Complex.continuous_conj.comp
    (continuous_nlRep (L := L) (summable_norm_h1 a))).mul (S1 b).continuous
  have hX : ∫ x, Y x = ⟪m10 (Fh (le_refl (1 : ℝ)) a), m10 b⟫_ℂ := by
    rw [inner_h0]
    have hp := parseval (L := L) (continuous_nlRep (L := L) (summable_norm_h1 a)) (S1 b).continuous
    simp only [coeff_S1] at hp
    exact hp
  have h1 : Integrable (fun x => 2 * Y x) := (integrable_cont hYc).const_mul 2
  have h2 : Integrable (fun x => 2 * conj (Y x)) :=
    (integrable_cont (Complex.continuous_conj.comp hYc)).const_mul 2
  rw [intCLM_apply, ← hX, ← integral_conj, ← integral_const_mul, ← integral_const_mul,
    ← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hm := Complex.mul_conj (S1 a x)
  rw [Complex.normSq_eq_norm_sq] at hm
  have e : ((‖seriesRep L a.val x‖ ^ 2 : ℝ) : ℂ) = S1 a x * conj (S1 a x) := by
    rw [hm]; simp
  show (((S1 b x * conj (S1 a x) + S1 a x * conj (S1 b x)) * S1 a x + S1 a x * conj (S1 a x) * S1 b x) *
      conj (S1 a x) + S1 a x * conj (S1 a x) * S1 a x * conj (S1 b x)) =
    2 * (conj (nlRep L a.val x) * S1 b x) + 2 * conj (conj (nlRep L a.val x) * S1 b x)
  simp only [nlRep]
  rw [e]
  simp only [S1_apply, map_mul, Complex.conj_conj]
  ring

/-- **Derivative of the quartic functional**: `d/dt ∫|u|⁴ = 4 Re ⟨F(u), u'⟩`. -/
lemma hasDerivAt_quart {w : ℝ → h04 L 1} {w' : h04 L 1} {t : ℝ} (h : HasDerivAt w w' t) :
    HasDerivAt (fun s => quart (w s))
      (4 * (⟪m10 (Fh (le_refl (1 : ℝ)) (w t)), m10 w'⟫_ℂ).re) t := by
  set V : ℝ → C(AddCircle L, ℂ) := fun s => S1 (w s)
  have hV : HasDerivAt V (S1 w') t := by
    have := ((S1 (L := L)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h
    exact this
  have hP := ((hV.mul hV.star).mul hV).mul hV.star
  have hI := (intCLM (L := L)).hasFDerivAt.comp_hasDerivAt t hP
  have hR := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hI
  convert hR using 1
  · funext s
    simp only [Function.comp_apply, Complex.reCLM_apply, Pi.mul_apply, V, intCLM_P,
      Complex.ofReal_re]
  · simp only [Complex.reCLM_apply, Pi.mul_apply, V]
    rw [intCLM_dP]
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    norm_num
    ring

#print axioms hasDerivAt_normSq
#print axioms intCLM_P
#print axioms hasDerivAt_quart

/-! ## 4. The conservation identities at a fixed `H^3` state -/

lemma hs3 : (1 : ℝ) ≤ 3 := by norm_num

@[simp] lemma m10_val (a : h04 L 1) (n : ℤ) : (m10 a).val n = a.val n := rfl
@[simp] lemma m31_val (a : h04 L 3) (n : ℤ) : (m31 a).val n = a.val n := rfl
@[simp] lemma mL1_val (a : h04 L (3 - 2)) (n : ℤ) : (mL1 a).val n = a.val n := rfl

lemma inner_congr_terms {x y x' y' : h04 L 0}
    (h : ∀ n, conj (x.val n) * y.val n = conj (x'.val n) * y'.val n) : ⟪x, y⟫_ℂ = ⟪x', y'⟫_ℂ := by
  rw [inner_h0, inner_h0]; exact tsum_congr h

lemma im_inner_eq_zero {x y : h04 L 0}
    (h : ∀ n, conj (x.val n) * y.val n = conj (y.val n) * x.val n) : (⟪x, y⟫_ℂ).im = 0 := by
  have e : ⟪x, y⟫_ℂ = ⟪y, x⟫_ℂ := inner_congr_terms h
  have c := inner_conj_symm (𝕜 := ℂ) x y
  rw [← e] at c
  exact Complex.conj_eq_iff_im.mp c

/-- The nonlinearity of an `H^3` state, viewed in `H^1`, is the `H^1` nonlinearity. -/
lemma Fh_m31 (u : h04 L 3) : mL1 (ι2 3 (Fh hs3 u)) = Fh (le_refl (1 : ℝ)) (m31 u) := WSeq.ext rfl

/-- `i u_t = −∂_x²u + 2κ|u|²u` in `H^1`. -/
lemma I_smul_w (κ : ℝ) (u : h04 L 3) :
    Complex.I • mL1 (Gder hs3 κ u) =
      mL1 (lapOp 3 u) + ((2 * κ : ℝ) : ℂ) • Fh (le_refl (1 : ℝ)) (m31 u) := by
  rw [← map_smul, Gder_eq, map_add, map_smul, Fh_m31]

lemma inner_w (T : h04 L 1 →L[ℂ] h04 L 0) (x : h04 L 0) (κ : ℝ) (u : h04 L 3) :
    ⟪x, T (mL1 (Gder hs3 κ u))⟫_ℂ = -Complex.I * (⟪x, T (mL1 (lapOp 3 u))⟫_ℂ +
      ((2 * κ : ℝ) : ℂ) * ⟪x, T (Fh (le_refl (1 : ℝ)) (m31 u))⟫_ℂ) := by
  have e : mL1 (Gder hs3 κ u) = (-Complex.I) • (Complex.I • mL1 (Gder hs3 κ u)) := by
    rw [smul_smul]; simp
  rw [e, I_smul_w, map_smul, map_add, map_smul, inner_smul_right, inner_add_right,
    inner_smul_right]

lemma re_negI (z : ℂ) : (-Complex.I * z).re = z.im := by simp [Complex.mul_re]

/-- **Mass identity**: `Re ⟨u, u_t⟩_{L²} = 0`. -/
lemma mass_identity (κ : ℝ) (u : h04 L 3) :
    (⟪m10 (m31 u), m10 (mL1 (Gder hs3 κ u))⟫_ℂ).re = 0 := by
  rw [inner_w]
  have h1 : (⟪m10 (m31 u), m10 (mL1 (lapOp 3 u))⟫_ℂ).im = 0 :=
    im_inner_eq_zero fun n => by
      simp only [m10_val, m31_val, mL1_val, lapOp_val, map_mul, Complex.conj_ofReal]; ring
  rw [inner_F_eq_quart (m31 u)]
  simp [Complex.mul_re, Complex.mul_im, h1]

lemma kin_part (κ : ℝ) (u : h04 L 3) :
    (⟪D (m31 u), D (mL1 (Gder hs3 κ u))⟫_ℂ).re =
      2 * κ * (⟪D (m31 u), D (Fh (le_refl (1 : ℝ)) (m31 u))⟫_ℂ).im := by
  rw [inner_w]
  have h1 : (⟪D (m31 u), D (mL1 (lapOp 3 u))⟫_ℂ).im = 0 :=
    im_inner_eq_zero fun n => by
      simp only [D_val, m31_val, mL1_val, lapOp_val, map_mul, Complex.conj_ofReal]; ring
  rw [re_negI, Complex.add_im, Complex.im_ofReal_mul, h1, zero_add]

lemma lap_F_term (u : h04 L 3) (n : ℤ) :
    conj ((m10 (Fh (le_refl (1 : ℝ)) (m31 u))).val n) * (m10 (mL1 (lapOp 3 u))).val n =
      conj ((D (Fh (le_refl (1 : ℝ)) (m31 u))).val n) * (D (m31 u)).val n := by
  simp only [D_val, m10_val, m31_val, mL1_val, lapOp_val, map_mul, Complex.conj_ofReal,
    Complex.ofReal_pow]
  ring

lemma quart_part (κ : ℝ) (u : h04 L 3) :
    (⟪m10 (Fh (le_refl (1 : ℝ)) (m31 u)), m10 (mL1 (Gder hs3 κ u))⟫_ℂ).re =
      -(⟪D (m31 u), D (Fh (le_refl (1 : ℝ)) (m31 u))⟫_ℂ).im := by
  rw [inner_w]
  have h2 : ⟪m10 (Fh (le_refl (1 : ℝ)) (m31 u)), m10 (mL1 (lapOp 3 u))⟫_ℂ =
      ⟪D (Fh (le_refl (1 : ℝ)) (m31 u)), D (m31 u)⟫_ℂ := inner_congr_terms (lap_F_term u)
  have h3 : (⟪m10 (Fh (le_refl (1 : ℝ)) (m31 u)), m10 (Fh (le_refl (1 : ℝ)) (m31 u))⟫_ℂ).im = 0 :=
    im_inner_eq_zero fun n => rfl
  have h4 := inner_conj_symm (𝕜 := ℂ) (D (Fh (le_refl (1 : ℝ)) (m31 u))) (D (m31 u))
  rw [re_negI, Complex.add_im, Complex.im_ofReal_mul, h3, mul_zero, add_zero, h2, ← h4,
    Complex.conj_im]

/-- **Energy identity**: `2 Re⟨∂u, ∂u_t⟩ + κ · 4 Re⟨|u|²u, u_t⟩ = 0`. -/
lemma energy_identity (κ : ℝ) (u : h04 L 3) :
    2 * (⟪D (m31 u), D (mL1 (Gder hs3 κ u))⟫_ℂ).re +
      κ * (4 * (⟪m10 (Fh (le_refl (1 : ℝ)) (m31 u)), m10 (mL1 (Gder hs3 κ u))⟫_ℂ).re) = 0 := by
  rw [kin_part, quart_part]
  ring

#print axioms mass_identity
#print axioms energy_identity

/-! ## 5. Mass, kinetic energy and energy on `H^1` -/

/-- `M(a) = Σ |a_n|²`. -/
def mass (a : h04 L 1) : ℝ := ‖m10 a‖ ^ 2
/-- `Σ p_n² |a_n|²`. -/
def kin (a : h04 L 1) : ℝ := ‖D a‖ ^ 2
/-- `E(a) = Σ p_n²|a_n|² + κ ∫|u|⁴`. -/
def energy (κ : ℝ) (a : h04 L 1) : ℝ := kin a + κ * quart a

lemma quart_nonneg (a : h04 L 1) : 0 ≤ quart a :=
  integral_nonneg fun x => by positivity

lemma norm_sq_h1 (a : h04 L 1) : ‖a‖ ^ 2 = mass a + kin a := by
  unfold mass kin
  rw [norm_sq_eq_tsum, norm_sq_eq_tsum, norm_sq_eq_tsum,
    ← Summable.tsum_add (WSeq.summable _) (WSeq.summable _)]
  refine tsum_congr fun n => ?_
  have hw : (f04W L 1).w n = 1 + freq L n ^ 2 := by
    show f04Weight L 1 n = _; simp
  rw [hw, f04W_zero, m10_val, D_val, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring

lemma norm_sq_le_mass_energy {κ : ℝ} (hκ : 0 ≤ κ) (a : h04 L 1) :
    ‖a‖ ^ 2 ≤ mass a + energy κ a := by
  rw [norm_sq_h1, energy]
  have := mul_nonneg hκ (quart_nonneg a)
  linarith

/-- Bridge to the literal invariants of `F04:eq-invariants`. -/
lemma mass_eq_integral (a : h04 L 1) : mass a = ∫ x, ‖S1 a x‖ ^ 2 := by
  have hp := parseval (L := L) (S1 a).continuous (S1 a).continuous
  simp only [coeff_S1] at hp
  have h1 : ((mass a : ℝ) : ℂ) = ∑' n, conj (a.val n) * a.val n := by
    have e := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (m10 a)
    rw [inner_h0] at e
    rw [mass, Complex.ofReal_pow]
    exact e.symm
  have h2 : ((∫ x, ‖S1 a x‖ ^ 2 : ℝ) : ℂ) = ∫ x, conj (S1 a x) * S1 a x := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h1.trans (hp.symm.trans h2.symm)

lemma energy_eq_energyH1 (κ : ℝ) (a : h04 L 1) :
    energy κ a = ChargeEnergy.energyH1 κ (S1 a) := by
  unfold energy ChargeEnergy.energyH1 ChargeEnergy.kinetic ChargeEnergy.quartic kin quart
  congr 1
  rw [norm_sq_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [f04W_zero, coeff_S1, D_val, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

#print axioms norm_sq_h1
#print axioms mass_eq_integral
#print axioms energy_eq_energyH1

/-! ## 6. Conservation on the maximal `H^3` interval -/

section Flow

variable {κ : ℝ}

@[simp] lemma ι2_val3 (a : h04 L 3) (n : ℤ) : (ι2 3 a).val n = a.val n := rfl

lemma m31_eq (a : h04 L 3) : m31 a = mL1 (ι2 3 a) :=
  WSeq.ext (funext fun n => (m31_val a n).trans ((ι2_val3 a n).symm.trans (mL1_val _ n).symm))

lemma hasDerivAt_m31 (hκ : 0 ≤ κ) (u0 : h04 L 3) {t : ℝ} (ht : t ∈ Imax hs3 κ u0) :
    HasDerivAt (fun t => m31 (umax hs3 κ u0 t)) (mL1 (Gder hs3 κ (umax hs3 κ u0 t))) t := by
  have hC := mild_C1 (umax_mild (hs := hs3) hκ u0)
  have hI := Imax_isOpen (hs := hs3) hκ u0
  have h1 := hC.2.2.2.1 t (by rwa [hI.interior_eq])
  have h2 : HasDerivAt (fun s => mL1 (ι2 3 (umax hs3 κ u0 s)))
      (mL1 (Gder hs3 κ (umax hs3 κ u0 t))) t :=
    ((mL1 (L := L)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  exact h2.congr_of_eventuallyEq (Eventually.of_forall fun s => m31_eq _)

lemma hasDerivAt_mass (hκ : 0 ≤ κ) (u0 : h04 L 3) {t : ℝ} (ht : t ∈ Imax hs3 κ u0) :
    HasDerivAt (fun t => mass (m31 (umax hs3 κ u0 t))) 0 t := by
  have h : HasDerivAt (fun s => m10 (m31 (umax hs3 κ u0 s)))
      (m10 (mL1 (Gder hs3 κ (umax hs3 κ u0 t)))) t :=
    ((m10 (L := L)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_m31 hκ u0 ht)
  have h2 := hasDerivAt_normSq h
  rw [mass_identity, mul_zero] at h2
  exact h2

lemma hasDerivAt_energy (hκ : 0 ≤ κ) (u0 : h04 L 3) {t : ℝ} (ht : t ∈ Imax hs3 κ u0) :
    HasDerivAt (fun t => energy κ (m31 (umax hs3 κ u0 t))) 0 t := by
  have hv := hasDerivAt_m31 hκ u0 ht
  have hD : HasDerivAt (fun s => D (m31 (umax hs3 κ u0 s)))
      (D (mL1 (Gder hs3 κ (umax hs3 κ u0 t)))) t :=
    ((D (L := L)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hk := hasDerivAt_normSq hD
  have hq := hasDerivAt_quart hv
  have h := hk.add (hq.const_mul κ)
  rw [energy_identity] at h
  exact h

lemma const_on_Imax (hκ : 0 ≤ κ) (u0 : h04 L 3) {f : ℝ → ℝ}
    (hf : ∀ t ∈ Imax hs3 κ u0, HasDerivAt f 0 t) {t : ℝ} (ht : t ∈ Imax hs3 κ u0) :
    f t = f 0 :=
  (Imax_isOpen (hs := hs3) hκ u0).is_const_of_deriv_eq_zero
    (Imax_ordConnected (hs := hs3) (κ := κ) u0).isPreconnected
    (fun r hr => (hf r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hf r hr).deriv) ht (zero_mem_Imax hκ u0)

/-- The `H^3` tame estimate with the `H^1` norm: `‖F(u)‖_{H^3} ≤ C_{3,L} ‖u‖²_{H^1} ‖u‖_{H^3}`. -/
lemma norm_Fh3_le (a : h04 L 3) : ‖Fh hs3 a‖ ≤ Cs L 3 * ‖m31 a‖ ^ 2 * ‖a‖ := by
  have h := (f04_tame hs3 (h04_mem L 3 a)).2
  rw [norm_eq_sqrt 3 (Fh hs3 a), norm_eq_sqrt 1 (m31 a), norm_eq_sqrt 3 a]
  exact h

#print axioms hasDerivAt_mass
#print axioms hasDerivAt_energy
#print axioms norm_Fh3_le

end Flow

/-! ## 7. A priori bounds and globality (`F04:eq-regular-bounds`) -/

section Global

variable {κ : ℝ}

/-- `K² = M(u₀) + E(u₀)`. -/
def K2 (κ : ℝ) (u0 : h04 L 3) : ℝ := mass (m31 u0) + energy κ (m31 u0)

lemma umax_zero (hκ : 0 ≤ κ) (u0 : h04 L 3) : umax hs3 κ u0 0 = u0 :=
  (umax_mild (hs := hs3) hκ u0).at_zero

lemma mass_const_Imax (hκ : 0 ≤ κ) (u0 : h04 L 3) {t : ℝ} (ht : t ∈ Imax hs3 κ u0) :
    mass (m31 (umax hs3 κ u0 t)) = mass (m31 u0) := by
  have h := const_on_Imax hκ u0 (fun r hr => hasDerivAt_mass hκ u0 hr) ht
  simp only [umax_zero hκ u0] at h
  exact h

lemma energy_const_Imax (hκ : 0 ≤ κ) (u0 : h04 L 3) {t : ℝ} (ht : t ∈ Imax hs3 κ u0) :
    energy κ (m31 (umax hs3 κ u0 t)) = energy κ (m31 u0) := by
  have h := const_on_Imax hκ u0 (fun r hr => hasDerivAt_energy hκ u0 hr) ht
  simp only [umax_zero hκ u0] at h
  exact h

lemma h1_bound_Imax (hκ : 0 ≤ κ) (u0 : h04 L 3) {t : ℝ} (ht : t ∈ Imax hs3 κ u0) :
    ‖m31 (umax hs3 κ u0 t)‖ ^ 2 ≤ K2 κ u0 := by
  have := norm_sq_le_mass_energy hκ (m31 (umax hs3 κ u0 t))
  rw [mass_const_Imax hκ u0 ht, energy_const_Imax hκ u0 ht] at this
  exact this

lemma K2_nonneg (hκ : 0 ≤ κ) (u0 : h04 L 3) : 0 ≤ K2 κ u0 :=
  le_trans (sq_nonneg _) (h1_bound_Imax hκ u0 (zero_mem_Imax hκ u0))

/-- The `H^3` Grönwall bound on the maximal interval. -/
lemma h3_bound_Imax (hκ : 0 ≤ κ) (u0 : h04 L 3) {t : ℝ} (ht : t ∈ Imax hs3 κ u0) :
    ‖umax hs3 κ u0 t‖ ≤ ‖u0‖ * Real.exp (2 * κ * Cs L 3 * K2 κ u0 * |t|) := by
  have hu := umax_mild (hs := hs3) hκ u0
  set u := umax hs3 κ u0
  set I := Imax hs3 κ u0
  set c := Cs L 3
  have hc : 0 ≤ c := le_trans zero_le_one (one_le_Cs L 3)
  have hK : 0 ≤ K2 κ u0 := K2_nonneg hκ u0
  set b := 2 * κ * c * K2 κ u0
  have hb : 0 ≤ b := by positivity
  set a := ‖u0‖
  have h0 : (0 : ℝ) ∈ I := zero_mem_Imax hκ u0
  have hsub : Set.uIcc 0 t ⊆ I := hu.ordConnected.uIcc_subset h0 ht
  set lo := min 0 t
  set hi := max 0 t
  have hlohi : lo ≤ hi := min_le_max
  set φ0 : ℝ → ℝ := fun r => ‖u r‖
  have hφ0 : ContinuousOn φ0 (Set.Icc lo hi) := (hu.cont.mono hsub).norm
  set φ : ℝ → ℝ := fun r => φ0 (Set.projIcc lo hi hlohi r)
  have hφ : Continuous φ := hφ0.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun r => (Set.projIcc lo hi hlohi r).2)
  have hφeq : ∀ r ∈ Set.Icc lo hi, φ r = φ0 r := fun r hr => by
    simp only [φ, Set.projIcc_of_mem hlohi hr]
  have key : ∀ r ∈ Set.uIcc 0 t, φ0 r ≤ a + b * |∫ x in (0 : ℝ)..r, φ x| := by
    intro r hr
    have hrI := hsub hr
    have hsubr : Set.uIcc 0 r ⊆ Set.uIcc 0 t := Set.uIcc_subset_uIcc_left hr
    have hpt : ∀ x ∈ Set.uIcc 0 r,
        ‖Sgrp 3 (r - x) (Fh hs3 (u x))‖ ≤ (c * K2 κ u0) * φ x := by
      intro x hx
      have hxI := hsub (hsubr hx)
      rw [norm_Sgrp, hφeq x (hsubr hx)]
      have h1 := h1_bound_Imax hκ u0 hxI
      calc ‖Fh hs3 (u x)‖ ≤ c * ‖m31 (u x)‖ ^ 2 * ‖u x‖ := norm_Fh3_le _
        _ ≤ c * K2 κ u0 * ‖u x‖ := by gcongr
    have hgc : ContinuousOn (fun x => ‖Sgrp 3 (r - x) (Fh hs3 (u x))‖) (Set.uIcc 0 r) :=
      (continuousOn_Sgrp (continuous_const.sub continuous_id)
        ((continuous_Fh hs3).comp_continuousOn (hu.cont.mono (hsubr.trans hsub)))).norm
    have hint := abs_integral_le_of_le (fun x _ => norm_nonneg _) hpt hgc.intervalIntegrable
      ((hφ.const_mul _).intervalIntegrable _ _)
    have hn : ‖u r‖ ≤ a + 2 * κ * |∫ x in (0 : ℝ)..r, ‖Sgrp 3 (r - x) (Fh hs3 (u x))‖| := by
      rw [hu.duhamel_eq r hrI]
      unfold duhamel
      refine (norm_sub_le _ _).trans ?_
      rw [norm_Sgrp, norm_smul, norm_coef κ hκ]
      have := intervalIntegral.norm_integral_le_abs_integral_norm (μ := volume) (a := 0) (b := r)
        (f := fun x => Sgrp 3 (r - x) (Fh hs3 (u x)))
      nlinarith
    have hlin : |∫ x in (0 : ℝ)..r, (c * K2 κ u0) * φ x| =
        (c * K2 κ u0) * |∫ x in (0 : ℝ)..r, φ x| := by
      rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity)]
    show ‖u r‖ ≤ a + b * |∫ x in (0 : ℝ)..r, φ x|
    rw [hlin] at hint
    have hb' : b = 2 * κ * (c * K2 κ u0) := by simp only [b]; ring
    rw [hb']
    nlinarith
  rcases le_total 0 t with h | h
  · have hfwd : ∀ r ∈ Set.Icc 0 t, φ r ≤ a + b * ∫ x in (0 : ℝ)..r, φ x := by
      intro r hr
      have hrI : r ∈ Set.uIcc 0 t := Set.Icc_subset_uIcc hr
      have hmem : r ∈ Set.Icc lo hi := hrI
      rw [hφeq r hmem]
      have := key r hrI
      rwa [abs_of_nonneg (intervalIntegral.integral_nonneg hr.1 fun x _ => norm_nonneg _)] at this
    have := gronwall_fwd hφ hb hfwd t ⟨h, le_rfl⟩
    rw [hφeq t Set.right_mem_uIcc, sub_zero] at this
    rw [abs_of_nonneg h]
    exact this
  · have hbwd : ∀ r ∈ Set.Icc t 0, φ r ≤ a + b * ∫ x in r..(0 : ℝ), φ x := by
      intro r hr
      have hrI : r ∈ Set.uIcc 0 t := Set.Icc_subset_uIcc' hr
      have hmem : r ∈ Set.Icc lo hi := hrI
      rw [hφeq r hmem]
      have := key r hrI
      rwa [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (intervalIntegral.integral_nonneg hr.2 fun x _ => norm_nonneg _)] at this
    have := gronwall_bwd hφ hb hbwd t ⟨le_rfl, h⟩
    rw [hφeq t Set.right_mem_uIcc, zero_sub] at this
    rw [abs_of_nonpos h]
    exact this

/-- **Globality**: the maximal `H^3` interval is all of `ℝ`. -/
lemma Imax_eq_univ (hκ : 0 ≤ κ) (u0 : h04 L 3) : Imax hs3 κ u0 = Set.univ := by
  set I := Imax hs3 κ u0
  set B := 2 * κ * Cs L 3 * K2 κ u0
  have hB : 0 ≤ B := by
    have := le_trans zero_le_one (one_le_Cs L 3)
    have := K2_nonneg hκ u0
    positivity
  have hcap : ∀ t ∈ I, ∀ S : ℝ, |t| ≤ |S| + 1 →
      ‖umax hs3 κ u0 t‖ ≤ ‖u0‖ * Real.exp (B * (|S| + 1)) := by
    intro t ht S hS
    refine (h3_bound_Imax hκ u0 ht).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hS hB))
      (norm_nonneg _)
  have hA : ¬ BddAbove I := by
    intro hb
    obtain ⟨t, htI, ht1, ht2⟩ := blowup_right (hs := hs3) hκ u0 hb
      (‖u0‖ * Real.exp (B * (|sSup I| + 1))) 1 one_pos
    have htS : t ≤ sSup I := le_csSup hb htI
    have habs : |t| ≤ |sSup I| + 1 :=
      abs_le.mpr ⟨by linarith [neg_abs_le (sSup I)], by linarith [le_abs_self (sSup I)]⟩
    linarith [hcap t htI _ habs]
  have hA' : ¬ BddBelow I := by
    intro hb
    obtain ⟨t, htI, ht1, ht2⟩ := blowup_left (hs := hs3) hκ u0 hb
      (‖u0‖ * Real.exp (B * (|sInf I| + 1))) 1 one_pos
    have htS : sInf I ≤ t := csInf_le hb htI
    have habs : |t| ≤ |sInf I| + 1 :=
      abs_le.mpr ⟨by linarith [neg_abs_le (sInf I)], by linarith [le_abs_self (sInf I)]⟩
    linarith [hcap t htI _ habs]
  ext x
  simp only [Set.mem_univ, iff_true]
  obtain ⟨y, hyI, hxy⟩ := not_bddAbove_iff.mp hA x
  obtain ⟨z, hzI, hzx⟩ := not_bddBelow_iff.mp hA' x
  exact (Imax_ordConnected u0).out hzI hyI ⟨hzx.le, hxy.le⟩

#print axioms h3_bound_Imax
#print axioms Imax_eq_univ

/-- **`F04:lem-regular` (R-3F6AA186)**. For `u₀ ∈ H³` (and `κ ≥ 0`) the maximal `H³` mild
solution `u` of `F04:eq-nls` is global and unique, `u ∈ C(ℝ; H³) ∩ C¹(ℝ; H¹)`, the invariants
`M(u) = ∫|u|²` and `E(u) = ∫(|∂_x u|² + κ|u|⁴)` are constant, and with `K² = M(u₀) + E(u₀)`:
`‖u(t)‖_{H¹} ≤ K` and `‖u(t)‖_{H³} ≤ ‖u₀‖_{H³} e^{2κ C_{3,L} K² |t|}`. -/
theorem lem_regular (hκ : 0 ≤ κ) (u0 : h04 L 3) :
    IsMild hs3 κ Set.univ u0 (umax hs3 κ u0) ∧
    (∀ (J : Set ℝ) (v : ℝ → h04 L 3), IsMild hs3 κ J u0 v → ∀ t ∈ J, v t = umax hs3 κ u0 t) ∧
    Continuous (umax hs3 κ u0) ∧
    ContDiff ℝ 1 (fun t => m31 (umax hs3 κ u0 t)) ∧
    (∀ t, HasDerivAt (fun t => m31 (umax hs3 κ u0 t)) (mL1 (Gder hs3 κ (umax hs3 κ u0 t))) t) ∧
    (∀ t, ∫ x, ‖S1 (m31 (umax hs3 κ u0 t)) x‖ ^ 2 = ∫ x, ‖S1 (m31 u0) x‖ ^ 2) ∧
    (∀ t, ChargeEnergy.energyH1 κ (S1 (m31 (umax hs3 κ u0 t))) =
      ChargeEnergy.energyH1 κ (S1 (m31 u0))) ∧
    K2 κ u0 = (∫ x, ‖S1 (m31 u0) x‖ ^ 2) + ChargeEnergy.energyH1 κ (S1 (m31 u0)) ∧
    (∀ t, ‖m31 (umax hs3 κ u0 t)‖ ≤ Real.sqrt (K2 κ u0)) ∧
    (∀ t, ‖umax hs3 κ u0 t‖ ≤ ‖u0‖ * Real.exp (2 * κ * Cs L 3 * K2 κ u0 * |t|)) := by
  have hU := Imax_eq_univ hκ u0
  have hu := umax_mild (hs := hs3) hκ u0
  rw [hU] at hu
  have hmem : ∀ t : ℝ, t ∈ Imax hs3 κ u0 := fun t => hU ▸ Set.mem_univ t
  have hcont : Continuous (umax hs3 κ u0) := continuousOn_univ.mp hu.cont
  have hder := fun t => hasDerivAt_m31 hκ u0 (hmem t)
  refine ⟨hu, fun J v hv t ht => ?_, hcont, ?_, hder, fun t => ?_, fun t => ?_, ?_,
    fun t => ?_, fun t => h3_bound_Imax hκ u0 (hmem t)⟩
  · exact mild_unique hs3 hκ hv (hu.mono (Set.subset_univ J) hv.zero_mem hv.ordConnected) t ht
  · rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hder t).differentiableAt, ?_⟩
    have e : deriv (fun t => m31 (umax hs3 κ u0 t)) = fun t => mL1 (Gder hs3 κ (umax hs3 κ u0 t)) :=
      funext fun t => (hder t).deriv
    rw [e]
    exact (mL1 (L := L)).continuous.comp ((continuous_Gder hs3 κ).comp hcont)
  · rw [← mass_eq_integral, ← mass_eq_integral, mass_const_Imax hκ u0 (hmem t)]
  · rw [← energy_eq_energyH1, ← energy_eq_energyH1, energy_const_Imax hκ u0 (hmem t)]
  · rw [K2, mass_eq_integral, energy_eq_energyH1]
  · exact Real.le_sqrt_of_sq_le (h1_bound_Imax hκ u0 (hmem t))

#print axioms lem_regular

end Global

end QuantumNLS.F04Regularity
