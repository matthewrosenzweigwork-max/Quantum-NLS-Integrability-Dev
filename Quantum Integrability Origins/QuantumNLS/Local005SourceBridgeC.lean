import QuantumNLS.Local005SourceNeumannC
import QuantumNLS.Local002Free



set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Metric
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.Local002

variable {L r κ : ℝ} [Fact (0 < L)]

/-- Multiplication by the source's moment factor on the actual contour. -/
def momentWeight (n : ℤ) : ContourOp L r n →L[ℂ] ContourOp L r n := by
  let f : ContourOp L r n →ₗ[ℂ] ContourOp L r n :=
    { toFun := fun F => ⟨fun z => ((z : ℂ) - center L n) • F z,
        (continuous_subtype_val.sub continuous_const).smul F.continuous⟩
      map_add' := fun F G => by ext z : 1; exact smul_add _ _ _
      map_smul' := fun a F => by
        ext z : 1
        change ((z : ℂ) - center L n) • (a • F z) = a • (((z : ℂ) - center L n) • F z)
        exact smul_comm _ _ _ }
  have hb : ∀ F : ContourOp L r n, ‖f F‖ ≤ |r| * ‖F‖ := by
    intro F
    apply (ContinuousMap.norm_le (f F) (mul_nonneg (abs_nonneg r) (norm_nonneg F))).2
    intro z
    change ‖((z : ℂ) - center L n) • F z‖ ≤ _
    rw [norm_smul, mem_sphere_iff_norm.mp z.2]
    exact mul_le_mul (le_abs_self r) (F.norm_coe_le_norm z) (norm_nonneg _) (abs_nonneg _)
  exact { toLinearMap := f, cont := AddMonoidHomClass.continuous_of_bound f |r| hb }

def weight (kind : WordKind) (n : ℤ) : ContourOp L r n →L[ℂ] ContourOp L r n :=
  match kind with
  | .projection => ContinuousLinearMap.id ℂ _
  | .moment => momentWeight n

def contourJ (hr : 0 < r) (n : ℤ) : ContourOp L r n →L[ℂ] Op L :=
  Classical.choose (exists_J (L := L) (c := center L n) hr)

theorem contourJ_apply (hr : 0 < r) (n : ℤ) (F : ContourOp L r n) :
    contourJ hr n F = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(center L n, r), extC F z :=
  Classical.choose_spec (exists_J (L := L) (c := center L n) hr) F

/-- The source operators, with the free projection on both sides for either kind. -/
def sourceCompressed (kind : WordKind) (u : ScalarInterval L) (n : ℤ) : Op L :=
  match kind with
  | .projection => compression L κ (u : ℝ → ℂ) n r
  | .moment => freeProj L κ n r * dressedIntegral L κ (u : ℝ → ℂ) n r * freeProj L κ n r

/-- A genuine operator-valued Neumann term, integrated before taking matrix entries. -/
def sourceWord (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (n : ℤ) (k : ℕ) : Op L :=
  freeProj L κ n r *
    contourJ hr n (weight kind n (freeContour (κ := κ) hL hr hsmall n *
      potentialContour hL hκ hr hsmall n u ^ k)) * freeProj L κ n r

theorem weighted_inverse_integral (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ScalarInterval L)
    (hu : potentialConstant L r κ * ‖u‖ < 1) (kind : WordKind) :
    freeProj L κ n r *
      contourJ hr n (weight kind n (freeContour (κ := κ) hL hr hsmall n *
        Ring.inverse (1 - potentialContour hL hκ hr hsmall n u))) * freeProj L κ n r =
      sourceCompressed (κ := κ) (r := r) kind u n := by
  let F := freeContour (κ := κ) hL hr hsmall n *
    Ring.inverse (1 - potentialContour hL hκ hr hsmall n u)
  have he (z : ℂ) (hz : z ∈ sphere (center L n) r) :
      extC F z = LocalSpectral.resolvent L κ (u : ℝ → ℂ) (parity n) z := by
    rw [extC_apply F hz]
    exact (source_resolvent_eq_inverse hL hκ hr hsmall n u hu ⟨z, hz⟩).symm
  cases kind with
  | projection =>
    change freeProj L κ n r * contourJ hr n F * freeProj L κ n r = _
    rw [contourJ_apply]
    unfold sourceCompressed compression perturbedProj rieszProj
    rw [circleIntegral.integral_congr hr.le he]
  | moment =>
    change freeProj L κ n r * contourJ hr n (momentWeight n F) * freeProj L κ n r = _
    rw [contourJ_apply]
    unfold sourceCompressed dressedIntegral
    congr 2
    congr 1
    apply circleIntegral.integral_congr hr.le
    intro z hz
    rw [extC_apply _ hz]
    change (z - center L n) • F ⟨z, hz⟩ = _
    rw [← extC_apply F hz, he z hz]

/-- Contour integration term by term in operator norm, for both printed source objects. -/
theorem source_word_hasSum (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ScalarInterval L)
    (hu : potentialConstant L r κ * ‖u‖ < 1) (kind : WordKind) :
    HasSum (sourceWord hL hκ hr hsmall kind u n)
      (sourceCompressed (κ := κ) (r := r) kind u n) := by
  have h := ((contourJ hr n).comp (weight kind n)).hasSum
    (source_neumann_uniform hL hκ hr hsmall n u hu)
  have hc := (h.mul_left (freeProj L κ n r)).mul_right (freeProj L κ n r)
  simp only [ContinuousLinearMap.comp_apply] at hc
  rw [weighted_inverse_integral hL hκ hr hsmall n u hu kind] at hc
  exact hc

theorem potentialContour_real_smul (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ScalarInterval L) (a : ℝ) :
    potentialContour hL hκ hr hsmall n (a • u) =
      (a : ℂ) • potentialContour hL hκ hr hsmall n u := by
  ext z : 1
  exact Mop_real_smul ⟨_, (mop_data hL hκ hr hsmall n
    (mem_sphere_iff_norm.mp z.2) u).1⟩ a

/-- These source operator terms have exactly degree k under real scaling of the physical field. -/
theorem sourceWord_real_smul (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (n : ℤ) (k : ℕ) (a : ℝ) :
    sourceWord hL hκ hr hsmall kind (a • u) n k =
      (a : ℂ) ^ k • sourceWord hL hκ hr hsmall kind u n k := by
  unfold sourceWord
  rw [potentialContour_real_smul, smul_pow (a : ℂ) (potentialContour hL hκ hr hsmall n u) k]
  simp only [mul_smul_comm, map_smul, RingHom.id_apply, smul_mul_assoc]

/-- A locally convergent power series for the actual source S and K along every physical input. -/
theorem source_degree_series (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ScalarInterval L) (a : ℝ)
    (ha : potentialConstant L r κ * ‖a • u‖ < 1) (kind : WordKind) :
    HasSum (fun k : ℕ => (a : ℂ) ^ k • sourceWord hL hκ hr hsmall kind u n k)
      (sourceCompressed (κ := κ) (r := r) kind (a • u) n) := by
  exact (source_word_hasSum hL hκ hr hsmall n (a • u) ha kind).congr_fun
    (fun k => (sourceWord_real_smul hL hκ hr hsmall kind u n k a).symm)

/-- The convergence neighborhood is supplied, rather than added as a scientific premise. -/
theorem source_series_on_ball (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (n : ℤ) (u : ScalarInterval L), ‖u‖ < ρ →
      ∀ kind : WordKind, HasSum (sourceWord hL hκ hr hsmall kind u n)
        (sourceCompressed (κ := κ) (r := r) kind u n) := by
  let K := potentialConstant L r κ
  have hK : 0 ≤ K := potentialConstant_nonneg L r κ
  have hpos : 0 < 1 + K := by linarith
  refine ⟨(1 + K)⁻¹, inv_pos.mpr hpos, ?_⟩
  intro n u hu kind
  apply source_word_hasSum hL hκ hr hsmall n u _ kind
  have hmul : ‖u‖ * (1 + K) < 1 := by
    have hh := mul_lt_mul_of_pos_right hu hpos
    rwa [inv_mul_cancel₀ hpos.ne'] at hh
  change K * ‖u‖ < 1
  nlinarith [norm_nonneg u]

#print axioms weighted_inverse_integral
#print axioms source_word_hasSum
#print axioms sourceWord_real_smul
#print axioms source_degree_series
#print axioms source_series_on_ball
end QuantumNLS.Local005.SourceC


set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.ResolventWordEstimateStage2LOCAL005

variable {L : ℝ} [Fact (0 < L)]

/-- The physical Fourier sequence uses the source's orthonormal mass-L normalization. -/
def physicalFourier (u : ScalarInterval L) : ℤ → ℂ := intervalFourierIso L u

theorem physicalFourier_inner (u : ScalarInterval L) (m : ℤ) :
    physicalFourier u m = ⟪intervalMode L m, u⟫_ℂ := by
  rw [← intervalBasis_apply L m]
  exact HilbertBasis.repr_apply_apply (intervalBasis L) u m

theorem physicalFourier_integral (u : ScalarInterval L) (m : ℤ) :
    physicalFourier u m = ∫ x, conj (QuantumNLS.Fourier.mode L m (x : AddCircle L)) * u x
      ∂μI L := by
  rw [physicalFourier_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalMode_coe L m] with x hx
  simp only [hx, RCLike.inner_apply]
  ring

theorem physicalFourier_sq (u : ScalarInterval L) :
    Summable (fun m : ℤ => ‖physicalFourier u m‖ ^ 2) ∧
      ∑' m : ℤ, ‖physicalFourier u m‖ ^ 2 = ‖u‖ ^ 2 := by
  constructor
  · simpa [physicalFourier] using (lp.memℓp (intervalFourierIso L u)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  · exact interval_fourier_parseval L u

/-- Component 0 uses the field coefficient; component 1 uses its conjugate. -/
def physicalSlot (j : Fin 2) (u : ScalarInterval L) (m : ℤ) : ℂ :=
  if j = 0 then physicalFourier u m else conj (physicalFourier u m)

theorem physicalSlot_norm (j : Fin 2) (u : ScalarInterval L) (m : ℤ) :
    ‖physicalSlot j u m‖ = ‖physicalFourier u m‖ := by
  by_cases hj : j = 0 <;> simp [physicalSlot, hj]

/-- Ordered independent physical inputs transported to the frozen path's independent slots. -/
def physicalInputs {k : ℕ} (j : Fin 2) (u : Fin k → ScalarInterval L)
    (t : Fin k) (m : ℤ) : ℂ := physicalSlot (componentAfter t.val j) (u t) m

theorem physicalInputs_summable {k : ℕ} (j : Fin 2) (u : Fin k → ScalarInterval L) :
    ∀ t, Summable (fun m : ℤ => ‖physicalInputs j u t m‖ ^ 2) := by
  intro t
  simpa only [physicalInputs, physicalSlot_norm] using (physicalFourier_sq (u t)).1

theorem physicalInputs_norm {k : ℕ} (j : Fin 2) (u : Fin k → ScalarInterval L) (t : Fin k) :
    inputL2Norm (physicalInputs j u) t = ‖u t‖ := by
  unfold inputL2Norm
  simp only [physicalInputs, physicalSlot_norm, (physicalFourier_sq (u t)).2,
    Real.sqrt_sq (norm_nonneg (u t))]

/-- The phase in the frozen coefficient is exactly the physical potential normalization. -/
theorem slotPhase_physical {κ : ℝ} (hκ : 0 ≤ κ) (j : Fin 2) :
    slotPhase L κ j =
      if j = 0 then (2 * Complex.I) * (Real.sqrt κ : ℂ) * ((Real.sqrt L : ℂ)⁻¹)
      else -((2 * Complex.I) * (Real.sqrt κ : ℂ) * ((Real.sqrt L : ℂ)⁻¹)) := by
  have he : Real.sqrt (κ / L) = Real.sqrt κ / Real.sqrt L := Real.sqrt_div hκ L
  unfold slotPhase
  rw [he]
  split_ifs <;> push_cast <;> ring

#print axioms physicalFourier_inner
#print axioms physicalFourier_sq
#print axioms physicalInputs_summable
#print axioms physicalInputs_norm
#print axioms slotPhase_physical
end QuantumNLS.Local005.SourceC


set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.Local002

variable {L r κ : ℝ} [Fact (0 < L)]

theorem cross_exponential (n a b : ℤ) (x : ℝ) :
    conj (Complex.exp (rate L (n + 2 * a) 1 * (x : ℂ))) *
      Complex.exp (rate L (n + 2 * b) 0 * (x : ℂ)) =
      conj (Complex.exp (2 * Real.pi * Complex.I * (n + a + b : ℤ) * x / L)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_conj]
  congr 1
  simp [rate, sgn, pm, map_mul, map_div]
  push_cast
  have htwo : conj (2 : ℂ) = 2 := by
    change conj ((2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ)
    exact Complex.conj_ofReal _
  rw [htwo]
  norm_num
  ring

theorem cross_mode (n a b : ℤ) (x : ℝ) :
    conj ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
      Complex.exp (rate L (n + 2 * a) 1 * (x : ℂ))) *
      ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (rate L (n + 2 * b) 0 * (x : ℂ))) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
        conj (QuantumNLS.Fourier.mode L (n + a + b) (x : AddCircle L)) := by
  rw [QuantumNLS.Fourier.mode_coe]
  simp only [map_mul, Complex.conj_ofReal]
  have h := cross_exponential (L := L) n a b x
  calc
    _ = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) ^ 2 *
        (conj (Complex.exp (rate L (n + 2 * a) 1 * (x : ℂ))) *
          Complex.exp (rate L (n + 2 * b) 0 * (x : ℂ))) := by ring
    _ = _ := by rw [h]; ring

/-- The source potential's two actual pointwise matrix entries, including their Fourier labels. -/
theorem potential_pointwise (hκ : 0 ≤ κ) (n a b : ℤ) (x : ℝ) (w : ℂ)
    (i j : Fin 2) :
    ⟪chiFun L (n + 2 * a) i x, potentialPt κ w (chiFun L (n + 2 * b) j x)⟫_ℂ =
      if i = componentAfter 1 j then
        slotPhase L κ j *
          (if j = 0 then conj (QuantumNLS.Fourier.mode L (n + a + b) (x : AddCircle L)) * w
            else conj (conj (QuantumNLS.Fourier.mode L (n + a + b) (x : AddCircle L)) * w))
      else 0 := by
  have hc := cross_mode (L := L) n a b x
  have hc' := cross_mode (L := L) n b a x
  have hcc := congrArg conj hc'
  simp only [map_mul, starRingEnd_self_apply] at hcc
  rw [show n + b + a = n + a + b by omega] at hcc
  push_cast at hc hcc
  simp only [map_mul, map_inv₀, Complex.conj_ofReal] at hc hcc
  fin_cases i <;> fin_cases j <;>
    simp [chiFun, potentialPt, vec2, EuclideanSpace.inner_single_left,
      componentAfter, slotPhase_physical hκ, PiLp.smul_apply] <;>
    simp only [map_mul, Complex.conj_ofReal] at *
  · linear_combination (2 * Complex.I) * (Real.sqrt κ : ℂ) * conj w * hcc
  · linear_combination (2 * Complex.I) * (Real.sqrt κ : ℂ) * w * hc

#print axioms cross_exponential
#print axioms cross_mode
#print axioms potential_pointwise

/-- The actual bounded source potential-resolvent factor in every Fourier component. -/
theorem mop_matrix_entry (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n a b : ℤ) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) (i j : Fin 2) :
    ⟪chi L (n + 2 * a) i, Mop κ (free L κ n z) u (chi L (n + 2 * b) j)⟫_ℂ =
      if i = componentAfter 1 j then
        slotPhase L κ j * physicalSlot j u (n + a + b) * (z - (pm L (n + 2 * b) : ℂ))⁻¹
      else 0 := by
  have hm : parity (n + 2 * b) = parity n := sourceMode_parity n b
  have hden := contour_denominator_lower hL hsmall hz hm
  have hne : z ≠ (pm L (n + 2 * b) : ℂ) := by
    intro he
    rw [he, sub_self, norm_zero] at hden
    linarith
  let c : ℂ := (z - (pm L (n + 2 * b) : ℂ))⁻¹
  have he : free L κ n z (chi L (n + 2 * b) j) = c • chi L (n + 2 * b) j :=
    Local002Free.res_chi hL j (free_isResolvent hL hr hsmall n hz) hm hne
  have hae : ∀ᵐ x ∂μI L,
      (free L κ n z (chi L (n + 2 * b) j)) x = c • chiFun L (n + 2 * b) j x := by
    rw [he]
    filter_upwards [Lp.coeFn_smul c (chi L (n + 2 * b) j),
      (memLp_chiFun L (n + 2 * b) j).coeFn_toLp] with x hx hj
    change (chi L (n + 2 * b) j : ℝ → E2) x = chiFun L (n + 2 * b) j x at hj
    rw [hx, Pi.smul_apply, hj]
  have hpt : ∀ᵐ x ∂μI L,
      ⟪(chi L (n + 2 * a) i) x, (Mop κ (free L κ n z) u (chi L (n + 2 * b) j)) x⟫_ℂ =
        c * (if i = componentAfter 1 j then slotPhase L κ j *
          (if j = 0 then conj (QuantumNLS.Fourier.mode L (n + a + b) (x : AddCircle L)) * u x
            else conj (conj (QuantumNLS.Fourier.mode L (n + a + b) (x : AddCircle L)) * u x))
          else 0) := by
    filter_upwards [(mop_data hL hκ hr hsmall n hz u).1 (chi L (n + 2 * b) j),
      (memLp_chiFun L (n + 2 * a) i).coeFn_toLp, hae] with x hT hi hR
    change (chi L (n + 2 * a) i : ℝ → E2) x = chiFun L (n + 2 * a) i x at hi
    rw [hT, hi, hR]
    have hV (g : E2) : Vpt κ (u x) g = potentialPt κ (u x) g := by
      simp only [Vpt, lopPt, Local002.Jm_zero, smul_zero, zero_add]
      rfl
    rw [hV, potentialPt_smul, inner_smul_right, potential_pointwise hκ.le]
  rw [MeasureTheory.L2.inner_def, integral_congr_ae hpt, integral_const_mul]
  by_cases hij : i = componentAfter 1 j
  · simp only [if_pos hij, integral_const_mul]
    by_cases hj : j = 0
    · simp only [if_pos hj, physicalSlot, physicalFourier_integral]
      ring
    · simp only [if_neg hj, physicalSlot, physicalFourier_integral, integral_conj]
      ring
  · simp only [if_neg hij, integral_zero, mul_zero]

#print axioms mop_matrix_entry
end QuantumNLS.Local005.SourceC


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Metric
open scoped BigOperators ENNReal ComplexConjugate
namespace QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResolventWordCoefficientLOCAL005
open QuantumNLS.Local002

abbrev ScalarContour (L r : ℝ) (n : ℤ) := C(sphere (center L n) r, ℂ)

def scalarExtend {L r : ℝ} {n : ℤ} (F : ScalarContour L r n) (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ sphere (center L n) r then F ⟨z, h⟩ else 0

theorem scalarExtend_apply {L r : ℝ} {n : ℤ} (F : ScalarContour L r n)
    {z : ℂ} (hz : z ∈ sphere (center L n) r) : scalarExtend F z = F ⟨z, hz⟩ := by
  simp only [scalarExtend, dif_pos hz]

theorem scalarExtend_continuous {L r : ℝ} {n : ℤ} (F : ScalarContour L r n) :
    ContinuousOn (scalarExtend F) (sphere (center L n) r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (sphere (center L n) r).domRestrict (scalarExtend F) = F := by
    funext z
    exact scalarExtend_apply F z.2
  rw [he]
  exact F.continuous

/-- The actual scalar contour integral as a bounded linear functional. -/
def scalarJ {L r : ℝ} (hr : 0 < r) (n : ℤ) : ScalarContour L r n →L[ℂ] ℂ := by
  classical
  let f : ScalarContour L r n →ₗ[ℂ] ℂ :=
    { toFun := fun F => (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ z in C(center L n, r), scalarExtend F z
      map_add' := fun F G => by
        have he : scalarExtend (F + G) = fun z => scalarExtend F z + scalarExtend G z := by
          funext z
          by_cases hz : z ∈ sphere (center L n) r
          · simp only [scalarExtend, dif_pos hz, ContinuousMap.add_apply, ContinuousMap.smul_apply]
          · simp only [scalarExtend, dif_neg hz, add_zero, smul_zero]
        rw [he, circleIntegral.integral_add
          ((scalarExtend_continuous F).circleIntegrable hr.le)
          ((scalarExtend_continuous G).circleIntegrable hr.le), mul_add]
      map_smul' := fun a F => by
        have he : scalarExtend (a • F) = fun z => a • scalarExtend F z := by
          funext z
          by_cases hz : z ∈ sphere (center L n) r
          · simp only [scalarExtend, dif_pos hz, ContinuousMap.add_apply, ContinuousMap.smul_apply]
          · simp only [scalarExtend, dif_neg hz, add_zero, smul_zero]
        rw [he, circleIntegral.integral_smul]
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }
  apply f.mkContinuous r
  intro F
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le
    (fun z hz => by rw [scalarExtend_apply F hz]; exact F.norm_coe_le_norm _)

/-- The pre-integration scalar path integrand, using the frozen path labels and phases. -/
def pathIntegrand (L r κ : ℝ) (kind : WordKind) {k : ℕ} (j : Fin 2)
    (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) (z : ℂ) : ℂ :=
  (∏ t : Fin k, slotPhase L κ (componentAfter t.val j)) *
    (∏ t : Fin k, u t (wordLabel n q t)) *
      ((z - (pm L n : ℂ))⁻¹ ^ endpointOrder kind *
        ∏ t, (z - (pm L (sourceMode n (q t)) : ℂ))⁻¹)

def pathUniformBound (L r κ : ℝ) (kind : WordKind) {k : ℕ}
    (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) : ℝ :=
  (2 * Real.sqrt (κ / L)) ^ k * amplitude u n q *
    (r⁻¹ ^ endpointOrder kind * pathWeight L r q)

theorem pathUniformBound_nonneg (L r κ : ℝ) (hr : 0 < r) (kind : WordKind) {k : ℕ}
    (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) :
    0 ≤ pathUniformBound L r κ kind u n q := by
  exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (amplitude_nonneg u n q))
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) _) (pathWeight_nonneg L r q))

theorem pathIntegrand_bound {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (kind : WordKind) {k : ℕ} (j : Fin 2)
    (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) {z : ℂ}
    (hz : OnGamma L r n z) :
    ‖pathIntegrand L r κ kind j u n q z‖ ≤ pathUniformBound L r κ kind u n q := by
  change ‖z - (pm L n : ℂ)‖ = r at hz
  simp only [pathIntegrand, norm_mul, norm_prod, slotPhase_norm, norm_pow, norm_inv,
    hz, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg (by positivity) _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hb : (∏ t, ‖(z - (pm L (sourceMode n (q t)) : ℂ))⁻¹‖) ≤ pathWeight L r q :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun t _ => multiplier_le_gapWeight hL hr hsmall hz (q t))
  simpa only [norm_inv] using hb

theorem pathUniformBound_summable {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (kind : WordKind) {k : ℕ}
    (u : Fin k → ℤ → ℂ) (hu : ∀ t, Summable fun m => ‖u t m‖ ^ 2) (n : ℤ) :
    Summable (pathUniformBound L r κ kind u n) := by
  have hs := (envelope_row hL hr hsmall κ u hu n).1
  convert hs.mul_left ((2 * Real.sqrt (κ / L)) ^ k * r⁻¹ ^ endpointOrder kind) using 1
  funext q
  unfold pathUniformBound
  ring

def pathContour {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (kind : WordKind) {k : ℕ} (j : Fin 2)
    (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) : ScalarContour L r n := by
  refine ⟨fun z => pathIntegrand L r κ kind j u n q z, ?_⟩
  have hc : ContinuousOn (fun z : ℂ =>
      (z - (pm L n : ℂ))⁻¹ ^ endpointOrder kind *
        ∏ t, (z - (pm L (sourceMode n (q t)) : ℂ))⁻¹) (sphere (center L n) r) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.pow
      apply (continuousOn_id.sub continuousOn_const).inv₀
      intro z hz
      apply norm_pos_iff.mp
      change 0 < ‖z - (pm L n : ℂ)‖
      rw [show ‖z - (pm L n : ℂ)‖ = r from mem_sphere_iff_norm.mp hz]
      exact hr
    · apply continuousOn_finsetProd
      intro t _
      apply (continuousOn_id.sub continuousOn_const).inv₀
      intro z hz
      apply norm_pos_iff.mp
      exact lt_of_lt_of_le hr (contour_denominator_lower hL hsmall
        (mem_sphere_iff_norm.mp hz) (sourceMode_parity n (q t)))
  exact continuous_const.mul hc.restrict

theorem pathContour_summable {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (kind : WordKind) {k : ℕ} (j : Fin 2)
    (u : Fin k → ℤ → ℂ) (hu : ∀ t, Summable fun m => ‖u t m‖ ^ 2) (n : ℤ) :
    Summable (fun q => ‖pathContour hL hr hsmall κ kind j u n q‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (pathUniformBound_summable hL hr hsmall κ kind u hu n)
  intro q
  apply (ContinuousMap.norm_le _ (pathUniformBound_nonneg L r κ hr kind u n q)).2
  intro z
  exact pathIntegrand_bound hL hr hsmall κ kind j u n q (mem_sphere_iff_norm.mp z.2)

theorem scalarJ_pathContour {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (kind : WordKind) {k : ℕ} (j : Fin 2)
    (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) :
    scalarJ hr n (pathContour hL hr hsmall κ kind j u n q) =
      pathCoefficient L r κ kind j u n q := by
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    (∮ z in C(center L n, r), scalarExtend (pathContour hL hr hsmall κ kind j u n q) z) = _
  have he : (∮ z in C(center L n, r), scalarExtend (pathContour hL hr hsmall κ kind j u n q) z) =
      ∮ z in C(center L n, r), pathIntegrand L r κ kind j u n q z :=
    circleIntegral.integral_congr hr.le (fun z hz => scalarExtend_apply _ hz)
  rw [he]
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    (∮ z in C((pm L n : ℂ), r), pathIntegrand L r κ kind j u n q z) = _
  unfold pathIntegrand pathCoefficient contourScalar
  rw [circleIntegral.integral_const_mul]
  simp only [smul_eq_mul]
  ring

/-- The majorant justifies integrating the full Fourier path sum term by term. -/
theorem path_integral_hasSum {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (kind : WordKind) {k : ℕ} (j : Fin 2)
    (u : Fin k → ℤ → ℂ) (hu : ∀ t, Summable fun m => ‖u t m‖ ^ 2) (n : ℤ) :
    HasSum (fun q => pathCoefficient L r κ kind j u n q)
      (scalarJ hr n (∑' q, pathContour hL hr hsmall κ kind j u n q)) := by
  have hs := (pathContour_summable hL hr hsmall κ kind j u hu n).of_norm
  simpa only [scalarJ_pathContour] using (scalarJ hr n).hasSum hs.hasSum

#print axioms pathIntegrand_bound
#print axioms pathUniformBound_summable
#print axioms pathContour_summable
#print axioms scalarJ_pathContour
#print axioms path_integral_hasSum
end QuantumNLS.Local005.SourceC


set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local005.SourceC." ||
        n.toString.startsWith "_private.QuantumNLS.Local005Source" then
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
  Lean.logInfo m!"Local005SourceBridgeC audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
