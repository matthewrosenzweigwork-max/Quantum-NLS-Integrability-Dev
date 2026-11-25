import Mathlib

/-!
# U1 / DEF-001 / DEF-002: Fourier carrier and normalization bridge

Source anchors (pinned PR11 commit 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f):
* `source/chapters/definitions.tex`, `def:report-1` (DEF-001): `T_L = R/LZ`, Lebesgue measure
  of mass `L`, `<f,g> = ∫₀^L conj f · g` linear in the second slot,
  `e_n(x) = L^{-1/2} exp(2πinx/L)`, `û(n) = <e_n,u>`.
* `def:report-2` (DEF-002): `‖·‖_{H^s}² = Σ (1+|2πn/L|)^{2s} |û(n)|²`, same weight for `h^s(ℤ)`.
* `fable-reconciled-plan.md` §2 (U1 row, "Norms (exact)" table).

Conventions enforced here:
* the circle is `AddCircle L` for an arbitrary `L > 0` (`[Fact (0 < L)]`), and the measure is
  mathlib's `volume`, of total mass `L` (NOT a probability measure unless `L = 1`);
* mathlib's `fourierCoeff` is defined with the Haar *probability* measure on `AddCircle L`
  (`AddCircle.haarAddCircle`); the report's orthonormal coefficient `û(n)` differs from it by
  the exact factor `√L` (`coeff_eq_sqrt_mul_fourierCoeff`).  Nothing is assumed: all statements
  below are proved from mathlib.

No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory AddCircle
open scoped ENNReal ComplexConjugate

namespace QuantumNLS.Fourier

/-! ## Mass-L measure versus probability normalization -/

section Carrier

variable (L : ℝ) [Fact (0 < L)]

/-- The report measure on `T_L` has total mass `L` (DEF-001). -/
theorem torus_mass : (volume : Measure (AddCircle L)) Set.univ = ENNReal.ofReal L :=
  AddCircle.measure_univ L

/-- mathlib's Haar measure on `AddCircle L` (used by `fourierCoeff`) has total mass `1`. -/
theorem haar_mass : (haarAddCircle : Measure (AddCircle L)) Set.univ = 1 :=
  measure_univ

/-- The mass-`L` measure is `L` times the Haar probability measure. -/
theorem volume_eq_smul_haar :
    (volume : Measure (AddCircle L)) = ENNReal.ofReal L • (haarAddCircle : Measure (AddCircle L)) :=
  AddCircle.volume_eq_smul_haarAddCircle

/-- The report measure is a probability measure only for `L = 1`: the two normalizations
are genuinely different for every other `L > 0`. -/
theorem torus_isProbabilityMeasure_iff :
    IsProbabilityMeasure (volume : Measure (AddCircle L)) ↔ L = 1 := by
  constructor
  · intro h
    have h1 := h.measure_univ
    rw [torus_mass] at h1
    exact (ENNReal.ofReal_eq_one).1 h1
  · intro h
    refine ⟨?_⟩
    rw [torus_mass, h]
    simp

/-- The report orthonormal Fourier function `e_n(x) = L^{-1/2} exp(2πinx/L)` (DEF-001). -/
def mode (n : ℤ) (x : AddCircle L) : ℂ :=
  (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * fourier n x

/-- The report Fourier coefficient `û(n) = <e_n, u> = ∫ conj(e_n) u` against the
mass-`L` measure (inner product linear in the second slot). -/
def coeff (u : AddCircle L → ℂ) (n : ℤ) : ℂ :=
  ∫ x, conj (mode L n x) * u x ∂(volume : Measure (AddCircle L))

omit [Fact (0 < L)] in
/-- Value of `e_n` in terms of an explicit real exponential at a real lift:
`e_n(x) = L^{-1/2} exp(2πi n x / L)`. -/
theorem mode_coe (n : ℤ) (x : ℝ) :
    mode L n (x : AddCircle L) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * n * x / L) := by
  unfold mode
  rw [fourier_coe_apply]

/-- **Exact normalization relation.**  The report's orthonormal coefficient equals `√L` times
mathlib's probability-normalized `fourierCoeff`.  No integrability hypothesis is needed. -/
theorem coeff_eq_sqrt_mul_fourierCoeff (u : AddCircle L → ℂ) (n : ℤ) :
    coeff L u n = (Real.sqrt L : ℂ) * fourierCoeff u n := by
  have hL : 0 < L := Fact.out
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hs2 : (Real.sqrt L : ℂ) ^ 2 = (L : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hL.le]
  have hsne : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hLne : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have step : ∀ x : AddCircle L, conj (mode L n x) * u x =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (fourier (-n) x • u x) := by
    intro x
    unfold mode
    rw [map_mul, Complex.conj_ofReal, ← fourier_neg, smul_eq_mul]
    ring
  unfold coeff
  simp_rw [step]
  rw [integral_const_mul]
  have hc : fourierCoeff u n = (L : ℂ)⁻¹ * ∫ x : AddCircle L, fourier (-n) x • u x := by
    unfold fourierCoeff
    rw [integral_haarAddCircle]
    simp [Complex.real_smul]
  rw [hc]
  push_cast
  rw [← hs2]
  field_simp

/-- The probability-normalized coefficient is the report coefficient divided by `√L`. -/
theorem fourierCoeff_eq_coeff_div (u : AddCircle L → ℂ) (n : ℤ) :
    fourierCoeff u n = ((Real.sqrt L)⁻¹ : ℝ) * coeff L u n := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 Fact.out
  have hsne : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [coeff_eq_sqrt_mul_fourierCoeff]
  push_cast
  field_simp

/-- **a.e.-invariance of the report coefficient** (mass-`L` null sets). -/
theorem coeff_congr_ae {u v : AddCircle L → ℂ}
    (h : u =ᵐ[(volume : Measure (AddCircle L))] v) (n : ℤ) : coeff L u n = coeff L v n := by
  unfold coeff
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- Second-slot linearity of the report coefficient with respect to scalars. -/
theorem coeff_const_mul (c : ℂ) (u : AddCircle L → ℂ) (n : ℤ) :
    coeff L (fun x => c * u x) n = c * coeff L u n := by
  rw [coeff_eq_sqrt_mul_fourierCoeff, coeff_eq_sqrt_mul_fourierCoeff, fourierCoeff.const_mul]
  ring

/-- Second-slot additivity of the report coefficient on integrable fields (for the
mass-`L` measure; integrability transfers to the Haar probability measure). -/
theorem coeff_add {f g : AddCircle L → ℂ} (hf : Integrable f (volume : Measure (AddCircle L)))
    (hg : Integrable g (volume : Measure (AddCircle L))) (n : ℤ) :
    coeff L (fun x => f x + g x) n = coeff L f n + coeff L g n := by
  have h1 : Integrable f (haarAddCircle : Measure (AddCircle L)) :=
    memLp_one_iff_integrable.1 (MemLp.haarAddCircle (memLp_one_iff_integrable.2 hf))
  have h2 : Integrable g (haarAddCircle : Measure (AddCircle L)) :=
    memLp_one_iff_integrable.1 (MemLp.haarAddCircle (memLp_one_iff_integrable.2 hg))
  have := fourierCoeff.add h1 h2
  rw [coeff_eq_sqrt_mul_fourierCoeff, coeff_eq_sqrt_mul_fourierCoeff,
    coeff_eq_sqrt_mul_fourierCoeff]
  have h3 : fourierCoeff (fun x => f x + g x) n = fourierCoeff f n + fourierCoeff g n := by
    have h := congrFun (fourierCoeff.add (T := L) h1 h2) n
    exact h
  rw [h3]
  ring

/-- **Orthonormality of the report modes** in the mass-`L` inner product:
`<e_n, e_m> = δ_{nm}`, for every `L > 0`. -/
theorem coeff_mode (m n : ℤ) : coeff L (mode L m) n = if n = m then 1 else 0 := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 Fact.out
  have hsne : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [coeff_eq_sqrt_mul_fourierCoeff]
  have : fourierCoeff (mode L m) n =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * fourierCoeff (fourier m : AddCircle L → ℂ) n := by
    unfold mode
    exact fourierCoeff.const_mul _ _ _
  rw [this, fourierCoeff_fourier, Pi.single_apply]
  split_ifs
  · push_cast; field_simp
  · simp

/-- **Parseval for the mass-`L` measure.**  For an `L²(T_L)` field, the orthonormal report
coefficients are square-summable with sum exactly `∫ |u|²` against the mass-`L` measure. -/
theorem hasSum_sq_coeff {f : AddCircle L → ℂ} (hf : MemLp f 2 (volume : Measure (AddCircle L))) :
    HasSum (fun n : ℤ => ‖coeff L f n‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2 ∂(volume : Measure (AddCircle L))) := by
  have hL : 0 < L := Fact.out
  have hh : MemLp f 2 (haarAddCircle : Measure (AddCircle L)) := hf.haarAddCircle
  have hae := hh.coeFn_toLp
  have h1 := hasSum_sq_fourierCoeff (hh.toLp f)
  have hc : fourierCoeff (hh.toLp f : AddCircle L → ℂ) = fourierCoeff f :=
    fourierCoeff_congr_ae hae
  have hi : ∫ t, ‖(hh.toLp f : AddCircle L → ℂ) t‖ ^ 2 ∂(haarAddCircle : Measure (AddCircle L)) =
      ∫ t, ‖f t‖ ^ 2 ∂(haarAddCircle : Measure (AddCircle L)) :=
    integral_congr_ae (hae.mono fun t ht => by simp only [ht])
  rw [hc, hi] at h1
  have h2 := h1.mul_left L
  have e1 : ∫ t, ‖f t‖ ^ 2 ∂(volume : Measure (AddCircle L)) =
      L * ∫ t, ‖f t‖ ^ 2 ∂(haarAddCircle : Measure (AddCircle L)) := by
    rw [integral_haarAddCircle, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  rw [e1]
  convert h2 using 2 with n
  rw [coeff_eq_sqrt_mul_fourierCoeff, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg L), Real.sq_sqrt hL.le]

/-- The squared `ℓ²` norm of the report coefficients is the mass-`L` squared `L²` norm. -/
theorem tsum_sq_coeff {f : AddCircle L → ℂ} (hf : MemLp f 2 (volume : Measure (AddCircle L))) :
    ∑' n : ℤ, ‖coeff L f n‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(volume : Measure (AddCircle L)) :=
  (hasSum_sq_coeff L hf).tsum_eq

/-- Contrast: with the probability-normalized coefficient, Parseval carries the factor `L⁻¹`.
(Equal to the report identity only when `L = 1`.) -/
theorem tsum_sq_fourierCoeff_probability {f : AddCircle L → ℂ}
    (hf : MemLp f 2 (volume : Measure (AddCircle L))) :
    ∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2 =
      L⁻¹ * ∫ t, ‖f t‖ ^ 2 ∂(volume : Measure (AddCircle L)) := by
  have hL : 0 < L := Fact.out
  rw [← tsum_sq_coeff L hf, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [coeff_eq_sqrt_mul_fourierCoeff, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg L), Real.sq_sqrt hL.le]
  field_simp

omit [Fact (0 < L)] in
/-- `e_n(-x) = conj (e_n(x))`. -/
theorem mode_neg (n : ℤ) (x : AddCircle L) : mode L n (-x) = conj (mode L n x) := by
  unfold mode
  rw [map_mul, Complex.conj_ofReal, fourier_apply, fourier_apply, smul_neg, fourier_neg']
  rw [fourier_apply]

/-- **Reflection–conjugation convention** (needed for the `w(ū(-·)) = conj w(u)` normalization
of DEF-020): the orthonormal coefficient of `x ↦ conj (u (-x))` is `conj (û(n))`,
for every `L > 0` and every field `u` (no integrability hypothesis). -/
theorem coeff_conj_reflect (u : AddCircle L → ℂ) (n : ℤ) :
    coeff L (fun x => conj (u (-x))) n = conj (coeff L u n) := by
  unfold coeff
  have h1 : ∀ x : AddCircle L, conj (mode L n x) * conj (u (-x)) =
      conj (mode L n x * u (-x)) := fun x => by rw [map_mul]
  simp_rw [h1]
  rw [integral_conj]
  congr 1
  rw [← integral_neg_eq_self (fun x => mode L n x * u (-x)) (volume : Measure (AddCircle L))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [neg_neg, mode_neg]

end Carrier

/-! ## DEF-002 weights, norms, and explicit conversion constants -/

section Weights

/-- DEF-002 weight `(1+|2πn/L|)^{2s}` on frequency `n ∈ ℤ`. -/
def sobolevWeight (L s : ℝ) (n : ℤ) : ℝ :=
  (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (2 * s)

/-- DEF-002 squared norm `Σ (1+|2πn/L|)^{2s}|x_n|²` (the value `0` when not summable is the
`tsum` junk value; use `MemHs` for membership). -/
def hsNormSq (L s : ℝ) (x : ℤ → ℂ) : ℝ :=
  ∑' n : ℤ, sobolevWeight L s n * ‖x n‖ ^ 2

/-- DEF-002 membership in `h^s(ℤ)`: finiteness of the weighted square sum. -/
def MemHs (L s : ℝ) (x : ℤ → ℂ) : Prop :=
  Summable fun n : ℤ => sobolevWeight L s n * ‖x n‖ ^ 2

/-- `H^s(T_L)` of DEF-002: an **`L²(T_L)` field** (`MemLp u 2 volume`) whose weighted sum over
the *orthonormal* coefficients `û(n) = <e_n,u>` of `coeff` is finite.

The `MemLp` conjunct is essential: `coeff` is a Bochner integral, hence junk (`0`) for
non-integrable integrands, so without it an arbitrary non-`L²` function could satisfy the
weighted-sum condition vacuously (first-pass defect, repaired in the T1 pass). -/
def MemHsField (L s : ℝ) [Fact (0 < L)] (u : AddCircle L → ℂ) : Prop :=
  MemLp u 2 (volume : Measure (AddCircle L)) ∧ MemHs L s (coeff L u)

theorem MemHsField.memLp {L s : ℝ} [Fact (0 < L)] {u : AddCircle L → ℂ}
    (h : MemHsField L s u) : MemLp u 2 (volume : Measure (AddCircle L)) := h.1

/-- The DEF-002 squared `H^s(T_L)` norm of a field: the weighted sum over `û`. It is
meaningful (not a `tsum` junk value) exactly on `MemHsField L s u`; it is a.e.-invariant
(`hsFieldNormSq_congr_ae`) and equals the `Lp`-level norm (`hsFieldNormSq_eq_lp`). -/
def hsFieldNormSq (L s : ℝ) [Fact (0 < L)] (u : AddCircle L → ℂ) : ℝ :=
  hsNormSq L s (coeff L u)

/-- The U1-restriction is isometric in the DEF-002 norms (definitional, recorded for use). -/
theorem hsFieldNormSq_eq (L s : ℝ) [Fact (0 < L)] (u : AddCircle L → ℂ) :
    hsFieldNormSq L s u = hsNormSq L s (coeff L u) := rfl

/-- `H^s` membership is a.e.-invariant (mass-`L` null sets). -/
theorem memHsField_congr_ae {L s : ℝ} [Fact (0 < L)] {u v : AddCircle L → ℂ}
    (h : u =ᵐ[(volume : Measure (AddCircle L))] v) : MemHsField L s u ↔ MemHsField L s v := by
  have hc : coeff L u = coeff L v := funext (coeff_congr_ae L h)
  unfold MemHsField
  rw [hc]
  exact and_congr_left' (memLp_congr_ae h)

/-- The `H^s` squared norm of a field is a.e.-invariant. -/
theorem hsFieldNormSq_congr_ae {L s : ℝ} [Fact (0 < L)] {u v : AddCircle L → ℂ}
    (h : u =ᵐ[(volume : Measure (AddCircle L))] v) : hsFieldNormSq L s u = hsFieldNormSq L s v := by
  unfold hsFieldNormSq
  rw [funext (coeff_congr_ae L h)]

/-- Weighted sum at `s = 0`: weight `1`. -/
@[simp] theorem sobolevWeight_zero (L : ℝ) (n : ℤ) : sobolevWeight L 0 n = 1 := by
  simp [sobolevWeight]

theorem sobolevWeight_pos (L s : ℝ) (n : ℤ) : 0 < sobolevWeight L s n := by
  unfold sobolevWeight
  exact Real.rpow_pos_of_pos (by positivity) _

/-- For `s ≥ 0` the DEF-002 weight is at least `1` (so `h^s ⊆ ℓ²`). -/
theorem one_le_sobolevWeight (L s : ℝ) (hs : 0 ≤ s) (n : ℤ) : 1 ≤ sobolevWeight L s n := by
  unfold sobolevWeight
  exact Real.one_le_rpow (by linarith [abs_nonneg (2 * Real.pi * (n : ℝ) / L)])
    (by linarith)

/-- At `s = 0`, DEF-002 gives the plain `ℓ²` sum. -/
theorem hsNormSq_zero (L : ℝ) (x : ℤ → ℂ) : hsNormSq L 0 x = ∑' n : ℤ, ‖x n‖ ^ 2 := by
  simp [hsNormSq]

/-- **Mass-`L` `L²` identification** of the DEF-002 norm at `s = 0`:
`‖u‖²_{H^0} = ∫ |u|²` against the Lebesgue measure of mass `L`, for every `L > 0`. -/
theorem hsFieldNormSq_zero {L : ℝ} [Fact (0 < L)] {u : AddCircle L → ℂ}
    (hu : MemLp u 2 (volume : Measure (AddCircle L))) :
    hsFieldNormSq L 0 u = ∫ t, ‖u t‖ ^ 2 ∂(volume : Measure (AddCircle L)) := by
  rw [hsFieldNormSq_eq, hsNormSq_zero]
  exact tsum_sq_coeff L hu

/-- The report's `H^0` membership is automatic for `L²` fields. -/
theorem memHsField_zero {L : ℝ} [Fact (0 < L)] {u : AddCircle L → ℂ}
    (hu : MemLp u 2 (volume : Measure (AddCircle L))) : MemHsField L 0 u := by
  refine ⟨hu, ?_⟩
  unfold MemHs
  simpa using (hasSum_sq_coeff L hu).summable

/-- Conversely `H^0 = L²`: `MemHsField L 0 u ↔ MemLp u 2 volume`. -/
theorem memHsField_zero_iff {L : ℝ} [Fact (0 < L)] {u : AddCircle L → ℂ} :
    MemHsField L 0 u ↔ MemLp u 2 (volume : Measure (AddCircle L)) :=
  ⟨fun h => h.1, memHsField_zero⟩

/-- The unit-circle bracket weight `(1+n²)^s = (japaneseBracket n)^{2s}` used by the GGE
candidate (`NlsGge.Pilot.SobolevSquareSummable`, `WeightedSquareSummable`); a DIFFERENT weight
from DEF-002.  Every use of it must go through the conversion constants below. -/
def bracketWeight (s : ℝ) (n : ℤ) : ℝ := (1 + (n : ℝ) ^ 2) ^ s

/-- Same formula as the GGE source: `Real.rpow (Real.sqrt (1 + n²)) (2 s)`. -/
theorem bracketWeight_eq_sqrt_rpow (s : ℝ) (n : ℤ) :
    Real.rpow (Real.sqrt (1 + (n : ℝ) ^ 2)) (2 * s) = bracketWeight s n := by
  unfold bracketWeight
  have h0 : (0 : ℝ) ≤ 1 + (n : ℝ) ^ 2 := by positivity
  show (Real.sqrt (1 + (n : ℝ) ^ 2)) ^ (2 * s) = _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h0]
  congr 1
  ring

/-- Explicit lower conversion constant (depends on `L` and `s`). -/
def lowerConst (L s : ℝ) : ℝ := (min 1 (2 * Real.pi / L) ^ 2) ^ s

/-- Explicit upper conversion constant (depends on `L` and `s`). -/
def upperConst (L s : ℝ) : ℝ := (2 * (max 1 (2 * Real.pi / L)) ^ 2) ^ s

theorem lowerConst_pos (L s : ℝ) (hL : 0 < L) : 0 < lowerConst L s := by
  unfold lowerConst
  have : 0 < min 1 (2 * Real.pi / L) := lt_min one_pos (by positivity)
  exact Real.rpow_pos_of_pos (by positivity) _

theorem upperConst_pos (L s : ℝ) : 0 < upperConst L s := by
  unfold upperConst
  exact Real.rpow_pos_of_pos (by positivity) _

/-- **Pointwise weight conversion** (`s ≥ 0`, any `L > 0`):
`lowerConst · (1+n²)^s ≤ (1+|2πn/L|)^{2s} ≤ upperConst · (1+n²)^s`. -/
theorem sobolevWeight_comparison (L s : ℝ) (hL : 0 < L) (hs : 0 ≤ s) (n : ℤ) :
    lowerConst L s * bracketWeight s n ≤ sobolevWeight L s n ∧
      sobolevWeight L s n ≤ upperConst L s * bracketWeight s n := by
  set a : ℝ := 2 * Real.pi / L with ha
  have ha0 : 0 < a := by positivity
  set t : ℝ := |(n : ℝ)| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have ht2 : t ^ 2 = (n : ℝ) ^ 2 := sq_abs _
  have habs : |2 * Real.pi * (n : ℝ) / L| = a * t := by
    rw [ha, ht, show 2 * Real.pi * (n : ℝ) / L = 2 * Real.pi / L * (n : ℝ) by ring,
      abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / L)]
  have hw : sobolevWeight L s n = ((1 + a * t) ^ 2) ^ s := by
    unfold sobolevWeight
    rw [habs, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
  have hB : 0 < 1 + (n : ℝ) ^ 2 := by positivity
  set m : ℝ := min 1 a with hm
  set M : ℝ := max 1 a with hM
  have hm0 : 0 < m := lt_min one_pos ha0
  have hm1 : m ≤ 1 := min_le_left _ _
  have hma : m ≤ a := min_le_right _ _
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMa : a ≤ M := le_max_right _ _
  have hlow : m ^ 2 * (1 + (n : ℝ) ^ 2) ≤ (1 + a * t) ^ 2 := by
    have h1 : m * (1 + t) ≤ 1 + a * t := by nlinarith
    have h2 : 0 ≤ m * (1 + t) := by positivity
    have h3 : (m * (1 + t)) ^ 2 ≤ (1 + a * t) ^ 2 := pow_le_pow_left₀ h2 h1 2
    nlinarith [sq_nonneg (t - 1), sq_nonneg m]
  have hup : (1 + a * t) ^ 2 ≤ 2 * M ^ 2 * (1 + (n : ℝ) ^ 2) := by
    have h1 : 1 + a * t ≤ M * (1 + t) := by nlinarith
    have h0 : 0 ≤ 1 + a * t := by positivity
    have h3 : (1 + a * t) ^ 2 ≤ (M * (1 + t)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    nlinarith [sq_nonneg (t - 1), sq_nonneg M]
  constructor
  · rw [hw]
    unfold lowerConst bracketWeight
    rw [← Real.mul_rpow (by positivity) hB.le]
    exact Real.rpow_le_rpow (by positivity) hlow hs
  · rw [hw]
    unfold upperConst bracketWeight
    rw [← Real.mul_rpow (by positivity) hB.le]
    exact Real.rpow_le_rpow (by positivity) hup hs

/-- Membership in the DEF-002 weighted space implies bracket-weighted summability. -/
theorem summable_bracket_of_memHs (L s : ℝ) (hL : 0 < L) (hs : 0 ≤ s) {x : ℤ → ℂ}
    (hx : MemHs L s x) :
    Summable fun n : ℤ => bracketWeight s n * ‖x n‖ ^ 2 := by
  have hc := lowerConst_pos L s hL
  have : Summable fun n : ℤ => (lowerConst L s)⁻¹ * (sobolevWeight L s n * ‖x n‖ ^ 2) :=
    hx.mul_left _
  refine Summable.of_nonneg_of_le (fun n => by
      have := (sobolevWeight_pos L s n); unfold bracketWeight; positivity) (fun n => ?_) this
  have h := (sobolevWeight_comparison L s hL hs n).1
  have hn : 0 ≤ ‖x n‖ ^ 2 := by positivity
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right ((le_inv_mul_iff₀ hc).2 h) hn

/-- Bracket-weighted summability implies membership in the DEF-002 weighted space. -/
theorem memHs_of_summable_bracket (L s : ℝ) (hL : 0 < L) (hs : 0 ≤ s) {x : ℤ → ℂ}
    (hx : Summable fun n : ℤ => bracketWeight s n * ‖x n‖ ^ 2) : MemHs L s x := by
  have : Summable fun n : ℤ => upperConst L s * (bracketWeight s n * ‖x n‖ ^ 2) := hx.mul_left _
  refine Summable.of_nonneg_of_le (fun n => by
      have := (sobolevWeight_pos L s n); positivity) (fun n => ?_) this
  have h := (sobolevWeight_comparison L s hL hs n).2
  have hn : 0 ≤ ‖x n‖ ^ 2 := by positivity
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right h hn

/-- Two-sided conversion of the *norms* with explicit constants:
`lowerConst · Σ(1+n²)^s|x|² ≤ ‖x‖²_{h^s,DEF-002} ≤ upperConst · Σ(1+n²)^s|x|²`. -/
theorem hsNormSq_comparison (L s : ℝ) (hL : 0 < L) (hs : 0 ≤ s) {x : ℤ → ℂ}
    (hx : MemHs L s x) :
    lowerConst L s * ∑' n : ℤ, bracketWeight s n * ‖x n‖ ^ 2 ≤ hsNormSq L s x ∧
      hsNormSq L s x ≤ upperConst L s * ∑' n : ℤ, bracketWeight s n * ‖x n‖ ^ 2 := by
  have hb := summable_bracket_of_memHs L s hL hs hx
  constructor
  · rw [← tsum_mul_left]
    refine hb.mul_left _ |>.tsum_le_tsum (fun n => ?_) hx
    have h := (sobolevWeight_comparison L s hL hs n).1
    have hn : 0 ≤ ‖x n‖ ^ 2 := by positivity
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h hn
  · rw [← tsum_mul_left]
    refine hx.tsum_le_tsum (fun n => ?_) (hb.mul_left _)
    have h := (sobolevWeight_comparison L s hL hs n).2
    have hn : 0 ≤ ‖x n‖ ^ 2 := by positivity
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h hn

end Weights

/-! ## Lp-level U1: mass-`L` `L²(T_L)` → `ℓ²(ℤ)` -/

section LpBridge

/-- For any measure, the `L²` norm squared of an `Lp` element is `∫ |f|²`. -/
theorem lp_norm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  have H₃ := congr_arg RCLike.re (@L2.inner_def α ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re] at H₃
  · simp only [← norm_sq_eq_re_inner] at H₃
    exact H₃
  · exact L2.integrable_inner f f

variable (L : ℝ) [Fact (0 < L)]

/-- Null sets of the mass-`L` measure and of the Haar probability measure agree (`L > 0`). -/
theorem ae_volume_iff {p : AddCircle L → Prop} :
    (∀ᵐ x ∂(volume : Measure (AddCircle L)), p x) ↔
      ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle L)), p x := by
  rw [volume_eq_smul_haar]
  exact Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 Fact.out).ne'

variable {L}

theorem memLp_haar_of_vol (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    MemLp (u : AddCircle L → ℂ) 2 (haarAddCircle : Measure (AddCircle L)) :=
  (Lp.memLp u).haarAddCircle

theorem memLp_vol_of_haar (u : Lp ℂ 2 (haarAddCircle : Measure (AddCircle L))) :
    MemLp (u : AddCircle L → ℂ) 2 (volume : Measure (AddCircle L)) :=
  (Lp.memLp u).of_haarAddCircle

variable (L)

/-- Identity on functions, `L²(volume) → L²(haar)` (not yet normalized). -/
def volToHaar : Lp ℂ 2 (volume : Measure (AddCircle L)) →ₗ[ℂ]
    Lp ℂ 2 (haarAddCircle : Measure (AddCircle L)) where
  toFun u := (memLp_haar_of_vol u).toLp u
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(memLp_haar_of_vol (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memLp_haar_of_vol u).toLp u) ((memLp_haar_of_vol v).toLp v),
      (memLp_haar_of_vol u).coeFn_toLp, (memLp_haar_of_vol v).coeFn_toLp,
      (ae_volume_iff L).1 (Lp.coeFn_add u v)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5]
    rfl
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(memLp_haar_of_vol (c • u)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_haar_of_vol u).toLp u),
      (memLp_haar_of_vol u).coeFn_toLp,
      (ae_volume_iff L).1 (Lp.coeFn_smul c u)] with x h1 h2 h3 h5
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h5]
    rfl

/-- Identity on functions, `L²(haar) → L²(volume)`. -/
def haarToVol : Lp ℂ 2 (haarAddCircle : Measure (AddCircle L)) →ₗ[ℂ]
    Lp ℂ 2 (volume : Measure (AddCircle L)) where
  toFun u := (memLp_vol_of_haar u).toLp u
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(ae_volume_iff L).2 (Lp.coeFn_add u v),
      (memLp_vol_of_haar (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memLp_vol_of_haar u).toLp u) ((memLp_vol_of_haar v).toLp v),
      (memLp_vol_of_haar u).coeFn_toLp, (memLp_vol_of_haar v).coeFn_toLp] with x h5 h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4, h5]
    rfl
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(ae_volume_iff L).2 (Lp.coeFn_smul c u),
      (memLp_vol_of_haar (c • u)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_vol_of_haar u).toLp u),
      (memLp_vol_of_haar u).coeFn_toLp] with x h5 h1 h2 h3
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h5]
    rfl

theorem coeFn_volToHaar (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    (volToHaar L u : AddCircle L → ℂ) =ᵐ[(haarAddCircle : Measure (AddCircle L))]
      (u : AddCircle L → ℂ) :=
  (memLp_haar_of_vol u).coeFn_toLp

theorem coeFn_haarToVol (u : Lp ℂ 2 (haarAddCircle : Measure (AddCircle L))) :
    (haarToVol L u : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))]
      (u : AddCircle L → ℂ) :=
  (memLp_vol_of_haar u).coeFn_toLp

theorem haarToVol_volToHaar (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    haarToVol L (volToHaar L u) = u := by
  apply Lp.ext
  filter_upwards [coeFn_haarToVol L (volToHaar L u), (ae_volume_iff L).2 (coeFn_volToHaar L u)]
    with x h1 h2
  rw [h1, h2]

theorem volToHaar_haarToVol (u : Lp ℂ 2 (haarAddCircle : Measure (AddCircle L))) :
    volToHaar L (haarToVol L u) = u := by
  apply Lp.ext
  filter_upwards [coeFn_volToHaar L (haarToVol L u), (ae_volume_iff L).1 (coeFn_haarToVol L u)]
    with x h1 h2
  rw [h1, h2]

/-- `‖volToHaar u‖² = L⁻¹ ‖u‖²`: the unnormalized identification rescales norms by `√L`. -/
theorem norm_sq_volToHaar (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    ‖volToHaar L u‖ ^ 2 = L⁻¹ * ‖u‖ ^ 2 := by
  have h : ∫ t, ‖(volToHaar L u : AddCircle L → ℂ) t‖ ^ 2 ∂(haarAddCircle : Measure (AddCircle L)) =
      ∫ t, ‖(u : AddCircle L → ℂ) t‖ ^ 2 ∂(haarAddCircle : Measure (AddCircle L)) :=
    integral_congr_ae ((coeFn_volToHaar L u).mono fun t ht => by simp only [ht])
  rw [lp_norm_sq, lp_norm_sq, h, integral_haarAddCircle, smul_eq_mul]

theorem sqrt_ne_zero_complex : (Real.sqrt L : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (Fact.out : 0 < L)).ne'

/-- The `√L`-rescaled linear equivalence `L²(T_L, volume) ≃ L²(T_L, haar)`:
`u ↦ √L · u` (identity on functions up to the scalar). -/
def rescale : Lp ℂ 2 (volume : Measure (AddCircle L)) ≃ₗ[ℂ]
    Lp ℂ 2 (haarAddCircle : Measure (AddCircle L)) where
  toFun u := (Real.sqrt L : ℂ) • volToHaar L u
  map_add' u v := by rw [map_add, smul_add]
  map_smul' c u := by rw [map_smul, smul_comm, RingHom.id_apply]
  invFun w := (Real.sqrt L : ℂ)⁻¹ • haarToVol L w
  left_inv u := by
    beta_reduce
    rw [map_smul, haarToVol_volToHaar, smul_smul, inv_mul_cancel₀ (sqrt_ne_zero_complex (L := L)),
      one_smul]
  right_inv w := by
    beta_reduce
    rw [map_smul, volToHaar_haarToVol, smul_smul, mul_inv_cancel₀ (sqrt_ne_zero_complex (L := L)),
      one_smul]

theorem rescale_apply (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    rescale L u = (Real.sqrt L : ℂ) • volToHaar L u := rfl

/-- **`rescale` is an isometry**: it carries the mass-`L` `L²` norm to the Haar `L²` norm. -/
theorem norm_rescale (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    ‖rescale L u‖ = ‖u‖ := by
  have hL : 0 < L := Fact.out
  have h : ‖rescale L u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [rescale_apply, norm_smul, mul_pow, norm_sq_volToHaar, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg L), Real.sq_sqrt hL.le]
    field_simp
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **U1 (DEF-001), Lp level.**  The unitary `L²(T_L, mass-L Lebesgue) ≃ₗᵢ[ℂ] ℓ²(ℤ)`, built as
`√L`-rescaling to the Haar `L²` followed by mathlib's `fourierBasis.repr` (Parseval/completeness
of the Fourier basis on the Haar probability `L²`).  Surjectivity (completeness) is inherited from
mathlib's `HilbertBasis`; norm preservation is `norm_rescale`. -/
def fourierL2 : Lp ℂ 2 (volume : Measure (AddCircle L)) ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  ({ rescale L with norm_map' := norm_rescale L } :
    Lp ℂ 2 (volume : Measure (AddCircle L)) ≃ₗᵢ[ℂ] Lp ℂ 2 (haarAddCircle : Measure (AddCircle L))).trans
    (fourierBasis (T := L)).repr

/-- **U1 computes the report coefficients** `û(n) = <e_n, u>` of DEF-001, exactly (orthonormal
`mass-L` coefficient, not the probability-normalized one). -/
theorem fourierL2_apply (u : Lp ℂ 2 (volume : Measure (AddCircle L))) (n : ℤ) :
    fourierL2 L u n = coeff L (u : AddCircle L → ℂ) n := by
  have h1 : fourierL2 L u n = fourierCoeff (⇑(rescale L u)) n := by
    exact fourierBasis_repr (T := L) (rescale L u) n
  rw [h1, coeff_eq_sqrt_mul_fourierCoeff]
  have hae : (⇑(rescale L u) : AddCircle L → ℂ) =ᵐ[(haarAddCircle : Measure (AddCircle L))]
      fun x => (Real.sqrt L : ℂ) * (u : AddCircle L → ℂ) x := by
    filter_upwards [Lp.coeFn_smul (Real.sqrt L : ℂ) (volToHaar L u), coeFn_volToHaar L u]
      with x h1 h2
    rw [rescale_apply, h1, Pi.smul_apply, h2, smul_eq_mul]
  rw [fourierCoeff_congr_ae hae, fourierCoeff.const_mul]

/-- U1 is isometric: `‖(û(n))_n‖_{ℓ²} = ‖u‖_{L²(mass L)}`. -/
theorem norm_fourierL2 (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    ‖fourierL2 L u‖ = ‖u‖ :=
  (fourierL2 L).norm_map u

/-- Every square-summable sequence is the report-coefficient sequence of a unique `L²(mass-L)`
field (surjectivity / completeness of `e_n` for every `L > 0`). -/
theorem fourierL2_surjective : Function.Surjective (fourierL2 L) :=
  (fourierL2 L).surjective

/-- Synthesis: `û` determines the field. -/
theorem fourierL2_symm_apply_coeff (a : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    coeff L ((fourierL2 L).symm a : AddCircle L → ℂ) n = a n := by
  rw [← fourierL2_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **U1 restricts to `H^s → h^s` isometrically in the DEF-002 norms** (every `s`, every `L>0`):
for an `L²` class `u`, `u ∈ H^s(T_L)` iff `U1 u ∈ h^s(ℤ)`, and the DEF-002 squared norms agree. -/
theorem memHs_fourierL2_iff (s : ℝ) (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    MemHsField L s (u : AddCircle L → ℂ) ↔ MemHs L s (fun n => fourierL2 L u n) := by
  unfold MemHsField
  simp_rw [fourierL2_apply]
  exact ⟨fun h => h.2, fun h => ⟨Lp.memLp u, h⟩⟩

theorem hsNormSq_fourierL2 (s : ℝ) (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    hsNormSq L s (fun n => fourierL2 L u n) = hsFieldNormSq L s (u : AddCircle L → ℂ) := by
  unfold hsFieldNormSq
  simp_rw [fourierL2_apply]

/-- At `s = 0` the DEF-002 norm of `U1 u` is the mass-`L` `L²` norm squared. -/
theorem hsNormSq_zero_fourierL2 (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    hsNormSq L 0 (fun n => fourierL2 L u n) = ‖u‖ ^ 2 := by
  rw [hsNormSq_fourierL2, hsFieldNormSq_zero (Lp.memLp u), lp_norm_sq]

/-! ### T2: Fourier-series synthesis in `Lp volume` -/

variable {L}

omit [Fact (0 < L)] in
theorem continuous_mode (n : ℤ) : Continuous (mode L n) :=
  continuous_const.mul (fourier n).continuous

/-- `e_n` is bounded by `L^{-1/2}`, hence lies in `L²(volume)` (finite mass `L`). -/
theorem memLp_mode (n : ℤ) : MemLp (mode L n) 2 (volume : Measure (AddCircle L)) := by
  refine MemLp.of_bound (continuous_mode n).aestronglyMeasurable ((Real.sqrt L)⁻¹) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h1 : ‖fourier n x‖ = 1 := Circle.norm_coe _
  unfold mode
  rw [norm_mul, Complex.norm_real, h1, mul_one, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg L))]

variable (L)

/-- The report's orthonormal Fourier function `e_n`, as an element of `L²(T_L, mass-L)`. -/
def modeLp (n : ℤ) : Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  (memLp_mode n).toLp (mode L n)

theorem coeFn_modeLp (n : ℤ) :
    (modeLp L n : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))] mode L n :=
  (memLp_mode n).coeFn_toLp

/-- `U1 e_m = δ_m`: the unit basis vector of `ℓ²(ℤ)` (orthonormality, now at the `Lp` level). -/
theorem fourierL2_modeLp (m : ℤ) : fourierL2 L (modeLp L m) = lp.single 2 m (1 : ℂ) := by
  ext n
  rw [fourierL2_apply, coeff_congr_ae L (coeFn_modeLp L m), coeff_mode, lp.single_apply,
    Pi.single_apply]

/-- **Fourier-series synthesis** (DEF-001 / U1 inversion): for every `L² (mass-L)` class `u`,
`u = Σ_n û(n) e_n` unconditionally in the `L²` norm, with `û(n) = <e_n,u>`. -/
theorem hasSum_coeff_smul_modeLp (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    HasSum (fun n : ℤ => coeff L (u : AddCircle L → ℂ) n • modeLp L n) u := by
  have h := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (fourierL2 L u)
  have h2 := h.map (fourierL2 L).symm.toContinuousLinearEquiv.toContinuousLinearMap.toAddMonoidHom
    (fourierL2 L).symm.toContinuousLinearEquiv.continuous
  rw [show (fourierL2 L).symm.toContinuousLinearEquiv.toContinuousLinearMap.toAddMonoidHom
      (fourierL2 L u) = u from (fourierL2 L).symm_apply_apply u] at h2
  convert h2 using 1
  funext n
  have hs : lp.single (E := fun _ : ℤ => ℂ) 2 n (fourierL2 L u n) =
      (fourierL2 L u n) • lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) := by
    ext k; simp [lp.single_apply, Pi.single_apply]
  show _ = (fourierL2 L).symm (lp.single (E := fun _ : ℤ => ℂ) 2 n (fourierL2 L u n))
  rw [hs, map_smul, ← fourierL2_modeLp L n, LinearIsometryEquiv.symm_apply_apply, fourierL2_apply]

/-- **Lp-level `H^s(T_L)` membership** (no representative issues): `U1 u ∈ h^s(ℤ)`. -/
def MemHsLp (L s : ℝ) [Fact (0 < L)] (u : Lp ℂ 2 (volume : Measure (AddCircle L))) : Prop :=
  MemHs L s (fun n => fourierL2 L u n)

/-- Lp-level squared `H^s(T_L)` norm: the DEF-002 sum of `U1 u`. -/
def hsLpNormSq (L s : ℝ) [Fact (0 < L)] (u : Lp ℂ 2 (volume : Measure (AddCircle L))) : ℝ :=
  hsNormSq L s (fun n => fourierL2 L u n)

theorem memHsLp_iff (s : ℝ) (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    MemHsLp L s u ↔ MemHsField L s (u : AddCircle L → ℂ) :=
  (memHs_fourierL2_iff L s u).symm

theorem hsLpNormSq_eq_field (s : ℝ) (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    hsLpNormSq L s u = hsFieldNormSq L s (u : AddCircle L → ℂ) :=
  hsNormSq_fourierL2 L s u

/-- A function-level `H^s` field and its `L²` class agree on membership. -/
theorem memHsField_iff_memHsLp (s : ℝ) {f : AddCircle L → ℂ}
    (hf : MemLp f 2 (volume : Measure (AddCircle L))) :
    MemHsField L s f ↔ MemHsLp L s (hf.toLp f) := by
  rw [memHsLp_iff]
  exact memHsField_congr_ae hf.coeFn_toLp.symm

/-- ... and on the DEF-002 squared norm. -/
theorem hsFieldNormSq_eq_lp (s : ℝ) {f : AddCircle L → ℂ}
    (hf : MemLp f 2 (volume : Measure (AddCircle L))) :
    hsFieldNormSq L s f = hsLpNormSq L s (hf.toLp f) := by
  rw [hsLpNormSq_eq_field]
  exact hsFieldNormSq_congr_ae hf.coeFn_toLp.symm

end LpBridge

/-! ## T3 (first part of R-00E786F0 = `F04:lem-products`): ℓ¹ bound and continuous representative

Source: `chapters/foundations/F04.tex` lines 20–60, `\ReportID{R-00E786F0}`. F04 uses
`p_n = 2πn/L`, orthonormal `f̂(n) = <e_n,f>`, and the **bracket norm**
`‖f‖²_{H^s} = Σ (1+p_n²)^s |f̂(n)|²` — which is neither DEF-002's `(1+|p_n|)^{2s}` nor the
unit-circle `(1+n²)^s`.  Conversions are proved below.  Only the **first** displayed part of the
lemma (finiteness of `c_L`, the `ℓ¹` bound, the sup bound and the continuous representative) is
treated here; the algebra, triple-product, tame and Lipschitz estimates are NOT covered, so the
node R-00E786F0 is not discharged by this section. -/

section F04

/-- `p_n = 2πn/L`. -/
def freq (L : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * (n : ℝ) / L

/-- F04 bracket weight `(1+p_n²)^s`. -/
def f04Weight (L s : ℝ) (n : ℤ) : ℝ := (1 + freq L n ^ 2) ^ s

/-- F04 membership: `Σ (1+p_n²)^s |x_n|² < ∞`. -/
def Mem04 (L s : ℝ) (x : ℤ → ℂ) : Prop :=
  Summable fun n : ℤ => f04Weight L s n * ‖x n‖ ^ 2

/-- F04 squared norm `‖x‖²_{H^s} = Σ (1+p_n²)^s |x_n|²`. -/
def f04NormSq (L s : ℝ) (x : ℤ → ℂ) : ℝ := ∑' n : ℤ, f04Weight L s n * ‖x n‖ ^ 2

/-- `Σ (1+p_n²)⁻¹` (finite for `L > 0`, `summable_f04`). -/
def f04Sum (L : ℝ) : ℝ := ∑' n : ℤ, (1 + freq L n ^ 2)⁻¹

/-- F04's constant `c_L = ((1/L) Σ (1+p_n²)⁻¹)^{1/2}`. -/
def cL (L : ℝ) : ℝ := Real.sqrt (L⁻¹ * f04Sum L)

@[simp] theorem f04Weight_one (L : ℝ) (n : ℤ) : f04Weight L 1 n = 1 + freq L n ^ 2 := by
  simp [f04Weight]

theorem f04Weight_pos (L s : ℝ) (n : ℤ) : 0 < f04Weight L s n :=
  Real.rpow_pos_of_pos (by positivity) _

/-- **F04 bracket ↔ DEF-002 conversion** (`s ≥ 0`, exact constants `1` and `2^s`):
`(1+p_n²)^s ≤ (1+|p_n|)^{2s} ≤ 2^s (1+p_n²)^s`. -/
theorem f04Weight_comparison (L s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    f04Weight L s n ≤ sobolevWeight L s n ∧
      sobolevWeight L s n ≤ (2 : ℝ) ^ s * f04Weight L s n := by
  have hp : |2 * Real.pi * (n : ℝ) / L| = |freq L n| := rfl
  set t : ℝ := |freq L n| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have ht2 : t ^ 2 = freq L n ^ 2 := sq_abs _
  have hsw : sobolevWeight L s n = ((1 + t) ^ 2) ^ s := by
    unfold sobolevWeight
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
  have h1 : 1 + freq L n ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
  have h2 : (1 + t) ^ 2 ≤ 2 * (1 + freq L n ^ 2) := by nlinarith [sq_nonneg (t - 1)]
  have hpos : 0 ≤ 1 + freq L n ^ 2 := by positivity
  constructor
  · rw [hsw]
    exact Real.rpow_le_rpow hpos h1 hs
  · rw [hsw]
    unfold f04Weight
    rw [← Real.mul_rpow (by norm_num) hpos]
    exact Real.rpow_le_rpow (by positivity) h2 hs

/-- `c_L` is finite: `Σ (1+p_n²)⁻¹ < ∞` for every `L > 0` (comparison with `Σ n⁻²`). -/
theorem summable_f04 {L : ℝ} (hL : 0 < L) : Summable fun n : ℤ => (1 + freq L n ^ 2)⁻¹ := by
  set a : ℝ := 2 * Real.pi / L with ha
  have ha0 : 0 < a := by positivity
  have hg : Summable fun n : ℤ => (a ^ 2)⁻¹ * (1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow.2 (by norm_num : 1 < 2)).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hf : freq L n = a * n := by unfold freq; rw [ha]; ring
  have hpos : 0 < (a * n) ^ 2 := by positivity
  rw [hf, Real.norm_of_nonneg (by positivity)]
  rw [mul_pow, show (a ^ 2)⁻¹ * (1 / (n : ℝ) ^ 2) = (a ^ 2 * (n : ℝ) ^ 2)⁻¹ by
    field_simp]
  exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg (a * n)])

theorem f04Sum_nonneg (L : ℝ) : 0 ≤ f04Sum L :=
  tsum_nonneg fun n => by unfold freq; positivity

theorem cL_nonneg (L : ℝ) : 0 ≤ cL L := Real.sqrt_nonneg _

/-- `√L · c_L = (Σ (1+p_n²)⁻¹)^{1/2}`: the constant in the `ℓ¹` bound. -/
theorem sqrt_mul_cL {L : ℝ} (hL : 0 < L) : Real.sqrt L * cL L = Real.sqrt (f04Sum L) := by
  unfold cL
  rw [← Real.sqrt_mul hL.le, mul_inv_cancel_left₀ hL.ne']

/-- **ℓ¹ bound of F04 (`eq:l1`, first inequality)**: for `x` with finite F04 `H¹` norm,
`Σ|x_n|` converges and `Σ|x_n| ≤ √L · c_L · ‖x‖_{H¹}` with
`‖x‖²_{H¹} = Σ (1+p_n²)|x_n|²` and `c_L` as defined by F04. -/
theorem tsum_norm_le_cL {L : ℝ} (hL : 0 < L) {x : ℤ → ℂ} (hx : Mem04 L 1 x) :
    Summable (fun n => ‖x n‖) ∧
      ∑' n, ‖x n‖ ≤ Real.sqrt L * cL L * Real.sqrt (f04NormSq L 1 x) := by
  have hq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hw : ∀ n : ℤ, 0 < 1 + freq L n ^ 2 := fun n => by positivity
  set f : ℤ → ℝ := fun n => Real.sqrt ((1 + freq L n ^ 2)⁻¹) with hf
  set g : ℤ → ℝ := fun n => Real.sqrt (1 + freq L n ^ 2) * ‖x n‖ with hg
  have hfg : ∀ n, f n * g n = ‖x n‖ := fun n => by
    simp only [hf, hg]
    rw [← mul_assoc, ← Real.sqrt_mul (inv_nonneg.2 (hw n).le), inv_mul_cancel₀ (hw n).ne',
      Real.sqrt_one, one_mul]
  have hf2 : ∀ n, f n ^ (2 : ℝ) = (1 + freq L n ^ 2)⁻¹ := fun n => by
    simp only [hf]
    rw [Real.rpow_two, Real.sq_sqrt (inv_nonneg.2 (hw n).le)]
  have hg2 : ∀ n, g n ^ (2 : ℝ) = f04Weight L 1 n * ‖x n‖ ^ 2 := fun n => by
    simp only [hg]
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hw n).le, f04Weight_one]
  have hf_sum : Summable fun n => f n ^ (2 : ℝ) := by
    simp_rw [hf2]; exact summable_f04 hL
  have hg_sum : Summable fun n => g n ^ (2 : ℝ) := by
    simp_rw [hg2]; exact hx
  have hf0 : ∀ n, 0 ≤ f n := fun n => Real.sqrt_nonneg _
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; positivity
  obtain ⟨hs1, hs2⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hq hf0 hg0 hf_sum hg_sum
  simp_rw [hfg] at hs1 hs2
  refine ⟨hs1, ?_⟩
  rw [sqrt_mul_cL hL]
  have e1 : ∑' n, f n ^ (2 : ℝ) = f04Sum L := by simp_rw [hf2]; rfl
  have e2 : ∑' n, g n ^ (2 : ℝ) = f04NormSq L 1 x := by simp_rw [hg2]; rfl
  rw [e1, e2] at hs2
  simpa [Real.sqrt_eq_rpow, one_div] using hs2

/-! ### Absolutely convergent Fourier series and its continuous sum -/

section Series

variable (L : ℝ) [Fact (0 < L)]

omit [Fact (0 < L)] in
theorem norm_mode (n : ℤ) (x : AddCircle L) : ‖mode L n x‖ = (Real.sqrt L)⁻¹ := by
  have h1 : ‖fourier n x‖ = 1 := Circle.norm_coe _
  unfold mode
  rw [norm_mul, Complex.norm_real, h1, mul_one,
    Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg L))]

/-- The pointwise Fourier series `x ↦ Σ_n a_n e_n(x)` (value `0` where not summable). -/
def seriesRep (a : ℤ → ℂ) (x : AddCircle L) : ℂ := ∑' n : ℤ, a n * mode L n x

variable {L}

omit [Fact (0 < L)] in
theorem continuous_seriesRep {a : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) :
    Continuous (seriesRep L a) :=
  continuous_tsum (fun n => continuous_const.mul (continuous_mode n))
    (ha.mul_right (Real.sqrt L)⁻¹) (fun n x => by rw [norm_mul, norm_mode])

omit [Fact (0 < L)] in
/-- Sup bound for the series: `|Σ a_n e_n(x)| ≤ L^{-1/2} Σ|a_n|`. -/
theorem norm_seriesRep_le {a : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) (x : AddCircle L) :
    ‖seriesRep L a x‖ ≤ (Real.sqrt L)⁻¹ * ∑' n, ‖a n‖ := by
  unfold seriesRep
  calc ‖∑' n : ℤ, a n * mode L n x‖ ≤ ∑' n : ℤ, ‖a n * mode L n x‖ := norm_tsum_le_tsum_norm
        (by simpa [norm_mul, norm_mode] using ha.mul_right (Real.sqrt L)⁻¹)
    _ = ∑' n : ℤ, ‖a n‖ * (Real.sqrt L)⁻¹ := tsum_congr fun n => by rw [norm_mul, norm_mode]
    _ = (Real.sqrt L)⁻¹ * ∑' n, ‖a n‖ := by rw [tsum_mul_right, mul_comm]

theorem memLp_seriesRep {a : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) :
    MemLp (seriesRep L a) 2 (volume : Measure (AddCircle L)) :=
  MemLp.of_bound (continuous_seriesRep ha).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun x => norm_seriesRep_le ha x)

/-- **The coefficients of the continuous sum are the given ones**: for `a ∈ ℓ¹`,
`<e_m, Σ_n a_n e_n> = a_m` (termwise integration, justified by absolute summability). -/
theorem coeff_seriesRep {a : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) (m : ℤ) :
    coeff L (seriesRep L a) m = a m := by
  have hL : 0 < L := Fact.out
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  set F : ℤ → AddCircle L → ℂ := fun n x => conj (mode L m x) * (a n * mode L n x) with hF
  have hFc : ∀ n, Continuous (F n) := fun n =>
    (Complex.continuous_conj.comp (continuous_mode m)).mul
      (continuous_const.mul (continuous_mode n))
  have hFnorm : ∀ n x, ‖F n x‖ = ‖a n‖ / L := fun n x => by
    simp only [hF]
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_mode, norm_mode]
    have h2 : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL.le
    have h' : ‖a n‖ / L = ‖a n‖ / (Real.sqrt L) ^ 2 := by rw [h2]
    rw [h']
    field_simp
  have hint : ∀ n, Integrable (F n) (volume : Measure (AddCircle L)) := fun n =>
    (hFc n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnorm : ∀ n, ∫ x, ‖F n x‖ ∂(volume : Measure (AddCircle L)) = ‖a n‖ := fun n => by
    simp_rw [hFnorm]
    rw [integral_const, measureReal_def, torus_mass, ENNReal.toReal_ofReal hL.le, smul_eq_mul]
    field_simp
  have hsum : Summable fun n => ∫ x, ‖F n x‖ ∂(volume : Measure (AddCircle L)) := by
    simp_rw [hnorm]; exact ha
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hI : ∀ n, ∫ x, F n x ∂(volume : Measure (AddCircle L)) =
      if m = n then a n else 0 := fun n => by
    have : ∫ x, F n x ∂(volume : Measure (AddCircle L)) = a n * coeff L (mode L n) m := by
      unfold coeff
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hF]; ring
    rw [this, coeff_mode]
    by_cases hmn : m = n
    · simp [hmn]
    · simp [hmn]
  have h2 : HasSum (fun n => if m = n then a n else 0) (a m) := by
    simpa using hasSum_single (f := fun n : ℤ => if m = n then a n else 0) m
      (fun n hn => by simp [Ne.symm hn])
  have h3 : ∫ x, (∑' n, F n x) ∂(volume : Measure (AddCircle L)) = a m := by
    refine h.unique ?_
    simpa [hI] using h2
  rw [← h3]
  unfold coeff seriesRep
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hF]
  rw [tsum_mul_left]

end Series

/-- F04 membership is implied by DEF-002 membership (`s ≥ 0`), with `‖·‖_{F04} ≤ ‖·‖_{DEF-002}`. -/
theorem mem04_of_memHs {L s : ℝ} (hs : 0 ≤ s) {x : ℤ → ℂ} (hx : MemHs L s x) : Mem04 L s x := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hx
  · have := f04Weight_pos L s n; positivity
  · exact mul_le_mul_of_nonneg_right (f04Weight_comparison L s hs n).1 (by positivity)

theorem f04NormSq_le_hsNormSq {L s : ℝ} (hs : 0 ≤ s) {x : ℤ → ℂ} (hx : MemHs L s x) :
    f04NormSq L s x ≤ hsNormSq L s x :=
  (mem04_of_memHs hs hx).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (f04Weight_comparison L s hs n).1 (by positivity)) hx

/-- **R-00E786F0 (`F04:lem-products`), first part — `Lp` form.**  For every `L > 0` and every
`u ∈ L²(T_L)` (mass-`L` measure) with finite F04 `H¹` norm
`‖u‖²_{H¹} = Σ (1+p_n²)|û(n)|²`:
* `Σ|û(n)|` converges and `Σ|û(n)| ≤ √L · c_L · ‖u‖_{H¹}`;
* `u` has a continuous representative `g = Σ û(n) e_n` (a.e. equal to `u`) with
  `‖g‖_∞ ≤ c_L ‖u‖_{H¹}`.
NOT covered: the `H¹` algebra, triple-product, tame and Lipschitz estimates of the same lemma. -/
theorem f04_l1_sup_continuous_representative {L : ℝ} [Fact (0 < L)]
    (u : Lp ℂ 2 (volume : Measure (AddCircle L)))
    (hu : Mem04 L 1 (fun n => fourierL2 L u n)) :
    Summable (fun n => ‖fourierL2 L u n‖) ∧
    ∑' n, ‖fourierL2 L u n‖ ≤
      Real.sqrt L * cL L * Real.sqrt (f04NormSq L 1 (fun n => fourierL2 L u n)) ∧
    ∃ g : AddCircle L → ℂ, Continuous g ∧
      (u : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))] g ∧
      ∀ x, ‖g x‖ ≤ cL L * Real.sqrt (f04NormSq L 1 (fun n => fourierL2 L u n)) := by
  have hL : 0 < L := Fact.out
  obtain ⟨ha, hle⟩ := tsum_norm_le_cL hL hu
  refine ⟨ha, hle, seriesRep L (fun n => fourierL2 L u n), continuous_seriesRep ha, ?_, ?_⟩
  · have hg := memLp_seriesRep (L := L) ha
    have heq : hg.toLp (seriesRep L (fun n => fourierL2 L u n)) = u := by
      apply (fourierL2 L).injective
      ext n
      rw [fourierL2_apply, coeff_congr_ae L hg.coeFn_toLp, coeff_seriesRep ha]
    have h := hg.coeFn_toLp
    rw [heq] at h
    exact h
  · intro x
    have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
    calc ‖seriesRep L (fun n => fourierL2 L u n) x‖
        ≤ (Real.sqrt L)⁻¹ * ∑' n, ‖fourierL2 L u n‖ := norm_seriesRep_le ha x
      _ ≤ (Real.sqrt L)⁻¹ * (Real.sqrt L * cL L *
            Real.sqrt (f04NormSq L 1 (fun n => fourierL2 L u n))) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hs.le)
      _ = cL L * Real.sqrt (f04NormSq L 1 (fun n => fourierL2 L u n)) := by
          field_simp

/-- The same, for the DEF-002 `H¹` space: `Σ|û(n)| ≤ √L c_L ‖u‖_{H¹,DEF-002}` (the F04 norm is
dominated by the DEF-002 norm, constant `1`, `f04NormSq_le_hsNormSq`). -/
theorem tsum_norm_fourierL2_le_def002 {L : ℝ} [Fact (0 < L)]
    (u : Lp ℂ 2 (volume : Measure (AddCircle L)))
    (hu : MemHs L 1 (fun n => fourierL2 L u n)) :
    ∑' n, ‖fourierL2 L u n‖ ≤
      Real.sqrt L * cL L * Real.sqrt (hsNormSq L 1 (fun n => fourierL2 L u n)) := by
  have hL : 0 < L := Fact.out
  have h04 := mem04_of_memHs (by norm_num) hu
  refine (f04_l1_sup_continuous_representative u h04).2.1.trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (f04NormSq_le_hsNormSq (by norm_num) hu))
    (mul_nonneg (Real.sqrt_nonneg _) (cL_nonneg L))

/-! ### Three-term bracket inequality (used in `eq:algebra`/`eq:triple`) -/

/-- `√(1+(a+b)²) ≤ √(1+a²) + √(1+b²)`. -/
theorem sqrt_one_add_sq_add_le (a b : ℝ) :
    Real.sqrt (1 + (a + b) ^ 2) ≤ Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) := by
  have hA := Real.sqrt_nonneg (1 + a ^ 2)
  have hB := Real.sqrt_nonneg (1 + b ^ 2)
  have hA2 : Real.sqrt (1 + a ^ 2) ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hB2 : Real.sqrt (1 + b ^ 2) ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hAB : (1 + a * b) ^ 2 ≤ (Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2)) ^ 2 := by
    rw [mul_pow, hA2, hB2]; nlinarith [sq_nonneg (a - b)]
  have hAB' : 1 + a * b ≤ Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2) :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq hAB (mul_nonneg hA hB))
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith

/-- Three-term version, as in the proof of F04 `lem-products`:
`√(1+(a+b+c)²) ≤ √(1+a²) + √(1+b²) + √(1+c²)`. -/
theorem sqrt_one_add_sq_add_add_le (a b c : ℝ) :
    Real.sqrt (1 + (a + b + c) ^ 2) ≤
      Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) + Real.sqrt (1 + c ^ 2) :=
  (sqrt_one_add_sq_add_le (a + b) c).trans
    (by linarith [sqrt_one_add_sq_add_le a b])

theorem freq_add (L : ℝ) (k l : ℤ) : freq L (k + l) = freq L k + freq L l := by
  unfold freq; push_cast; ring

theorem f04Weight_half (L : ℝ) (n : ℤ) : f04Weight L (1 / 2) n = Real.sqrt (1 + freq L n ^ 2) := by
  unfold f04Weight; rw [Real.sqrt_eq_rpow]

/-- F04 weight at `s = 1/2` is subadditive in the frequency index: the pointwise inequality
that lets the `H¹` weight be split over a convolution. -/
theorem f04Weight_half_add_le (L : ℝ) (k l : ℤ) :
    f04Weight L (1 / 2) (k + l) ≤ f04Weight L (1 / 2) k + f04Weight L (1 / 2) l := by
  simp only [f04Weight_half, freq_add]
  exact sqrt_one_add_sq_add_le _ _

theorem f04Weight_half_add_add_le (L : ℝ) (k l m : ℤ) :
    f04Weight L (1 / 2) (k + l + m) ≤
      f04Weight L (1 / 2) k + f04Weight L (1 / 2) l + f04Weight L (1 / 2) m := by
  simp only [f04Weight_half, freq_add]
  exact sqrt_one_add_sq_add_add_le _ _ _

end F04

/-! ## R-00E786F0 remainder, step 1: sequence Young inequality `ℓ¹ * ℓ² ⊆ ℓ²` -/

section Young

/-- Cauchy–Schwarz for nonnegative square-summable families (series form). -/
theorem tsum_mul_sq_le {ι : Type*} {f g : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i)
    (hf : Summable fun i => f i ^ 2) (hg : Summable fun i => g i ^ 2) :
    Summable (fun i => f i * g i) ∧
      (∑' i, f i * g i) ^ 2 ≤ (∑' i, f i ^ 2) * ∑' i, g i ^ 2 := by
  have hq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf' : Summable fun i => f i ^ (2 : ℝ) := by simpa [Real.rpow_two] using hf
  have hg' : Summable fun i => g i ^ (2 : ℝ) := by simpa [Real.rpow_two] using hg
  obtain ⟨h1, h2⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hq hf0 hg0 hf' hg'
  refine ⟨h1, ?_⟩
  have hA : 0 ≤ ∑' i, f i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hB : 0 ≤ ∑' i, g i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hX : 0 ≤ ∑' i, f i * g i := tsum_nonneg fun i => mul_nonneg (hf0 i) (hg0 i)
  simp only [Real.rpow_two] at h2
  have e : ((∑' i, f i ^ 2) ^ (1 / (2 : ℝ)) * (∑' i, g i ^ 2) ^ (1 / (2 : ℝ))) ^ 2 =
      (∑' i, f i ^ 2) * ∑' i, g i ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hA, ← Real.rpow_mul hB]
    norm_num
  calc (∑' i, f i * g i) ^ 2 ≤ ((∑' i, f i ^ 2) ^ (1 / (2 : ℝ)) *
        (∑' i, g i ^ 2) ^ (1 / (2 : ℝ))) ^ 2 := pow_le_pow_left₀ hX h2 2
    _ = _ := e

/-- **Young's inequality `ℓ¹ * ℓ² ≤ ℓ²` on `ℤ`** (nonnegative sequences; F04 proof text
"`‖a*b‖_{ℓ²} ≤ ‖a‖_{ℓ¹}‖b‖_{ℓ²}`").  The convolution series converge for every `n`, the
convolution is square summable, and its squared `ℓ²` norm is at most `(Σα)² Σβ²`. -/
theorem young_l1_l2 {α β : ℤ → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα : Summable α) (hβ : Summable fun k => β k ^ 2) :
    (∀ n, Summable fun k => α k * β (n - k)) ∧
    Summable (fun n => (∑' k, α k * β (n - k)) ^ 2) ∧
    ∑' n, (∑' k, α k * β (n - k)) ^ 2 ≤ (∑' k, α k) ^ 2 * ∑' k, β k ^ 2 := by
  set A := ∑' k, α k with hA
  set B := ∑' k, β k ^ 2 with hB
  have hA0 : 0 ≤ A := tsum_nonneg hα0
  have hB0 : 0 ≤ B := tsum_nonneg fun k => sq_nonneg _
  have hβB : ∀ m, β m ^ 2 ≤ B := fun m => hβ.le_tsum m (fun j _ => sq_nonneg _)
  have hβM : ∀ m, β m ≤ Real.sqrt B := fun m => Real.le_sqrt_of_sq_le (hβB m)
  -- summability of the convolution series
  have S1 : ∀ n, Summable fun k => α k * β (n - k) := fun n =>
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hα0 k) (hβ0 _))
      (fun k => mul_le_mul_of_nonneg_left (hβM _) (hα0 k)) (hα.mul_right _)
  have S2 : ∀ n, Summable fun k => α k * β (n - k) ^ 2 := fun n =>
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hα0 k) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (hβB _) (hα0 k)) (hα.mul_right _)
  -- pointwise weighted Cauchy–Schwarz
  have CS : ∀ n, (∑' k, α k * β (n - k)) ^ 2 ≤ A * ∑' k, α k * β (n - k) ^ 2 := fun n => by
    have hf2 : Summable fun k => Real.sqrt (α k) ^ 2 := by
      simpa [Real.sq_sqrt (hα0 _)] using hα
    have hg2 : Summable fun k => (Real.sqrt (α k) * β (n - k)) ^ 2 := by
      simpa [mul_pow, Real.sq_sqrt (hα0 _)] using S2 n
    have := (tsum_mul_sq_le (fun k => Real.sqrt_nonneg (α k))
      (fun k => mul_nonneg (Real.sqrt_nonneg _) (hβ0 _)) hf2 hg2).2
    have e1 : ∀ k, Real.sqrt (α k) * (Real.sqrt (α k) * β (n - k)) = α k * β (n - k) := fun k => by
      rw [← mul_assoc, Real.mul_self_sqrt (hα0 k)]
    simp_rw [e1, mul_pow, Real.sq_sqrt (hα0 _)] at this
    exact this
  -- finite partial sums bound
  have FIN : ∀ S : Finset ℤ, ∑ n ∈ S, (∑' k, α k * β (n - k)) ^ 2 ≤ A ^ 2 * B := fun S => by
    calc ∑ n ∈ S, (∑' k, α k * β (n - k)) ^ 2
        ≤ ∑ n ∈ S, A * ∑' k, α k * β (n - k) ^ 2 := Finset.sum_le_sum fun n _ => CS n
      _ = A * ∑' k, ∑ n ∈ S, α k * β (n - k) ^ 2 := by
          rw [← Finset.mul_sum, Summable.tsum_finsetSum (fun n _ => S2 n)]
      _ ≤ A * ∑' k, α k * B := by
          refine mul_le_mul_of_nonneg_left ?_ hA0
          refine Summable.tsum_le_tsum (fun k => ?_) ?_ (hα.mul_right B)
          · rw [← Finset.mul_sum]
            refine mul_le_mul_of_nonneg_left ?_ (hα0 k)
            calc ∑ n ∈ S, β (n - k) ^ 2
                = ∑ m ∈ S.map (Equiv.subRight k).toEmbedding, β m ^ 2 := by
                  rw [Finset.sum_map]; rfl
              _ ≤ B := hβ.sum_le_tsum _ (fun j _ => sq_nonneg _)
          · exact summable_sum fun n _ => S2 n
      _ = A ^ 2 * B := by rw [tsum_mul_right]; ring
  have hd0 : ∀ n, 0 ≤ (∑' k, α k * β (n - k)) ^ 2 := fun n => sq_nonneg _
  have hsum : Summable fun n => (∑' k, α k * β (n - k)) ^ 2 := summable_of_sum_le hd0 FIN
  exact ⟨S1, hsum, by
    have := hsum.tsum_le_of_sum_le FIN
    calc _ ≤ A ^ 2 * B := this
      _ = _ := rfl⟩

end Young

/-! ## R-00E786F0 remainder, step 2: Fourier coefficients of a product = `L^{-1/2}` convolution -/

section Product

variable {L : ℝ} [Fact (0 < L)]

omit [Fact (0 < L)] in
/-- `conj(e_n) · e_k = L^{-1/2} conj(e_{n-k})`: the exact normalization behind
`\widehat{fg} = L^{-1/2} (\widehat f * \widehat g)`. -/
theorem conj_mode_mul_mode (n k : ℤ) (x : AddCircle L) :
    conj (mode L n x) * mode L k x = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * conj (mode L (n - k) x) := by
  have h : fourier (-(n - k)) x = fourier (-n) x * fourier k x := by
    rw [← fourier_add]; congr 2; ring
  unfold mode
  rw [map_mul, map_mul, Complex.conj_ofReal, ← fourier_neg, ← fourier_neg, h]
  ring

/-- **Fourier product formula, general second factor.**  For `a ∈ ℓ¹` and any continuous `φ`,
`<e_n, (Σ a_k e_k)·φ> = L^{-1/2} Σ_k a_k <e_{n-k}, φ>` (termwise integration). -/
theorem hasSum_coeff_mul_continuous {a : ℤ → ℂ} (ha : Summable fun n => ‖a n‖)
    {φ : AddCircle L → ℂ} (hφ : Continuous φ) (n : ℤ) :
    HasSum (fun k : ℤ => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (a k * coeff L φ (n - k)))
      (coeff L (fun x => seriesRep L a x * φ x) n) := by
  have hL : 0 < L := Fact.out
  set c : ℝ := (Real.sqrt L)⁻¹ with hc
  set G : AddCircle L → ℂ := φ with hG
  obtain ⟨M, hGM'⟩ := isCompact_univ.exists_bound_of_continuousOn (f := φ) hφ.continuousOn
  have hGc : Continuous G := hφ
  have hGM : ∀ x, ‖G x‖ ≤ M := fun x => hGM' x (Set.mem_univ x)
  set H : ℤ → AddCircle L → ℂ := fun k x => conj (mode L n x) * (a k * mode L k x) * G x with hH
  have hHc : ∀ k, Continuous (H k) := fun k =>
    ((Complex.continuous_conj.comp (continuous_mode n)).mul
      (continuous_const.mul (continuous_mode k))).mul hGc
  have hint : ∀ k, Integrable (H k) (volume : Measure (AddCircle L)) := fun k =>
    (hHc k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbd : ∀ k x, ‖H k x‖ ≤ ‖a k‖ * c * c * M := fun k x => by
    simp only [hH]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, norm_mode, norm_mode]
    have h1 := hGM x
    have h2 : 0 ≤ ‖a k‖ * c * c := by positivity
    calc c * (‖a k‖ * c) * ‖G x‖ = (‖a k‖ * c * c) * ‖G x‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  have hnorm : ∀ k, ∫ x, ‖H k x‖ ∂(volume : Measure (AddCircle L)) ≤ ‖a k‖ * M := fun k => by
    have := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure (AddCircle L))) (f := fun x => ‖H k x‖) (C := ‖a k‖ * c * c * M)
      (Filter.Eventually.of_forall fun x => by rw [norm_norm]; exact hbd k x)
    refine (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ this).trans ?_)
    rw [measureReal_def, torus_mass, ENNReal.toReal_ofReal hL.le]
    have hcc : c * c * L = 1 := by
      have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
      have : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
      rw [hc]; field_simp; linarith
    calc ‖a k‖ * c * c * M * L = ‖a k‖ * M * (c * c * L) := by ring
      _ = ‖a k‖ * M := by rw [hcc, mul_one]
      _ ≤ _ := le_refl _
  have hsum : Summable fun k => ∫ x, ‖H k x‖ ∂(volume : Measure (AddCircle L)) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _) hnorm
      (ha.mul_right M)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hI : ∀ k, ∫ x, H k x ∂(volume : Measure (AddCircle L)) =
      c * (a k * coeff L φ (n - k)) := fun k => by
    have e : ∀ x, H k x = a k * (c * (conj (mode L (n - k) x) * G x)) := fun x => by
      simp only [hH]
      calc conj (mode L n x) * (a k * mode L k x) * G x
          = a k * ((conj (mode L n x) * mode L k x) * G x) := by ring
        _ = _ := by rw [conj_mode_mul_mode]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_const_mul]
    have : ∫ x, conj (mode L (n - k) x) * G x ∂(volume : Measure (AddCircle L)) =
        coeff L φ (n - k) := rfl
    rw [this]; ring
  have hlim : ∫ x, (∑' k, H k x) ∂(volume : Measure (AddCircle L)) =
      coeff L (fun x => seriesRep L a x * φ x) n := by
    unfold coeff
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hH]
    unfold seriesRep
    rw [show (fun k => conj (mode L n x) * (a k * mode L k x) * G x) =
        fun k => (conj (mode L n x) * G x) * (a k * mode L k x) from funext fun k => by ring,
      tsum_mul_left]
    ring
  simp_rw [hI] at h
  rw [hlim] at h
  exact h

/-- **Fourier product formula** (F04 proof: `\widehat{fg} = L^{-1/2}(\widehat f * \widehat g)`),
for the continuous sums of two absolutely summable series: the convolution series converges to
the `n`-th orthonormal coefficient of the pointwise product. -/
theorem hasSum_coeff_mul_seriesRep {a b : ℤ → ℂ} (ha : Summable fun n => ‖a n‖)
    (hb : Summable fun n => ‖b n‖) (n : ℤ) :
    HasSum (fun k : ℤ => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (a k * b (n - k)))
      (coeff L (fun x => seriesRep L a x * seriesRep L b x) n) := by
  have := hasSum_coeff_mul_continuous (L := L) ha (continuous_seriesRep hb) n
  simp only [coeff_seriesRep (L := L) hb] at this
  exact this

theorem coeff_mul_seriesRep {a b : ℤ → ℂ} (ha : Summable fun n => ‖a n‖)
    (hb : Summable fun n => ‖b n‖) (n : ℤ) :
    coeff L (fun x => seriesRep L a x * seriesRep L b x) n =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∑' k : ℤ, a k * b (n - k) := by
  rw [← (hasSum_coeff_mul_seriesRep ha hb n).tsum_eq, tsum_mul_left]

end Product

/-! ## R-00E786F0 remainder, step 3: `eq:algebra`, `‖fg‖_{H¹} ≤ 2 c_L ‖f‖_{H¹} ‖g‖_{H¹}` -/

section Algebra

/-- `ℓ²` Minkowski for nonnegative square-summable families (proved from Cauchy–Schwarz). -/
theorem sqrt_tsum_add_le {ι : Type*} {f g : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i)
    (hf : Summable fun i => f i ^ 2) (hg : Summable fun i => g i ^ 2) :
    Summable (fun i => (f i + g i) ^ 2) ∧
      Real.sqrt (∑' i, (f i + g i) ^ 2) ≤
        Real.sqrt (∑' i, f i ^ 2) + Real.sqrt (∑' i, g i ^ 2) := by
  obtain ⟨hfg, hcs⟩ := tsum_mul_sq_le hf0 hg0 hf hg
  have hexp : (fun i => (f i + g i) ^ 2) = fun i => f i ^ 2 + 2 * (f i * g i) + g i ^ 2 :=
    funext fun i => by ring
  have hsum : Summable (fun i => (f i + g i) ^ 2) := by
    rw [hexp]; exact (hf.add (hfg.mul_left 2)).add hg
  refine ⟨hsum, ?_⟩
  have hF : 0 ≤ ∑' i, f i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hG : 0 ≤ ∑' i, g i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hX : ∑' i, f i * g i ≤ Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) := by
    rw [← Real.sqrt_mul hF]; exact Real.le_sqrt_of_sq_le hcs
  have e : ∑' i, (f i + g i) ^ 2 =
      ∑' i, f i ^ 2 + 2 * ∑' i, f i * g i + ∑' i, g i ^ 2 := by
    rw [hexp, (hf.add (hfg.mul_left 2)).tsum_add hg, hf.tsum_add (hfg.mul_left 2), tsum_mul_left]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [e]
  have h1 := Real.sq_sqrt hF
  have h2 := Real.sq_sqrt hG
  nlinarith [Real.sqrt_nonneg (∑' i, f i ^ 2), Real.sqrt_nonneg (∑' i, g i ^ 2)]

/-- Commutativity of the (real) convolution series on `ℤ`. -/
theorem conv_comm_tsum (f g : ℤ → ℝ) (n : ℤ) :
    ∑' k, f k * g (n - k) = ∑' j, g j * f (n - j) := by
  have := (Equiv.subLeft n).tsum_eq (fun j => g j * f (n - j))
  rw [← this]
  exact tsum_congr fun k => by simp [Equiv.subLeft_apply, mul_comm]

theorem summable_conv_comm (f g : ℤ → ℝ) (n : ℤ) :
    (Summable fun k => f k * g (n - k)) ↔ Summable fun j => g j * f (n - j) := by
  have := (Equiv.subLeft n).summable_iff (f := fun j => g j * f (n - j))
  rw [← this]
  exact summable_congr fun k => by simp [Equiv.subLeft_apply, mul_comm]

theorem f04Weight_half_sq (L : ℝ) (n : ℤ) : f04Weight L (1 / 2) n ^ 2 = f04Weight L 1 n := by
  rw [f04Weight_half, f04Weight_one, Real.sq_sqrt (by positivity)]

theorem one_le_f04Weight_one (L : ℝ) (n : ℤ) : 1 ≤ f04Weight L 1 n := by
  rw [f04Weight_one]; nlinarith [sq_nonneg (freq L n)]

/-- **R-00E786F0, `eq:algebra` (sequence/coefficient form).**  For `L > 0` and coefficient
sequences `a, b` of finite F04 `H¹` norm, the pointwise product of the continuous sums
`f = Σ a_n e_n`, `g = Σ b_n e_n` has orthonormal coefficients `ĥ` of finite F04 `H¹` norm with
`‖fg‖_{H¹} ≤ 2 c_L ‖f‖_{H¹} ‖g‖_{H¹}`. -/
theorem f04_algebra {L : ℝ} [Fact (0 < L)] {a b : ℤ → ℂ} (ha : Mem04 L 1 a) (hb : Mem04 L 1 b) :
    Mem04 L 1 (coeff L (fun x => seriesRep L a x * seriesRep L b x)) ∧
    Real.sqrt (f04NormSq L 1 (coeff L (fun x => seriesRep L a x * seriesRep L b x))) ≤
      2 * cL L * Real.sqrt (f04NormSq L 1 a) * Real.sqrt (f04NormSq L 1 b) := by
  have hL : 0 < L := Fact.out
  obtain ⟨haS, haL⟩ := tsum_norm_le_cL hL ha
  obtain ⟨hbS, hbL⟩ := tsum_norm_le_cL hL hb
  set w : ℤ → ℝ := fun n => f04Weight L (1 / 2) n with hw
  have hw0 : ∀ n, 0 < w n := fun n => by simp only [hw, f04Weight_half]; positivity
  set c0 : ℝ := (Real.sqrt L)⁻¹ with hc0
  have hc00 : 0 ≤ c0 := inv_nonneg.2 (Real.sqrt_nonneg _)
  set α : ℤ → ℝ := fun k => ‖a k‖ with hα
  set β : ℤ → ℝ := fun k => ‖b k‖ with hβ
  set α' : ℤ → ℝ := fun k => w k * ‖a k‖ with hα'
  set β' : ℤ → ℝ := fun k => w k * ‖b k‖ with hβ'
  have hα0 : ∀ k, 0 ≤ α k := fun k => norm_nonneg _
  have hβ0 : ∀ k, 0 ≤ β k := fun k => norm_nonneg _
  have hα'0 : ∀ k, 0 ≤ α' k := fun k => mul_nonneg (hw0 k).le (norm_nonneg _)
  have hβ'0 : ∀ k, 0 ≤ β' k := fun k => mul_nonneg (hw0 k).le (norm_nonneg _)
  have hsq : ∀ (x : ℤ → ℂ) k, (w k * ‖x k‖) ^ 2 = f04Weight L 1 k * ‖x k‖ ^ 2 := fun x k => by
    rw [mul_pow, hw]; simp only [f04Weight_half_sq]
  have hα'2 : Summable fun k => α' k ^ 2 := by simp only [hα', hsq]; exact ha
  have hβ'2 : Summable fun k => β' k ^ 2 := by simp only [hβ', hsq]; exact hb
  have hα2 : Summable fun k => α k ^ 2 := Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (fun k => by
      have := hsq a k
      simp only [hα]
      nlinarith [one_le_f04Weight_one L k, sq_nonneg ‖a k‖, this]) hα'2
  have hβ2 : Summable fun k => β k ^ 2 := Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (fun k => by
      have := hsq b k
      simp only [hβ]
      nlinarith [one_le_f04Weight_one L k, sq_nonneg ‖b k‖, this]) hβ'2
  have e_a : ∑' k, α' k ^ 2 = f04NormSq L 1 a := by simp only [hα', hsq]; rfl
  have e_b : ∑' k, β' k ^ 2 = f04NormSq L 1 b := by simp only [hβ', hsq]; rfl
  -- two Young estimates (ℓ¹ factor first)
  obtain ⟨Y1s, Y1sq, Y1b⟩ := young_l1_l2 hβ0 hα'0 hbS hα'2   -- Σ_j β j α' (n-j)
  obtain ⟨Y2s, Y2sq, Y2b⟩ := young_l1_l2 hα0 hβ'0 haS hβ'2   -- Σ_k α k β' (n-k)
  set D1 : ℤ → ℝ := fun n => ∑' j, β j * α' (n - j) with hD1
  set D2 : ℤ → ℝ := fun n => ∑' k, α k * β' (n - k) with hD2
  have hD10 : ∀ n, 0 ≤ D1 n := fun n => tsum_nonneg fun j => mul_nonneg (hβ0 _) (hα'0 _)
  have hD20 : ∀ n, 0 ≤ D2 n := fun n => tsum_nonneg fun j => mul_nonneg (hα0 _) (hβ'0 _)
  obtain ⟨Msum, Mle⟩ := sqrt_tsum_add_le hD10 hD20 Y1sq Y2sq
  -- coefficient identity and pointwise bound
  set P : ℤ → ℂ := coeff L (fun x => seriesRep L a x * seriesRep L b x) with hP
  have hPeq : ∀ n, P n = (c0 : ℂ) * ∑' k, a k * b (n - k) := fun n => by
    simp only [hP, hc0]; exact coeff_mul_seriesRep haS hbS n
  have hpt : ∀ n, w n * ‖P n‖ ≤ c0 * (D1 n + D2 n) := fun n => by
    have hSa : Summable fun k => α k * β (n - k) := by
      have := (young_l1_l2 hα0 hβ0 haS hβ2).1 n; exact this
    have h1 : ‖∑' k, a k * b (n - k)‖ ≤ ∑' k, α k * β (n - k) :=
      (norm_tsum_le_tsum_norm (by simpa [norm_mul] using hSa)).trans
        (le_of_eq (tsum_congr fun k => by simp [hα, hβ]))
    have hS1 : Summable fun k => α' k * β (n - k) := (summable_conv_comm _ _ n).2 (Y1s n)
    have hS2 : Summable fun k => α k * β' (n - k) := Y2s n
    have h2 : w n * ∑' k, α k * β (n - k) ≤ D1 n + D2 n := by
      have hD1' : D1 n = ∑' k, α' k * β (n - k) := (conv_comm_tsum α' β n).symm
      rw [← tsum_mul_left, hD1', hD2, ← (hS1.tsum_add hS2)]
      refine Summable.tsum_le_tsum (fun k => ?_) (hSa.mul_left _) (hS1.add hS2)
      have hwk := f04Weight_half_add_le L k (n - k)
      rw [show k + (n - k) = n by ring] at hwk
      have := mul_le_mul_of_nonneg_right hwk (mul_nonneg (hα0 k) (hβ0 (n - k)))
      simp only [hw, hα', hβ']
      nlinarith [this]
    rw [hPeq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc00]
    calc w n * (c0 * ‖∑' k, a k * b (n - k)‖) = c0 * (w n * ‖∑' k, a k * b (n - k)‖) := by ring
      _ ≤ c0 * (w n * ∑' k, α k * β (n - k)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (hw0 n).le) hc00
      _ ≤ c0 * (D1 n + D2 n) := mul_le_mul_of_nonneg_left h2 hc00
  -- ℓ² comparison
  have hsqP : ∀ n, f04Weight L 1 n * ‖P n‖ ^ 2 = (w n * ‖P n‖) ^ 2 := fun n => (hsq P n).symm
  have hdom : ∀ n, (w n * ‖P n‖) ^ 2 ≤ (c0 * (D1 n + D2 n)) ^ 2 := fun n =>
    pow_le_pow_left₀ (mul_nonneg (hw0 n).le (norm_nonneg _)) (hpt n) 2
  have hMs : Summable fun n => (c0 * (D1 n + D2 n)) ^ 2 := by
    simp_rw [mul_pow]; exact Msum.mul_left _
  have hmem : Mem04 L 1 P := by
    unfold Mem04
    simp_rw [hsqP]
    exact Summable.of_nonneg_of_le (fun n => sq_nonneg _) hdom hMs
  refine ⟨hmem, ?_⟩
  have hnorm : f04NormSq L 1 P = ∑' n, (w n * ‖P n‖) ^ 2 := by
    unfold f04NormSq; exact tsum_congr fun n => hsqP n
  have hc : (c0 * 1) = c0 := mul_one _
  have step1 : Real.sqrt (f04NormSq L 1 P) ≤ c0 * Real.sqrt (∑' n, (D1 n + D2 n) ^ 2) := by
    rw [hnorm, ← Real.sqrt_sq hc00, ← Real.sqrt_mul (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    calc ∑' n, (w n * ‖P n‖) ^ 2 ≤ ∑' n, (c0 * (D1 n + D2 n)) ^ 2 :=
          Summable.tsum_le_tsum hdom (by
            have := hmem; unfold Mem04 at this; simp_rw [hsqP] at this; exact this) hMs
      _ = c0 ^ 2 * ∑' n, (D1 n + D2 n) ^ 2 := by simp_rw [mul_pow]; rw [tsum_mul_left]
  have hNa : 0 ≤ Real.sqrt (f04NormSq L 1 a) := Real.sqrt_nonneg _
  have hNb : 0 ≤ Real.sqrt (f04NormSq L 1 b) := Real.sqrt_nonneg _
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hD1n : Real.sqrt (∑' n, D1 n ^ 2) ≤ (∑' k, β k) * Real.sqrt (f04NormSq L 1 a) := by
    rw [← e_a, ← Real.sqrt_sq (tsum_nonneg hβ0), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt Y1b
  have hD2n : Real.sqrt (∑' n, D2 n ^ 2) ≤ (∑' k, α k) * Real.sqrt (f04NormSq L 1 b) := by
    rw [← e_b, ← Real.sqrt_sq (tsum_nonneg hα0), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt Y2b
  have hαL : ∑' k, α k ≤ Real.sqrt L * cL L * Real.sqrt (f04NormSq L 1 a) := haL
  have hβL : ∑' k, β k ≤ Real.sqrt L * cL L * Real.sqrt (f04NormSq L 1 b) := hbL
  calc Real.sqrt (f04NormSq L 1 P) ≤ c0 * Real.sqrt (∑' n, (D1 n + D2 n) ^ 2) := step1
    _ ≤ c0 * (Real.sqrt (∑' n, D1 n ^ 2) + Real.sqrt (∑' n, D2 n ^ 2)) :=
        mul_le_mul_of_nonneg_left Mle hc00
    _ ≤ c0 * ((∑' k, β k) * Real.sqrt (f04NormSq L 1 a) +
          (∑' k, α k) * Real.sqrt (f04NormSq L 1 b)) :=
        mul_le_mul_of_nonneg_left (add_le_add hD1n hD2n) hc00
    _ ≤ c0 * ((Real.sqrt L * cL L * Real.sqrt (f04NormSq L 1 b)) * Real.sqrt (f04NormSq L 1 a) +
          (Real.sqrt L * cL L * Real.sqrt (f04NormSq L 1 a)) * Real.sqrt (f04NormSq L 1 b)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hc00
        · exact mul_le_mul_of_nonneg_right hβL hNa
        · exact mul_le_mul_of_nonneg_right hαL hNb
    _ = 2 * cL L * Real.sqrt (f04NormSq L 1 a) * Real.sqrt (f04NormSq L 1 b) := by
        rw [hc0]; field_simp; ring

end Algebra

/-! ## R-00E786F0 remainder, step 4 helpers for `eq:triple` -/

section TripleHelpers

/-- Young `ℓ¹ * ℓ¹ ⊆ ℓ¹` on `ℤ` (nonnegative sequences). -/
theorem young_l1_l1 {α β : ℤ → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα : Summable α) (hβ : Summable β) :
    (∀ n, Summable fun k => α k * β (n - k)) ∧
    Summable (fun n => ∑' k, α k * β (n - k)) ∧
    ∑' n, ∑' k, α k * β (n - k) ≤ (∑' k, α k) * ∑' k, β k := by
  set A := ∑' k, α k with hA
  set B := ∑' k, β k with hB
  have hA0 : 0 ≤ A := tsum_nonneg hα0
  have hβB : ∀ m, β m ≤ B := fun m => hβ.le_tsum m (fun j _ => hβ0 j)
  have S1 : ∀ n, Summable fun k => α k * β (n - k) := fun n =>
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hα0 k) (hβ0 _))
      (fun k => mul_le_mul_of_nonneg_left (hβB _) (hα0 k)) (hα.mul_right _)
  have FIN : ∀ S : Finset ℤ, ∑ n ∈ S, ∑' k, α k * β (n - k) ≤ A * B := fun S => by
    calc ∑ n ∈ S, ∑' k, α k * β (n - k)
        = ∑' k, ∑ n ∈ S, α k * β (n - k) := (Summable.tsum_finsetSum (fun n _ => S1 n)).symm
      _ ≤ ∑' k, α k * B := by
          refine Summable.tsum_le_tsum (fun k => ?_) (summable_sum fun n _ => S1 n) (hα.mul_right B)
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (hα0 k)
          calc ∑ n ∈ S, β (n - k) = ∑ m ∈ S.map (Equiv.subRight k).toEmbedding, β m := by
                rw [Finset.sum_map]; rfl
            _ ≤ B := hβ.sum_le_tsum _ (fun j _ => hβ0 j)
      _ = A * B := by rw [tsum_mul_right]
  have hd0 : ∀ n, 0 ≤ ∑' k, α k * β (n - k) := fun n =>
    tsum_nonneg fun k => mul_nonneg (hα0 k) (hβ0 _)
  have hsum : Summable fun n => ∑' k, α k * β (n - k) := summable_of_sum_le hd0 FIN
  exact ⟨S1, hsum, hsum.tsum_le_of_sum_le FIN⟩

/-- Convexity: `(x+y+z)^s ≤ 3^{s-1}(x^s+y^s+z^s)` for `s ≥ 1`, `x,y,z ≥ 0`. -/
theorem add_add_rpow_le {x y z s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hs : 1 ≤ s) :
    (x + y + z) ^ s ≤ (3 : ℝ) ^ (s - 1) * (x ^ s + y ^ s + z ^ s) := by
  have h := Real.rpow_arith_mean_le_arith_mean_rpow (Finset.univ : Finset (Fin 3))
    (fun _ => (1 / 3 : ℝ)) ![x, y, z] (fun _ _ => by norm_num) (by simp)
    (fun i _ => by fin_cases i <;> simpa) hs
  have h' : (1 / 3 * x + 1 / 3 * y + 1 / 3 * z) ^ s ≤ 1 / 3 * x ^ s + 1 / 3 * y ^ s + 1 / 3 * z ^ s := by
    simpa [Fin.sum_univ_three] using h
  have e1 : (1 / 3 * x + 1 / 3 * y + 1 / 3 * z) = (x + y + z) / 3 := by ring
  rw [e1, Real.div_rpow (by positivity) (by norm_num)] at h'
  have h3 : (0 : ℝ) < (3 : ℝ) ^ s := by positivity
  have h3' : (3 : ℝ) ^ s = 3 ^ (s - 1) * 3 := by
    rw [← Real.rpow_add_one (by norm_num)]; ring_nf
  rw [div_le_iff₀ h3, h3'] at h'
  nlinarith [h']

/-- F04 weight of order `s/2` is `(√(1+p²))^s`. -/
theorem f04Weight_half_mul (L s : ℝ) (n : ℤ) :
    f04Weight L (s / 2) n = f04Weight L (1 / 2) n ^ s := by
  unfold f04Weight
  rw [← Real.rpow_mul (by positivity)]
  congr 1; ring

/-- **Weight splitting with the exact constant `3^{s-1}`** (F04 proof, convexity step):
`(1+p_{k+j+l}²)^{s/2} ≤ 3^{s-1} ((1+p_k²)^{s/2} + (1+p_j²)^{s/2} + (1+p_l²)^{s/2})`, `s ≥ 1`. -/
theorem f04Weight_triple_le (L s : ℝ) (hs : 1 ≤ s) (k j l : ℤ) :
    f04Weight L (s / 2) (k + j + l) ≤
      (3 : ℝ) ^ (s - 1) * (f04Weight L (s / 2) k + f04Weight L (s / 2) j + f04Weight L (s / 2) l) := by
  rw [f04Weight_half_mul L s (k + j + l), f04Weight_half_mul L s k, f04Weight_half_mul L s j,
    f04Weight_half_mul L s l]
  have h0 : ∀ n, 0 ≤ f04Weight L (1 / 2) n := fun n => by
    rw [f04Weight_half]; exact Real.sqrt_nonneg _
  calc f04Weight L (1 / 2) (k + j + l) ^ s
      ≤ (f04Weight L (1 / 2) k + f04Weight L (1 / 2) j + f04Weight L (1 / 2) l) ^ s :=
        Real.rpow_le_rpow (h0 _) (f04Weight_half_add_add_le L k j l) (by linarith)
    _ ≤ _ := add_add_rpow_le (h0 k) (h0 j) (h0 l) hs

/-- Order monotonicity of the F04 weight in `s` (base `≥ 1`). -/
theorem f04Weight_mono (L : ℝ) {s t : ℝ} (hst : s ≤ t) (n : ℤ) :
    f04Weight L s n ≤ f04Weight L t n :=
  Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (freq L n)]) hst

theorem mem04_mono {L s t : ℝ} (hst : s ≤ t) {x : ℤ → ℂ} (hx : Mem04 L t x) : Mem04 L s x :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (f04Weight_pos L s n).le (by positivity))
    (fun n => mul_le_mul_of_nonneg_right (f04Weight_mono L hst n) (by positivity)) hx

theorem f04NormSq_mono {L s t : ℝ} (hst : s ≤ t) {x : ℤ → ℂ} (hx : Mem04 L t x) :
    f04NormSq L s x ≤ f04NormSq L t x :=
  (mem04_mono hst hx).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (f04Weight_mono L hst n) (by positivity)) hx

end TripleHelpers

/-! ## R-00E786F0 remainder, step 5: `eq:triple` -/

section Triple

/-- Young with the `ℓ²` factor on the left: `‖f*g‖₂ ≤ ‖g‖₁‖f‖₂`. -/
theorem young_l2_l1 {f g : ℤ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
    (hf : Summable fun k => f k ^ 2) (hg : Summable g) :
    (∀ n, Summable fun k => f k * g (n - k)) ∧
    Summable (fun n => (∑' k, f k * g (n - k)) ^ 2) ∧
    ∑' n, (∑' k, f k * g (n - k)) ^ 2 ≤ (∑' k, g k) ^ 2 * ∑' k, f k ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := young_l1_l2 hg0 hf0 hg hf
  have e : ∀ n, ∑' k, f k * g (n - k) = ∑' k, g k * f (n - k) := conv_comm_tsum f g
  refine ⟨fun n => (summable_conv_comm f g n).2 (h1 n), ?_, ?_⟩
  · simp_rw [e]; exact h2
  · simp_rw [e]; exact h3

theorem f04Weight_half_sq' (L s : ℝ) (n : ℤ) : f04Weight L (s / 2) n ^ 2 = f04Weight L s n := by
  unfold f04Weight
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

/-- `|\widehat{fg}(m)| ≤ L^{-1/2} Σ_j |\hat f(j)||\hat g(m-j)|`. -/
theorem norm_coeff_mul_le {L : ℝ} [Fact (0 < L)] {a b : ℤ → ℂ} (ha : Summable fun n => ‖a n‖)
    (hb : Summable fun n => ‖b n‖) (m : ℤ) :
    ‖coeff L (fun x => seriesRep L a x * seriesRep L b x) m‖ ≤
      (Real.sqrt L)⁻¹ * ∑' j, ‖a j‖ * ‖b (m - j)‖ := by
  have hS := (young_l1_l1 (fun k => norm_nonneg (a k)) (fun k => norm_nonneg (b k)) ha hb).1 m
  rw [coeff_mul_seriesRep ha hb, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
  exact (norm_tsum_le_tsum_norm (by simpa [norm_mul] using hS)).trans
    (le_of_eq (tsum_congr fun k => by simp))

end Triple

section Triple2

/-- `√(Σ f²) ≤ A √B` from `Σ f² ≤ A² B` (`A ≥ 0`). -/
theorem sqrt_tsum_sq_le {ι : Type*} {f : ι → ℝ} {A B : ℝ} (hA : 0 ≤ A)
    (h : ∑' i, f i ^ 2 ≤ A ^ 2 * B) : Real.sqrt (∑' i, f i ^ 2) ≤ A * Real.sqrt B := by
  calc Real.sqrt (∑' i, f i ^ 2) ≤ Real.sqrt (A ^ 2 * B) := Real.sqrt_le_sqrt h
    _ = A * Real.sqrt B := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA]

/-- **R-00E786F0, `eq:triple` (sequence/coefficient form).**  For `s ≥ 1` and coefficient sequences
`a,b,c` with finite F04 `H^s` norm, the pointwise triple product of the continuous sums has
`H^s` coefficients and
`‖fgh‖_{H^s} ≤ 3^{s-1} c_L² (‖f‖_{H^s}‖g‖_{H¹}‖h‖_{H¹} + ‖f‖_{H¹}‖g‖_{H^s}‖h‖_{H¹}
+ ‖f‖_{H¹}‖g‖_{H¹}‖h‖_{H^s})`, with `‖·‖²_{H^s} = Σ(1+p_n²)^s|·|²` (F04 bracket norm). -/
theorem f04_triple {L : ℝ} [Fact (0 < L)] {s : ℝ} (hs : 1 ≤ s) {a b c : ℤ → ℂ}
    (ha : Mem04 L s a) (hb : Mem04 L s b) (hc : Mem04 L s c) :
    Mem04 L s (coeff L (fun x => seriesRep L a x * seriesRep L b x * seriesRep L c x)) ∧
    Real.sqrt (f04NormSq L s
        (coeff L (fun x => seriesRep L a x * seriesRep L b x * seriesRep L c x))) ≤
      (3 : ℝ) ^ (s - 1) * cL L ^ 2 *
        (Real.sqrt (f04NormSq L s a) * Real.sqrt (f04NormSq L 1 b) * Real.sqrt (f04NormSq L 1 c) +
         Real.sqrt (f04NormSq L 1 a) * Real.sqrt (f04NormSq L s b) * Real.sqrt (f04NormSq L 1 c) +
         Real.sqrt (f04NormSq L 1 a) * Real.sqrt (f04NormSq L 1 b) * Real.sqrt (f04NormSq L s c)) := by
  have hL : 0 < L := Fact.out
  have ha1 : Mem04 L 1 a := mem04_mono hs ha
  have hb1 : Mem04 L 1 b := mem04_mono hs hb
  have hc1 : Mem04 L 1 c := mem04_mono hs hc
  obtain ⟨haS, haL⟩ := tsum_norm_le_cL hL ha1
  obtain ⟨hbS, hbL⟩ := tsum_norm_le_cL hL hb1
  obtain ⟨hcS, hcL⟩ := tsum_norm_le_cL hL hc1
  set W : ℤ → ℝ := fun n => f04Weight L (s / 2) n with hW
  have hW0 : ∀ n, 0 < W n := fun n => f04Weight_pos L _ n
  set c0 : ℝ := (Real.sqrt L)⁻¹ with hc0
  have hc00 : 0 ≤ c0 := inv_nonneg.2 (Real.sqrt_nonneg _)
  set K : ℝ := (3 : ℝ) ^ (s - 1) with hK
  have hK0 : 0 < K := by positivity
  set α : ℤ → ℝ := fun k => ‖a k‖ with hα
  set β : ℤ → ℝ := fun k => ‖b k‖ with hβ
  set γ : ℤ → ℝ := fun k => ‖c k‖ with hγ
  set αW : ℤ → ℝ := fun k => W k * ‖a k‖ with hαW
  set βW : ℤ → ℝ := fun k => W k * ‖b k‖ with hβW
  set γW : ℤ → ℝ := fun k => W k * ‖c k‖ with hγW
  have hα0 : ∀ k, 0 ≤ α k := fun k => norm_nonneg _
  have hβ0 : ∀ k, 0 ≤ β k := fun k => norm_nonneg _
  have hγ0 : ∀ k, 0 ≤ γ k := fun k => norm_nonneg _
  have hαW0 : ∀ k, 0 ≤ αW k := fun k => mul_nonneg (hW0 k).le (norm_nonneg _)
  have hβW0 : ∀ k, 0 ≤ βW k := fun k => mul_nonneg (hW0 k).le (norm_nonneg _)
  have hγW0 : ∀ k, 0 ≤ γW k := fun k => mul_nonneg (hW0 k).le (norm_nonneg _)
  have hsq : ∀ (x : ℤ → ℂ) k, (W k * ‖x k‖) ^ 2 = f04Weight L s k * ‖x k‖ ^ 2 := fun x k => by
    rw [mul_pow, hW]; simp only [f04Weight_half_sq']
  have hαW2 : Summable fun k => αW k ^ 2 := by simp only [hαW, hsq]; exact ha
  have hβW2 : Summable fun k => βW k ^ 2 := by simp only [hβW, hsq]; exact hb
  have hγW2 : Summable fun k => γW k ^ 2 := by simp only [hγW, hsq]; exact hc
  have e_a : ∑' k, αW k ^ 2 = f04NormSq L s a := by simp only [hαW, hsq]; rfl
  have e_b : ∑' k, βW k ^ 2 = f04NormSq L s b := by simp only [hβW, hsq]; rfl
  have e_c : ∑' k, γW k ^ 2 = f04NormSq L s c := by simp only [hγW, hsq]; rfl
  -- inner convolutions
  set U : ℤ → ℝ := fun m => ∑' j, β j * γ (m - j) with hU
  set UB : ℤ → ℝ := fun m => ∑' j, βW j * γ (m - j) with hUB
  set UC : ℤ → ℝ := fun m => ∑' j, β j * γW (m - j) with hUC
  obtain ⟨YU_s, YU_sum, YU_b⟩ := young_l1_l1 hβ0 hγ0 hbS hcS
  obtain ⟨YB_s, YB_sq, YB_b⟩ := young_l2_l1 hβW0 hγ0 hβW2 hcS
  obtain ⟨YC_s, YC_sq, YC_b⟩ := young_l1_l2 hβ0 hγW0 hbS hγW2
  have hU0 : ∀ m, 0 ≤ U m := fun m => tsum_nonneg fun j => mul_nonneg (hβ0 _) (hγ0 _)
  have hUB0 : ∀ m, 0 ≤ UB m := fun m => tsum_nonneg fun j => mul_nonneg (hβW0 _) (hγ0 _)
  have hUC0 : ∀ m, 0 ≤ UC m := fun m => tsum_nonneg fun j => mul_nonneg (hβ0 _) (hγW0 _)
  -- outer convolutions
  set E1 : ℤ → ℝ := fun n => ∑' k, αW k * U (n - k) with hE1
  set E2 : ℤ → ℝ := fun n => ∑' k, α k * UB (n - k) with hE2
  set E3 : ℤ → ℝ := fun n => ∑' k, α k * UC (n - k) with hE3
  obtain ⟨Y1_s, Y1_sq, Y1_b⟩ := young_l2_l1 hαW0 hU0 hαW2 YU_sum
  obtain ⟨Y2_s, Y2_sq, Y2_b⟩ := young_l1_l2 hα0 hUB0 haS YB_sq
  obtain ⟨Y3_s, Y3_sq, Y3_b⟩ := young_l1_l2 hα0 hUC0 haS YC_sq
  obtain ⟨YaU_s, -, -⟩ := young_l1_l1 hα0 hU0 haS YU_sum
  have hE10 : ∀ n, 0 ≤ E1 n := fun n => tsum_nonneg fun k => mul_nonneg (hαW0 _) (hU0 _)
  have hE20 : ∀ n, 0 ≤ E2 n := fun n => tsum_nonneg fun k => mul_nonneg (hα0 _) (hUB0 _)
  have hE30 : ∀ n, 0 ≤ E3 n := fun n => tsum_nonneg fun k => mul_nonneg (hα0 _) (hUC0 _)
  obtain ⟨M12s, M12⟩ := sqrt_tsum_add_le hE10 hE20 Y1_sq Y2_sq
  have hE120 : ∀ n, 0 ≤ E1 n + E2 n := fun n => add_nonneg (hE10 n) (hE20 n)
  obtain ⟨M123s, M123⟩ := sqrt_tsum_add_le hE120 hE30 M12s Y3_sq
  -- inner weighted bound (weight splitting with the exact constant 3^{s-1})
  have inner : ∀ k m : ℤ, W (k + m) * U m ≤ K * (W k * U m + UB m + UC m) := fun k m => by
    have hs1 : Summable fun j => β j * γ (m - j) := YU_s m
    have hs2 : Summable fun j => βW j * γ (m - j) := YB_s m
    have hs3 : Summable fun j => β j * γW (m - j) := YC_s m
    have hs1' : Summable fun j => W k * (β j * γ (m - j)) := hs1.mul_left _
    have hs12 : Summable fun j => W k * (β j * γ (m - j)) + βW j * γ (m - j) := hs1'.add hs2
    have hs123 : Summable fun j =>
        W k * (β j * γ (m - j)) + βW j * γ (m - j) + β j * γW (m - j) := hs12.add hs3
    calc W (k + m) * U m = ∑' j, W (k + m) * (β j * γ (m - j)) := by
          simp only [hU]; rw [tsum_mul_left]
      _ ≤ ∑' j, K * (W k * (β j * γ (m - j)) + βW j * γ (m - j) + β j * γW (m - j)) := by
          refine Summable.tsum_le_tsum (fun j => ?_) (hs1.mul_left _) (hs123.mul_left K)
          have h := f04Weight_triple_le L s hs k j (m - j)
          rw [show k + j + (m - j) = k + m by ring] at h
          have hp : 0 ≤ β j * γ (m - j) := mul_nonneg (hβ0 _) (hγ0 _)
          calc W (k + m) * (β j * γ (m - j))
              ≤ (K * (W k + W j + W (m - j))) * (β j * γ (m - j)) :=
                mul_le_mul_of_nonneg_right h hp
            _ = _ := by simp only [hβW, hγW]; ring
      _ = K * (W k * U m + UB m + UC m) := by
          rw [tsum_mul_left, hs12.tsum_add hs3, hs1'.tsum_add hs2, tsum_mul_left]
  -- the product's coefficients
  set T : AddCircle L → ℂ := fun x => seriesRep L a x * seriesRep L b x * seriesRep L c x with hT
  set P : ℤ → ℂ := coeff L T with hP
  set φ : AddCircle L → ℂ := fun x => seriesRep L b x * seriesRep L c x with hφ
  have hφc : Continuous φ := (continuous_seriesRep hbS).mul (continuous_seriesRep hcS)
  have hTfun : T = fun x => seriesRep L a x * φ x := funext fun x => mul_assoc _ _ _
  have hφb : ∀ m, ‖coeff L φ m‖ ≤ c0 * U m := fun m => norm_coeff_mul_le hbS hcS m
  have hpt : ∀ n, W n * ‖P n‖ ≤ c0 * c0 * K * (E1 n + E2 n + E3 n) := fun n => by
    have hHS := hasSum_coeff_mul_continuous haS hφc n
    have hterm : ∀ k, ‖(c0 : ℂ) * (a k * coeff L φ (n - k))‖ ≤ c0 * c0 * (α k * U (n - k)) :=
      fun k => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc00, norm_mul]
        calc c0 * (‖a k‖ * ‖coeff L φ (n - k)‖) ≤ c0 * (α k * (c0 * U (n - k))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hφb _) (hα0 k)) hc00
          _ = c0 * c0 * (α k * U (n - k)) := by ring
    have hnS : Summable fun k => ‖(c0 : ℂ) * (a k * coeff L φ (n - k))‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm ((YaU_s n).mul_left (c0 * c0))
    have hPn : P n = ∑' k, (c0 : ℂ) * (a k * coeff L φ (n - k)) := by
      show coeff L T n = _
      rw [hTfun]; exact hHS.tsum_eq.symm
    have h1 : ‖P n‖ ≤ c0 * c0 * ∑' k, α k * U (n - k) := by
      rw [hPn, ← tsum_mul_left]
      exact (norm_tsum_le_tsum_norm hnS).trans
        (Summable.tsum_le_tsum hterm hnS ((YaU_s n).mul_left (c0 * c0)))
    have hS1 : Summable fun k => α k * (W n * U (n - k)) :=
      ((YaU_s n).mul_left (W n)).congr fun k => by ring
    have hS2 : Summable fun k =>
        K * (αW k * U (n - k) + α k * UB (n - k) + α k * UC (n - k)) :=
      (((Y1_s n).add (Y2_s n)).add (Y3_s n)).mul_left K
    calc W n * ‖P n‖ ≤ W n * (c0 * c0 * ∑' k, α k * U (n - k)) :=
          mul_le_mul_of_nonneg_left h1 (hW0 n).le
      _ = c0 * c0 * ∑' k, α k * (W n * U (n - k)) := by
          rw [mul_left_comm, ← tsum_mul_left]
          congr 1; exact tsum_congr fun k => by ring
      _ ≤ c0 * c0 * ∑' k, K * (αW k * U (n - k) + α k * UB (n - k) + α k * UC (n - k)) := by
          refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun k => ?_) hS1 hS2)
            (mul_nonneg hc00 hc00)
          have h := inner k (n - k)
          rw [show k + (n - k) = n by ring] at h
          calc α k * (W n * U (n - k)) ≤ α k * (K * (W k * U (n - k) + UB (n - k) + UC (n - k))) :=
                mul_le_mul_of_nonneg_left h (hα0 k)
            _ = _ := by simp only [hαW]; ring
      _ = c0 * c0 * K * (E1 n + E2 n + E3 n) := by
          rw [tsum_mul_left, ((Y1_s n).add (Y2_s n)).tsum_add (Y3_s n),
            (Y1_s n).tsum_add (Y2_s n)]
          simp only [hE1, hE2, hE3]; ring
  -- ℓ² comparison
  have hsqP : ∀ n, f04Weight L s n * ‖P n‖ ^ 2 = (W n * ‖P n‖) ^ 2 := fun n => by
    rw [mul_pow, hW]; simp only [f04Weight_half_sq']
  have hdom : ∀ n, (W n * ‖P n‖) ^ 2 ≤ (c0 * c0 * K * (E1 n + E2 n + E3 n)) ^ 2 := fun n =>
    pow_le_pow_left₀ (mul_nonneg (hW0 n).le (norm_nonneg _)) (hpt n) 2
  have hMs : Summable fun n => (c0 * c0 * K * (E1 n + E2 n + E3 n)) ^ 2 := by
    simp_rw [mul_pow]; exact M123s.mul_left _
  have hmem : Mem04 L s P := by
    unfold Mem04
    simp_rw [hsqP]
    exact Summable.of_nonneg_of_le (fun n => sq_nonneg _) hdom hMs
  refine ⟨hmem, ?_⟩
  have hnorm : f04NormSq L s P = ∑' n, (W n * ‖P n‖) ^ 2 := by
    unfold f04NormSq; exact tsum_congr fun n => hsqP n
  have hmem' : Summable fun n => (W n * ‖P n‖) ^ 2 := by
    have := hmem; unfold Mem04 at this; simp_rw [hsqP] at this; exact this
  have hcK : 0 ≤ c0 * c0 * K := by positivity
  have hQ : ∑' n, (W n * ‖P n‖) ^ 2 ≤
      (c0 * c0 * K) ^ 2 * ∑' n, (E1 n + E2 n + E3 n) ^ 2 := by
    calc ∑' n, (W n * ‖P n‖) ^ 2 ≤ ∑' n, (c0 * c0 * K * (E1 n + E2 n + E3 n)) ^ 2 :=
          Summable.tsum_le_tsum hdom hmem' hMs
      _ = _ := by simp_rw [mul_pow]; rw [tsum_mul_left]
  have step1 : Real.sqrt (f04NormSq L s P) ≤
      (c0 * c0 * K) * Real.sqrt (∑' n, (E1 n + E2 n + E3 n) ^ 2) := by
    rw [hnorm]; exact sqrt_tsum_sq_le hcK hQ
  have hR : Real.sqrt (∑' n, (E1 n + E2 n + E3 n) ^ 2) ≤
      Real.sqrt (∑' n, E1 n ^ 2) + Real.sqrt (∑' n, E2 n ^ 2) + Real.sqrt (∑' n, E3 n ^ 2) := by
    have := M123
    linarith [M12]
  have hSα : 0 ≤ ∑' k, α k := tsum_nonneg hα0
  have hSβ : 0 ≤ ∑' k, β k := tsum_nonneg hβ0
  have hSγ : 0 ≤ ∑' k, γ k := tsum_nonneg hγ0
  have hSU : 0 ≤ ∑' k, U k := tsum_nonneg hU0
  have hNas : 0 ≤ Real.sqrt (f04NormSq L s a) := Real.sqrt_nonneg _
  have hNbs : 0 ≤ Real.sqrt (f04NormSq L s b) := Real.sqrt_nonneg _
  have hNcs : 0 ≤ Real.sqrt (f04NormSq L s c) := Real.sqrt_nonneg _
  have hNa1 : 0 ≤ Real.sqrt (f04NormSq L 1 a) := Real.sqrt_nonneg _
  have hNb1 : 0 ≤ Real.sqrt (f04NormSq L 1 b) := Real.sqrt_nonneg _
  have hNc1 : 0 ≤ Real.sqrt (f04NormSq L 1 c) := Real.sqrt_nonneg _
  have hRn : 0 ≤ Real.sqrt L * cL L := mul_nonneg (Real.sqrt_nonneg _) (cL_nonneg L)
  have hE1n : Real.sqrt (∑' n, E1 n ^ 2) ≤ (∑' k, U k) * Real.sqrt (f04NormSq L s a) := by
    rw [← e_a]; exact sqrt_tsum_sq_le hSU Y1_b
  have hUBn : Real.sqrt (∑' n, UB n ^ 2) ≤ (∑' k, γ k) * Real.sqrt (f04NormSq L s b) := by
    rw [← e_b]; exact sqrt_tsum_sq_le hSγ YB_b
  have hUCn : Real.sqrt (∑' n, UC n ^ 2) ≤ (∑' k, β k) * Real.sqrt (f04NormSq L s c) := by
    rw [← e_c]; exact sqrt_tsum_sq_le hSβ YC_b
  have hE2n : Real.sqrt (∑' n, E2 n ^ 2) ≤ (∑' k, α k) * Real.sqrt (∑' n, UB n ^ 2) :=
    sqrt_tsum_sq_le hSα Y2_b
  have hE3n : Real.sqrt (∑' n, E3 n ^ 2) ≤ (∑' k, α k) * Real.sqrt (∑' n, UC n ^ 2) :=
    sqrt_tsum_sq_le hSα Y3_b
  have hUs : ∑' k, U k ≤ (∑' k, β k) * ∑' k, γ k := YU_b
  have hαL : ∑' k, α k ≤ Real.sqrt L * cL L * Real.sqrt (f04NormSq L 1 a) := haL
  have hβL : ∑' k, β k ≤ Real.sqrt L * cL L * Real.sqrt (f04NormSq L 1 b) := hbL
  have hγL : ∑' k, γ k ≤ Real.sqrt L * cL L * Real.sqrt (f04NormSq L 1 c) := hcL
  set Rr : ℝ := Real.sqrt L * cL L with hRr
  have t1 : Real.sqrt (∑' n, E1 n ^ 2) ≤ (Rr * Real.sqrt (f04NormSq L 1 b)) *
      (Rr * Real.sqrt (f04NormSq L 1 c)) * Real.sqrt (f04NormSq L s a) := by
    refine hE1n.trans (mul_le_mul_of_nonneg_right (hUs.trans ?_) hNas)
    exact mul_le_mul hβL hγL hSγ (mul_nonneg hRn hNb1)
  have t2 : Real.sqrt (∑' n, E2 n ^ 2) ≤ (Rr * Real.sqrt (f04NormSq L 1 a)) *
      ((Rr * Real.sqrt (f04NormSq L 1 c)) * Real.sqrt (f04NormSq L s b)) := by
    refine hE2n.trans (hUBn.trans' (le_refl _) |> fun _ => ?_)
    calc (∑' k, α k) * Real.sqrt (∑' n, UB n ^ 2)
        ≤ (∑' k, α k) * ((∑' k, γ k) * Real.sqrt (f04NormSq L s b)) :=
          mul_le_mul_of_nonneg_left hUBn hSα
      _ ≤ (Rr * Real.sqrt (f04NormSq L 1 a)) *
          ((Rr * Real.sqrt (f04NormSq L 1 c)) * Real.sqrt (f04NormSq L s b)) :=
          mul_le_mul hαL (mul_le_mul_of_nonneg_right hγL hNbs)
            (mul_nonneg hSγ hNbs) (mul_nonneg hRn hNa1)
  have t3 : Real.sqrt (∑' n, E3 n ^ 2) ≤ (Rr * Real.sqrt (f04NormSq L 1 a)) *
      ((Rr * Real.sqrt (f04NormSq L 1 b)) * Real.sqrt (f04NormSq L s c)) := by
    refine hE3n.trans ?_
    calc (∑' k, α k) * Real.sqrt (∑' n, UC n ^ 2)
        ≤ (∑' k, α k) * ((∑' k, β k) * Real.sqrt (f04NormSq L s c)) :=
          mul_le_mul_of_nonneg_left hUCn hSα
      _ ≤ (Rr * Real.sqrt (f04NormSq L 1 a)) *
          ((Rr * Real.sqrt (f04NormSq L 1 b)) * Real.sqrt (f04NormSq L s c)) :=
          mul_le_mul hαL (mul_le_mul_of_nonneg_right hβL hNcs)
            (mul_nonneg hSβ hNcs) (mul_nonneg hRn hNa1)
  have hc0R : c0 * Rr = cL L := by
    have hs0 : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
    simp only [hc0, hRr]; field_simp
  calc Real.sqrt (f04NormSq L s P)
      ≤ (c0 * c0 * K) * Real.sqrt (∑' n, (E1 n + E2 n + E3 n) ^ 2) := step1
    _ ≤ (c0 * c0 * K) * (Real.sqrt (∑' n, E1 n ^ 2) + Real.sqrt (∑' n, E2 n ^ 2) +
          Real.sqrt (∑' n, E3 n ^ 2)) := mul_le_mul_of_nonneg_left hR hcK
    _ ≤ (c0 * c0 * K) * ((Rr * Real.sqrt (f04NormSq L 1 b)) * (Rr * Real.sqrt (f04NormSq L 1 c)) *
            Real.sqrt (f04NormSq L s a) +
          (Rr * Real.sqrt (f04NormSq L 1 a)) *
            ((Rr * Real.sqrt (f04NormSq L 1 c)) * Real.sqrt (f04NormSq L s b)) +
          (Rr * Real.sqrt (f04NormSq L 1 a)) *
            ((Rr * Real.sqrt (f04NormSq L 1 b)) * Real.sqrt (f04NormSq L s c))) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add t1 t2) t3) hcK
    _ = K * (c0 * Rr) ^ 2 *
          (Real.sqrt (f04NormSq L s a) * Real.sqrt (f04NormSq L 1 b) * Real.sqrt (f04NormSq L 1 c) +
           Real.sqrt (f04NormSq L 1 a) * Real.sqrt (f04NormSq L s b) * Real.sqrt (f04NormSq L 1 c) +
           Real.sqrt (f04NormSq L 1 a) * Real.sqrt (f04NormSq L 1 b) * Real.sqrt (f04NormSq L s c)) := by
        ring
    _ = _ := by rw [hc0R]

end Triple2

/-! ## R-00E786F0 remainder, step 6 (for `eq:tame` / `eq:lipschitz`): conjugation and triangle inequality -/

section ConjTriangle

variable {L : ℝ}

/-- Coefficients of the complex conjugate field: `\widehat{\bar f}(n) = conj(\hat f(-n))`. -/
def cjSeq (a : ℤ → ℂ) : ℤ → ℂ := fun n => conj (a (-n))

theorem norm_cjSeq (a : ℤ → ℂ) (n : ℤ) : ‖cjSeq a n‖ = ‖a (-n)‖ := by
  simp [cjSeq]

theorem cjSeq_cjSeq (a : ℤ → ℂ) : cjSeq (cjSeq a) = a := by
  funext n; simp [cjSeq]

theorem freq_neg (L : ℝ) (n : ℤ) : freq L (-n) = - freq L n := by
  unfold freq; push_cast; ring

theorem f04Weight_neg (L s : ℝ) (n : ℤ) : f04Weight L s (-n) = f04Weight L s n := by
  unfold f04Weight; rw [freq_neg, neg_sq]

theorem summable_norm_cjSeq {a : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) :
    Summable fun n => ‖cjSeq a n‖ := by
  simp_rw [norm_cjSeq]
  exact (Equiv.neg ℤ).summable_iff.2 ha

theorem mem04_cjSeq {s : ℝ} {a : ℤ → ℂ} (ha : Mem04 L s a) : Mem04 L s (cjSeq a) := by
  unfold Mem04 at *
  have := (Equiv.neg ℤ).summable_iff.2 ha
  refine this.congr fun n => ?_
  simp [norm_cjSeq, f04Weight_neg]

theorem f04NormSq_cjSeq (s : ℝ) (a : ℤ → ℂ) : f04NormSq L s (cjSeq a) = f04NormSq L s a := by
  unfold f04NormSq
  rw [← (Equiv.neg ℤ).tsum_eq (fun n => f04Weight L s n * ‖a n‖ ^ 2)]
  refine tsum_congr fun n => ?_
  simp [norm_cjSeq, f04Weight_neg]

theorem conj_mode (n : ℤ) (x : AddCircle L) : conj (mode L n x) = mode L (-n) x := by
  unfold mode
  rw [map_mul, Complex.conj_ofReal, ← fourier_neg]

/-- The series of the conjugate coefficients is the conjugate of the series. -/
theorem seriesRep_cjSeq (a : ℤ → ℂ) (x : AddCircle L) :
    seriesRep L (cjSeq a) x = conj (seriesRep L a x) := by
  unfold seriesRep
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n => conj (a n * mode L n x))]
  refine tsum_congr fun n => ?_
  simp only [cjSeq, Equiv.neg_apply, map_mul, conj_mode, neg_neg]

/-- Weighted triangle inequality: if `‖z_n‖ ≤ ‖x_n‖ + ‖y_n‖` pointwise, then `H^s` norms satisfy
the triangle inequality (any order `s`; F04 bracket norm). -/
theorem f04_le_of_norm_le {s : ℝ} {x y z : ℤ → ℂ} (hx : Mem04 L s x) (hy : Mem04 L s y)
    (hz : ∀ n, ‖z n‖ ≤ ‖x n‖ + ‖y n‖) :
    Mem04 L s z ∧ Real.sqrt (f04NormSq L s z) ≤
      Real.sqrt (f04NormSq L s x) + Real.sqrt (f04NormSq L s y) := by
  set W : ℤ → ℝ := fun n => f04Weight L (s / 2) n with hW
  have hW0 : ∀ n, 0 < W n := fun n => f04Weight_pos L _ n
  have hsq : ∀ (v : ℤ → ℂ) k, (W k * ‖v k‖) ^ 2 = f04Weight L s k * ‖v k‖ ^ 2 := fun v k => by
    rw [mul_pow, hW]; simp only [f04Weight_half_sq']
  have hf0 : ∀ n, 0 ≤ W n * ‖x n‖ := fun n => mul_nonneg (hW0 n).le (norm_nonneg _)
  have hg0 : ∀ n, 0 ≤ W n * ‖y n‖ := fun n => mul_nonneg (hW0 n).le (norm_nonneg _)
  have hf2 : Summable fun n => (W n * ‖x n‖) ^ 2 := by simp only [hsq]; exact hx
  have hg2 : Summable fun n => (W n * ‖y n‖) ^ 2 := by simp only [hsq]; exact hy
  obtain ⟨hms, hm⟩ := sqrt_tsum_add_le hf0 hg0 hf2 hg2
  have hdom : ∀ n, (W n * ‖z n‖) ^ 2 ≤ (W n * ‖x n‖ + W n * ‖y n‖) ^ 2 := fun n =>
    pow_le_pow_left₀ (mul_nonneg (hW0 n).le (norm_nonneg _))
      (by nlinarith [hz n, (hW0 n).le]) 2
  have hzs : Summable fun n => (W n * ‖z n‖) ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hdom hms
  refine ⟨by unfold Mem04; simpa only [hsq] using hzs, ?_⟩
  have e : ∀ v : ℤ → ℂ, f04NormSq L s v = ∑' n, (W n * ‖v n‖) ^ 2 := fun v => by
    unfold f04NormSq; exact tsum_congr fun n => (hsq v n).symm
  rw [e z, e x, e y]
  exact (Real.sqrt_le_sqrt (Summable.tsum_le_tsum hdom hzs hms)).trans hm

end ConjTriangle

/-! ## R-00E786F0 remainder, step 7: `eq:tame` -/

section Tame

variable {L : ℝ} [Fact (0 < L)]

/-- `F(f) = |f|² f` evaluated on the continuous sum `f = Σ a_n e_n`. -/
def nlRep (L : ℝ) [Fact (0 < L)] (a : ℤ → ℂ) (x : AddCircle L) : ℂ :=
  (((‖seriesRep L a x‖ ^ 2 : ℝ)) : ℂ) * seriesRep L a x

theorem nlRep_eq (a : ℤ → ℂ) (x : AddCircle L) :
    nlRep L a x = seriesRep L a x * seriesRep L (cjSeq a) x * seriesRep L a x := by
  unfold nlRep
  rw [seriesRep_cjSeq, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem three_pow_succ_le (s : ℝ) : (3 : ℝ) ^ (s - 1) * 3 ≤ (3 : ℝ) ^ (s + 1) := by
  have h : (3 : ℝ) ^ (s + 1) = (3 : ℝ) ^ (s - 1) * 9 := by
    rw [show s + 1 = (s - 1) + 2 by ring, Real.rpow_add (by norm_num), Real.rpow_two]; norm_num
  rw [h]
  have : (0 : ℝ) < (3 : ℝ) ^ (s - 1) := by positivity
  nlinarith

/-- **R-00E786F0, `eq:tame` (coefficient form):** for `s ≥ 1`, `‖F(u)‖_{H^s} ≤ C_{s,L}‖u‖²_{H¹}‖u‖_{H^s}`
with `C_{s,L} = max{1, 3^{s+1} c_L²}` and `F(u) = |u|²u` on the continuous representative. -/
theorem f04_tame {s : ℝ} (hs : 1 ≤ s) {a : ℤ → ℂ} (ha : Mem04 L s a) :
    Mem04 L s (coeff L (nlRep L a)) ∧
    Real.sqrt (f04NormSq L s (coeff L (nlRep L a))) ≤
      max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) * Real.sqrt (f04NormSq L 1 a) ^ 2 *
        Real.sqrt (f04NormSq L s a) := by
  have hfun : nlRep L a = fun x => seriesRep L a x * seriesRep L (cjSeq a) x * seriesRep L a x :=
    funext (nlRep_eq a)
  have h := f04_triple hs ha (mem04_cjSeq ha) ha
  rw [f04NormSq_cjSeq, f04NormSq_cjSeq] at h
  rw [hfun]
  refine ⟨h.1, h.2.trans ?_⟩
  set N1 := Real.sqrt (f04NormSq L 1 a) with hN1
  set Ns := Real.sqrt (f04NormSq L s a) with hNs
  have hN1 : 0 ≤ N1 := Real.sqrt_nonneg _
  have hNs : 0 ≤ Ns := Real.sqrt_nonneg _
  have hc2 : 0 ≤ cL L ^ 2 := sq_nonneg _
  calc (3 : ℝ) ^ (s - 1) * cL L ^ 2 * (Ns * N1 * N1 + N1 * Ns * N1 + N1 * N1 * Ns)
      = ((3 : ℝ) ^ (s - 1) * 3 * cL L ^ 2) * (N1 ^ 2 * Ns) := by ring
    _ ≤ ((3 : ℝ) ^ (s + 1) * cL L ^ 2) * (N1 ^ 2 * Ns) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (three_pow_succ_le s) hc2)
          (by positivity)
    _ ≤ max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) * (N1 ^ 2 * Ns) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ = _ := by ring

end Tame

/-! ## R-00E786F0 remainder, step 8: `eq:lipschitz` -/

section Lipschitz

variable {L : ℝ} [Fact (0 < L)]

theorem summable_norm_of_mem04 {s : ℝ} (hs : 1 ≤ s) {a : ℤ → ℂ} (ha : Mem04 L s a) :
    Summable fun n => ‖a n‖ :=
  (tsum_norm_le_cL Fact.out (mem04_mono hs ha)).1

theorem coeff_add_cont {f g : AddCircle L → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    coeff L (fun x => f x + g x) n = coeff L f n + coeff L g n :=
  coeff_add L (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) n

omit [Fact (0 < L)] in
theorem seriesRep_sub {a b : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (x : AddCircle L) :
    seriesRep L (fun n => a n - b n) x = seriesRep L a x - seriesRep L b x := by
  have h1 : Summable fun n => a n * mode L n x :=
    Summable.of_norm (by simpa [norm_mul, norm_mode] using ha.mul_right (Real.sqrt L)⁻¹)
  have h2 : Summable fun n => b n * mode L n x :=
    Summable.of_norm (by simpa [norm_mul, norm_mode] using hb.mul_right (Real.sqrt L)⁻¹)
  unfold seriesRep
  simp_rw [sub_mul]
  exact h1.tsum_sub h2

theorem three_pow_succ_eq (s : ℝ) : (3 : ℝ) ^ (s + 1) = (3 : ℝ) ^ (s - 1) * 9 := by
  rw [show s + 1 = (s - 1) + 2 by ring, Real.rpow_add (by norm_num), Real.rpow_two]; norm_num

theorem tri_bound {x x1 y y1 z z1 : ℝ} (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1) (hz1 : 0 ≤ z1)
    (hx : x1 ≤ x) (hy : y1 ≤ y) (hz : z1 ≤ z) :
    x * y1 * z1 + x1 * y * z1 + x1 * y1 * z ≤ 3 * (x * y * z) := by
  have hx0 : 0 ≤ x := hx1.trans hx
  have hy0 : 0 ≤ y := hy1.trans hy
  have hz0 : 0 ≤ z := hz1.trans hz
  have e1 : x * y1 * z1 ≤ x * y * z := by gcongr
  have e2 : x1 * y * z1 ≤ x * y * z := by gcongr
  have e3 : x1 * y1 * z ≤ x * y * z := by gcongr
  linarith

/-- **R-00E786F0, `eq:lipschitz` (coefficient form):** for `s ≥ 1`,
`‖F(u) - F(v)‖_{H^s} ≤ C_{s,L} (‖u‖²_{H^s} + ‖v‖²_{H^s}) ‖u - v‖_{H^s}`,
`C_{s,L} = max{1, 3^{s+1} c_L²}`, `F(u) = |u|²u`, via the exact decomposition
`F(u)-F(v) = (u-v)ū u + v \overline{(u-v)} u + v v̄ (u-v)` and `eq:triple`. -/
theorem f04_lipschitz {s : ℝ} (hs : 1 ≤ s) {a b : ℤ → ℂ} (ha : Mem04 L s a) (hb : Mem04 L s b) :
    Mem04 L s (fun n => coeff L (nlRep L a) n - coeff L (nlRep L b) n) ∧
    Real.sqrt (f04NormSq L s (fun n => coeff L (nlRep L a) n - coeff L (nlRep L b) n)) ≤
      max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) *
        (Real.sqrt (f04NormSq L s a) ^ 2 + Real.sqrt (f04NormSq L s b) ^ 2) *
        Real.sqrt (f04NormSq L s (fun n => a n - b n)) := by
  have hL : 0 < L := Fact.out
  obtain ⟨hw, -⟩ := f04_le_of_norm_le ha hb (fun n => norm_sub_le (a n) (b n))
  have haS := summable_norm_of_mem04 hs ha
  have hbS := summable_norm_of_mem04 hs hb
  have hwS := summable_norm_of_mem04 hs hw
  have hcaS := summable_norm_cjSeq haS
  have hcbS := summable_norm_cjSeq hbS
  have hcwS := summable_norm_cjSeq hwS
  have hca := mem04_cjSeq ha
  have hcb := mem04_cjSeq hb
  have hcw := mem04_cjSeq hw
  -- the three trilinear terms
  set T1 : AddCircle L → ℂ := fun x => seriesRep L (fun n => a n - b n) x *
    seriesRep L (cjSeq a) x * seriesRep L a x with hT1
  set T2 : AddCircle L → ℂ := fun x => seriesRep L b x *
    seriesRep L (cjSeq (fun n => a n - b n)) x * seriesRep L a x with hT2
  set T3 : AddCircle L → ℂ := fun x => seriesRep L b x * seriesRep L (cjSeq b) x *
    seriesRep L (fun n => a n - b n) x with hT3
  have hc1 : Continuous T1 :=
    ((continuous_seriesRep hwS).mul (continuous_seriesRep hcaS)).mul (continuous_seriesRep haS)
  have hc2 : Continuous T2 :=
    ((continuous_seriesRep hbS).mul (continuous_seriesRep hcwS)).mul (continuous_seriesRep haS)
  have hc3 : Continuous T3 :=
    ((continuous_seriesRep hbS).mul (continuous_seriesRep hcbS)).mul (continuous_seriesRep hwS)
  have hcb' : Continuous (nlRep L b) := by
    have : nlRep L b = fun x => seriesRep L b x * seriesRep L (cjSeq b) x * seriesRep L b x :=
      funext (nlRep_eq b)
    rw [this]
    exact ((continuous_seriesRep hbS).mul (continuous_seriesRep hcbS)).mul (continuous_seriesRep hbS)
  have hid : ∀ x, nlRep L a x = nlRep L b x + (T1 x + T2 x + T3 x) := fun x => by
    simp only [hT1, hT2, hT3, nlRep_eq, seriesRep_cjSeq, seriesRep_sub haS hbS, map_sub]
    ring
  have hc12 : Continuous fun x => T1 x + T2 x := hc1.add hc2
  have hc123 : Continuous fun x => (T1 x + T2 x) + T3 x := hc12.add hc3
  have hcoef : ∀ n, coeff L (nlRep L a) n - coeff L (nlRep L b) n =
      coeff L T1 n + coeff L T2 n + coeff L T3 n := fun n => by
    have e : nlRep L a = fun x => nlRep L b x + ((T1 x + T2 x) + T3 x) := funext fun x => hid x
    rw [e, coeff_add_cont hcb' hc123, coeff_add_cont hc12 hc3, coeff_add_cont hc1 hc2]
    ring
  -- eq:triple for each term
  obtain ⟨m1, b1⟩ := f04_triple hs hw hca ha
  obtain ⟨m2, b2⟩ := f04_triple hs hb hcw ha
  obtain ⟨m3, b3⟩ := f04_triple hs hb hcb hw
  rw [f04NormSq_cjSeq, f04NormSq_cjSeq] at b1
  rw [f04NormSq_cjSeq, f04NormSq_cjSeq] at b2
  rw [f04NormSq_cjSeq, f04NormSq_cjSeq] at b3
  -- triangle inequality, twice
  set P1 : ℤ → ℂ := coeff L T1 with hP1
  set P2 : ℤ → ℂ := coeff L T2 with hP2
  set P3 : ℤ → ℂ := coeff L T3 with hP3
  set Q12 : ℤ → ℂ := fun n => P1 n + P2 n with hQ12
  obtain ⟨m12, b12⟩ := f04_le_of_norm_le (x := P1) (y := P2) (z := Q12) m1 m2
    (fun n => norm_add_le (P1 n) (P2 n))
  have hz : ∀ n, ‖coeff L (nlRep L a) n - coeff L (nlRep L b) n‖ ≤ ‖Q12 n‖ + ‖P3 n‖ := fun n => by
    rw [hcoef n]; exact norm_add_le (Q12 n) (P3 n)
  obtain ⟨mz, bz⟩ := f04_le_of_norm_le
    (z := fun n => coeff L (nlRep L a) n - coeff L (nlRep L b) n) m12 m3 hz
  refine ⟨mz, ?_⟩
  -- numerical end-game
  set p := Real.sqrt (f04NormSq L s a) with hp
  set q := Real.sqrt (f04NormSq L s b) with hq
  set r := Real.sqrt (f04NormSq L s (fun n => a n - b n)) with hr
  have hp1 : Real.sqrt (f04NormSq L 1 a) ≤ p := Real.sqrt_le_sqrt (f04NormSq_mono hs ha)
  have hq1 : Real.sqrt (f04NormSq L 1 b) ≤ q := Real.sqrt_le_sqrt (f04NormSq_mono hs hb)
  have hr1 : Real.sqrt (f04NormSq L 1 (fun n => a n - b n)) ≤ r :=
    Real.sqrt_le_sqrt (f04NormSq_mono hs hw)
  have n0 : ∀ t : ℝ, 0 ≤ Real.sqrt t := fun t => Real.sqrt_nonneg t
  have hk : 0 ≤ (3 : ℝ) ^ (s - 1) * cL L ^ 2 := by positivity
  have B1 := b1.trans (mul_le_mul_of_nonneg_left
    (tri_bound (n0 _) (n0 _) (n0 _) hr1 hp1 hp1) hk)
  have B2 := b2.trans (mul_le_mul_of_nonneg_left
    (tri_bound (n0 _) (n0 _) (n0 _) hq1 hr1 hp1) hk)
  have B3 := b3.trans (mul_le_mul_of_nonneg_left
    (tri_bound (n0 _) (n0 _) (n0 _) hq1 hq1 hr1) hk)
  have hp0 : 0 ≤ p := n0 _
  have hq0 : 0 ≤ q := n0 _
  have hr0 : 0 ≤ r := n0 _
  have key : 0 ≤ ((3 : ℝ) ^ (s - 1) * cL L ^ 2) * r * (6 * p ^ 2 + 6 * q ^ 2 - 3 * p * q) :=
    mul_nonneg (mul_nonneg hk hr0) (by nlinarith [sq_nonneg (p - q), sq_nonneg p, sq_nonneg q])
  calc Real.sqrt (f04NormSq L s (fun n => coeff L (nlRep L a) n - coeff L (nlRep L b) n))
      ≤ Real.sqrt (f04NormSq L s Q12) + Real.sqrt (f04NormSq L s P3) := bz
    _ ≤ (Real.sqrt (f04NormSq L s P1) + Real.sqrt (f04NormSq L s P2)) +
          Real.sqrt (f04NormSq L s P3) := by linarith [b12]
    _ ≤ ((3 : ℝ) ^ (s - 1) * cL L ^ 2 * (3 * (r * p * p)) +
          (3 : ℝ) ^ (s - 1) * cL L ^ 2 * (3 * (q * r * p))) +
          (3 : ℝ) ^ (s - 1) * cL L ^ 2 * (3 * (q * q * r)) := by linarith [B1, B2, B3]
    _ ≤ ((3 : ℝ) ^ (s + 1) * cL L ^ 2) * ((p ^ 2 + q ^ 2) * r) := by
        rw [three_pow_succ_eq]; nlinarith [key]
    _ ≤ max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) * ((p ^ 2 + q ^ 2) * r) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ = _ := by ring

end Lipschitz

/-! ## R-00E786F0, function-level statements (fields `f,g,h ∈ H^s` with the repaired L² condition) -/

section FunctionLevel

variable {L : ℝ} [Fact (0 < L)]

/-- F04 `H^s(T_L)`: an `L²(T_L)` field (`MemLp`, the repaired condition) whose F04 bracket sum
`Σ (1+p_n²)^s |f̂(n)|²` over orthonormal coefficients is finite. -/
def H04 (L : ℝ) [Fact (0 < L)] (s : ℝ) (f : AddCircle L → ℂ) : Prop :=
  MemLp f 2 (volume : Measure (AddCircle L)) ∧ Mem04 L s (coeff L f)

/-- The F04 norm `‖f‖_{H^s} = (Σ (1+p_n²)^s |f̂(n)|²)^{1/2}`. -/
def h04Norm (L : ℝ) [Fact (0 < L)] (s : ℝ) (f : AddCircle L → ℂ) : ℝ :=
  Real.sqrt (f04NormSq L s (coeff L f))

theorem memLp_of_continuous {f : AddCircle L → ℂ} (hc : Continuous f) :
    MemLp f 2 (volume : Measure (AddCircle L)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (f := f) hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))

/-- An `L²` field with finite F04 `H¹` norm equals (a.e.) the continuous sum of its Fourier series. -/
theorem ae_eq_seriesRep {f : AddCircle L → ℂ} (hf : MemLp f 2 (volume : Measure (AddCircle L)))
    (h1 : Mem04 L 1 (coeff L f)) :
    f =ᵐ[(volume : Measure (AddCircle L))] seriesRep L (coeff L f) := by
  have hL : 0 < L := Fact.out
  have hS := (tsum_norm_le_cL hL h1).1
  have hg := memLp_seriesRep (L := L) hS
  set u := hf.toLp f with hu
  have hco : ∀ n, fourierL2 L u n = coeff L f n := fun n => by
    rw [fourierL2_apply]; exact coeff_congr_ae L hf.coeFn_toLp n
  have heq : hg.toLp (seriesRep L (coeff L f)) = u := by
    apply (fourierL2 L).injective
    ext n
    rw [fourierL2_apply, coeff_congr_ae L hg.coeFn_toLp, coeff_seriesRep hS, hco]
  have h2 := hg.coeFn_toLp
  rw [heq] at h2
  exact hf.coeFn_toLp.symm.trans h2

/-- **R-00E786F0, first display, function level:** `f ∈ H¹` has `Σ|f̂(n)| ≤ √L c_L ‖f‖_{H¹}` and
a continuous representative with `‖f‖_∞ ≤ c_L ‖f‖_{H¹}`. -/
theorem h04_l1_sup {f : AddCircle L → ℂ} (hf : H04 L 1 f) :
    Summable (fun n => ‖coeff L f n‖) ∧
    ∑' n, ‖coeff L f n‖ ≤ Real.sqrt L * cL L * h04Norm L 1 f ∧
    ∃ g : AddCircle L → ℂ, Continuous g ∧ f =ᵐ[(volume : Measure (AddCircle L))] g ∧
      ∀ x, ‖g x‖ ≤ cL L * h04Norm L 1 f := by
  have hL : 0 < L := Fact.out
  obtain ⟨hS, hle⟩ := tsum_norm_le_cL hL hf.2
  refine ⟨hS, hle, seriesRep L (coeff L f), continuous_seriesRep hS,
    ae_eq_seriesRep hf.1 hf.2, fun x => ?_⟩
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  calc ‖seriesRep L (coeff L f) x‖ ≤ (Real.sqrt L)⁻¹ * ∑' n, ‖coeff L f n‖ :=
        norm_seriesRep_le hS x
    _ ≤ (Real.sqrt L)⁻¹ * (Real.sqrt L * cL L * h04Norm L 1 f) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hs.le)
    _ = cL L * h04Norm L 1 f := by field_simp

end FunctionLevel

section FunctionLevel2

variable {L : ℝ} [Fact (0 < L)]

/-- `F(u) = |u|² u` on fields. -/
def nlF (f : AddCircle L → ℂ) (x : AddCircle L) : ℂ := (((‖f x‖ ^ 2 : ℝ)) : ℂ) * f x

theorem coeff_sub_integrable {f g : AddCircle L → ℂ}
    (hf : Integrable f (volume : Measure (AddCircle L)))
    (hg : Integrable g (volume : Measure (AddCircle L))) (n : ℤ) :
    coeff L (fun x => f x - g x) n = coeff L f n - coeff L g n := by
  have h : coeff L (fun x => f x + (-g) x) n = coeff L f n + coeff L (-g) n :=
    coeff_add L hf hg.neg n
  have e2 : coeff L (-g) n = - coeff L g n := by
    have h1 : (-g) = fun x => (-1 : ℂ) * g x := funext fun x => by simp
    rw [h1, coeff_const_mul]; ring
  have e : (fun x => f x - g x) = fun x => f x + (-g) x :=
    funext fun x => by simp [sub_eq_add_neg]
  rw [e, h, e2]; ring

theorem integrable_of_h04 {f : AddCircle L → ℂ} (hf : MemLp f 2 (volume : Measure (AddCircle L))) :
    Integrable f (volume : Measure (AddCircle L)) :=
  hf.integrable (by norm_num)

/-- **`eq:algebra` of R-00E786F0, function level:** `f,g ∈ H¹ ⇒ fg ∈ H¹` and
`‖fg‖_{H¹} ≤ 2 c_L ‖f‖_{H¹} ‖g‖_{H¹}`. -/
theorem h04_mul {f g : AddCircle L → ℂ} (hf : H04 L 1 f) (hg : H04 L 1 g) :
    H04 L 1 (fun x => f x * g x) ∧
      h04Norm L 1 (fun x => f x * g x) ≤ 2 * cL L * h04Norm L 1 f * h04Norm L 1 g := by
  have haf := ae_eq_seriesRep hf.1 hf.2
  have hag := ae_eq_seriesRep hg.1 hg.2
  have hae : (fun x => f x * g x) =ᵐ[(volume : Measure (AddCircle L))]
      fun x => seriesRep L (coeff L f) x * seriesRep L (coeff L g) x := by
    filter_upwards [haf, hag] with x h1 h2; rw [h1, h2]
  obtain ⟨m, b⟩ := f04_algebra hf.2 hg.2
  have hco : coeff L (fun x => f x * g x) =
      coeff L (fun x => seriesRep L (coeff L f) x * seriesRep L (coeff L g) x) :=
    funext (coeff_congr_ae L hae)
  have hcont : Continuous fun x => seriesRep L (coeff L f) x * seriesRep L (coeff L g) x :=
    (continuous_seriesRep (summable_norm_of_mem04 le_rfl hf.2)).mul
      (continuous_seriesRep (summable_norm_of_mem04 le_rfl hg.2))
  refine ⟨⟨(memLp_of_continuous hcont).ae_eq hae.symm, ?_⟩, ?_⟩
  · rw [hco]; exact m
  · unfold h04Norm at *; rw [hco]; exact b

/-- **`eq:triple` of R-00E786F0, function level** (`s ≥ 1`). -/
theorem h04_triple {s : ℝ} (hs : 1 ≤ s) {f g h : AddCircle L → ℂ}
    (hf : H04 L s f) (hg : H04 L s g) (hh : H04 L s h) :
    H04 L s (fun x => f x * g x * h x) ∧
      h04Norm L s (fun x => f x * g x * h x) ≤
        (3 : ℝ) ^ (s - 1) * cL L ^ 2 *
          (h04Norm L s f * h04Norm L 1 g * h04Norm L 1 h +
           h04Norm L 1 f * h04Norm L s g * h04Norm L 1 h +
           h04Norm L 1 f * h04Norm L 1 g * h04Norm L s h) := by
  have haf := ae_eq_seriesRep hf.1 (mem04_mono hs hf.2)
  have hag := ae_eq_seriesRep hg.1 (mem04_mono hs hg.2)
  have hah := ae_eq_seriesRep hh.1 (mem04_mono hs hh.2)
  have hae : (fun x => f x * g x * h x) =ᵐ[(volume : Measure (AddCircle L))]
      fun x => seriesRep L (coeff L f) x * seriesRep L (coeff L g) x *
        seriesRep L (coeff L h) x := by
    filter_upwards [haf, hag, hah] with x h1 h2 h3; rw [h1, h2, h3]
  obtain ⟨m, b⟩ := f04_triple hs hf.2 hg.2 hh.2
  have hco : coeff L (fun x => f x * g x * h x) =
      coeff L (fun x => seriesRep L (coeff L f) x * seriesRep L (coeff L g) x *
        seriesRep L (coeff L h) x) := funext (coeff_congr_ae L hae)
  have hcont : Continuous fun x => seriesRep L (coeff L f) x * seriesRep L (coeff L g) x *
      seriesRep L (coeff L h) x :=
    ((continuous_seriesRep (summable_norm_of_mem04 hs hf.2)).mul
      (continuous_seriesRep (summable_norm_of_mem04 hs hg.2))).mul
      (continuous_seriesRep (summable_norm_of_mem04 hs hh.2))
  refine ⟨⟨(memLp_of_continuous hcont).ae_eq hae.symm, ?_⟩, ?_⟩
  · rw [hco]; exact m
  · unfold h04Norm at *; rw [hco]; exact b

theorem nlF_ae {f : AddCircle L → ℂ} (hf : H04 L 1 f) :
    nlF f =ᵐ[(volume : Measure (AddCircle L))] nlRep L (coeff L f) := by
  filter_upwards [ae_eq_seriesRep hf.1 hf.2] with x hx
  unfold nlF nlRep; rw [hx]

theorem continuous_nlRep {a : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) : Continuous (nlRep L a) := by
  have : nlRep L a = fun x => seriesRep L a x * seriesRep L (cjSeq a) x * seriesRep L a x :=
    funext (nlRep_eq a)
  rw [this]
  exact ((continuous_seriesRep ha).mul (continuous_seriesRep (summable_norm_cjSeq ha))).mul
    (continuous_seriesRep ha)

/-- **`eq:tame` of R-00E786F0, function level:** `‖F(u)‖_{H^s} ≤ C_{s,L} ‖u‖²_{H¹} ‖u‖_{H^s}`,
`C_{s,L} = max{1, 3^{s+1} c_L²}`, for `s ≥ 1`. -/
theorem h04_tame {s : ℝ} (hs : 1 ≤ s) {f : AddCircle L → ℂ} (hf : H04 L s f) :
    H04 L s (nlF f) ∧
      h04Norm L s (nlF f) ≤
        max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) * h04Norm L 1 f ^ 2 * h04Norm L s f := by
  have hf1 : H04 L 1 f := ⟨hf.1, mem04_mono hs hf.2⟩
  have hae := nlF_ae hf1
  obtain ⟨m, b⟩ := f04_tame hs hf.2
  have hco : coeff L (nlF f) = coeff L (nlRep L (coeff L f)) := funext (coeff_congr_ae L hae)
  refine ⟨⟨(memLp_of_continuous (continuous_nlRep (L := L) (summable_norm_of_mem04 hs hf.2))).ae_eq
    hae.symm, ?_⟩, ?_⟩
  · rw [hco]; exact m
  · unfold h04Norm at *; rw [hco]; exact b

/-- **`eq:lipschitz` of R-00E786F0, function level:**
`‖F(u) - F(v)‖_{H^s} ≤ C_{s,L} (‖u‖²_{H^s} + ‖v‖²_{H^s}) ‖u - v‖_{H^s}`, `s ≥ 1`. -/
theorem h04_lipschitz {s : ℝ} (hs : 1 ≤ s) {f g : AddCircle L → ℂ} (hf : H04 L s f)
    (hg : H04 L s g) :
    H04 L s (fun x => nlF f x - nlF g x) ∧
      h04Norm L s (fun x => nlF f x - nlF g x) ≤
        max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) *
          (h04Norm L s f ^ 2 + h04Norm L s g ^ 2) * h04Norm L s (fun x => f x - g x) := by
  have hf1 : H04 L 1 f := ⟨hf.1, mem04_mono hs hf.2⟩
  have hg1 : H04 L 1 g := ⟨hg.1, mem04_mono hs hg.2⟩
  have haeF := nlF_ae hf1
  have haeG := nlF_ae hg1
  have hcF := continuous_nlRep (L := L) (summable_norm_of_mem04 hs hf.2)
  have hcG := continuous_nlRep (L := L) (summable_norm_of_mem04 hs hg.2)
  have hae : (fun x => nlF f x - nlF g x) =ᵐ[(volume : Measure (AddCircle L))]
      fun x => nlRep L (coeff L f) x - nlRep L (coeff L g) x := by
    filter_upwards [haeF, haeG] with x h1 h2; rw [h1, h2]
  have hiF := integrable_of_h04 (memLp_of_continuous hcF)
  have hiG := integrable_of_h04 (memLp_of_continuous hcG)
  have hco : coeff L (fun x => nlF f x - nlF g x) =
      fun n => coeff L (nlRep L (coeff L f)) n - coeff L (nlRep L (coeff L g)) n := by
    funext n
    rw [coeff_congr_ae L hae n]
    exact coeff_sub_integrable hiF hiG n
  have hcw : coeff L (fun x => f x - g x) = fun n => coeff L f n - coeff L g n := by
    funext n
    exact coeff_sub_integrable (integrable_of_h04 hf.1) (integrable_of_h04 hg.1) n
  obtain ⟨m, b⟩ := f04_lipschitz hs hf.2 hg.2
  have hcont : Continuous fun x => nlRep L (coeff L f) x - nlRep L (coeff L g) x := hcF.sub hcG
  refine ⟨⟨(memLp_of_continuous hcont).ae_eq hae.symm, ?_⟩, ?_⟩
  · rw [hco]; exact m
  · unfold h04Norm at *; rw [hco, hcw]; exact b

end FunctionLevel2

/-! ## R-00E786F0 (`F04:lem-products`) packaged statement (candidate for statement freeze) -/

/-- **R-00E786F0 as one statement** (source `chapters/foundations/F04.tex:34`, `eq:l1`,
`eq:algebra`, `eq:triple`, `eq:tame`, `eq:lipschitz`), for an arbitrary `L > 0`, `T_L = ℝ/Lℤ` with
mass-`L` Lebesgue measure, `p_n = 2πn/L`, orthonormal coefficients `f̂(n) = <e_n, f>`,
`‖f‖²_{H^s} = Σ (1+p_n²)^s |f̂(n)|²`, fields in `L²` (`H04`), and `F(u) = |u|²u`.
* `c_L` is finite (summability of `Σ(1+p_n²)⁻¹`);
* `f ∈ H¹` ⇒ `Σ|f̂(n)| ≤ √L c_L ‖f‖_{H¹}` and a continuous representative `g` with `‖g‖_∞ ≤ c_L‖f‖_{H¹}`;
* `‖fg‖_{H¹} ≤ 2 c_L ‖f‖_{H¹}‖g‖_{H¹}`;
* for `s ≥ 1`: `eq:triple`; with `C_{s,L} = max{1, 3^{s+1}c_L²}`: `eq:tame`, `eq:lipschitz`. -/
theorem R00E786F0 (L : ℝ) [Fact (0 < L)] :
    (Summable fun n : ℤ => (1 + freq L n ^ 2)⁻¹) ∧
    (∀ f : AddCircle L → ℂ, H04 L 1 f →
      Summable (fun n => ‖coeff L f n‖) ∧
      ∑' n, ‖coeff L f n‖ ≤ Real.sqrt L * cL L * h04Norm L 1 f ∧
      ∃ g : AddCircle L → ℂ, Continuous g ∧ f =ᵐ[(volume : Measure (AddCircle L))] g ∧
        ∀ x, ‖g x‖ ≤ cL L * h04Norm L 1 f) ∧
    (∀ f g : AddCircle L → ℂ, H04 L 1 f → H04 L 1 g →
      H04 L 1 (fun x => f x * g x) ∧
        h04Norm L 1 (fun x => f x * g x) ≤ 2 * cL L * h04Norm L 1 f * h04Norm L 1 g) ∧
    (∀ s : ℝ, 1 ≤ s → ∀ f g h : AddCircle L → ℂ, H04 L s f → H04 L s g → H04 L s h →
      H04 L s (fun x => f x * g x * h x) ∧
        h04Norm L s (fun x => f x * g x * h x) ≤
          (3 : ℝ) ^ (s - 1) * cL L ^ 2 *
            (h04Norm L s f * h04Norm L 1 g * h04Norm L 1 h +
             h04Norm L 1 f * h04Norm L s g * h04Norm L 1 h +
             h04Norm L 1 f * h04Norm L 1 g * h04Norm L s h)) ∧
    (∀ s : ℝ, 1 ≤ s →
      (∀ u : AddCircle L → ℂ, H04 L s u → H04 L s (nlF u) ∧
        h04Norm L s (nlF u) ≤
          max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) * h04Norm L 1 u ^ 2 * h04Norm L s u) ∧
      (∀ u v : AddCircle L → ℂ, H04 L s u → H04 L s v →
        H04 L s (fun x => nlF u x - nlF v x) ∧
        h04Norm L s (fun x => nlF u x - nlF v x) ≤
          max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) *
            (h04Norm L s u ^ 2 + h04Norm L s v ^ 2) * h04Norm L s (fun x => u x - v x))) :=
  ⟨summable_f04 Fact.out,
   fun _ hf => ⟨(h04_l1_sup hf).1, (h04_l1_sup hf).2.1, (h04_l1_sup hf).2.2⟩,
   fun _ _ hf hg => h04_mul hf hg,
   fun _ hs _ _ _ hf hg hh => h04_triple hs hf hg hh,
   fun _ hs => ⟨fun _ hu => h04_tame hs hu, fun _ _ hu hv => h04_lipschitz hs hu hv⟩⟩

end QuantumNLS.Fourier
