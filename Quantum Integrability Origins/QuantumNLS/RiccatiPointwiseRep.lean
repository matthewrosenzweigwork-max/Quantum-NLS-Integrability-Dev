import Mathlib
import QuantumNLS.RiccatiPointwise
import QuantumNLS.RiccatiPointwiseCoef
import QuantumNLS.ComplexifiedSobolevField

/-!
# R-3FEAD88B step C3, stage RiccatiPointwiseRep: continuous representatives and the pointwise ODE

Proved here (all for `a > 1/2`, `L > 0`, `Im z > 0`, a fixed point `r` of `riccatiT`):

* `series_mul_convC`: the Cauchy product identity `series(convC f g) = series f · series g` for
  `ℓ¹` coefficient sequences (sum over `ℤ × ℤ`, shear `(j,m) ↦ (j,j+m)`);
* `series_sub_const_mul`, `series_rhsD`: linearity of `series` and
  `series(rhsD) = series(toField u) - κ · series(toField v) · series(toField r)²`;
* `seriesRep_coe`: the Mathlib representative `Fourier.seriesRep` evaluated on the lift `y ∈ ℝ`
  equals `(√L)⁻¹ · series L c y` (the two normalisations differ by the factor `(√L)⁻¹`);
* `rep_of_coeff`: for an `L²` element `f` with `ℓ¹` Fourier coefficients `c`, a continuous
  representative `g = seriesRep c`, with `g(y) = (√L)⁻¹ series c y` and sup bound
  `‖g‖∞ ≤ (√L)⁻¹ Σ|c_k|` (Rb);
* `fieldMap_rep`: the same for `fieldMap L a r` (Fourier coefficients `toField r`);
* `riccati_series_ode`: `d/dy series(toField r) = i z series(toField r) + series(toField u)
  - κ series(toField v) series(toField r)²` for every `y ∈ ℝ`;
* `physical_rep_ode`: the same for the physical representative `(√L)⁻¹ series`, with the
  physical coupling `κ_phys = κ · L` (so `κ_model = κ_phys / L`).

Standard axioms only; no sorry, admit, native_decide.
-/

set_option autoImplicit false

noncomputable section

namespace QuantumNLS.RiccatiPointwiseRep

open Complex MeasureTheory QuantumNLS.RiccatiPointwise QuantumNLS.RiccatiSobolevBanach
  QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiPointwiseCoef QuantumNLS.RiccatiPicardBall

/-- Exponentials add: `e_{j+m}(y) = e_j(y) e_m(y)`. -/
theorem ex_add (L : ℝ) (j m : ℤ) (y : ℝ) :
    ex L (j + m) y = ex L j y * ex L m y := by
  unfold ex
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The shear `(j, m) ↦ (j, j + m)` of `ℤ × ℤ`. -/
def shearEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1, p.1 + p.2)
  invFun q := (q.1, q.2 - q.1)
  left_inv p := by simp
  right_inv q := by simp

/-- Norm-summability of the modulated family `f_k e_k(y)`, from the norm-summability of `f`. -/
theorem norm_fam_summable (L : ℝ) (y : ℝ) {f : ℤ → ℂ} (hf : Summable (fun k => ‖f k‖)) :
    Summable (fun k => ‖f k * ex L k y‖) := by
  refine hf.congr (fun k => ?_)
  show ‖f k‖ = ‖f k * ex L k y‖
  rw [norm_mul, norm_ex, mul_one]

/-- Product of two modulated series, as a sum over `ℤ × ℤ`. -/
theorem tsum_prod_factor (L : ℝ) (y : ℝ) {f g : ℤ → ℂ} (hf : Summable (fun k => ‖f k‖))
    (hg : Summable (fun k => ‖g k‖)) :
    (∑' k : ℤ, f k * ex L k y) * (∑' k : ℤ, g k * ex L k y)
      = ∑' p : ℤ × ℤ, (f p.1 * ex L p.1 y) * (g p.2 * ex L p.2 y) :=
  tsum_mul_tsum_of_summable_norm (norm_fam_summable L y hf) (norm_fam_summable L y hg)

/-- The shear identity: the convolution term composed with the shear is the product term. -/
theorem shear_comp (L : ℝ) (y : ℝ) {f g : ℤ → ℂ} :
    (fun p : ℤ × ℤ => f p.1 * g (p.2 - p.1) * ex L p.2 y) ∘ shearEquiv
      = fun p : ℤ × ℤ => (f p.1 * ex L p.1 y) * (g p.2 * ex L p.2 y) := by
  funext p
  simp only [Function.comp, shearEquiv, Equiv.coe_fn_mk, add_sub_cancel_left]
  rw [ex_add]
  ring

/-- Summability of the convolution-indexed family over `ℤ × ℤ`. -/
theorem summable_shear (L : ℝ) (y : ℝ) {f g : ℤ → ℂ} (hf : Summable (fun k => ‖f k‖))
    (hg : Summable (fun k => ‖g k‖)) :
    Summable (fun p : ℤ × ℤ => f p.1 * g (p.2 - p.1) * ex L p.2 y) := by
  have hF : Summable (fun p : ℤ × ℤ => (f p.1 * ex L p.1 y) * (g p.2 * ex L p.2 y)) :=
    summable_mul_of_summable_norm (f := fun k => f k * ex L k y) (g := fun k => g k * ex L k y)
      (norm_fam_summable L y hf) (norm_fam_summable L y hg)
  exact shearEquiv.summable_iff.1 (by rw [shear_comp L y]; exact hF)

/-- Reindexing the product family along the shear. -/
theorem tsum_shear (L : ℝ) (y : ℝ) {f g : ℤ → ℂ} :
    ∑' p : ℤ × ℤ, (f p.1 * ex L p.1 y) * (g p.2 * ex L p.2 y)
      = ∑' p : ℤ × ℤ, f p.1 * g (p.2 - p.1) * ex L p.2 y := by
  rw [← shearEquiv.tsum_eq (fun p : ℤ × ℤ => f p.1 * g (p.2 - p.1) * ex L p.2 y)]
  exact tsum_congr (fun p => (congrFun (shear_comp L y (f := f) (g := g)) p).symm)

/-- Regrouping the shear sum by the output index `k = j + m`. -/
theorem tsum_reindex (L : ℝ) (y : ℝ) {f g : ℤ → ℂ} (hf : Summable (fun k => ‖f k‖))
    (hg : Summable (fun k => ‖g k‖)) :
    ∑' p : ℤ × ℤ, f p.1 * g (p.2 - p.1) * ex L p.2 y
      = ∑' k : ℤ, convC f g k * ex L k y := by
  have hGs := summable_shear L y hf hg
  calc ∑' p : ℤ × ℤ, f p.1 * g (p.2 - p.1) * ex L p.2 y
      = ∑' j : ℤ, ∑' k : ℤ, f j * g (k - j) * ex L k y := hGs.tsum_prod
    _ = ∑' k : ℤ, ∑' j : ℤ, f j * g (k - j) * ex L k y :=
        (Summable.tsum_comm (f := fun j k => f j * g (k - j) * ex L k y) hGs).symm
    _ = ∑' k : ℤ, convC f g k * ex L k y := by
        refine tsum_congr (fun k => ?_)
        unfold convC
        rw [← tsum_mul_right]

/-- **Cauchy product for the pointwise series.** For `ℓ¹` coefficient sequences `f, g`:
`Σ_k (Σ_j f_j g_{k-j}) e_k(y) = (Σ_j f_j e_j(y)) (Σ_m g_m e_m(y))`. -/
theorem series_mul_convC (L : ℝ) {f g : ℤ → ℂ} (hf : Summable (fun k => ‖f k‖))
    (hg : Summable (fun k => ‖g k‖)) (y : ℝ) :
    series L (convC f g) y = series L f y * series L g y := by
  unfold series
  rw [tsum_prod_factor L y hf hg, tsum_shear L y, tsum_reindex L y hf hg]

/-- Linearity of the pointwise series: `series(f - κ g) = series f - κ series g` for `ℓ¹` data. -/
theorem series_sub_const_mul (L : ℝ) {f g : ℤ → ℂ} (κ : ℂ) (hf : Summable (fun k => ‖f k‖))
    (hg : Summable (fun k => ‖g k‖)) (y : ℝ) :
    series L (fun k => f k - κ * g k) y = series L f y - κ * series L g y := by
  have h1 : Summable (fun k => f k * ex L k y) := summable_mul_ex hf y
  have h2 : Summable (fun k => g k * ex L k y) := summable_mul_ex hg y
  simp only [series]
  rw [← tsum_mul_left, ← Summable.tsum_sub h1 (h2.mul_left κ)]
  exact tsum_congr (fun k => by ring)

/-- Summability of the coefficients of `convC(toField v, convC(c, c))`, a point of `H^a`. -/
theorem summable_norm_convC_rhs {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (v r : Ell2) :
    Summable (fun k => ‖convC (toField L a v) (convC (toField L a r) (toField L a r)) k‖) := by
  rw [← toField_mulBil_eq hL ha v r]
  exact summable_norm_toField hL ha _

/-- Summability of the coefficients of `convC(toField r, toField r)`. -/
theorem summable_norm_convC_rr {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (r : Ell2) :
    Summable (fun k => ‖convC (toField L a r) (toField L a r) k‖) := by
  rw [← toField_mulEll hL ha r r]
  exact summable_norm_toField hL ha _

/-- The pointwise right-hand side: `series(rhsD) = series(toField u) - κ series(toField v) (series(toField r))²`. -/
theorem series_rhsD {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (κ : ℝ) (u v r : Ell2) (y : ℝ) :
    series L (rhsD L a κ u v r) y
      = series L (toField L a u) y
        - (κ : ℂ) * (series L (toField L a v) y * series L (toField L a r) y ^ 2) := by
  have hc := summable_norm_toField hL ha r
  have hcc := summable_norm_convC_rr hL ha r
  have hv := summable_norm_toField hL ha v
  have hu := summable_norm_toField hL ha u
  have hX := summable_norm_convC_rhs hL ha v r
  have h1 : series L (convC (toField L a v) (convC (toField L a r) (toField L a r))) y
      = series L (toField L a v) y * (series L (toField L a r) y * series L (toField L a r) y) := by
    rw [series_mul_convC L hv hcc y, series_mul_convC L hc hc y]
  have hrhs : rhsD L a κ u v r
      = fun k => toField L a u k
        - (κ : ℂ) * convC (toField L a v) (convC (toField L a r) (toField L a r)) k := rfl
  rw [hrhs, series_sub_const_mul L (κ : ℂ) hu hX y, h1]
  ring

/-- Physical-to-Mathlib normalisation: `seriesRep c (y : AddCircle L) = (√L)⁻¹ · series c y`. -/
theorem seriesRep_coe (L : ℝ) [Fact (0 < L)] (c : ℤ → ℂ) (y : ℝ) :
    Fourier.seriesRep (L := L) c (y : AddCircle L)
      = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L c y := by
  unfold Fourier.seriesRep
  rw [series, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  have e : ex L n y = Complex.exp (2 * Real.pi * Complex.I * n * y / L) := by
    unfold ex
    congr 1
    ring
  rw [Fourier.mode_coe L n y, e]
  ring

/-- **Continuous representative.** An `L²` element `f` whose Fourier coefficients are an `ℓ¹`
sequence `c` equals a.e. a continuous `g` with `g(y) = (√L)⁻¹ series c y` and the sup bound
`‖g‖∞ ≤ (√L)⁻¹ Σ_k |c_k|`. -/
theorem rep_of_coeff (L : ℝ) [Fact (0 < L)] (f : QuantumNLS.PhysicalTensor.L2T L) (c : ℤ → ℂ)
    (hc : Summable (fun k => ‖c k‖))
    (hf : ∀ n : ℤ, Fourier.coeff L (f : AddCircle L → ℂ) n = c n) :
    ∃ g : AddCircle L → ℂ, Continuous g ∧ (f : AddCircle L → ℂ) =ᵐ[volume] g ∧
      (∀ y : ℝ, g (y : AddCircle L) = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L c y) ∧
      (∀ x : AddCircle L, ‖g x‖ ≤ (Real.sqrt L)⁻¹ * ∑' k, ‖c k‖) := by
  have hcont := Fourier.continuous_seriesRep (L := L) hc
  have hmem := Fourier.memLp_seriesRep (L := L) hc
  have heq : hmem.toLp (Fourier.seriesRep (L := L) c) = f := by
    apply (Fourier.fourierL2 L).injective
    ext n
    rw [Fourier.fourierL2_apply, Fourier.fourierL2_apply, Fourier.coeff_congr_ae L hmem.coeFn_toLp,
      Fourier.coeff_seriesRep hc, hf n]
  refine ⟨Fourier.seriesRep (L := L) c, hcont, ?_, ?_, ?_⟩
  · have h := hmem.coeFn_toLp
    rw [heq] at h
    exact h
  · intro y
    exact seriesRep_coe L c y
  · intro x
    exact Fourier.norm_seriesRep_le hc x

/-- **Representative of a field map.** For `r : Ell2`, `a > 1/2`, the `L²` field
`fieldMap L a r` (Fourier coefficients `toField r`) has a continuous representative. -/
theorem fieldMap_rep (L : ℝ) [Fact (0 < L)] {a : ℝ} (ha : 1 / 2 < a) (r : Ell2) :
    ∃ g : AddCircle L → ℂ, Continuous g ∧
      (QuantumNLS.ComplexifiedSobolevField.fieldMap L a (by linarith : (0 : ℝ) ≤ a) r
        : AddCircle L → ℂ) =ᵐ[volume] g ∧
      (∀ y : ℝ, g (y : AddCircle L) = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a r) y) ∧
      (∀ x : AddCircle L, ‖g x‖ ≤ (Real.sqrt L)⁻¹ * ∑' k, ‖toField L a r k‖) := by
  have hL : 0 < L := Fact.out
  exact rep_of_coeff L _ (toField L a r) (summable_norm_toField hL ha r)
    (fun n => QuantumNLS.ComplexifiedSobolevField.coeff_fieldMap L a (by linarith : (0 : ℝ) ≤ a) r n)

/-- **Pointwise Riccati ODE for the coefficient series.** For a fixed point `r` of `riccatiT`:
`d/dy series(toField r) = i z series(toField r) + series(toField u) - κ series(toField v) series(toField r)²`
for every real `y`. -/
theorem riccati_series_ode {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ : ℝ) {u v r : Ell2} (hr : riccatiT hL ha hz κ u v r = r) (y : ℝ) :
    HasDerivAt (fun y : ℝ => series L (toField L a r) y)
      (Complex.I * z * series L (toField L a r) y
        + (series L (toField L a u) y
          - (κ : ℂ) * (series L (toField L a v) y * series L (toField L a r) y ^ 2))) y := by
  have hc := summable_norm_toField hL ha r
  have hd := summable_norm_rhsD hL ha κ u v r
  have hrec := hrec_of_fixed hL ha hz κ hr
  have hder := series_hasDerivAt (L := L) hc hd hrec y
  rw [series_rhsD hL ha κ u v r y] at hder
  exact hder

/-- Physical scale: `s = (√L)⁻¹` satisfies `s² L = 1`. -/
theorem sqrt_inv_sq_mul (L : ℝ) (hL : 0 < L) :
    (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (L : ℂ) = 1 := by
  have hpos : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  have h : ((Real.sqrt L)⁻¹ : ℝ) * ((Real.sqrt L)⁻¹ : ℝ) * L = 1 := by
    calc ((Real.sqrt L)⁻¹ : ℝ) * ((Real.sqrt L)⁻¹ : ℝ) * L
        = ((Real.sqrt L)⁻¹ : ℝ) * ((Real.sqrt L)⁻¹ : ℝ) * (Real.sqrt L * Real.sqrt L) := by
          rw [hsq]
      _ = 1 := by field_simp
  exact_mod_cast h

/-- **Physical pointwise ODE.** For a scalar `s` with `s² L = 1` (`s = (√L)⁻¹`), the function
`y ↦ s · series(toField r)(y)` (the continuous representative of the `L²` field with coefficients
`toField r`, up to the `(√L)⁻¹` normalisation) satisfies the Riccati equation with physical
coupling `κ_phys = κ · L`:
`d/dy R = i z R + U - κ_phys V R²`, with `R = s·series(toField r)`, `U = s·series(toField u)`,
`V = s·series(toField v)`. -/
theorem physical_rep_ode {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ : ℝ) {u v r : Ell2} (hr : riccatiT hL ha hz κ u v r = r) (s : ℂ)
    (hs : s * s * (L : ℂ) = 1) (y : ℝ) :
    HasDerivAt (fun y : ℝ => s * series L (toField L a r) y)
      (Complex.I * z * (s * series L (toField L a r) y)
        + s * series L (toField L a u) y
        - (κ : ℂ) * (L : ℂ) * (s * series L (toField L a v) y)
          * (s * series L (toField L a r) y) ^ 2) y := by
  have h := (riccati_series_ode hL ha hz κ hr y).const_mul s
  convert h using 1
  linear_combination (-(κ : ℂ) * s * series L (toField L a v) y
    * series L (toField L a r) y ^ 2) * hs

/-- The physical representative satisfies the Riccati ODE with `s = (√L)⁻¹`. -/
theorem physical_rep_ode_sqrt {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ : ℝ) {u v r : Ell2} (hr : riccatiT hL ha hz κ u v r = r) (y : ℝ) :
    HasDerivAt (fun y : ℝ => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a r) y)
      (Complex.I * z * ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a r) y)
        + (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a u) y
        - (κ : ℂ) * (L : ℂ) * ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a v) y)
          * ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a r) y) ^ 2) y :=
  physical_rep_ode hL ha hz κ hr _ (sqrt_inv_sq_mul L hL) y

end QuantumNLS.RiccatiPointwiseRep

#print axioms QuantumNLS.RiccatiPointwiseRep.series_mul_convC
#print axioms QuantumNLS.RiccatiPointwiseRep.series_sub_const_mul
#print axioms QuantumNLS.RiccatiPointwiseRep.series_rhsD
#print axioms QuantumNLS.RiccatiPointwiseRep.seriesRep_coe
#print axioms QuantumNLS.RiccatiPointwiseRep.rep_of_coeff
#print axioms QuantumNLS.RiccatiPointwiseRep.fieldMap_rep
#print axioms QuantumNLS.RiccatiPointwiseRep.riccati_series_ode
#print axioms QuantumNLS.RiccatiPointwiseRep.physical_rep_ode
#print axioms QuantumNLS.RiccatiPointwiseRep.physical_rep_ode_sqrt
#print axioms QuantumNLS.RiccatiPointwiseRep.sqrt_inv_sq_mul
