import Mathlib
import QuantumNLS.ParamContinuity
import QuantumNLS.IntrinsicContact

/-!
# R-043AB9AA `prop:root-full-mass` (part 1): the arbitrary-mass measure `M_{κ,u} = m μ_{κm, u/√m}`

Source: `ROOT_measure_extensions.tex`, `prop:root-full-mass`.  Routing (recorded for Terra): the scope lists `FIN-EXT025-GP-10` for this node; the proof
here (and in `ParamContinuity`, `FreeLimit`, `RootMeasureExistence`) uses NO EXT-025 contract: compactness is mathlib's Prokhorov theorem on the tight
sequences produced by the mass-one tail inequality (`CauchyLimitCriterion`), identification is `CauchyUniqueness`.

Defined and proved here:
* `Mmeas κ u` (`= 0` for `u = 0`, else `‖u‖² · μ_{κ‖u‖², u/‖u‖}` with `μ_{lam,v} = muKappa v hv lam` of `FreeLimit`), `Mfin` as a `FiniteMeasure`;
  `Mmeas_univ`: total mass `‖u‖²`;
* `productSymbol_smul`: `s_κ(z; c v) = s_{κ‖c‖²}(z; v)` (the printed `(κm)^r⟨v^r,K v^r⟩ = κ^r⟨u^r,K u^r⟩`), `kps_smul`;
* `mass_characterization`: for `Im z` large (`HighHalf L (κ‖u‖²) z`) the Cauchy transform `G` of `M_{κ,u}` satisfies `|G| ≤ ‖u‖²/Im z`,
  `e^{iκG} + e^{izL}e^{-iκG} = 1 + e^{izL} + Σ κ^r⟨u^r,K_{r,z}u^r⟩` (`eq:root-mass-characterization`) and is the unique such value; `u = 0` included;
* `Mmeas_zero_coupling`: `M_{0,u} = Σ_n |û(n)|² δ_{2πn/L}` (`freeMeasure`);
* `Mmeas_eq_of_symbol`: equal masses and equal symbols on a high half-plane give equal measures; hence `Mmeas_phase`: common-phase invariance.
Weak continuity and the Born-product-law statement are in `FullMassLimit`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

open Classical

namespace QuantumNLS.FullMass

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.CauchyUniqueness (cauchyTransform cauchy_ext)
open QuantumNLS.RootMeasureComplex (fz HighHalf)
open QuantumNLS.RootMeasureConcentration (gStar gStar_spec unique_fixed)
open QuantumNLS.NormalizedTransfer (productSymbol symbolTerm orderedKernel)
open QuantumNLS.KernelDefinition (kernelProductSymbol BoundedSymmetricKernel)
open QuantumNLS.FreeLimit (freeMeasure freeProb muKappa muKappa_spec)
open QuantumNLS.HighMomentsOps (wvec)

variable {L : ℝ} [Fact (0 < L)]

/-! ### The measure -/

/-- `u/‖u‖`. -/
def unitDir (u : L2T L) : L2T L := ((‖u‖⁻¹ : ℝ) : ℂ) • u

theorem norm_unitDir {u : L2T L} (h : u ≠ 0) : ‖unitDir u‖ = 1 := by
  unfold unitDir
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

theorem smul_unitDir {u : L2T L} (h : u ≠ 0) : ((‖u‖ : ℝ) : ℂ) • unitDir u = u := by
  unfold unitDir
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), Complex.ofReal_one, one_smul]

/-- **`M_{κ,u} = m μ_{κm, u/√m}`**, `M_{κ,0} = 0` (`m = ‖u‖²`). -/
def Mmeas (κ : ℝ) (u : L2T L) : Measure ℝ :=
  if h : u = 0 then 0 else
    ENNReal.ofReal (‖u‖ ^ 2) • (muKappa (unitDir u) (norm_unitDir h) (κ * ‖u‖ ^ 2) : Measure ℝ)

theorem Mmeas_zero (κ : ℝ) : Mmeas κ (0 : L2T L) = 0 := by
  unfold Mmeas; rw [dif_pos rfl]

theorem Mmeas_of_ne (κ : ℝ) {u : L2T L} (h : u ≠ 0) :
    Mmeas κ u = ENNReal.ofReal (‖u‖ ^ 2) • (muKappa (unitDir u) (norm_unitDir h) (κ * ‖u‖ ^ 2) : Measure ℝ) := by
  unfold Mmeas; rw [dif_neg h]

/-- **Total mass `‖u‖²`.** -/
theorem Mmeas_univ (κ : ℝ) (u : L2T L) : Mmeas κ u Set.univ = ENNReal.ofReal (‖u‖ ^ 2) := by
  by_cases h : u = 0
  · subst h; simp [Mmeas_zero]
  · rw [Mmeas_of_ne κ h]; simp

instance isFinite_Mmeas (κ : ℝ) (u : L2T L) : IsFiniteMeasure (Mmeas κ u) :=
  ⟨by rw [Mmeas_univ]; exact ENNReal.ofReal_lt_top⟩

/-- `M_{κ,u}` as a finite measure (the space with the topology of weak convergence against bounded continuous functions). -/
def Mfin (κ : ℝ) (u : L2T L) : FiniteMeasure ℝ := ⟨Mmeas κ u, isFinite_Mmeas κ u⟩

/-! ### Scaling of the symbol -/

theorem kps_smul {r : ℕ} (A : BoundedSymmetricKernel (L2T L) r) (c : ℂ) (v : L2T L) :
    kernelProductSymbol A (c • v) = ((‖c‖ ^ (2 * r) : ℝ) : ℂ) * kernelProductSymbol A v := by
  have e : ∀ w : L2T L, kernelProductSymbol A w = ⟪wvec r w, A (wvec r w)⟫_ℂ := fun w => rfl
  have hw : wvec r (c • v) = c ^ r • wvec r v := Subtype.ext (QuantumNLS.IntrinsicContact.htpow_smul r c v)
  rw [e, e, hw]
  have hA := map_smul A (c ^ r) (wvec r v)
  rw [hA]
  have key : ⟪c ^ r • wvec r v, c ^ r • A (wvec r v)⟫_ℂ =
      (starRingEnd ℂ) (c ^ r) * (c ^ r * ⟪wvec r v, A (wvec r v)⟫_ℂ) :=
    (inner_smul_left (𝕜 := ℂ) (E := QuantumNLS.TensorCarrier.SymSector ℂ (L2T L) r) _ _ _).trans
      (congrArg _ (inner_smul_right (𝕜 := ℂ) (E := QuantumNLS.TensorCarrier.SymSector ℂ (L2T L) r) _ _ _))
  rw [key, ← mul_assoc, Complex.conj_mul', norm_pow]
  push_cast
  ring

theorem productSymbol_smul (κ : ℝ) (c : ℂ) (v : L2T L) (z : ℂ) :
    productSymbol L κ (c • v) z = productSymbol L (κ * ‖c‖ ^ 2) v z := by
  unfold productSymbol
  congr 1
  refine tsum_congr (fun j => ?_)
  unfold symbolTerm
  rw [kps_smul, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [mul_pow, ← pow_mul]

theorem productSymbol_zero_coupling (v : L2T L) (z : ℂ) :
    productSymbol L 0 v z = 1 + Complex.exp (Complex.I * z * L) := by
  unfold productSymbol symbolTerm
  simp

theorem productSymbol_zero_vec (κ : ℝ) (z : ℂ) :
    productSymbol L κ (0 : L2T L) z = 1 + Complex.exp (Complex.I * z * L) := by
  have h := productSymbol_smul κ (0 : ℂ) (0 : L2T L) z
  rw [zero_smul] at h
  rw [h]
  simpa using productSymbol_zero_coupling (0 : L2T L) z

theorem productSymbol_unit (κ : ℝ) {u : L2T L} (h : u ≠ 0) (z : ℂ) :
    productSymbol L κ u z = productSymbol L (κ * ‖u‖ ^ 2) (unitDir u) z := by
  have := productSymbol_smul κ ((‖u‖ : ℝ) : ℂ) (unitDir u) z
  rw [smul_unitDir h, Complex.norm_real, Real.norm_eq_abs, abs_norm] at this
  exact this

/-! ### Cauchy transform and characterization -/

theorem cauchy_smul (c : ℝ≥0∞) (μ : Measure ℝ) (z : ℂ) :
    cauchyTransform (c • μ) z = c.toReal • cauchyTransform μ z := by
  unfold cauchyTransform
  exact integral_smul_measure _ _

theorem cauchy_Mmeas {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (h : u ≠ 0) {z : ℂ}
    (hz : HighHalf L (κ * ‖u‖ ^ 2) z) :
    cauchyTransform (Mmeas κ u) z =
      ((‖u‖ ^ 2 : ℝ) : ℂ) * gStar L (κ * ‖u‖ ^ 2) (mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2))
        (unitDir u) (norm_unitDir h) z := by
  have hlam : 0 < κ * ‖u‖ ^ 2 := mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2)
  rw [Mmeas_of_ne κ h, cauchy_smul, ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  congr 1
  exact QuantumNLS.RootMeasureExistence.cauchy_limiting_measure hlam (unitDir u) (norm_unitDir h)
    (muKappa_spec (unitDir u) (norm_unitDir h) hlam) hz

theorem fz_scale (κ m : ℝ) (z w : ℂ) :
    fz L κ z ((m : ℂ) * w) = fz L (κ * m) z w := by
  unfold fz
  have e : Complex.I * (κ : ℂ) * ((m : ℂ) * w) = Complex.I * ((κ * m : ℝ) : ℂ) * w := by push_cast; ring
  rw [e]

/-- **`eq:root-mass-characterization`**: for `Im z` large, the Cauchy transform of `M_{κ,u}` (`u ≠ 0`) is the unique value in `|G| ≤ ‖u‖²/Im z`
solving `e^{iκG} + e^{izL}e^{-iκG} = 1 + e^{izL} + Σ_r κ^r ⟨u^r, K_{r,z} u^r⟩`. -/
theorem mass_characterization {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (h : u ≠ 0) {z : ℂ}
    (hz : HighHalf L (κ * ‖u‖ ^ 2) z) :
    ‖cauchyTransform (Mmeas κ u) z‖ ≤ ‖u‖ ^ 2 / z.im ∧
    fz L κ z (cauchyTransform (Mmeas κ u) z) = productSymbol L κ u z ∧
    ∀ G' : ℂ, ‖G'‖ ≤ ‖u‖ ^ 2 / z.im → fz L κ z G' = productSymbol L κ u z →
      G' = cauchyTransform (Mmeas κ u) z := by
  have hm : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.2 h) 2
  have hlam : 0 < κ * ‖u‖ ^ 2 := mul_pos hκ hm
  have hη : 0 < z.im := by linarith [hz.1]
  have hv : ‖unitDir u‖ = 1 := norm_unitDir h
  obtain ⟨hg1, hg2⟩ := gStar_spec hlam (unitDir u) hv hz
  have hG := cauchy_Mmeas hκ h hz
  set m : ℝ := ‖u‖ ^ 2 with hmdef
  set v := unitDir u with hvdef
  set g := gStar L (κ * m) hlam v hv z with hgdef
  have hsym : productSymbol L κ u z = productSymbol L (κ * m) v z := productSymbol_unit κ h z
  have hfz : fz L κ z ((m : ℂ) * g) = productSymbol L κ u z := by
    rw [fz_scale, hg2, hsym]
  refine ⟨?_, ?_, ?_⟩
  · rw [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm.le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hg1 hm.le
  · rw [hG]; exact hfz
  · intro G' hG'1 hG'2
    rw [hG]
    have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hw1 : ‖G' / (m : ℂ)‖ ≤ (z.im)⁻¹ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm.le, div_le_iff₀ hm]
      calc ‖G'‖ ≤ m / z.im := hG'1
        _ = (z.im)⁻¹ * m := by rw [div_eq_mul_inv, mul_comm]
    have hw2 : fz L (κ * m) z (G' / (m : ℂ)) = fz L (κ * m) z g := by
      rw [← fz_scale, mul_div_cancel₀ _ hmc, hG'2, hg2, hsym]
    have := unique_fixed hlam hz hw1 hg1 hw2
    rw [← this, mul_div_cancel₀ _ hmc]

theorem mass_characterization_zero (κ : ℝ) {z : ℂ} (hz : 0 < z.im) :
    cauchyTransform (Mmeas κ (0 : L2T L)) z = 0 ∧
    fz L κ z 0 = productSymbol L κ (0 : L2T L) z ∧
    ∀ G' : ℂ, ‖G'‖ ≤ ‖(0 : L2T L)‖ ^ 2 / z.im → G' = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Mmeas_zero]; unfold cauchyTransform; simp
  · rw [productSymbol_zero_vec]; unfold fz; simp
  · intro G' hG'
    simpa using hG'

/-! ### Zero coupling -/

theorem coeff_smul (c : ℂ) (u : L2T L) (n : ℤ) :
    QuantumNLS.Fourier.coeff L ((c • u : L2T L) : AddCircle L → ℂ) n =
      c * QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n := by
  rw [QuantumNLS.Fourier.coeff_congr_ae L (Lp.coeFn_smul c u)]
  exact QuantumNLS.Fourier.coeff_const_mul L c _ n

theorem Mmeas_zero_coupling (u : L2T L) : Mmeas 0 u = freeMeasure L u := by
  by_cases h : u = 0
  · subst h
    rw [Mmeas_zero]
    have hc : ∀ n : ℤ, QuantumNLS.Fourier.coeff L (((0 : L2T L)) : AddCircle L → ℂ) n = 0 := fun n => by
      simpa using coeff_smul (0 : ℂ) (0 : L2T L) n
    unfold freeMeasure
    have hz0 : (fun n : ℤ => ENNReal.ofReal (‖QuantumNLS.Fourier.coeff L (((0 : L2T L)) : AddCircle L → ℂ) n‖ ^ 2) •
        Measure.dirac (2 * Real.pi * n / L)) = fun _ => 0 := by
      funext n; rw [hc n]; simp
    rw [hz0]
    simp
  · rw [Mmeas_of_ne 0 h, zero_mul]
    have hf : (muKappa (unitDir u) (norm_unitDir h) 0 : Measure ℝ) = freeMeasure L (unitDir u) := by
      unfold muKappa; rw [dif_neg (lt_irrefl 0)]; rfl
    rw [hf]
    have hcoef : ∀ n : ℤ, ‖QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n‖ ^ 2 =
        ‖u‖ ^ 2 * ‖QuantumNLS.Fourier.coeff L ((unitDir u : L2T L) : AddCircle L → ℂ) n‖ ^ 2 := by
      intro n
      have := coeff_smul ((‖u‖ : ℝ) : ℂ) (unitDir u) n
      rw [smul_unitDir h] at this
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, mul_pow]
    unfold freeMeasure
    ext s hs
    simp only [Measure.smul_apply, Measure.sum_apply _ hs, smul_eq_mul, ← ENNReal.tsum_mul_left]
    congr 1
    funext n
    rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), hcoef n]

/-! ### Equal symbols give equal measures; common phase -/

theorem Mmeas_eq_of_symbol {κ : ℝ} (hκ : 0 < κ) {u u' : L2T L} (hm : ‖u‖ = ‖u'‖) {η₁ : ℝ} (hη₁ : 0 < η₁)
    (hs : ∀ z : ℂ, η₁ ≤ z.im → productSymbol L κ u z = productSymbol L κ u' z) :
    Mmeas κ u = Mmeas κ u' := by
  by_cases h : u = 0
  · subst h
    have : u' = 0 := by rw [← norm_eq_zero, ← hm]; simp
    subst this; rfl
  have h' : u' ≠ 0 := by
    intro h0; apply h; rw [← norm_eq_zero, hm, h0]; simp
  have hL : 0 < L := Fact.out
  set m : ℝ := ‖u‖ ^ 2 with hmdef
  have hm' : ‖u'‖ ^ 2 = m := by rw [hmdef, hm]
  set η₀ : ℝ := max η₁ (max (4 * (κ * m)) (Real.log 16 / L)) with hη₀
  have hη0 : 0 < η₀ := lt_of_lt_of_le hη₁ (le_max_left _ _)
  haveI := isFinite_Mmeas κ u
  haveI := isFinite_Mmeas κ u'
  refine cauchy_ext (Mmeas κ u) (Mmeas κ u') hη0 (fun t => ?_)
  set z : ℂ := (t : ℂ) + η₀ * Complex.I with hz
  have him : z.im = η₀ := by simp [hz]
  have hHigh : HighHalf L (κ * ‖u‖ ^ 2) z := by
    refine ⟨by rw [him]; exact (le_max_left (4 * (κ * m)) (Real.log 16 / L)).trans (le_max_right _ _), ?_⟩
    rw [him]
    have : Real.log 16 / L ≤ η₀ := (le_max_right _ _).trans (le_max_right _ _)
    rwa [div_le_iff₀ hL, mul_comm] at this
  have hHigh' : HighHalf L (κ * ‖u'‖ ^ 2) z := by rw [hm']; rw [← hmdef] at hHigh; exact hHigh
  obtain ⟨b1, e1, u1⟩ := mass_characterization hκ h hHigh
  obtain ⟨b2, e2, _⟩ := mass_characterization hκ h' hHigh'
  rw [hm'] at b2
  refine (u1 _ b2 ?_).symm
  rw [e2]
  exact (hs z (by rw [him]; exact le_max_left _ _)).symm

/-- **Common-phase invariance** for `κ > 0`. -/
theorem Mmeas_phase {κ : ℝ} (hκ : 0 < κ) (u : L2T L) {c : ℂ} (hc : ‖c‖ = 1) :
    Mmeas κ (c • u) = Mmeas κ u := by
  refine Mmeas_eq_of_symbol hκ (by rw [norm_smul, hc, one_mul]) one_pos (fun z _ => ?_)
  rw [productSymbol_smul, hc]
  simp

/-- **Common-phase invariance at zero coupling.** -/
theorem Mmeas_phase_zero (u : L2T L) {c : ℂ} (hc : ‖c‖ = 1) : Mmeas 0 (c • u) = Mmeas 0 u := by
  rw [Mmeas_zero_coupling, Mmeas_zero_coupling]
  unfold freeMeasure
  congr 1
  funext n
  rw [coeff_smul, norm_mul, hc, one_mul]

end QuantumNLS.FullMass

#print axioms QuantumNLS.FullMass.Mmeas_univ
#print axioms QuantumNLS.FullMass.productSymbol_smul
#print axioms QuantumNLS.FullMass.mass_characterization
#print axioms QuantumNLS.FullMass.mass_characterization_zero
#print axioms QuantumNLS.FullMass.Mmeas_zero_coupling
#print axioms QuantumNLS.FullMass.Mmeas_eq_of_symbol
#print axioms QuantumNLS.FullMass.Mmeas_phase
#print axioms QuantumNLS.FullMass.Mmeas_phase_zero
