import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairPotentialProbe

/-!
# F2 probes: `φ = 0` and the constant potential

Regression instances for the Volterra construction of `PairVolterra.lean` (plan section 6.2, F2):

* `φ = 0`: `volterra 0 z = 0`, `fundPair 0 z = freeFund z` (`E_z(t) = diag(e^{-izt}, e^{izt})`), and
  the monodromy trace is `2 cos z` (book Lemma 3.1 normalization);
* constant real-slice potential `u ≡ a`: `fundPair (realSlice (constL2 a)) z t` is the closed form
  `zsConstFund a z κ t = cos(κt) I + (sin(κt)/κ) A`, `κ² = z² - |a|²` (`Defs.lean`), obtained by
  checking the integral equation (variation of constants) and applying `fundCont_unique`;
* the trace of the monodromy of the constant potential is `2 cos κ` (`zsConstFund_trace`).
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis NlsGge.SpectralFoundations

/-! ### Zero potential -/

theorem coverRep38_zero_ae : ∀ᵐ t : ℝ, coverRep38 (0 : PhysicalL2) t = 0 := by
  have h := ae_real_of_ae_spectral (p := fun x => naturalPhysicalCoverL2 (0 : PhysicalL2) x = 0) (by
    rw [map_zero]; exact Lp.coeFn_zero _ _ _)
  exact h

theorem potCoeff38_zero_ae : ∀ᵐ s : ℝ, potCoeff38 (0 : PotPair) s = 0 := by
  filter_upwards [coverRep38_zero_ae] with s hs
  ext i j
  fin_cases i <;> fin_cases j <;> simp [potCoeff38, potRepFst38, potRepSnd38, hs]

theorem volterra_zero (z : ℂ) : volterra 0 z = 0 := by
  ext N t i j
  rw [volterra_apply]
  have : ∀ᵐ s : ℝ, (freeE z (t - s) * potCoeff38 (0 : PotPair) s * Set.IccExtend zero_le_one N s)
      i j = 0 := by
    filter_upwards [potCoeff38_zero_ae] with s hs
    simp [hs]
  rw [intervalIntegral.integral_congr_ae (by filter_upwards [this] with s hs _ using hs)]
  simp

/-- Probe 1: at `φ = 0` the fundamental solution is the free one, `E_z(t) = diag(e^{-izt}, e^{izt})`. -/
theorem fundCont_zero (z : ℂ) : fundCont 0 z = freeFund z := by
  unfold fundCont
  have h10 : (1 - volterra 0 z) = 1 := by
    rw [volterra_zero]; exact sub_zero (1 : C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ) →L[ℂ]
      C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ))
  rw [h10, Ring.inverse_one]
  rfl

theorem fundPair_zero_potential (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    fundPair 0 z t = !![Complex.exp (-(Complex.I * z * t)), 0; 0, Complex.exp (Complex.I * z * t)] := by
  rw [fundPair_eq, fundCont_zero]; rfl

theorem monodromyPair_zero_potential (z : ℂ) : monodromyPair 0 z = freeE z 1 := by
  rw [monodromyPair_eq_fundPair, fundPair_eq, fundCont_zero]; rfl

/-- The monodromy trace at `φ = 0` is `2 cos z` (so `Δ = 2 Δh`, `Δh(0, z) = cos z`). -/
theorem trace_monodromyPair_zero (z : ℂ) : Matrix.trace (monodromyPair 0 z) = 2 * Complex.cos z := by
  rw [monodromyPair_zero_potential, freeE_eq]
  exact zsFullTrace_zeroPotential z

/-! ### Constant real-slice potential `u ≡ a` -/

/-- `Φ̃` of the constant potential `(a, ā)`. -/
def constPc (a : ℂ) : PairMat38 := !![0, Complex.I * a; -(Complex.I * star a), 0]

theorem potCoeff38_realSlice_const_ae (a : ℂ) :
    ∀ᵐ s : ℝ, potCoeff38 (realSlice (constL2 a)) s = constPc a := by
  rw [realSlice_constL2]
  filter_upwards [coverRep38_const_ae a, coverRep38_const_ae (star a)] with s h1 h2
  have h2' : coverRep38 (constL2 ((starRingEnd ℂ) a)) s = (starRingEnd ℂ) a := h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [potCoeff38, constPc, potRepFst38, potRepSnd38, h1, h2']

theorem hasDerivAt_entry38 {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {f' : Matrix (Fin 2) (Fin 2) ℂ}
    {x : ℝ} (h : HasDerivAt f f' x) (i j : Fin 2) : HasDerivAt (fun y => f y i j) (f' i j) x :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j

theorem hasDerivAt_cexp_mul (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * y)) (c * Complex.exp (c * x)) x := by
  have h : HasDerivAt (fun w : ℂ => Complex.exp (c * w)) (Complex.exp (c * x) * c) (x : ℂ) := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_mul c).cexp
  simpa [mul_comm] using h.comp_ofReal

/-- Variation of constants: `d/ds [E_z(-s) G(s)] = E_z(-s) Φ̃ G(s)` for `G' = (-zR + Φ̃) G`. -/
theorem const_entry_hasDerivAt (a z κ : ℂ) (hκ : κ ≠ 0) (hκ2 : κ ^ 2 = z ^ 2 - a * star a)
    (i j : Fin 2) (x : ℝ) :
    HasDerivAt (fun y : ℝ => freeE z (-y) i i * zsConstFund a z κ y i j)
      ((freeE z (-x) * constPc a * zsConstFund a z κ x) i j) x := by
  have hG := ((zsConstFund_isFundamental a z κ hκ hκ2).2 x)
  have hGe := hasDerivAt_entry38 hG i j
  fin_cases i
  · have hE : HasDerivAt (fun y : ℝ => freeE z (-y) 0 0) (Complex.I * z * freeE z (-x) 0 0) x := by
      have := hasDerivAt_cexp_mul (Complex.I * z) x
      convert this using 1
      · funext y; simp [freeE]
      · simp [freeE]
    refine (hE.mul hGe).congr_deriv ?_
    fin_cases j <;>
      simp [zsCoefficientComplex, constPc, Matrix.mul_apply, Fin.sum_univ_two, freeE] <;> ring
  · have hE : HasDerivAt (fun y : ℝ => freeE z (-y) 1 1) (-(Complex.I * z) * freeE z (-x) 1 1) x := by
      have := hasDerivAt_cexp_mul (-(Complex.I * z)) x
      convert this using 1
      · funext y; simp [freeE]
      · simp [freeE]
    refine (hE.mul hGe).congr_deriv ?_
    fin_cases j <;>
      simp [zsCoefficientComplex, constPc, Matrix.mul_apply, Fin.sum_univ_two, freeE] <;> ring

theorem continuous_zsConstFund (a z κ : ℂ) (hκ : κ ≠ 0) (hκ2 : κ ^ 2 = z ^ 2 - a * star a) :
    Continuous (zsConstFund a z κ) :=
  continuous_pi fun i => continuous_pi fun j => continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_entry38 ((zsConstFund_isFundamental a z κ hκ hκ2).2 x) i j).continuousAt

/-- The closed form as a continuous function on `[0,1]`. -/
def constFundCont (a z κ : ℂ) (hκ : κ ≠ 0) (hκ2 : κ ^ 2 = z ^ 2 - a * star a) :
    C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨fun t => zsConstFund a z κ t, (continuous_zsConstFund a z κ hκ hκ2).comp continuous_subtype_val⟩

theorem freeE_mul_freeE_neg (z : ℂ) (t : ℝ) (i : Fin 2) :
    freeE z t i i * freeE z (-t) i i = 1 := by
  have h := congrArg (fun M => M i i) (freeE_add z t (-t))
  simp only [add_neg_cancel, freeE_zero, freeE_mul_apply, Matrix.one_apply_eq] at h
  exact h.symm

theorem freeE_apply_eq (z : ℂ) (t : ℝ) (i j : Fin 2) :
    freeE z t i j = freeE z t i i * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  fin_cases i <;> fin_cases j <;> simp [freeE]

/-- Probe 2 (integral equation): the closed form solves `M = E + 𝒱 M` for the constant potential. -/
theorem constFundCont_integral_eq (a z κ : ℂ) (hκ : κ ≠ 0) (hκ2 : κ ^ 2 = z ^ 2 - a * star a)
    (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    constFundCont a z κ hκ hκ2 t i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 (realSlice (constL2 a)) s *
        Set.IccExtend zero_le_one (constFundCont a z κ hκ hκ2) s) i j := by
  set G := constFundCont a z κ hκ hκ2 with hGdef
  have hfac : ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 (realSlice (constL2 a)) s *
        Set.IccExtend zero_le_one G s) i j =
      freeE z t i i * ∫ s in (0 : ℝ)..t, (freeE z (-s) * potCoeff38 (realSlice (constL2 a)) s *
        Set.IccExtend zero_le_one G s) i j := by
    have h := congrArg (fun M => M i j) (volterraFun_eq (realSlice (constL2 a)) z G t)
    simp only [volterraKer, Matrix.of_apply, freeE_mul_apply] at h
    exact h
  have hae : ∫ s in (0 : ℝ)..t, (freeE z (-s) * potCoeff38 (realSlice (constL2 a)) s *
        Set.IccExtend zero_le_one G s) i j =
      ∫ s in (0 : ℝ)..t, (freeE z (-s) * constPc a * zsConstFund a z κ s) i j := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [potCoeff38_realSlice_const_ae a] with s hs hsI
    rw [Set.uIoc_of_le t.2.1] at hsI
    have hs1 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hsI.1.le, hsI.2.trans t.2.2⟩
    have : Set.IccExtend zero_le_one G s = zsConstFund a z κ s := by
      rw [Set.IccExtend_of_mem _ _ hs1]; rfl
    rw [hs, this]
  have hftc : ∫ s in (0 : ℝ)..t, (freeE z (-s) * constPc a * zsConstFund a z κ s) i j =
      freeE z (-t) i i * zsConstFund a z κ t i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    have hc : Continuous fun s : ℝ => (freeE z (-s) * constPc a * zsConstFund a z κ s) i j := by
      have h1 : Continuous fun s : ℝ => freeE z (-s) := (continuous_freeE z).comp continuous_neg
      have h2 := continuous_zsConstFund a z κ hκ hκ2
      have h3 : Continuous fun s : ℝ => freeE z (-s) * constPc a * zsConstFund a z κ s :=
        (h1.mul continuous_const).mul h2
      exact (continuous_apply j).comp ((continuous_apply i).comp h3)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => freeE z (-y) i i * zsConstFund a z κ y i j)
      (a := 0) (b := (t : ℝ)) (fun x _ => const_entry_hasDerivAt a z κ hκ hκ2 i j x)
      (hc.intervalIntegrable _ _)
    rw [this]
    have h0 := (zsConstFund_isFundamental a z κ hκ hκ2).1
    simp [h0, freeE_zero]
  rw [hfac, hae, hftc]
  have hu := freeE_mul_freeE_neg z t i
  have he := freeE_apply_eq z t i j
  have hG : G t i j = zsConstFund a z κ t i j := rfl
  rw [hG, he]
  linear_combination (-(zsConstFund a z κ t i j)) * hu

/-- Probe 2: for the constant real-slice potential `u ≡ a`, `fundPair` is the closed form
`cos(κt) I + (sin(κt)/κ) A`, `κ² = z² - |a|²` (`zsConstFund`, `Defs.lean`). -/
theorem fundPair_realSlice_const (a z κ : ℂ) (hκ : κ ≠ 0) (hκ2 : κ ^ 2 = z ^ 2 - a * star a)
    (t : Set.Icc (0 : ℝ) 1) :
    fundPair (realSlice (constL2 a)) z t = zsConstFund a z κ t := by
  have h := fundCont_unique (realSlice (constL2 a)) z (constFundCont a z κ hκ hκ2)
    (fun t i j => constFundCont_integral_eq a z κ hκ hκ2 t i j)
  rw [fundPair_eq, ← h]
  rfl

/-- Probe 2 (monodromy): `tr M(1) = 2 cos κ`, i.e. `Δh = cos κ`; for real `z` with `|z| < |a|`,
`κ = i √(|a|² - z²)` and `Δh = cosh √(|a|² - z²) > 1` (the gap around `0`). -/
theorem trace_monodromyPair_realSlice_const (a z κ : ℂ) (hκ : κ ≠ 0)
    (hκ2 : κ ^ 2 = z ^ 2 - a * star a) :
    Matrix.trace (monodromyPair (realSlice (constL2 a)) z) = 2 * Complex.cos κ := by
  rw [monodromyPair_eq_fundPair, fundPair_realSlice_const a z κ hκ hκ2]
  exact zsConstFund_trace a z κ

/-- The monodromy of the constant potential for every spectral parameter off the double point
`z² = |a|²`. -/
theorem exists_trace_monodromyPair_realSlice_const (a z : ℂ) (h : z ^ 2 ≠ a * star a) :
    ∃ κ : ℂ, κ ^ 2 = z ^ 2 - a * star a ∧ κ ≠ 0 ∧
      Matrix.trace (monodromyPair (realSlice (constL2 a)) z) = 2 * Complex.cos κ := by
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq (z ^ 2 - a * star a) (n := 2) (by norm_num)
  have hne : κ ≠ 0 := by
    rintro rfl
    exact h (by linear_combination (-1 : ℂ) * hκ)
  exact ⟨κ, hκ, hne, trace_monodromyPair_realSlice_const a z κ hne hκ⟩

end

end NlsGge.GK38
