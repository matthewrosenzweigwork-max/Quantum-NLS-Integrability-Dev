import NlsGge.GK38.MolnarLocalization
import NlsGge.Sobolev.FiniteFourier
import NlsGge.Hierarchy.ALPlaneConsistency38

/-!
# Mo2 probes

Regression instances for `MolnarLocalizationA`, `MolnarLocalizationB1-B4`, `MolnarLocalization`.

* **`u = 0`**: the labelled gaps are the points `nπ` (`gap_zero38`); `MolnarZeroLoc38 0 0` holds
  (a nontrivial instance of the interface hypothesis of part A: zeros of `cos² - 1` in the strip
  are `nπ`); and part A, applied to `u = 0`, gives the localization of the gap UNCONDITIONALLY
  (`probe_zero_localization`), exercising the whole homotopy argument (`τ ↦ τ · 0 = 0`).
* **constant potential `u ≡ t`** (plane wave `k = 0`): `molnarNormSq u = 2 t²`
  (`molnarNormSq_const38`) and the Fourier system has the explicit solution
  `λ² = n²π² + t²`, `f₁ = δ_n`, `f₂ = ((λ - nπ)/t) δ_{-n}` (closed gap `n ≠ 0` at
  `√(n²π² + t²)`, endpoint `t` of the gap `(-t, t)` at `n = 0`), a valid `Mo2.Setup`.  Then
  `Mo2.molnar_ls_core` gives `|λ - nπ| ≤ 2t²/⟨n⟩ + 2t/⟨2n⟩` (`probe_const_localization`).
  (This is the check of the sequence-space estimate on an exactly solvable potential; the
  identification of this solution with the zero of `Δh² - 1` is the open bridge goal.)
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Topology

namespace NlsGge.GK38

open NlsGge.SpectralFoundations NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.AblowitzLadik

noncomputable section

/-! ### `u = 0` -/

theorem physicalFourier_zero38 (k : ℤ) :
    physicalFourier ((0 : PhysicalL2) : PhysicalCircle → ℂ) k = 0 := by
  have := physicalFourier_smul38 0 (0 : PhysicalL2) k
  simpa using this

theorem molnarNormSq_zero38 : molnarNormSq (0 : PhysicalL2) = 0 := by
  unfold molnarNormSq; simp only [physicalFourier_zero38]; simp

theorem molnarRadius_zero38 (n : ℤ) : molnarRadius38 0 n = 0 := by
  unfold molnarRadius38; simp

/-- For `u = 0` the labelled gap `n` is the point `nπ`. -/
theorem gap_zero38 (n : ℤ) :
    actualGapLowerAllE02_38 (0 : PhysicalL2) n = n * Real.pi ∧
    actualGapUpperAllE02_38 (0 : PhysicalL2) n = n * Real.pi := by
  have h : actualGapLevelSetE02_38 (0 : PhysicalL2) n = {(n : ℝ) * Real.pi} := by
    ext x
    simp [actualGapLevelSetE02_38, quasimomentumRealPart_zero38]
  unfold actualGapLowerAllE02_38 actualGapUpperAllE02_38
  rw [h]
  simp

/-- A nontrivial instance of the zero-localization interface: `Δh(0) = cos`. -/
theorem molnarZeroLoc_zero38 : MolnarZeroLoc38 (0 : PhysicalL2) 0 := by
  intro n _ x hx hz
  rw [molnarRadius_zero38]
  rw [halfTrace_zero38, ← Complex.ofReal_cos, ← Complex.ofReal_pow] at hz
  have hz' : Real.cos x ^ 2 = 1 := by exact_mod_cast hz
  have hsin : Real.sin x = 0 := by
    have := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (Real.sin x)]
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
  have hpi := Real.pi_pos
  have h1 : |((k : ℝ) - n) * Real.pi| ≤ Real.pi / 2 := by
    rw [show ((k : ℝ) - n) * Real.pi = x - n * Real.pi by rw [← hk]; ring]; exact hx
  rw [abs_mul, abs_of_pos hpi] at h1
  have h2 : |(k : ℝ) - n| ≤ 1 / 2 := by nlinarith
  have h3 : k = n := by
    have : |((k - n : ℤ) : ℝ)| < 1 := by push_cast; linarith
    have h4 : |k - n| < 1 := by exact_mod_cast this
    have h5 := abs_lt.mp h4
    omega
  subst h3
  rw [← hk]; simp

/-- For `u = 0`, part A yields the localization of the whole gap unconditionally. -/
theorem probe_zero_localization (n : ℤ) (l : ℝ)
    (hl : l ∈ Set.Icc (actualGapLowerAllE02_38 (0 : PhysicalL2) n)
      (actualGapUpperAllE02_38 (0 : PhysicalL2) n)) : l = n * Real.pi := by
  have hu : SobolevSquareSummable 1 (physicalFourier (0 : PhysicalL2)) := by
    have : (fun j : ℤ => Real.rpow (japaneseBracket j) (2 * 1) * ‖physicalFourier (0 : PhysicalL2) j‖ ^ 2) =
        fun _ => 0 := by
      funext j; simp only [physicalFourier_zero38]; simp
    unfold SobolevSquareSummable
    rw [this]; exact summable_zero
  have h := gap_localization_of_zeroLoc38 (0 : PhysicalL2) hu 0 le_rfl
    (fun τ _ => by simpa using molnarZeroLoc_zero38) n (by
      have := one_le_molnarBracket38 n; simp; linarith) l hl
  rw [molnarRadius_zero38] at h
  have := abs_nonneg (l - n * Real.pi)
  have h0 : |l - n * Real.pi| = 0 := le_antisymm h this
  linarith [abs_eq_zero.mp h0]

/-! ### The constant potential `u ≡ t` -/

theorem physicalFourier_const38 (t : ℝ) (n : ℤ) :
    physicalFourier (planeL2 0 (planeWaveCoeff38 0 0 t)) n = if n = 0 then (t : ℂ) else 0 := by
  rw [physicalFourier_planeL2, physicalFourier_planeField_sum]
  simp [planeWaveCoeff38, modeIndex, Pi.single_apply]

/-- `‖φ‖₁² = 2 t²` for the constant potential. -/
theorem molnarNormSq_const38 (t : ℝ) :
    molnarNormSq (planeL2 0 (planeWaveCoeff38 0 0 t)) = 2 * t ^ 2 := by
  unfold molnarNormSq
  rw [tsum_eq_single 0]
  · simp [physicalFourier_const38, molnarBracket38]
  · intro j hj
    simp [physicalFourier_const38, hj]

/-- The Fourier-side coefficients of the constant potential: `c(k) = t δ_{k,0}`. -/
def constCoeff38 (t : ℝ) : ℤ → ℂ := fun k => if k = 0 then (t : ℂ) else 0

theorem SW_constCoeff38 {t : ℝ} (ht : 0 ≤ t) :
    Mo2.SW (constCoeff38 t) = ENNReal.ofReal (t ^ 2) := by
  unfold Mo2.SW
  rw [tsum_eq_single 0]
  · simp [constCoeff38, Mo2.eW, ENNReal.ofReal_pow ht, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ht]
  · intro k hk; simp [constCoeff38, hk]

/-- The exact eigenvalue of the constant potential at the resonance `n ≥ 0`: `√(n²π² + t²)`. -/
def constLam38 (t : ℝ) (n : ℤ) : ℝ := Real.sqrt ((n : ℝ) ^ 2 * Real.pi ^ 2 + t ^ 2)

/-- The explicit solution of the Fourier system for the constant potential (`n ≥ 0`), a valid
`Mo2.Setup` in the range `16 t² ≤ ⟨n⟩`. -/
theorem constSetup38 {t : ℝ} (ht : 0 < t) {n : ℤ} (hn0 : 0 ≤ n) (hn : 16 * t ^ 2 ≤ 1 + |(n : ℝ)|) :
    Mo2.Setup n (constLam38 t n) (constCoeff38 t) (constCoeff38 t)
      (fun m => if m = n then 1 else 0)
      (fun m => if m = -n then (((constLam38 t n - n * Real.pi) / t : ℝ) : ℂ) else 0) (2 * t ^ 2) := by
  have hpi := Real.pi_pos
  have hn0' : (0 : ℝ) ≤ n := by exact_mod_cast hn0
  set lam := constLam38 t n with hlam
  have hlam2 : lam ^ 2 = (n : ℝ) ^ 2 * Real.pi ^ 2 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hlam0 : 0 ≤ lam := Real.sqrt_nonneg _
  have hge : (n : ℝ) * Real.pi ≤ lam := by
    apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg t]
  have hdiff : lam - n * Real.pi = t ^ 2 / (lam + n * Real.pi) := by
    have : 0 < lam + n * Real.pi := by
      have : 0 < lam := by
        rcases hlam0.lt_or_eq with h | h
        · exact h
        · exfalso; rw [← h] at hlam2; nlinarith [sq_nonneg ((n : ℝ) * Real.pi), sq_pos_of_pos ht]
      positivity
    field_simp
    nlinarith
  have hsmall : lam - n * Real.pi ≤ Real.pi / 2 := by
    rw [hdiff]
    rcases eq_or_lt_of_le hn0' with h0 | h1
    · rw [← h0] at hlam2 hn ⊢
      simp at hlam2 hn ⊢
      have : lam = t := by
        have h5 : lam ^ 2 = t ^ 2 := by simpa using hlam2
        nlinarith [hlam0]
      rw [this]
      have h7 : t ^ 2 / t = t := by field_simp
      rw [h7]
      have : t ≤ 1 / 4 := by nlinarith
      linarith [Real.pi_gt_three]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by exact_mod_cast h1)
      have h6 : t ^ 2 ≤ (1 + n) / 16 := by rw [abs_of_nonneg hn0'] at hn; linarith
      have hpi3 := Real.pi_gt_three
      have hpos : 0 < lam + n * Real.pi := by nlinarith
      rw [div_le_iff₀ hpos]
      have e1 : 2 * (n : ℝ) * Real.pi ≤ lam + n * Real.pi := by linarith
      calc t ^ 2 ≤ (1 + n) / 16 := h6
        _ ≤ n / 8 := by linarith
        _ ≤ Real.pi / 2 * (2 * n * Real.pi) := by
            have h9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
            calc (n : ℝ) / 8 ≤ 9 * n := by linarith
              _ ≤ Real.pi ^ 2 * n := mul_le_mul_of_nonneg_right h9 hn0'
              _ = _ := by ring
        _ ≤ Real.pi / 2 * (lam + n * Real.pi) := by gcongr
  have ha : (0 : ℝ) ≤ (lam - n * Real.pi) / t := div_nonneg (by linarith) ht.le
  refine ⟨?_, by positivity, ?_, by linarith, ?_, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg (by linarith)]; exact hsmall
  · rw [SW_constCoeff38 ht.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal; linarith
  · unfold Mo2.SW
    rw [tsum_eq_single n]
    · exact ENNReal.pow_ne_top (ENNReal.mul_ne_top (Mo2.eW_ne_top _) enorm_ne_top)
    · intro k hk; simp [hk]
  · unfold Mo2.SW
    rw [tsum_eq_single (-n)]
    · exact ENNReal.pow_ne_top (ENNReal.mul_ne_top (Mo2.eW_ne_top _) enorm_ne_top)
    · intro k hk; simp [hk]
  · intro m
    have hg : HasSum (fun l : ℤ => constCoeff38 t (m + l) *
        (if l = -n then (((lam - n * Real.pi) / t : ℝ) : ℂ) else 0))
        (constCoeff38 t (m + -n) * (((lam - n * Real.pi) / t : ℝ) : ℂ)) := by
      have := hasSum_single (-n) (f := fun l : ℤ => constCoeff38 t (m + l) *
        (if l = -n then (((lam - n * Real.pi) / t : ℝ) : ℂ) else 0)) (fun l hl => by simp [hl])
      simpa using this
    convert hg using 1
    by_cases hm : m = n
    · subst hm
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      simp only [Mo2.hF, constCoeff38, ite_true, add_neg_cancel, mul_one]
      push_cast
      field_simp
    · have : m + -n ≠ 0 := by omega
      simp [Mo2.hF, constCoeff38, hm, this]
  · intro m
    have hg : HasSum (fun l : ℤ => constCoeff38 t (m + l) * (if l = n then (1 : ℂ) else 0))
        (constCoeff38 t (m + n) * 1) := by
      have := hasSum_single n (f := fun l : ℤ => constCoeff38 t (m + l) *
        (if l = n then (1 : ℂ) else 0)) (fun l hl => by simp [hl])
      simpa using this
    convert hg using 1
    by_cases hm : m = -n
    · subst hm
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have hlam2' : (lam : ℂ) ^ 2 = (n : ℂ) ^ 2 * (Real.pi : ℂ) ^ 2 + (t : ℂ) ^ 2 := by
        exact_mod_cast hlam2
      simp only [Mo2.hF, constCoeff38, ite_true, neg_add_cancel, mul_one]
      push_cast
      field_simp
      linear_combination hlam2'
    · have : m + n ≠ 0 := by omega
      simp [Mo2.hF, constCoeff38, hm, this]

/-- **Probe (constant potential `u ≡ t`).**  `Mo2.molnar_ls_core` applied to the explicit
eigen-solution gives `|√(n²π² + t²) - nπ| ≤ 2t²/⟨n⟩ + 2t/⟨2n⟩` for `16 t² ≤ ⟨n⟩`
(closed gap `n ≥ 1`; for `n = 0` the left side is the endpoint `t` of the gap `(-t, t)`). -/
theorem probe_const_localization {t : ℝ} (ht : 0 < t) {n : ℤ} (hn0 : 0 ≤ n)
    (hn : 16 * t ^ 2 ≤ 1 + |(n : ℝ)|) :
    |constLam38 t n - n * Real.pi| ≤
      2 * t ^ 2 / (1 + |(n : ℝ)|) + 2 * t / (1 + |((2 * n : ℤ) : ℝ)|) := by
  have S := constSetup38 ht hn0 hn
  have h := Mo2.molnar_ls_core S (Or.inl ⟨n, by simp⟩)
  have e : Real.sqrt 2 * Real.sqrt (2 * t ^ 2) = 2 * t := by
    rw [← Real.sqrt_mul (by norm_num), show (2 : ℝ) * (2 * t ^ 2) = (2 * t) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rwa [e] at h

end

end NlsGge.GK38
