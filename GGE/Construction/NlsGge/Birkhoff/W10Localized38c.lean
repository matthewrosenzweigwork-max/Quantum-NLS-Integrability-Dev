import NlsGge.Birkhoff.W10Localized38b
import NlsGge.Birkhoff.W05ChargeSeries38

/-! # W10a, file 3 (W10.02): the cutoff `χ_R` and the exact head form of the localized integrand

Source: `paper/v2.tex` l.1635-1655. Conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`.

* `CutoffProfile38 χ`: v2's `χ : [0,∞) → [0,1]` continuous, nonincreasing, `= 1` on `[0,1]`, `= 0` on `[2,∞)`.
* `chiR38 χ R u = χ(‖𝓕u‖_{h²}/R)` (v2: "in Fourier coordinates `χ_R` is supported in a fixed `h²` ball";
  `= 0` when `𝓕u ∉ h²`, i.e. `χ(∞) = 0`).
* `locIntegrand38`: the integrand `F(𝓕⁻¹P_N x) χ_R(𝓕⁻¹P_N x) f_N(x)` of `D:eq:localized`.
* `Hv38`: the factor of the integrand that is NOT the new Gaussian quadratic part. With `v = P_N x ∈ V_N`,
  by `fN38_decomp` (W07) and the energy identity (W05) one has the exact identity (W10.02)
  `locIntegrand38 N x = Hv38 N (v) · exp(-(‖φ_N v‖² - ‖v‖²)/2)`, `φ_N v = v + P_N K(P_N v)`,
  where `Hv38 = F χ_R e^{-R_W} e^{-A((1-P_N)K(P_N x))}` and the nonnegative high Cameron-Martin energy
  `A((1-P_N)K(x_N))` is kept inside `Hv38`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.Ramer Filter Topology
open scoped ENNReal Real

/-- v2 l.1627-1629: `χ : [0,∞) → [0,1]` continuous, nonincreasing, `1` on `[0,1]`, `0` on `[2,∞)`. -/
structure CutoffProfile38 (χ : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn χ (Set.Ici 0)
  antitoneOn : AntitoneOn χ (Set.Ici 0)
  mem_Icc : ∀ t, 0 ≤ t → χ t ∈ Set.Icc (0 : ℝ) 1
  eq_one : ∀ t, 0 ≤ t → t ≤ 1 → χ t = 1
  eq_zero : ∀ t, 2 ≤ t → χ t = 0

open scoped Classical in
/-- `χ_R(u) = χ(‖𝓕 u‖_{h²}/R)` (Fourier coordinates; `0` if `𝓕 u ∉ h²`). -/
def chiR38 (χ : ℝ → ℝ) (R : ℝ) (u : PhysicalL2) : ℝ :=
  if h : fourierSeq38 u ∈ seqSobolev38 (((1 + 1 : ℕ)) : ℝ) then
    χ (‖carrierMk38 (((1 + 1 : ℕ)) : ℝ) (fourierSeq38 u) h‖ / R) else 0

section Chi

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem chiR38_physOfE38 (χ : ℝ → ℝ) (R : ℝ) (y : ECarrier38 c s) :
    chiR38 χ R (physOfE38 c s y) = χ (‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) y‖ / R) := by
  have hmem : fourierSeq38 (physOfE38 c s y) ∈ seqSobolev38 (((1 + 1 : ℕ)) : ℝ) := by
    rw [fourierSeq38_physOfE38]
    exact seqE38_subset_seqSobolev38 c s _ (eCoe38_mem c s y)
  unfold chiR38
  simp only [hmem, ↓reduceDIte]
  congr 3
  apply carrierExt38
  funext n
  rw [carrierCoe38_mk, carrierCoe_eToSob38, fourierSeq38_physOfE38]

variable {χ : ℝ → ℝ} {R : ℝ}

theorem continuous_chiR38_physOfE38 (hχ : CutoffProfile38 χ) (hR : 0 < R) :
    Continuous (fun y : ECarrier38 c s => chiR38 χ R (physOfE38 c s y)) := by
  simp only [chiR38_physOfE38]
  refine hχ.continuousOn.comp_continuous ?_ (fun y => ?_)
  · exact ((continuous_eToSob38 c s _).norm).div_const R
  · exact div_nonneg (norm_nonneg _) hR.le

theorem chiR38_mem_Icc (hχ : CutoffProfile38 χ) (hR : 0 < R) (u : PhysicalL2) :
    chiR38 χ R u ∈ Set.Icc (0 : ℝ) 1 := by
  unfold chiR38
  split_ifs with h
  · exact hχ.mem_Icc _ (div_nonneg (norm_nonneg _) hR.le)
  · exact ⟨le_refl _, zero_le_one⟩

theorem chiR38_physOfE38_eq_zero (hχ : CutoffProfile38 χ) (hR : 0 < R) (y : ECarrier38 c s)
    (hy : 2 * R ≤ ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) y‖) :
    chiR38 χ R (physOfE38 c s y) = 0 := by
  rw [chiR38_physOfE38]
  exact hχ.eq_zero _ (by rw [le_div_iff₀ hR]; linarith)

end Chi

/-- The integrand `F(𝓕⁻¹P_N x) χ_R(𝓕⁻¹P_N x) f_N(x)` of `D:eq:localized`. -/
def locIntegrand38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ}
    (χ : ℝ → ℝ) (R : ℝ) (F : PhysicalL2 → ℝ) (N : ℕ) (x : FullWeightedHilbert c s) : ℝ :=
  F (physOfE38 c s (projE38 c s N x)) * chiR38 χ R (physOfE38 c s (projE38 c s N x)) *
    fN38 c s N x

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

/-- The head factor `F χ_R e^{-R_W} e^{-A((1-P_N)K)}` of the transformed integrand
(v2 `D:eq:localtransformed`, without the Jacobian and the new Gaussian quadratic part). -/
def Hv38 (hs1 : s ≤ 1) (χ : ℝ → ℝ) (R : ℝ) (F : PhysicalL2 → ℝ) (N : ℕ)
    (v : actualCMHead c N) : ℝ :=
  F (physOfE38 c s (headToE c s N v)) * chiR38 χ R (physOfE38 c s (headToE c s N v)) *
    Real.exp (-(remainder38 c.val (physOfE38 c s (headToE c s N v)))) *
    Real.exp (-(‖B.KW06_38 O c hs1 (headToE c s N v) -
      ((cmTrunc c N (B.KW06_38 O c hs1 (headToE c s N v)) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2))

theorem norm_TNfin38_headPt (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) :
    ‖B.TNfin38 O c hs1 N (headPt c N (coordE c s x))‖ =
      ‖(headPt c N (coordE c s x) : ActualCM c) +
        ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ := by
  have e : truncField c s (B.KW06_38 O c hs1) N (headPt c N (coordE c s x)) =
      cmTrunc c N (B.yN38 O c hs1 N x) := by
    unfold truncField yN38
    rw [headToE_headPt_projE38_W07]
  show ‖(headPt c N (coordE c s x) +
      truncField c s (B.KW06_38 O c hs1) N (headPt c N (coordE c s x)) : actualCMHead c N)‖ = _
  rw [e]; rfl

/-- **W10.02 (exact form).** `F χ_R f_N = Hv · exp(-(‖φ_N v‖² - ‖v‖²)/2)` with `v = P_N x`, using the
complete trace identity (`fN38_decomp`). -/
theorem locIntegrand38_eq (hs' : s < 3 / 4) (hs1 : s ≤ 1) (χ : ℝ → ℝ) (R : ℝ) (F : PhysicalL2 → ℝ)
    (N : ℕ) (x : FullWeightedHilbert c s) :
    locIntegrand38 c χ R F N x =
      B.Hv38 O c hs1 χ R F N (headPt c N (coordE c s x)) *
        Real.exp (-(‖B.TNfin38 O c hs1 N (headPt c N (coordE c s x))‖ ^ 2 -
          ‖(headPt c N (coordE c s x) : actualCMHead c N)‖ ^ 2) / 2) := by
  unfold locIntegrand38 Hv38
  rw [B.fN38_decomp O c hs' hs1 N x, headToE_headPt_projE38_W07, B.norm_TNfin38_headPt O c hs1]
  have hy : B.yN38 O c hs1 N x = B.KW06_38 O c hs1 (projE38 c s N x) := rfl
  rw [hy]
  have hn2 : ‖(headPt c N (coordE c s x) : actualCMHead c N)‖ =
      ‖(headPt c N (coordE c s x) : ActualCM c)‖ := rfl
  rw [hn2]
  ring

theorem continuous_Hv38 (hs' : s < 3 / 4) (hs1 : s ≤ 1) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) (N : ℕ) :
    Continuous (B.Hv38 O c hs1 χ R F N) := by
  have hh : Continuous (headToE c s N) := (headToE c s N).continuous
  have hK : Continuous (B.KW06_38 O c hs1) :=
    continuousOn_univ.1 (B.analytic_KW06_38 O c hs1).continuousOn
  have hrem := B.continuous_remainder_physOfE38 c s O hs'
  have hchi := continuous_chiR38_physOfE38 c s hχ hR
  unfold Hv38
  have hk : Continuous (fun v : actualCMHead c N => B.KW06_38 O c hs1 (headToE c s N v)) :=
    hK.comp hh
  have hk2 : Continuous (fun v : actualCMHead c N =>
      ((cmTrunc c N (B.KW06_38 O c hs1 (headToE c s N v)) : actualCMHead c N) : ActualCM c)) :=
    continuous_subtype_val.comp ((cmTrunc c N).continuous.comp hk)
  refine (((hF.comp hh).mul (hchi.comp hh)).mul (hrem.comp hh).neg.rexp).mul ?_
  exact (((hk.sub hk2).norm.pow 2).div_const 2).neg.rexp

theorem abs_Hv38_le_chi (hs' : s < 3 / 4) (hs1 : s ≤ 1) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) (N : ℕ) (v : actualCMHead c N) :
    |B.Hv38 O c hs1 χ R F N v| ≤ M * chiR38 χ R (physOfE38 c s (headToE c s N v)) := by
  unfold Hv38
  have hrem : 0 ≤ remainder38 c.val (physOfE38 c s (headToE c s N v)) :=
    (B.finiteGap_approximation_PM_W05_38 c s O hs' (headToE c s N v)).2.2.2
  have h1 : Real.exp (-(remainder38 c.val (physOfE38 c s (headToE c s N v)))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith)
  have h2 : Real.exp (-(‖B.KW06_38 O c hs1 (headToE c s N v) -
      ((cmTrunc c N (B.KW06_38 O c hs1 (headToE c s N v)) : actualCMHead c N) : ActualCM c)‖ ^ 2 /
        2)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have := sq_nonneg ‖B.KW06_38 O c hs1 (headToE c s N v) -
      ((cmTrunc c N (B.KW06_38 O c hs1 (headToE c s N v)) : actualCMHead c N) : ActualCM c)‖
                              linarith)
  have hc := chiR38_mem_Icc hχ hR (physOfE38 c s (headToE c s N v))
  have hF := hM (headToE c s N v)
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc.1, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _)]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hF
  calc _ ≤ M * chiR38 χ R (physOfE38 c s (headToE c s N v)) * 1 * 1 := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hF hc.1) h1
          (Real.exp_pos _).le (mul_nonneg hM0 hc.1)) h2 (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hM0 hc.1) zero_le_one)
    _ = _ := by ring

theorem abs_Hv38_le (hs' : s < 3 / 4) (hs1 : s ≤ 1) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) (N : ℕ) (v : actualCMHead c N) :
    |B.Hv38 O c hs1 χ R F N v| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine (B.abs_Hv38_le_chi O c hs' hs1 hχ hR F M hM N v).trans ?_
  have hc := chiR38_mem_Icc hχ hR (physOfE38 c s (headToE c s N v))
  calc _ ≤ M * 1 := mul_le_mul_of_nonneg_left hc.2 hM0
    _ = M := mul_one M

theorem Hv38_eq_zero (hs1 : s ≤ 1) {χ : ℝ → ℝ} {R : ℝ} (hχ : CutoffProfile38 χ) (hR : 0 < R)
    (F : PhysicalL2 → ℝ) (N : ℕ) (v : actualCMHead c N) (hv : 2 * R ≤ hn2V38 c s N v) :
    B.Hv38 O c hs1 χ R F N v = 0 := by
  unfold Hv38
  rw [chiR38_physOfE38_eq_zero c s hχ hR _ hv]
  ring

end BirkhoffInput38

end NlsGge.Birkhoff
end
