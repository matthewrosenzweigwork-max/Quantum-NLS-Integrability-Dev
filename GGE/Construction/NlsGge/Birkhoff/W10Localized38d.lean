import NlsGge.Birkhoff.W10Localized38c

/-! # W10a, file 4 (W10.01-W10.04): the localized integral as a Gaussian integral of the transformed integrand

Source: `paper/v2.tex` l.1644-1663. Conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`,
for `1/2 < s < 3/4` and `c : BoundedCoefficients`.

`PsiN38 N` is v2's transformed integrand `D:eq:localtransformed` as a function of the target
`z_N = P_N z ∈ V_N`: it is `0` outside `φ_N(U_N)` and, with `x = (φ_N|_{U_N})⁻¹ z_N`,

`Ψ_N(z_N) = F(𝓕⁻¹x) χ_R(𝓕⁻¹x) / |det Dφ_N(x)| · exp[-R_W(𝓕⁻¹x) - A((Id-P_N)K(x))]`.

`W10a_localChange38`: for all large `N`,
(W10.01) `∫ F χ_R(𝓕⁻¹P_N x) f_N dγ_W = ∫ Ψ_N(P_N z) dγ_W(z)` (change of variables on the open ball
`U_N(2R+1)`, strictly larger than the support radius `2R`; the coupling `z_N = P_N z`, W10.04);
(W10.03) `|Ψ_N| ≤ 2 sup|F|` (reciprocal Jacobian `≤ 2`, both exponentials `≤ 1`);
(W10.02 is the identity `locIntegrand38_eq` of file 3) and `Ψ_N` is measurable.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.Ramer Filter Topology
open scoped ENNReal Real

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

/-- The transformed integrand `D:eq:localtransformed`, as a function of `z_N ∈ V_N`. -/
def PsiN38 (hs1 : s ≤ 1) (χ : ℝ → ℝ) (R : ℝ) (F : PhysicalL2 → ℝ) (N : ℕ) :
    actualCMHead c N → ℝ :=
  localPush38 (B.TNfin38 O c hs1 N) (ballU38 c s N (2 * R + 1))
    (fun x => B.Hv38 O c hs1 χ R F N x / |(fderiv ℝ (B.TNfin38 O c hs1 N) x).det|)

theorem continuous_TNfin38 (hs1 : s ≤ 1) (N : ℕ) : Continuous (B.TNfin38 O c hs1 N) :=
  continuous_iff_continuousAt.2 fun v => (B.hasFDerivAt_TNfin38 O c hs1 N v).continuousAt

theorem hasFDerivWithinAt_TNfin38 (hs1 : s ≤ 1) (N : ℕ) (U : Set (actualCMHead c N))
    (x : actualCMHead c N) :
    HasFDerivWithinAt (B.TNfin38 O c hs1 N) (fderiv ℝ (B.TNfin38 O c hs1 N) x) U x :=
  (B.hasFDerivAt_TNfin38 O c hs1 N x).differentiableAt.hasFDerivAt.hasFDerivWithinAt

theorem measurable_PsiN38 (hs' : s < 3 / 4) (hs1 : s ≤ 1) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (N : ℕ) (hinj : Set.InjOn (B.TNfin38 O c hs1 N) (ballU38 c s N (2 * R + 1))) :
    Measurable (B.PsiN38 O c hs1 χ R F N) := by
  have hdet : Measurable (fun x : actualCMHead c N => (fderiv ℝ (B.TNfin38 O c hs1 N) x).det) :=
    ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ _)
  have hH := (B.continuous_Hv38 O c hs' hs1 hχ hR F hF N).measurable
  refine measurable_localPush38 _ (fderiv ℝ (B.TNfin38 O c hs1 N)) _
    (measurableSet_ballU38 c s N _) (fun x _ => B.hasFDerivWithinAt_TNfin38 O c hs1 N _ x) hinj _ ?_
  exact (hH.comp measurable_subtype_coe).div
    (continuous_abs.measurable.comp (hdet.comp measurable_subtype_coe))

/-- **W10.03.** On `U_N`, where `|det Dφ_N|⁻¹ ≤ 2`: `|Ψ_N| ≤ 2 sup|F|` everywhere. -/
theorem abs_PsiN38_le (hs' : s < 3 / 4) (hs1 : s ≤ 1) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) (N : ℕ)
    (hdet : ∀ v ∈ ballU38 c s N (2 * R + 1),
      (fderiv ℝ (B.TNfin38 O c hs1 N) v).det ≠ 0 ∧
        |(fderiv ℝ (B.TNfin38 O c hs1 N) v).det|⁻¹ ≤ 2)
    (hinj : Set.InjOn (B.TNfin38 O c hs1 N) (ballU38 c s N (2 * R + 1))) (z : actualCMHead c N) :
    |B.PsiN38 O c hs1 χ R F N z| ≤ 2 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  by_cases hz : z ∈ B.TNfin38 O c hs1 N '' ballU38 c s N (2 * R + 1)
  · obtain ⟨x, hx, rfl⟩ := hz
    unfold PsiN38
    rw [localPush38_apply _ _ hinj _ x hx, abs_div, abs_abs]
    obtain ⟨hd0, hd2⟩ := hdet x hx
    have hpos : 0 < |(fderiv ℝ (B.TNfin38 O c hs1 N) x).det| := abs_pos.2 hd0
    rw [div_le_iff₀ hpos]
    have h1 := B.abs_Hv38_le O c hs' hs1 hχ hR F M hM N x
    have h2 : 1 ≤ 2 * |(fderiv ℝ (B.TNfin38 O c hs1 N) x).det| := by
      have := mul_le_mul_of_nonneg_left hd2 hpos.le
      rw [mul_inv_cancel₀ hpos.ne'] at this
      linarith
    nlinarith
  · unfold PsiN38
    rw [localPush38_eq_zero _ _ _ z hz, abs_zero]
    linarith

/-- **W10a (W10.01, W10.02, W10.03, W10.04).** For `1/2 < s < 3/4`, every cutoff profile `χ`, `R > 0`
and every `F` that is bounded and continuous on `𝓕⁻¹ E_s` (topology of `E_s`), for all large `N`:
the localized integral equals the Gaussian integral, over the coupling `z_N = P_N z`, `z ∼ γ_W`, of the
transformed integrand `Ψ_N`, which is measurable and bounded by `2 sup|F|`. -/
theorem W10a_localChange38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Set.InjOn (B.TNfin38 O c (by linarith : s ≤ 1) N) (ballU38 c s N (2 * R + 1)) ∧
      (∀ v ∈ ballU38 c s N (2 * R + 1),
        (fderiv ℝ (B.TNfin38 O c (by linarith : s ≤ 1) N) v).det ≠ 0 ∧
          |(fderiv ℝ (B.TNfin38 O c (by linarith : s ≤ 1) N) v).det|⁻¹ ≤ 2) ∧
      Measurable (B.PsiN38 O c (by linarith : s ≤ 1) χ R F N) ∧
      (∀ z, |B.PsiN38 O c (by linarith : s ≤ 1) χ R F N z| ≤ 2 * M) ∧
      ∫ x, locIntegrand38 c χ R F N x ∂(fullWeightedSequenceGaussian c s) =
        ∫ x, B.PsiN38 O c (by linarith : s ≤ 1) χ R F N (headPt c N (coordE c s x))
          ∂(fullWeightedSequenceGaussian c s) := by
  have hs1 : s ≤ 1 := by linarith
  obtain ⟨N₁, hN₁⟩ := B.eventually_injOn_ballU38 O c hs1 (2 * R + 1)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (B.eventually_det_ballU38 O c hs1 (2 * R + 1)).1
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hinj := hN₁ N (le_trans (le_max_left _ _) hN)
  have hdet := hN₂ N (le_trans (le_max_right _ _) hN)
  have hmeas := B.measurable_PsiN38 O c hs' hs1 hχ hR F hF N hinj
  refine ⟨hinj, hdet, hmeas, B.abs_PsiN38_le O c hs' hs1 hχ hR F M hM N hdet hinj, ?_⟩
  set φ := B.TNfin38 O c hs1 N with hφ
  set G : actualCMHead c N → ℝ := fun v => B.Hv38 O c hs1 χ R F N v *
    Real.exp (-(‖φ v‖ ^ 2 - ‖v‖ ^ 2) / 2) with hG
  have hGc : Continuous G := by
    have h1 := B.continuous_Hv38 O c hs' hs1 hχ hR F hF N
    have h2 := B.continuous_TNfin38 O c hs1 N
    exact h1.mul ((((h2.norm.pow 2).sub (continuous_norm.pow 2)).neg).div_const 2).rexp
  have hL : ∫ x, locIntegrand38 c χ R F N x ∂(fullWeightedSequenceGaussian c s) =
      ∫ v, G v ∂(finiteStdGaussian (actualCMHead c N)) := by
    have e1 : ∀ x : FullWeightedHilbert c s, locIntegrand38 c χ R F N x =
        G (headPt c N (coordE c s x)) := fun x => B.locIntegrand38_eq O c hs' hs1 χ R F N x
    simp only [e1]
    rw [integral_comp_coordE c s hs (f := fun z => G (headPt c N z))
      ((hGc.measurable.comp (measurable_headPt c N)).aestronglyMeasurable)]
    exact integral_comp_headPt c N G hGc
  rw [hL]
  have hcov := localCoV_gaussian38 φ (fderiv ℝ φ) (ballU38 c s N (2 * R + 1))
    (measurableSet_ballU38 c s N _) (fun x _ => B.hasFDerivWithinAt_TNfin38 O c hs1 N _ x) hinj
    (fun x hx => (hdet x hx).1) (B.Hv38 O c hs1 χ R F N)
    (fun v hv => B.Hv38_eq_zero O c hs1 hχ hR F N v (by
      have : ¬ (hn2V38 c s N v < 2 * R + 1) := hv
      linarith))
  rw [show (fun v => G v) = fun v => B.Hv38 O c hs1 χ R F N v *
      Real.exp (-(‖φ v‖ ^ 2 - ‖v‖ ^ 2) / 2) from rfl, hcov]
  have hmeasΨ : Measurable (fun z => B.PsiN38 O c hs1 χ R F N (headPt c N z)) :=
    hmeas.comp (measurable_headPt c N)
  change ∫ z, B.PsiN38 O c hs1 χ R F N z ∂(finiteStdGaussian (actualCMHead c N)) = _
  rw [integral_comp_coordE c s hs hmeasΨ.aestronglyMeasurable, ← headPt_map c N,
    integral_map (measurable_headPt c N).aemeasurable hmeas.aestronglyMeasurable]

end BirkhoffInput38

end NlsGge.Birkhoff
end
