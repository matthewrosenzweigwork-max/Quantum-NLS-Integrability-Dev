import QuantumNLS.Prop025OKer
import QuantumNLS.Prop025OEigen
import QuantumNLS.R52CFCoh
import QuantumNLS.R52CFDeriv
import QuantumNLS.Q07BUniformCutsR16
import QuantumNLS.Q07ContourApplicationR16
import QuantumNLS.Q07IntegratedHessiansR16

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O5b-1:
**eq:MP-window-gradient, eq:MP-action-gradient and eq:MP-full-gradient-agreement at the base profile**
(source lines 589-633, "Identification of the whole classical vector field").

"Let `h_{r,a}` be the classical window Hamiltonian `∫_{(-a,a)} x^r dM_{κ,v}(x)`.  Its contour formula and the
action contour formula are identities on neighborhoods of the smooth isospectral profiles ... their full real
differentials satisfy `dh_{r,a}(v)[w] = -(2πκ)⁻¹ Re ∮_{Γ_a} z^r ds_κ(z;v)[w]/D(z) dz`,
`da_n(v)[w] = -(2πκ)⁻¹ Re ∮_{Γ_n} ds_κ(z;v)[w]/D(z) dz` ... At each point of that trajectory [these] give
`dF_{a,t,θ} = d(Σ_r t_r h_{r,a} + Σ_n θ_n a_n)` as full real physical differentials."

This module proves the identity at the base profile `u` itself (the transport to the whole phase torus is stage
O5b-2):
* `rectContour_eq`: the Q07 rectangle contour is `LabelExactPeriod.rectIntegral` on `[-a,a] × [-h,h]`;
* `window_path`: on a Sobolev class, for every large regular cut `a = a_ℓ`, the full Cauchy field restricted to
  `Γ_a` has one real-analytic germ in the uniform norm (accepted `exists_analytic_regular_path`, with the gap and
  regularity from the accepted `q07Buniformcuts` / `uniform_field_operators`);
* **`window_fderiv`** (eq:MP-window-gradient, the scalar window differential of DEF-044 clause (3)): the full real
  differential of the joint window Hamiltonian `Σ_r t_r h_{r,a}` (`Prop025OInputs.windowFamily`, full-mass measure)
  is `-(2πκ)⁻¹ Re ∮_{Γ_a} p_t(z) ds(z;u)[k]/D_u(z) dz`, `p_t = Σ_r t_r z^r`, `D_u` the denominator of `u`;
* `coh_mix_eq`: the coherent energy of the summed kernels `Prop025OKer.mixK` is the frozen-denominator functional
  `F_{a,t,θ}` = window rectangle functional + `Σ_i θ_i ×` fixed rectangle functionals;
* **`grad_at`** (eq:MP-full-gradient-agreement at `u`):
  `dF_{a,t,θ}(u) = d(Σ_r t_r h_{r,a})(u) + Σ_i θ_i dI_{n_i}(u)`, for every large regular cut, every label family and
  every angle vector, with the action differential of the accepted `R52CFDeriv.fixed_rectangle_neighborhood`.
No hypothesis is added; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory Filter Set Metric Complex

namespace QuantumNLS.Prop025OGrad
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Extrapolation (Gfull)
open QuantumNLS.PeriodReconstructionCore (Df Af ef)
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ rectPieces polyT continuous_polyT continuous_zθ continuous_uθ)
open QuantumNLS.MPFixedContour (rectGen rectGen_mem_Gam)
open QuantumNLS.Prop026Uniform (rectFamily)
open QuantumNLS.Prop025OPhase (mixedPieces xmS xpS)
open QuantumNLS.Prop025OKer (mixK mixD)
open QuantumNLS.R52CFKernels (kerA physK)
open QuantumNLS.R52CFCoh (lam lam_hasFDerivAt)
open QuantumNLS.Prop010RectangleDifferentialR17 (Boundary boundaryIntegral boundaryIntegral_eq)
open QuantumNLS.RootCauchyFullBracketR8 (G)
open QuantumNLS.RootCauchyJointR9 (Regular)
open QuantumNLS.RootMassInvolutionR8 (mass)
open QuantumNLS.LabelExactPeriod (rectIntegral)
open QuantumNLS.PROP017UniformN (cutSeq)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### 1. Elementary identifications -/

theorem rectContour_eq (a h : ℝ) (f : ℂ → ℂ) :
    PropagationContour.rectContour a h f = rectIntegral f (-a) a h := by
  unfold PropagationContour.rectContour rectIntegral
  have e1 : (fun x : ℝ => f ((x : ℂ) - (h : ℂ) * I)) = fun x : ℝ => f ((x : ℂ) + ((-h : ℝ) : ℂ) * I) := by
    funext x; congr 1; push_cast; ring
  rw [e1, intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  simp only [smul_eq_mul]
  ring

/-- The frozen denominator of `u` is the source difference `e^{iκG} - e^{izL}e^{-iκG}`. -/
theorem Df_eq (hκ : 0 < κ) (u : L2T L) (z : ℂ) :
    Df L κ (fun w => G hκ w u) z =
      ScalarLogBranchR10.difference (RootScalarPeriodR10.exponential L z) (RootScalarPeriodR10.exponent hκ u z) := by
  simp only [Df, Af, ScalarLogBranchR10.difference, RootScalarPeriodR10.exponent,
    ← Prop010CutoffExistenceR11.ef_exp]

/-- At a regular point the frozen denominator is continuous and nonzero. -/
theorem D_regular (hκ : 0 < κ) (u : L2T L) {z : ℂ} (hz : Regular κ (u, z)) :
    ContinuousAt (fun w => (Df L κ (fun w => G hκ w u) w)⁻¹) z ∧ Df L κ (fun w => G hκ w u) z ≠ 0 := by
  have hne : Df L κ (fun w => G hκ w u) z ≠ 0 := by
    rw [Df_eq]; exact RootScalarPeriodR10.difference_ne hκ u z hz
  have hc : ContinuousAt (fun w => Q07LogDifferentialsR16.logarithm hκ w u) z :=
    (Q07LogDifferentialsR16.logarithm_spectral hκ hz).continuousAt
  have hD : ContinuousAt (fun w => Df L κ (fun w => G hκ w u) w) z := by
    show ContinuousAt (fun w => Complex.exp (Q07LogDifferentialsR16.logarithm hκ w u) -
      ef L w / Complex.exp (Q07LogDifferentialsR16.logarithm hκ w u)) z
    have hef : ContinuousAt (fun w => ef L w) z := by unfold ef; fun_prop
    exact (hc.cexp).sub (hef.div hc.cexp (Complex.exp_ne_zero _))
  exact ⟨hD.inv₀ hne, hne⟩

/-- The `ds/D = iκ dG` identity at a regular point. -/
theorem dsD_eq (hκ : 0 < κ) (u k : L2T L) {z : ℂ} (hz : Regular κ (u, z)) :
    fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k / Df L κ (fun w => G hκ w u) z =
      (I * (κ : ℂ)) * fderiv ℝ (G hκ z) u k := by
  rw [Df_eq]
  exact (Prop010ClassicalR10.exponent_differential hκ u k z hz).symm

theorem mem_GammaN {a h : ℝ} {z : ℂ} (hz : z ∈ Gam (-a) a h) : z ∈ ResolventNeighborhood.GammaN a h := by
  rcases hz with ⟨hre, him⟩ | ⟨him, hre⟩
  · refine Or.inr ⟨by rcases him with h1 | h1 <;> [right; left] <;> exact h1, ?_⟩
    rw [abs_le]; exact ⟨hre.1, hre.2⟩
  · refine Or.inl ⟨by rcases hre with h1 | h1 <;> [right; left] <;> exact h1, ?_⟩
    rw [abs_le]; exact ⟨him.1, him.2⟩

/-! ### 2. The window rectangle: analytic Cauchy germ and the window differential -/

/-- The full Cauchy field on `Γ_a` has one real-analytic germ in the uniform norm, at every point of a Sobolev
class, for every large regular cut; every point of `Γ_a` is regular. -/
theorem window_path (hκ : 0 < κ) {s B h : ℝ} (hs : 0 < s) (hh : 0 < h) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → 1 ≤ cutSeq L l ∧ ∀ u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B,
      (∀ z ∈ Gam (-(cutSeq L l)) (cutSeq L l) h, Regular κ (u, z)) ∧
      ∃ H : L2T L → C(Boundary (-(cutSeq L l)) (cutSeq L l) h, ℂ),
        AnalyticAt ℝ H u ∧ ∀ᶠ v : L2T L in 𝓝 u, ∀ z, H v z = G hκ z.1 v := by
  have hL : 0 < L := Fact.out
  obtain ⟨-, η, hη, l1, C, -, hd⟩ := Q07BUniformCutsR16.q07Buniformcuts (L := L) hκ hs B hh 0
  obtain ⟨δ, hδ, l2, A1, A2, -, -, hops⟩ :=
    Q07ContourApplicationR16.uniform_field_operators (L := L) hκ hs B hh
  refine ⟨max l1 l2, fun l hl => ?_⟩
  have hl1 := (le_max_left l1 l2).trans hl
  have hl2 := (le_max_right l1 l2).trans hl
  obtain ⟨ha1, hall⟩ := hd l hl1
  refine ⟨ha1, fun u hu => ?_⟩
  set a := cutSeq L l with ha
  refine ⟨fun z hz => (hops l hl2 u hu u (by simpa using hδ) z (mem_GammaN hz)).1, ?_⟩
  let Z : C(Boundary (-a) a h, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hZ : LipschitzWith 1 Z := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [NNReal.coe_one, one_mul]
    exact le_rfl
  have hreg : ∀ᶠ v : L2T L in 𝓝 u, ∀ z : Boundary (-a) a h, Regular κ (v, Z z) := by
    filter_upwards [ball_mem_nhds u hδ] with v hv z
    exact (hops l hl2 u hu v (by rw [← dist_eq_norm]; exact hv) z.1 (mem_GammaN z.2)).1
  have hmass : ∀ᶠ v : L2T L in 𝓝 u,
      (PhysicalQuantumMeasure.measure hκ v univ).toReal ≤ (‖u‖ + 1) ^ 2 := by
    filter_upwards [ball_mem_nhds u one_pos] with v hv
    rw [PhysicalQuantumMeasure.measure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
    have h1 : ‖v‖ ≤ ‖u‖ + 1 := by
      have := norm_le_norm_add_norm_sub' v u
      rw [mem_ball, dist_eq_norm] at hv
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hgap : ∀ᶠ v : L2T L in 𝓝 u,
      ∀ᵐ q : ℝ ∂(PhysicalQuantumMeasure.measure hκ v), ∀ z : Boundary (-a) a h,
        min (1 / L) h ≤ ‖Z z - (q : ℂ)‖ := by
    filter_upwards [ball_mem_nhds u hη] with v hv
    have hv' : ‖v - u‖ < η := by rw [← dist_eq_norm]; exact hv
    obtain ⟨hcuts, -⟩ := hall u hu v hv'
    have h0 := (hcuts a (Or.inl rfl)).2
    have h1 := (hcuts (-a) (Or.inr rfl)).2
    rw [← PhysicalL2Normalization.measure_eq_Mmeas hκ v] at h0 h1
    have e0 : ∀ᵐ q : ℝ ∂(PhysicalQuantumMeasure.measure hκ v), q ∉ Ioo (a - 1 / L) (a + 1 / L) :=
      ae_iff.mpr (by simpa only [not_not, setOf_mem_eq] using h0)
    have e1 : ∀ᵐ q : ℝ ∂(PhysicalQuantumMeasure.measure hκ v), q ∉ Ioo (-a - 1 / L) (-a + 1 / L) :=
      ae_iff.mpr (by simpa only [not_not, setOf_mem_eq] using h1)
    filter_upwards [e0, e1] with q hq0 hq1 z
    have hz := z.2
    change min (1 / L) h ≤ ‖z.1 - (q : ℂ)‖
    rcases hz with ⟨-, him⟩ | ⟨-, hre⟩
    · have hi : |(z.1 - (q : ℂ)).im| = h := by
        rcases him with h2 | h2 <;> simp [h2, abs_of_pos hh]
      exact (min_le_right _ _).trans ((le_of_eq hi.symm).trans (Complex.abs_im_le_norm _))
    · have hr : 1 / L ≤ |(z.1 - (q : ℂ)).re| := by
        simp only [Complex.sub_re, Complex.ofReal_re]
        rcases hre with h2 | h2
        · rw [h2]
          by_contra hc
          push_neg at hc
          rw [abs_lt] at hc
          exact hq1 ⟨by linarith [hc.2], by linarith [hc.1]⟩
        · rw [h2]
          by_contra hc
          push_neg at hc
          rw [abs_lt] at hc
          exact hq0 ⟨by linarith [hc.2], by linarith [hc.1]⟩
      exact (min_le_left _ _).trans (hr.trans (Complex.abs_re_le_norm _))
  exact RootScalarDifferentialR10.exists_analytic_regular_path hκ Z hZ u
    (lt_min (one_div_pos.mpr hL) hh) (sq_nonneg _) hgap hmass hreg

/-- **eq:MP-window-gradient** for the joint window Hamiltonian `Σ_{r∈R} t_r h_{r,a}` at a point of a Sobolev
class: full real differential with the denominator of the point itself. -/
theorem window_fderiv (hκ : 0 < κ) {s B h : ℝ} (hs : 0 < s) (hh : 0 < h) (R : Finset ℕ) (t : ℕ → ℝ) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → 1 ≤ cutSeq L l ∧ ∀ u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B,
      (∀ z ∈ Gam (-(cutSeq L l)) (cutSeq L l) h, Regular κ (u, z)) ∧
      DifferentiableAt ℝ (Prop025OInputs.windowFamily (L := L) κ R t (cutSeq L l)) u ∧
      ∀ k : L2T L, fderiv ℝ (Prop025OInputs.windowFamily (L := L) κ R t (cutSeq L l)) u k =
        -(2 * Real.pi * κ)⁻¹ * (rectIntegral (fun z => polyT R t z *
          (fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k / Df L κ (fun w => G hκ w u) z))
          (-(cutSeq L l)) (cutSeq L l) h).re := by
  obtain ⟨l1, hpath⟩ := window_path (L := L) hκ (B := B) hs hh
  have hq := fun r : ℕ => Q07BUniformCutsR16.q07Buniformcuts (L := L) hκ hs B hh r
  choose hstrip η hη lr C hC hd using hq
  refine ⟨max l1 (R.sup lr), fun l hl => ?_⟩
  have hl1 := (le_max_left _ _).trans hl
  have hlr : ∀ r ∈ R, lr r ≤ l := fun r hr => (Finset.le_sup hr).trans ((le_max_right _ _).trans hl)
  set a := cutSeq L l with ha
  obtain ⟨ha1, hp⟩ := hpath l hl1
  refine ⟨ha1, fun u hu => ?_⟩
  obtain ⟨hregu, H, hH, hHe⟩ := hp u hu
  have hab : -a ≤ a := by linarith
  set T := boundaryIntegral hab hh.le with hT
  let cr : ℕ → C(Boundary (-a) a h, ℂ) := fun r =>
    ⟨fun z => z.1 ^ r * (I * (κ : ℂ)), (continuous_subtype_val.pow r).mul continuous_const⟩
  let c : C(Boundary (-a) a h, ℂ) := ∑ r ∈ R, t r • cr r
  have hc : ∀ z : Boundary (-a) a h, c z = polyT R t z.1 * (I * (κ : ℂ)) := by
    intro z
    simp only [c, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply, cr,
      ContinuousMap.coe_mk, polyT, Finset.sum_mul, Complex.real_smul]
    refine Finset.sum_congr rfl fun r _ => by ring
  let Λ : C(Boundary (-a) a h, ℂ) →L[ℝ] ℝ :=
    Complex.reCLM.comp (T.comp (ContinuousLinearMap.mul ℝ C(Boundary (-a) a h, ℂ) c))
  -- the window Hamiltonian is the contour functional near `u`
  have hnear : ∀ᶠ v : L2T L in 𝓝 u, ∀ r ∈ R, ‖v - u‖ < η r := by
    have hR : ∀ r ∈ R, ∀ᶠ v : L2T L in 𝓝 u, ‖v - u‖ < η r := fun r _ => by
      filter_upwards [ball_mem_nhds u (hη r)] with v hv
      rw [← dist_eq_norm]; exact hv
    exact (Finset.eventually_all R).mpr hR
  have heq : Prop025OInputs.windowFamily (L := L) κ R t a =ᶠ[𝓝 u]
      fun v => -(1 / (2 * Real.pi * κ)) * Λ (H v) := by
    filter_upwards [hnear, hHe] with v hv hHv
    have hr : ∀ r ∈ R, Prop025OInputs.windowHam (L := L) κ r a v =
        -(1 / (2 * Real.pi * κ)) * (T (cr r * H v)).re := by
      intro r hrR
      obtain ⟨-, hall⟩ := hd r l (hlr r hrR)
      have hw := ((hall u hu v (hv r hrR)).2.1).symm
      unfold Prop025OInputs.windowHam
      rw [hw]
      unfold Q07IntegratedHessiansR16.windowContour ContourPrefactor.contourFunctional
      rw [rectContour_eq, ← boundaryIntegral_eq hab hh.le (cr r * H v)]
      intro z
      simp only [ContinuousMap.mul_apply, cr, ContinuousMap.coe_mk, hHv z, Q07LogDifferentialsR16.logarithm]
      ring
    unfold Prop025OInputs.windowFamily
    rw [Finset.sum_congr rfl fun r hrR => by rw [hr r hrR]]
    simp only [Λ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', Complex.reCLM_apply]
    have hsum : c * H v = ∑ r ∈ R, t r • (cr r * H v) := by
      simp only [c, Finset.sum_mul, smul_mul_assoc]
    rw [hsum, map_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, Complex.smul_re, smul_eq_mul]
    ring
  have hF := (Λ.hasFDerivAt.comp u hH.differentiableAt.hasFDerivAt).const_mul (-(1 / (2 * Real.pi * κ)))
  have hW := hF.congr_of_eventuallyEq heq
  refine ⟨hregu, hW.differentiableAt, fun k => ?_⟩
  rw [hW.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, Λ,
    Complex.reCLM_apply, ContinuousLinearMap.mul_apply']
  have hDH : ∀ z : Boundary (-a) a h, (fderiv ℝ H u k) z = fderiv ℝ (G hκ z.1) u k := by
    intro z
    have hd := (ContinuousMap.evalCLM ℝ z).hasFDerivAt.comp u hH.differentiableAt.hasFDerivAt
    have hev : (fun w => H w z) =ᶠ[𝓝 u] G hκ z.1 := hHe.mono fun w hw => hw z
    have hhd := (hd.congr_of_eventuallyEq hev.symm).fderiv
    simpa using (congrArg (fun A : L2T L →L[ℝ] ℂ => A k) hhd).symm
  rw [boundaryIntegral_eq hab hh.le (c * fderiv ℝ H u k)
    (fun z => polyT R t z * ((I * (κ : ℂ)) * fderiv ℝ (G hκ z) u k)) (fun z => by
      rw [ContinuousMap.mul_apply, hc z, hDH z]; ring)]
  have hcongr : rectIntegral (fun z => polyT R t z * ((I * (κ : ℂ)) * fderiv ℝ (G hκ z) u k)) (-a) a h =
      rectIntegral (fun z => polyT R t z *
        (fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k / Df L κ (fun w => G hκ w u) z))
        (-a) a h := by
    have hp : ∀ z ∈ Gam (-a) a h, polyT R t z * ((I * (κ : ℂ)) * fderiv ℝ (G hκ z) u k) =
        polyT R t z * (fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k /
          Df L κ (fun w => G hκ w u) z) := by
      intro z hz
      rw [dsD_eq hκ u k (hregu z hz)]
    apply LabelExactPeriod.rectIntegral_congr
    · exact fun x hx => hp _ (PeriodTwoTerm.bot_mem hab hx)
    · exact fun x hx => hp _ (PeriodTwoTerm.top_mem hab hx)
    · exact fun y hy => hp _ (PeriodTwoTerm.right_mem hh.le hy)
    · exact fun y hy => hp _ (PeriodTwoTerm.left_mem hh.le hy)
  rw [hcongr]
  have : (1 / (2 * Real.pi * κ)) = (2 * Real.pi * κ)⁻¹ := one_div _
  rw [this]

/-! ### 3. The coherent energy of the summed kernels as a frozen-denominator contour functional -/

theorem re_aux1 (p : ℝ) (X : ℂ) : (-(p : ℂ) * X).re = -p * X.re := by
  simp [Complex.mul_re]

theorem re_aux2 (p q : ℝ) (X : ℂ) : (-(p : ℂ) * (q : ℂ) * X).re = q * (-p * X.re) := by
  simp [Complex.mul_re]; ring

theorem integral_nu_splitC {m : ℕ} {f : ThetaSpace m → ℂ} (hf : Integrable f (nu m)) :
    ∫ θ, f θ ∂(nu m) = ∑ i : Fin m, ∫ τ : unitInterval, f (i, τ) := by
  unfold nu at hf ⊢
  rw [integral_prod _ hf, integral_count]

/-- A function continuous on a closed subset of `ℂ` agrees there with a continuous function (Tietze). -/
theorem exists_continuous_eqOn {K : Set ℂ} (hK : IsClosed K) {f : ℂ → ℂ} (hf : ContinuousOn f K) :
    ∃ g : ℂ → ℂ, Continuous g ∧ EqOn g f K := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hK (⟨K.restrict f, hf.restrict⟩ : C(K, ℂ))
  refine ⟨g, g.continuous, fun z hz => ?_⟩
  have := congrArg (fun F : C(K, ℂ) => F ⟨z, hz⟩) hg
  exact this

/-- Every parameter point of the mixed family lies on the window rectangle or on one fixed rectangle. -/
theorem mixed_mem (hκ : 0 < κ) (u : L2T L) {h a : ℝ} (hh : 0 ≤ h) (ha : 0 ≤ a) (ords : Finset ℕ)
    (t : ℕ → ℝ) {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ) (hlt : ∀ i, xmS hκ u n i ≤ xpS hκ u n i)
    (θ : ThetaSpace (6 + nI * 6)) :
    zθ (mixedPieces hκ u h a ords t n θf) θ ∈ Gam (-a) a h ∨
      ∃ i, zθ (mixedPieces hκ u h a ords t n θf) θ ∈ Gam (xmS hκ u n i) (xpS hκ u n i) h := by
  obtain ⟨j, τ⟩ := θ
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · left
    rw [mixedPieces, Prop025OEigen.zθ_left]
    exact Prop020Contour.rect_mem_Gam ha hh _ _ i ⟨τ.2.1, τ.2.2⟩
  · right
    rw [mixedPieces, Prop025OEigen.zθ_right]
    refine ⟨(finProdFinEquiv.symm j).1, ?_⟩
    exact rectGen_mem_Gam _ _ _ _ _ (hlt _) hh _ ⟨τ.2.1, τ.2.2⟩

/-- **`F_{a,t,θ}` (eq:MP-L, classical form).**  The coherent energy of the summed kernels is the frozen-denominator
window functional plus `Σ_i θ_i` times the frozen-denominator fixed rectangle functionals. -/
theorem coh_mix_eq (hκ : 0 < κ) (u : L2T L) (μ : Measure ℝ) {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ)
    (hlt : ∀ i, xmS hκ u n i < xpS hκ u n i)
    (hDw : ∀ z ∈ Gam (-a) a h, ContinuousAt (fun z => (Df L κ (Gfull μ) z)⁻¹) z)
    (hDf : ∀ i, ∀ z ∈ Gam (xmS hκ u n i) (xpS hκ u n i) h, ContinuousAt (fun z => (Df L κ (Gfull μ) z)⁻¹) z)
    (v : L2T L) :
    R52CFHartree.coh (mixK (L := L) hκ u μ h a ords t n θf) v =
      lam (L := L) κ (fun z => Df L κ (Gfull μ) z / polyT ords t z) (-a) a h v +
        ∑ i, θf i * lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h v := by
  set P := mixedPieces hκ u h a ords t n θf with hP
  set D : ℂ → ℂ := Df L κ (Gfull μ) with hDdef
  have hmem := mixed_mem hκ u hh.le ha.le ords t n θf (fun i => (hlt i).le)
  have hDP : Continuous fun θ => (D (zθ P θ))⁻¹ := by
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    rcases hmem θ with hw | ⟨i, hf⟩
    · exact (hDw _ hw).comp (continuous_zθ P).continuousAt
    · exact (hDf i _ hf).comp (continuous_zθ P).continuousAt
  have hg : Continuous fun θ => uθ κ P θ * mixD hκ u μ h a ords t n θf θ :=
    (continuous_uθ κ P).mul hDP
  have hzh : ∀ θ, |(zθ P θ).im| ≤ h := by
    intro θ
    rcases hmem θ with hw | ⟨i, hf⟩
    · exact R52CFCoh.Gam_abs_im_le hh.le hw
    · exact R52CFCoh.Gam_abs_im_le hh.le hf
  obtain ⟨W, hW⟩ := (isCompact_univ (X := ThetaSpace (6 + nI * 6))).exists_bound_of_continuousOn
    hg.continuousOn
  have hcoh := R52CFCoh.coh_eq (L := L) (nu (6 + nI * 6)) κ _ _ hg (continuous_zθ P) hzh
    (fun θ => hW θ (mem_univ θ)) v
  unfold mixK
  rw [hcoh]
  set S : ℂ → ℂ := fun z => NormalizedTransfer.productSymbol L κ v z - 1 - Complex.exp (I * z * L) with hS
  have hSc : Continuous S := by
    simp only [hS]
    exact ((R52CFCoh.continuous_productSymbol κ hκ.le v).sub continuous_const).sub (by fun_prop)
  have hint : Integrable (fun θ => uθ κ P θ * mixD hκ u μ h a ords t n θf θ * S (zθ P θ)) (nu (6 + nI * 6)) :=
    (hg.mul (hSc.comp (continuous_zθ P))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ θ, uθ κ P θ * mixD hκ u μ h a ords t n θf θ * S (zθ P θ) ∂(nu (6 + nI * 6))).re = _
  rw [integral_nu_splitC hint, Fin.sum_univ_add, Complex.add_re]
  congr 1
  · -- the window rectangle
    set Wp := rectPieces a h (polyT ords t) (continuous_polyT ords t) with hWp
    have hFw : ∀ z ∈ Gam (-a) a h, ContinuousAt (fun z => (D z)⁻¹ * S z) z :=
      fun z hz => (hDw z hz).mul hSc.continuousAt
    have hiw : Integrable (fun θ => uθ κ Wp θ * ((D (zθ Wp θ))⁻¹ * S (zθ Wp θ))) (nu 6) := by
      have hc : Continuous fun θ => uθ κ Wp θ * ((D (zθ Wp θ))⁻¹ * S (zθ Wp θ)) := by
        refine (continuous_uθ κ Wp).mul (continuous_iff_continuousAt.mpr fun θ => ?_)
        exact (hFw (zθ Wp θ) (Prop020Contour.rect_mem_Gam ha.le hh.le (polyT ords t) (continuous_polyT ords t)
          θ.1 ⟨θ.2.2.1, θ.2.2.2⟩)).comp (continuous_zθ Wp).continuousAt
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hsplit : ∑ i : Fin 6, ∫ τ : unitInterval,
        uθ κ P (Fin.castAdd (nI * 6) i, τ) * mixD hκ u μ h a ords t n θf (Fin.castAdd (nI * 6) i, τ) *
          S (zθ P (Fin.castAdd (nI * 6) i, τ)) =
        ∫ θ, uθ κ Wp θ * ((D (zθ Wp θ))⁻¹ * S (zθ Wp θ)) ∂(nu 6) := by
      rw [integral_nu_splitC hiw]
      refine Finset.sum_congr rfl fun i _ => integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [mixD, hP, mixedPieces, Prop025OEigen.uθ_left, Prop025OEigen.zθ_left, hWp, hDdef]
      ring
    rw [hsplit, Prop020Contour.theta_integral_rect ha hh κ (polyT ords t) (continuous_polyT ords t) _ hFw]
    unfold lam
    have hfun : (fun z => polyT ords t z * ((D z)⁻¹ * S z)) =
        fun z => (NormalizedTransfer.productSymbol L κ v z - 1 - Complex.exp (I * z * L)) /
          (D z / polyT ords t z) := by
      funext z
      rw [div_div_eq_mul_div]
      simp only [hS]
      ring
    rw [hfun, re_aux1]
  · -- the fixed rectangles
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set Pi : Fin 6 → Piece := rectGen (xmS hκ u n i) (xpS hκ u n i) h (fun _ => ((θf i : ℝ) : ℂ))
      continuous_const with hPi
    have hfam : ∀ k : Fin 6, rectFamily (xmS hκ u n) (xpS hκ u n) (fun _ => h) θf (finProdFinEquiv (i, k)) =
        Pi k := by
      intro k
      simp only [rectFamily, Equiv.symm_apply_apply, hPi]
    have hcF : ContinuousOn (fun z => (D z)⁻¹ * S z) (Gam (xmS hκ u n i) (xpS hκ u n i) h) :=
      fun z hz => ((hDf i z hz).mul hSc.continuousAt).continuousWithinAt
    obtain ⟨Φ, hΦc, hΦe⟩ := exists_continuous_eqOn
      (PeriodReconstruction.isCompact_Gam (xmS hκ u n i) (xpS hκ u n i) h).isClosed hcF
    have hpiece : ∀ k : Fin 6, ∫ τ : unitInterval,
        uθ κ P (Fin.natAdd 6 (finProdFinEquiv (i, k)), τ) *
          mixD hκ u μ h a ords t n θf (Fin.natAdd 6 (finProdFinEquiv (i, k)), τ) *
          S (zθ P (Fin.natAdd 6 (finProdFinEquiv (i, k)), τ)) =
        ∫ τ : unitInterval, uθ κ Pi (k, τ) * Φ (zθ Pi (k, τ)) := by
      intro k
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      have hz : zθ Pi (k, τ) ∈ Gam (xmS hκ u n i) (xpS hκ u n i) h :=
        rectGen_mem_Gam _ _ _ _ _ (hlt i).le hh.le k ⟨τ.2.1, τ.2.2⟩
      have hzP : zθ P (Fin.natAdd 6 (finProdFinEquiv (i, k)), τ) = zθ Pi (k, τ) := by
        rw [hP, mixedPieces, Prop025OEigen.zθ_right]
        simp only [zθ, hfam]
      have huP : uθ κ P (Fin.natAdd 6 (finProdFinEquiv (i, k)), τ) = uθ κ Pi (k, τ) := by
        rw [hP, mixedPieces, Prop025OEigen.uθ_right]
        simp only [uθ, zθ, hfam]
      simp only [mixD]
      rw [← hP, hzP, huP, ← hDdef, hΦe hz]
      ring
    simp_rw [hpiece]
    rw [Prop025OEigen.theta_integral_rectGen (hlt i) hh κ _ Φ hΦc]
    have hΦr : rectIntegral Φ (xmS hκ u n i) (xpS hκ u n i) h =
        rectIntegral (fun z => (NormalizedTransfer.productSymbol L κ v z - 1 - Complex.exp (I * z * L)) / D z)
          (xmS hκ u n i) (xpS hκ u n i) h := by
      have hp : ∀ z ∈ Gam (xmS hκ u n i) (xpS hκ u n i) h,
          Φ z = (NormalizedTransfer.productSymbol L κ v z - 1 - Complex.exp (I * z * L)) / D z := by
        intro z hz
        rw [hΦe hz, div_eq_inv_mul]
      apply LabelExactPeriod.rectIntegral_congr
      · exact fun x hx => hp _ (PeriodTwoTerm.bot_mem (hlt i).le hx)
      · exact fun x hx => hp _ (PeriodTwoTerm.top_mem (hlt i).le hx)
      · exact fun y hy => hp _ (PeriodTwoTerm.right_mem hh.le hy)
      · exact fun y hy => hp _ (PeriodTwoTerm.left_mem hh.le hy)
    rw [hΦr]
    unfold lam
    rw [re_aux2]

/-! ### 4. eq:MP-full-gradient-agreement at the base profile -/

/-- **Gradient agreement at `u`.**  For a profile `u` of a Sobolev class whose scalar measure is `μ`, every large
regular cut `a = a_ℓ`, every finite charge family `ords`, joint times `t`, labels `n` and angles `θ`:
`dF_{a,t,θ}(u) = d(Σ_r t_r h_{r,a})(u) + Σ_i θ_i dI_{n_i}(u)` (full real differentials on `L²`). -/
theorem grad_at (hκ : 0 < κ) (u : L2T L) {s B h : ℝ} (hs : 0 < s) (hh : 0 < h)
    (hu : u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B) (μ : Measure ℝ)
    (hμ : PhysicalQuantumMeasure.measure hκ u = μ) (ords : Finset ℕ) (t : ℕ → ℝ) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → 1 ≤ cutSeq L l ∧
      DifferentiableAt ℝ (Prop025OInputs.windowFamily (L := L) κ ords t (cutSeq L l)) u ∧
      ∀ {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ),
        fderiv ℝ (R52CFHartree.coh (mixK (L := L) hκ u μ h (cutSeq L l) ords t n θf)) u =
          fderiv ℝ (Prop025OInputs.windowFamily (L := L) κ ords t (cutSeq L l)) u +
            ∑ i, θf i • fderiv ℝ (mass hκ (n i)) u := by
  obtain ⟨l0, hw⟩ := window_fderiv (L := L) hκ (B := B) hs hh ords t
  refine ⟨l0, fun l hl => ?_⟩
  obtain ⟨ha1, hwu⟩ := hw l hl
  obtain ⟨hregw, hWd, hWf⟩ := hwu u hu
  refine ⟨ha1, hWd, fun {nI} n θf => ?_⟩
  set a := cutSeq L l with ha
  have ha0 : 0 < a := by linarith
  have hGD : Df L κ (Gfull μ) = Df L κ (fun w => G hκ w u) := by
    funext z
    have : Gfull μ = fun w => G hκ w u := by
      funext w
      rw [RootSpectralInputsDischarge.Gfull_eq, ← hμ]
      rfl
    rw [this]
  -- regularity on the fixed rectangles (accepted R52CF stage 1)
  have hfix : ∀ i, (∀ z ∈ Gam (xmS hκ u n i) (xpS hκ u n i) h, Regular κ (u, z)) ∧
      ∀ k : L2T L, fderiv ℝ (mass hκ (n i)) u k = -(2 * Real.pi * κ)⁻¹ *
        (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k /
          Df L κ (fun w => G hκ w u) z) (xmS hκ u n i) (xpS hκ u n i) h).re := by
    intro i
    obtain ⟨W, -, huW, hW⟩ := R52CFDeriv.fixed_rectangle_neighborhood hκ u (n i) hh
    obtain ⟨hr, -, hd⟩ := hW u huW
    exact ⟨hr, hd⟩
  have hlt : ∀ i, xmS hκ u n i < xpS hκ u n i := fun i => R52CFDeriv.cut_lt hκ u (n i)
  have hDw : ∀ z ∈ Gam (-a) a h, ContinuousAt (fun z => (Df L κ (Gfull μ) z)⁻¹) z := by
    intro z hz; rw [hGD]; exact (D_regular hκ u (hregw z hz)).1
  have hDf : ∀ i, ∀ z ∈ Gam (xmS hκ u n i) (xpS hκ u n i) h,
      ContinuousAt (fun z => (Df L κ (Gfull μ) z)⁻¹) z := by
    intro i z hz; rw [hGD]; exact (D_regular hκ u ((hfix i).1 z hz)).1
  have hfun : R52CFHartree.coh (mixK (L := L) hκ u μ h a ords t n θf) = fun v =>
      lam (L := L) κ (fun z => Df L κ (Gfull μ) z / polyT ords t z) (-a) a h v +
        ∑ i, θf i * lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h v :=
    funext fun v => coh_mix_eq hκ u μ hh ha0 ords t n θf hlt hDw hDf v
  -- differentials of the two kinds of frozen functionals
  have hcw : ContinuousOn (fun z => (Df L κ (Gfull μ) z / polyT ords t z)⁻¹) (Gam (-a) a h) := by
    intro z hz
    have h1 : ContinuousWithinAt (fun z => polyT ords t z * (Df L κ (Gfull μ) z)⁻¹) (Gam (-a) a h) z :=
      ((continuous_polyT ords t).continuousAt.mul (hDw z hz)).continuousWithinAt
    exact h1.congr (fun y _ => by rw [div_eq_mul_inv, mul_inv, inv_inv, mul_comm])
      (by rw [div_eq_mul_inv, mul_inv, inv_inv, mul_comm])
  have hLw := lam_hasFDerivAt (L := L) κ hκ.le (fun z => Df L κ (Gfull μ) z / polyT ords t z)
    (by linarith : -a ≤ a) hh.le hcw u
  have hLf : ∀ i, HasFDerivAt (lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h)
      (fderiv ℝ (lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h) u) u ∧
      ∀ k : L2T L, fderiv ℝ (lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h) u k =
        -(2 * Real.pi * κ)⁻¹ * (rectIntegral (fun z => fderiv ℝ (fun w : L2T L =>
          RootScalarPeriodR10.symbol κ w z) u k / Df L κ (Gfull μ) z) (xmS hκ u n i) (xpS hκ u n i) h).re :=
    fun i => lam_hasFDerivAt (L := L) κ hκ.le (Df L κ (Gfull μ)) (hlt i).le hh.le
      (fun z hz => (hDf i z hz).continuousWithinAt) u
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hLf i).1.const_mul (θf i))
  have htot : HasFDerivAt (fun v =>
      lam (L := L) κ (fun z => Df L κ (Gfull μ) z / polyT ords t z) (-a) a h v +
        ∑ i, θf i * lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h v) _ u :=
    hLw.1.add hsum
  rw [hfun, htot.fderiv]
  ext k
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [hLw.2 k, hWf k]
  congr 1
  · congr 2
    apply LabelExactPeriod.rectIntegral_congr <;> intros <;> rw [hGD, div_div_eq_mul_div] <;> ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hLf i).2 k, (hfix i).2 k, hGD]

end QuantumNLS.Prop025OGrad

#print axioms QuantumNLS.Prop025OGrad.window_fderiv
#print axioms QuantumNLS.Prop025OGrad.coh_mix_eq
#print axioms QuantumNLS.Prop025OGrad.grad_at

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OGrad." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop025OGrad aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
