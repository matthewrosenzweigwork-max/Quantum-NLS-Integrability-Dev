import QuantumNLS.R52CFCoh
import QuantumNLS.R52CFOrbit

/-!
# R-52CF5DA1 stage 8b: the frozen-contour Hartree flow is the action flow `T_t`

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101), proof paragraph "The limiting Hamiltonian is the
corresponding linear functional of the classical transfer with denominator frozen at `v`. ... Its flow consequently
preserves every transfer value and the full discriminant. Along that flow, the last identity in
Lemma `lem:audit-scalar-period` identifies its full vector field with `Σ t_n X_{I_n}` at every point of that level,
including points outside the original rough-center neighborhood. The new global canonical chart, by its full
symplectic chain rule and exact indexed actions, identifies this flow with `T_t`."

Data: the accepted chart statement `GlobalStatement` (R-F5355ABD), a finite label set `F`, finitely supported real
times `t` (`t_n = 0` off `F`), per-label rectangles `Γ_n = ∂([A_n, B_n] × [-h, h])`, a fixed denominator `D`
(continuous and nonvanishing as `D⁻¹` on each `Γ_n`), and a unit vector `v` at which the fixed-contour differential
identity `dI_n(v)[k] = -(2πκ)⁻¹ Re ∮_{Γ_n} ∂_v s(z;v)[k]/D(z) dz` holds for `n ∈ F` (stage 1 supplies it near a
rough center).  The frozen-contour kernels are those of stages 4-6 on the concatenated rectangles with weights `t_n`.
* `fam`, `wt`: the concatenated rectangle family and the weight `u_θ / D(z_θ)`;
* `norm_Tθ`: `‖T_θ u‖ = ‖u‖` (chart isometry and exact rotation of the coordinates);
* `flow_scaling`: the complete flow of `X_{H_t}` at time `s` is `T_{st} v`;
* **`trajectory_eq`**: the PROP-001 classical trajectory of the frozen-contour data from `v`, at time `1`, is
  `T_t v` (the coherent energy has the same differential as `H_t = Σ t_n I_n` along the whole orbit, by stage 8a,
  stage 1 at `v` and the stage 2 transport; stage 3 identifies its Hamiltonian field with the PROP-001 field; PROP-001
  uniqueness concludes).
No hypothesis is added; all inherited modules are read-only.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BigOperators

namespace QuantumNLS.R52CFClassical

section GenericField
attribute [local instance] InnerProductSpace.complexToReal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem hamField_congr_gen {f g : H → ℝ} {u : H} (h : fderiv ℝ f u = fderiv ℝ g u) :
    SymplecticBracket.hamField f u = SymplecticBracket.hamField g u := by
  unfold SymplecticBracket.hamField SymplecticBracket.gradient
  rw [h]

end GenericField

open PhysicalTensor (L2T)
open RootMassInvolutionR8 (mass)
open LabelExactPeriod (rectIntegral)
open SymplecticBracket (hamField)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.ProductTorusGenerator (Linf)
open QuantumNLS.RF535Final (Hθ Tθ GlobalStatement)
open QuantumNLS.R52CFKernels QuantumNLS.R52CFBudget QuantumNLS.R52CFCoh

variable {L κ : ℝ} [Fact (0 < L)]

/-- The labels of `F` in a fixed enumeration. -/
def lab (F : Finset ℤ) (i : Fin F.card) : ℤ := (F.equivFin.symm i : ℤ)

theorem lab_mem (F : Finset ℤ) (i : Fin F.card) : lab F i ∈ F := (F.equivFin.symm i).2

theorem sum_lab (F : Finset ℤ) (f : ℤ → ℝ) : ∑ i : Fin F.card, f (lab F i) = ∑ n ∈ F, f n := by
  unfold lab
  rw [Equiv.sum_comp F.equivFin.symm (fun x : F => f x)]
  exact Finset.sum_coe_sort F f

/-- The concatenated rectangles `Γ_n`, `n ∈ F`, with the weights `t_n`. -/
def fam (F : Finset ℤ) (t : Linf) (A B : ℤ → ℝ) (h : ℝ) : Fin (F.card * 4) → MPContour.Piece :=
  R52CFPieces.rectFam (fun i => A (lab F i)) (fun i => B (lab F i)) (fun _ => h) (fun i => ((t (lab F i) : ℝ) : ℂ))

/-- The weight `u_θ / D(z_θ)` of the frozen-contour kernels. -/
def wt (κ : ℝ) (F : Finset ℤ) (t : Linf) (A B : ℤ → ℝ) (h : ℝ) (Dz : ℂ → ℂ)
    (θ : MPContour.ThetaSpace (F.card * 4)) : ℂ :=
  MPContour.uθ κ (fam F t A B h) θ * (Dz (MPContour.zθ (fam F t A B h) θ))⁻¹

theorem continuous_dinv (F : Finset ℤ) (t : Linf) (A B : ℤ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hAB : ∀ n, A n ≤ B n) (Dz : ℂ → ℂ)
    (hD : ∀ n ∈ F, ContinuousOn (fun z => (Dz z)⁻¹) (PeriodReconstruction.Gam (A n) (B n) h)) :
    Continuous (fun θ => (Dz (MPContour.zθ (fam F t A B h) θ))⁻¹) := by
  apply continuous_prod_of_discrete_left.mpr
  intro k
  have hm : ∀ τ : unitInterval, MPContour.zθ (fam F t A B h) (k, τ) ∈
      PeriodReconstruction.Gam (A (lab F (finProdFinEquiv.symm k).1)) (B (lab F (finProdFinEquiv.symm k).1)) h :=
    fun τ => zθ_mem _ _ _ _ (fun i => hAB _) (fun _ => hh) (k, τ)
  have hc : Continuous (fun τ : unitInterval => MPContour.zθ (fam F t A B h) (k, τ)) :=
    (MPContour.continuous_zθ _).comp (Continuous.prodMk_right k)
  exact (hD _ (lab_mem F _)).comp_continuous hc hm

theorem continuous_wt (κ : ℝ) (F : Finset ℤ) (t : Linf) (A B : ℤ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hAB : ∀ n, A n ≤ B n) (Dz : ℂ → ℂ)
    (hD : ∀ n ∈ F, ContinuousOn (fun z => (Dz z)⁻¹) (PeriodReconstruction.Gam (A n) (B n) h)) :
    Continuous (wt κ F t A B h Dz) :=
  (MPContour.continuous_uθ κ _).mul (continuous_dinv F t A B hh hAB Dz hD)

/-! ### The chart: norm preservation and scaling of the action flows -/

variable {d : ℝ} {Φl : L2T L → K} {Ψl : K → L2T L}

theorem norm_Tθ (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (θ : Linf) (u : L2T L) :
    ‖Tθ (L := L) hκ θ u‖ = ‖u‖ := by
  obtain ⟨Y, Fl, Φ, Ψ, -, -, -, -, -, -, -, -, -, -, -, -, hn, -, -, -, -, -, -, -, hrot, -, -⟩ := hG.2
  have hc : ∀ n, ‖Φ (Tθ (L := L) hκ θ u) n‖ = ‖Φ u n‖ := by
    intro n
    rw [hrot θ u n, norm_mul]
    have he : Complex.exp (-(θ n : ℂ) * Complex.I) = Complex.exp (((-θ n : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring_nf
    rw [he, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have hΦ : ‖Φ (Tθ (L := L) hκ θ u)‖ = ‖Φ u‖ := by
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    simp_rw [hc]
  have h1 := hn (Tθ (L := L) hκ θ u)
  have h2 := hn u
  rw [hΦ, h2] at h1
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1).symm

theorem Hθ_smul (hκ : 0 < κ) (s : ℝ) (t : Linf) :
    Hθ (L := L) hκ (s • t) = fun u => s * Hθ (L := L) hκ t u := by
  funext u
  unfold Hθ
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem differentiableAt_Hθ (hκ : 0 < κ) (F : Finset ℤ) (t : Linf) (ht : ∀ n ∉ F, t n = 0) (u : L2T L) :
    DifferentiableAt ℝ (Hθ (L := L) hκ t) u := by
  rw [R52CFOrbit.Hθ_eq_sum hκ F t ht]
  exact DifferentiableAt.fun_sum fun n _ =>
    (R52CFOrbit.differentiableAt_mass hκ n u).const_mul (t n)

theorem hamField_Hθ_smul (hκ : 0 < κ) (F : Finset ℤ) (t : Linf) (ht : ∀ n ∉ F, t n = 0) (s : ℝ)
    (u : L2T L) :
    hamField (Hθ (L := L) hκ (s • t)) u = s • hamField (Hθ (L := L) hκ t) u := by
  have h := R52CFOrbit.hamField_sum_gen ({()} : Finset Unit) (fun _ => s) (fun _ => Hθ (L := L) hκ t) u
    (fun _ => differentiableAt_Hθ hκ F t ht u)
  simp only [Finset.sum_singleton] at h
  rw [Hθ_smul]
  exact h

/-- **The complete flow of `X_{H_t}` at time `s` is `T_{st}`.** -/
theorem flow_scaling (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (F : Finset ℤ) (t : Linf)
    (ht : ∀ n ∉ F, t n = 0) (v : L2T L) (γ : ℝ → L2T L) (hγ0 : γ 0 = v)
    (hγ : ∀ s, HasDerivAt γ (hamField (Hθ (L := L) hκ t) (γ s)) s) (s : ℝ) :
    γ s = Tθ (L := L) hκ (s • t) v := by
  obtain ⟨γs, hγs0, hγs, hu, hγs1⟩ := hG.1.1 (s • t) v
  have hcurve : (fun σ : ℝ => γ (s * σ)) = γs := by
    apply hu
    · simp [hγ0]
    · intro σ
      have h1 := (hγ (s * σ)).scomp σ ((hasDerivAt_id σ).const_mul s)
      rw [hamField_Hθ_smul hκ F t ht s]
      rw [mul_one] at h1
      first
        | exact h1
        | convert h1 using 1
  have := congrFun hcurve 1
  simp only [mul_one] at this
  rw [this, hγs1]

/-! ### The classical identification -/

theorem coh_fam (hκ : 0 < κ) (F : Finset ℤ) (t : Linf) (A B : ℤ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hAB : ∀ n, A n ≤ B n) (Dz : ℂ → ℂ)
    (hD : ∀ n ∈ F, ContinuousOn (fun z => (Dz z)⁻¹) (PeriodReconstruction.Gam (A n) (B n) h)) :
    R52CFHartree.coh (kerA (MPContour.nu (F.card * 4)) κ (wt κ F t A B h Dz)
      (physK (L := L) (MPContour.zθ (fam F t A B h)))) =
      fun w => ∑ i : Fin F.card, t (lab F i) * lam (L := L) κ Dz (A (lab F i)) (B (lab F i)) h w := by
  funext w
  exact coh_rect (L := L) κ hκ.le (fun i => A (lab F i)) (fun i => B (lab F i)) (fun _ => h)
    (fun i => t (lab F i)) Dz (continuous_dinv F t A B hh hAB Dz hD)
    (fun θ => zθ_im_le _ _ _ _ (fun i => hAB _) (fun _ => hh) (fun _ => le_rfl) θ) w

/-- **Along the orbit, the coherent energy has the differential of `H_t`.** -/
theorem fderiv_coh_orbit (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (F : Finset ℤ) (t : Linf)
    (ht : ∀ n ∉ F, t n = 0) (A B : ℤ → ℝ) {h : ℝ} (hh : 0 ≤ h) (hAB : ∀ n, A n ≤ B n) (Dz : ℂ → ℂ)
    (hD : ∀ n ∈ F, ContinuousOn (fun z => (Dz z)⁻¹) (PeriodReconstruction.Gam (A n) (B n) h))
    (v : L2T L)
    (hdiff : ∀ n ∈ F, ∀ k : L2T L, fderiv ℝ (mass hκ n) v k = -(2 * Real.pi * κ)⁻¹ *
      (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) v k / Dz z)
        (A n) (B n) h).re)
    (s : ℝ) :
    fderiv ℝ (R52CFHartree.coh (kerA (MPContour.nu (F.card * 4)) κ (wt κ F t A B h Dz)
      (physK (L := L) (MPContour.zθ (fam F t A B h))))) (Tθ (L := L) hκ (s • t) v) =
      fderiv ℝ (Hθ (L := L) hκ t) (Tθ (L := L) hκ (s • t) v) := by
  set w := Tθ (L := L) hκ (s • t) v
  have hst : ∀ n ∉ F, (s • t) n = 0 := by
    intro n hn
    rw [lp.coeFn_smul, Pi.smul_apply, ht n hn, smul_zero]
  have htr := (R52CFOrbit.orbit_transport hκ hG F (s • t) hst).2.2.2
  rw [coh_fam hκ F t A B hh hAB Dz hD]
  have hlam : ∀ i : Fin F.card, HasFDerivAt (fun w' => t (lab F i) *
      lam (L := L) κ Dz (A (lab F i)) (B (lab F i)) h w')
      (t (lab F i) • fderiv ℝ (lam (L := L) κ Dz (A (lab F i)) (B (lab F i)) h) w) w :=
    fun i => (lam_hasFDerivAt (L := L) κ hκ.le Dz (hAB _) hh (hD _ (lab_mem F i)) w).1.const_mul _
  have hC := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hlam i)
  have hH : HasFDerivAt (Hθ (L := L) hκ t) (∑ n ∈ F, t n • fderiv ℝ (mass hκ n) w) w := by
    rw [R52CFOrbit.Hθ_eq_sum hκ F t ht]
    exact HasFDerivAt.fun_sum fun n _ =>
      (R52CFOrbit.differentiableAt_mass hκ n w).hasFDerivAt.const_mul (t n)
  rw [hC.fderiv, hH.fderiv]
  ext k
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  rw [← sum_lab F (fun n => t n * fderiv ℝ (mass hκ n) w k)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [(lam_hasFDerivAt (L := L) κ hκ.le Dz (hAB _) hh (hD _ (lab_mem F i)) w).2 k]
  exact (htr (lab F i) v Dz (A (lab F i)) (B (lab F i)) h (hdiff _ (lab_mem F i)) k).symm

theorem hamField_congr {f g : L2T L → ℝ} {u : L2T L} (h : fderiv ℝ f u = fderiv ℝ g u) :
    hamField f u = hamField g u :=
  hamField_congr_gen h

/-- The PROP-001 summability hypothesis of stage 3 at radius `2`. -/
theorem coh_summable (κ : ℝ) {m : ℕ} (g z : MPContour.ThetaSpace m → ℂ) {H W : ℝ}
    (hzh : ∀ θ, |(z θ).im| ≤ H) (hgW : ∀ θ, ‖g θ‖ ≤ W) (hW0 : 0 ≤ W) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖kerA (MPContour.nu m) κ g (physK (L := L) z) n‖ *
      (2 : ℝ) ^ (2 * n + 1)) := by
  have hL : 0 < L := Fact.out
  have hs := (beta_geom_summable (L := L) κ H 4 (by norm_num)).mul_left ((MPContour.nu m).real univ * W)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have hk := kerA_le_bseq (L := L) (MPContour.nu m) κ g z hzh hgW hW0 n
  unfold bseq at hk
  have hb := beta_nonneg L κ H hL n
  have hV : 0 ≤ (MPContour.nu m).real univ := measureReal_nonneg
  have h1 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 3 * Real.exp n := by
    have ha : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 3 := by
      have hx : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
      have hx2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := one_le_pow₀ hx
      have hm := mul_le_mul_of_nonneg_left hx2 (by linarith : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
      have he : ((n + 1 : ℕ) : ℝ) ^ 3 = ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by ring
      rw [he]
      linarith
    have hb2 : (1 : ℝ) ≤ Real.exp n := Real.one_le_exp (by positivity)
    nlinarith
  have h2 : (2 : ℝ) ^ (2 * n + 1) ≤ (4 : ℝ) ^ (n + 1) := by
    have e1 : (2 : ℝ) ^ (2 * n + 1) = 2 * (4 : ℝ) ^ n := by
      rw [pow_succ, pow_mul, show ((2 : ℝ) ^ 2) = 4 by norm_num, mul_comm]
    have e2 : (4 : ℝ) ^ (n + 1) = 4 * (4 : ℝ) ^ n := by rw [pow_succ, mul_comm]
    rw [e1, e2]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) n]
  calc ((n + 1 : ℕ) : ℝ) * ‖kerA (MPContour.nu m) κ g (physK (L := L) z) n‖ * (2 : ℝ) ^ (2 * n + 1)
      ≤ ((n + 1 : ℕ) : ℝ) * ((MPContour.nu m).real univ * W * beta L κ H n) * (4 : ℝ) ^ (n + 1) := by
        gcongr
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ 3 * Real.exp n * ((MPContour.nu m).real univ * W * beta L κ H n) *
          (4 : ℝ) ^ (n + 1) := by gcongr
    _ = (MPContour.nu m).real univ * W *
          (((n + 1 : ℕ) : ℝ) ^ 3 * Real.exp n * (beta L κ H n * (4 : ℝ) ^ (n + 1))) := by ring

/-- **Stage 8 headline.**  The PROP-001 classical trajectory of the frozen-contour data from the unit vector `v`
is, at time `1`, the action flow `T_t v`. -/
theorem trajectory_eq (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (F : Finset ℤ) (t : Linf)
    (ht : ∀ n ∉ F, t n = 0) (A B : ℤ → ℝ) {h : ℝ} (hh : 0 ≤ h) (hAB : ∀ n, A n ≤ B n) (Dz : ℂ → ℂ)
    (hD : ∀ n ∈ F, ContinuousOn (fun z => (Dz z)⁻¹) (PeriodReconstruction.Gam (A n) (B n) h))
    (v : L2T L) (hv : ‖v‖ = 1)
    (hdiff : ∀ n ∈ F, ∀ k : L2T L, fderiv ℝ (mass hκ n) v k = -(2 * Real.pi * κ)⁻¹ *
      (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) v k / Dz z)
        (A n) (B n) h).re)
    {H W : ℝ} (hzh : ∀ θ, |(MPContour.zθ (fam F t A B h) θ).im| ≤ H)
    (hgW : ∀ θ, ‖wt κ F t A B h Dz θ‖ ≤ W) (hW0 : 0 ≤ W) :
    Prop001.trajectory (classicalData (L := L) (MPContour.nu (F.card * 4)) κ (wt κ F t A B h Dz)
      (MPContour.zθ (fam F t A B h)) hzh hgW hW0) ⟨v, hv⟩ 1 = Tθ (L := L) hκ t v := by
  set CD := classicalData (L := L) (MPContour.nu (F.card * 4)) κ (wt κ F t A B h Dz)
      (MPContour.zθ (fam F t A B h)) hzh hgW hW0 with hCD
  obtain ⟨γ, hγ0, hγ, -, hγ1⟩ := hG.1.1 t v
  have hon : ∀ s, γ s = Tθ (L := L) hκ (s • t) v := flow_scaling hκ hG F t ht v γ hγ0 hγ
  have hnorm : ∀ s, ‖γ s‖ = 1 := fun s => by rw [hon s, norm_Tθ hκ hG, hv]
  have hfield : ∀ s, hamField (Hθ (L := L) hκ t) (γ s) = Ext025A8.sourceHartreeField CD.A (γ s) := by
    intro s
    have h1 := fderiv_coh_orbit hκ hG F t ht A B hh hAB Dz hD v hdiff s
    rw [← hon s] at h1
    rw [← hamField_congr h1]
    exact (R52CFHartree.hamField_coh_eq CD.A CD.selfAdjoint (S := 2) (by norm_num)
      (coh_summable (L := L) κ _ _ hzh hgW hW0) (γ s) (by rw [hnorm s]; norm_num)).2
  have heq := (Prop001.trajectory_spec CD ⟨v, hv⟩).2.2.2 γ hγ0
    (fun s => ⟨hnorm s, by rw [← hfield s]; exact hγ s⟩)
  rw [← heq, hγ1]

end QuantumNLS.R52CFClassical

#print axioms QuantumNLS.R52CFClassical.trajectory_eq
