import Mathlib
import QuantumNLS.RB01Tail
import QuantumNLS.TerraMultiRound30HessianBridge

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01Main: the assembled theorem (source
`collective_actions.tex:47-66`).

* `P22R`, `P1R`: the coordinate products `ℓ²(ℤ;ℂ) × ℓ²(ℤ;ℂ) → ℓ¹(ℤ;ℝ)`, `(x, y) ↦ (Re(x̄_n y_n))_n`, and
  `ℓ¹(ℤ;ℝ) × ℓ∞(ℤ;ℂ) → ℓ¹(ℤ;ℝ)`, `(a, z) ↦ (a_n Re z_n)_n`, as real-bilinear Hölder maps (`lp.holderL`); these are
  the multiplication step of the source with the real part taken coordinatewise (the complex products
  `TerraMultiRound33SequenceProduct.product22/product1inf` are complex-bilinear and are not real-analytic in `ḡ`).
* `compact_of_singles`: if `B : ℓᵖ →L ...` (`p < ∞`) sends every `c e_n` to a compact operator, then every `B a` is
  compact (norm limit of the finite-rank `B(Σ_{n∈s} a_n e_n)`, closedness of compact operators). Hence
  `x ↦ (Re(ā_n x_n))` (`a ∈ ℓ²`) and `z ↦ (b_n Re z_n)` (`b ∈ ℓ¹`) are compact.
* `local_form`: on `U = B(u₀, ρ)`, `I = Σ_{|n|≤N} I_n e_n + P1R(P22R(g, g), r)` with
  `g = trunc(√(L/(4κ)) b)` and `r = trunc(G(u, ū))` (RB01Tail), hence real analytic into `ℓ¹`; the bounded
  holomorphic extensions (RB01Head) and `DI(u)` compact (finite rank head plus the compact product derivative).
* `analyticAt_actions`, `compact_derivative`: for every `u`.
* `hessian_tails`: `TerraMultiRound30HessianBridge.hessian_tail_lower_bound_of_derivative_field` with the derivative
  field now available: every tail of `D²I(0)` has norm `≥ 2` (the printed "false already at zero").
* **`global_B01_actions`**: the theorem. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace QuantumNLS.RB01Main

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ProductTorusComplexification (Cx)
open QuantumNLS.TerraMultiRound30HessianBridge (Actions)
open QuantumNLS.TerraMultiRound31CoordinateHessian (actionCoordinate coordinate_analytic)
open QuantumNLS.TerraMultiRound31FiniteActions (finiteActions finiteActions_analytic)
open QuantumNLS.RB01Head (trunc trunc_apply)

abbrev L1R := lp (fun _ : ℤ => ℝ) 1
abbrev L2C := lp (fun _ : ℤ => ℂ) 2
abbrev LinfC := lp (fun _ : ℤ => ℂ) ∞

/-! ## Real-bilinear coordinate products -/

/-- `(t, z) ↦ t Re z`. -/
def reB : ℝ →L[ℝ] ℂ →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (t : ℝ) (z : ℂ) => t * z.re) (fun a b z => by ring)
      (fun c a z => by simp only [smul_eq_mul]; ring)
      (fun t z w => by simp only [Complex.add_re]; ring)
      (fun c t z => by simp only [Complex.smul_re, smul_eq_mul]; ring))
    1 (fun t z => by
      simp only [LinearMap.mk₂_apply, norm_mul, one_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg t))

theorem reB_apply (t : ℝ) (z : ℂ) : reB t z = t * z.re := rfl

theorem reB_norm : ‖reB‖ ≤ 1 := LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- `ℓ² × ℓ² → ℓ¹`, `(x, y) ↦ (Re(x̄_n y_n))_n`. -/
def P22R : L2C →L[ℝ] L2C →L[ℝ] L1R :=
  lp.holderL (𝕜 := ℝ) 1 (fun _ : ℤ => innerSL ℝ (E := ℂ)) (K := 1) (fun _ => norm_innerSL_le ℝ)

/-- `ℓ¹ × ℓ∞ → ℓ¹`, `(a, z) ↦ (a_n Re z_n)_n`. -/
def P1R : L1R →L[ℝ] LinfC →L[ℝ] L1R :=
  lp.holderL (𝕜 := ℝ) 1 (fun _ : ℤ => reB) (K := 1) (fun _ => reB_norm)

theorem P22R_apply (x y : L2C) (n : ℤ) : P22R x y n = ⟪x n, y n⟫_ℝ := rfl

theorem P1R_apply (a : L1R) (z : LinfC) (n : ℤ) : P1R a z n = a n * (z n).re := rfl

/-! ## Compactness -/

theorem isCompact_sum {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {ι : Type*} (s : Finset ι) (f : ι → X →L[ℝ] Y) (h : ∀ i ∈ s, IsCompactOperator (f i)) :
    IsCompactOperator ⇑(∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, FunLike.coe_zero]; exact isCompactOperator_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, FunLike.coe_add]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem compact_of_singles {A Y Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (B : lp (fun _ : ℤ => A) p →L[ℝ] Y →L[ℝ] Z)
    (h : ∀ (n : ℤ) (c : A), IsCompactOperator (B (lp.single p n c))) (a : lp (fun _ : ℤ => A) p) :
    IsCompactOperator (B a) := by
  have hs : Tendsto (fun s : Finset ℤ => ∑ i ∈ s, lp.single p i (a i)) atTop (𝓝 a) := lp.hasSum_single hp a
  have ht : Tendsto (fun s : Finset ℤ => B (∑ i ∈ s, lp.single p i (a i))) atTop (𝓝 (B a)) :=
    (B.continuous.tendsto a).comp hs
  refine isCompactOperator_of_tendsto ht (Eventually.of_forall fun s => ?_)
  rw [map_sum]
  exact isCompact_sum s _ (fun i _ => h i (a i))

theorem rank_one_compact {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (n : ℤ) (ψ : X →L[ℝ] ℝ)
    (T : X →L[ℝ] L1R) (h : ∀ y, T y = lp.single 1 n (ψ y)) : IsCompactOperator T := by
  have e : T = (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℝ) 1 n).comp ψ := by
    ext1 y; rw [h]; rfl
  rw [e]
  exact (isCompactOperator_of_locallyCompactSpace_rng (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℝ) 1 n)).comp_clm ψ

theorem single_ite {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (n m : ℤ) (c : E) :
    (lp.single p n c : ℤ → E) m = if m = n then c else 0 := by
  rw [lp.single_apply, Pi.single_apply]

theorem P22R_compact (a : L2C) : IsCompactOperator (P22R a) := by
  refine compact_of_singles (by norm_num) P22R (fun n c => ?_) a
  refine rank_one_compact n ((innerSL ℝ c).comp (lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 n)) _ (fun y => ?_)
  apply lp.ext; funext m
  rw [P22R_apply, single_ite, single_ite]
  split_ifs with hm
  · subst hm; rfl
  · simp

theorem P22R_flip_compact (a : L2C) : IsCompactOperator (P22R.flip a) := by
  refine compact_of_singles (by norm_num) P22R.flip (fun n c => ?_) a
  refine rank_one_compact n ((innerSL ℝ c).comp (lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 n)) _ (fun y => ?_)
  apply lp.ext; funext m
  rw [ContinuousLinearMap.flip_apply, P22R_apply, single_ite, single_ite]
  split_ifs with hm
  · subst hm; exact real_inner_comm _ _
  · simp

theorem P1R_compact (a : L1R) : IsCompactOperator (P1R a) := by
  refine compact_of_singles (by norm_num) P1R (fun n c => ?_) a
  refine rank_one_compact n ((reB c).comp (lp.evalCLM ℝ (fun _ : ℤ => ℂ) ∞ n)) _ (fun y => ?_)
  apply lp.ext; funext m
  rw [P1R_apply, single_ite, single_ite]
  split_ifs with hm
  · subst hm; rfl
  · simp

theorem precompR_eq {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (a : E) (g' : X →L[ℝ] F) : B.precompR X a g' = (B a).comp g' := by
  ext1 h; rfl

theorem precompL_eq {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (f' : X →L[ℝ] E) (c : F) : B.precompL X f' c = (B.flip c).comp f' := by
  ext1 h; simp

/-! ## The local form -/

theorem memS (N : ℕ) (n : ℤ) : n ∈ Finset.Icc (-(N : ℤ)) N ↔ ¬ (N : ℝ) < |(n : ℝ)| := by
  rw [Finset.mem_Icc, not_lt, ← abs_le]
  have e : |(n : ℝ)| = ((|n| : ℤ) : ℝ) := by push_cast; rfl
  rw [e]
  exact_mod_cast Iff.rfl

theorem finiteActions_apply {κ : ℝ} (hκ : 0 < κ) {L : ℝ} [Fact (0 < L)] (S : Finset ℤ) (u : L2T L) (m : ℤ) :
    (finiteActions hκ S u : ℤ → ℝ) m = if m ∈ S then Actions hκ u m else 0 := by
  simp only [finiteActions, lp.coeFn_sum, Finset.sum_apply, single_ite]
  rw [Finset.sum_ite_eq]
  rfl

variable {L κ : ℝ} [Fact (0 < L)]

/-- **Local form**: on `U = B(u₀, ρ)` everything in the theorem except the global clauses. -/
theorem local_form (hκ : 0 < κ) (u₀ : L2T L) :
    ∃ ρ : ℝ, 0 < ρ ∧ AnalyticOnNhd ℝ (Actions hκ) (ball u₀ ρ) ∧
    ∃ N : ℕ, ∃ g : L2T L → lp (fun _ : ℤ => ℂ) 2, ∃ r : L2T L → lp (fun _ : ℤ => ℂ) ∞,
      AnalyticOnNhd ℝ g (ball u₀ ρ) ∧ AnalyticOnNhd ℝ r (ball u₀ ρ) ∧
      (∀ u ∈ ball u₀ ρ, ∀ n : ℤ, ¬ (N : ℝ) < |(n : ℝ)| → g u n = 0 ∧ r u n = 0) ∧
      (∀ u ∈ ball u₀ ρ, ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
        Actions hκ u n = ‖g u n‖ ^ 2 * (r u n).re ∧ (r u n).im = 0 ∧ 1 / 2 < (r u n).re ∧ (r u n).re < 3 / 2) ∧
      (∃ R > (0 : ℝ), R ≤ ρ ∧ ∃ M : ℝ, ∃ gc : Cx (L2T L) → lp (fun _ : ℤ => ℂ) 2,
        ∃ rc : Cx (L2T L) → lp (fun _ : ℤ => ℂ) ∞, ∃ Ic : ℤ → Cx (L2T L) → ℂ,
        AnalyticOnNhd ℂ gc (ball (Cx.ι u₀) R) ∧ AnalyticOnNhd ℂ rc (ball (Cx.ι u₀) R) ∧
        (∀ z ∈ ball (Cx.ι u₀) R, ‖gc z‖ ≤ M ∧ ‖rc z‖ ≤ M) ∧
        (∀ x ∈ ball u₀ R, gc (Cx.ι x) = g x ∧ rc (Cx.ι x) = r x) ∧
        ∀ n : ℤ, ¬ (N : ℝ) < |(n : ℝ)| → AnalyticOnNhd ℂ (Ic n) (ball (Cx.ι u₀) R) ∧
          (∀ z ∈ ball (Cx.ι u₀) R, ‖Ic n z‖ ≤ M) ∧ ∀ x ∈ ball u₀ R, Ic n (Cx.ι x) = ((Actions hκ x n : ℝ) : ℂ)) ∧
      (∀ u ∈ ball u₀ ρ, IsCompactOperator (fderiv ℝ (Actions hκ) u)) := by
  classical
  obtain ⟨N, ρ, hρ, b, G, hba, hGr, hGe, htail⟩ := QuantumNLS.RB01Tail.tail_form hκ u₀
  set S : Finset ℤ := Finset.Icc (-(N : ℤ)) N with hS
  set c : ℂ := ((√(L / (4 * κ)) : ℝ) : ℂ) with hc
  set A : L2C →L[ℂ] L2C := c • trunc 2 S with hA
  set g : L2T L → L2C := fun v => A (b v) with hg
  set r : L2T L → LinfC := fun v => trunc ∞ S (G (v, star v)) with hr
  set T : L2T L → L1R := fun v => P1R (P22R (g v) (g v)) (r v) with hT
  have hgn : ∀ v n, g v n = if n ∈ S then 0 else c * b v n := by
    intro v n
    simp only [hg, hA, smul_apply, lp.coeFn_smul, Pi.smul_apply, trunc_apply, smul_eq_mul]
    split_ifs <;> simp
  have hrn : ∀ v n, r v n = if n ∈ S then 0 else G (v, star v) n := fun v n => trunc_apply ∞ S _ n
  have hball : ∀ u ∈ ball u₀ ρ, ‖u - u₀‖ < ρ := fun u hu => by rwa [mem_ball, dist_eq_norm] at hu
  have hgA : ∀ u ∈ ball u₀ ρ, AnalyticAt ℝ g u := fun u hu =>
    (A.analyticAt (b u)).restrictScalars.comp (hba u hu)
  have hrA : ∀ u ∈ ball u₀ ρ, AnalyticAt ℝ r u := fun u hu =>
    ((trunc ∞ S).analyticAt _).restrictScalars.comp (hGr u (hball u hu))
  have hQA : ∀ u ∈ ball u₀ ρ, AnalyticAt ℝ (fun v => P22R (g v) (g v)) u := fun u hu =>
    (P22R.analyticAt_bilinear (g u, g u)).comp (f := fun v => (g v, g v)) ((hgA u hu).prod (hgA u hu))
  have hTA : ∀ u ∈ ball u₀ ρ, AnalyticAt ℝ T u := fun u hu =>
    (P1R.analyticAt_bilinear (P22R (g u) (g u), r u)).comp (f := fun v => (P22R (g v) (g v), r v))
      ((hQA u hu).prod (hrA u hu))
  -- the splitting `I = head + tail`
  have hsplit : ∀ u ∈ ball u₀ ρ, Actions hκ u = finiteActions hκ S u + T u := by
    intro u hu
    apply lp.ext; funext n
    rw [lp.coeFn_add, Pi.add_apply, finiteActions_apply, hT]
    simp only [P1R_apply, P22R_apply, hgn, hrn]
    by_cases hn : n ∈ S
    · simp [hn]
    · have hn' : (N : ℝ) < |(n : ℝ)| := not_not.mp (fun h => hn ((memS N n).2 h))
      simp only [hn, ↓reduceIte, zero_add, real_inner_self_eq_norm_sq]
      exact (htail u (hball u hu) n hn').1
  have hev : ∀ u ∈ ball u₀ ρ, (fun v => finiteActions hκ S v + T v) =ᶠ[𝓝 u] Actions hκ := fun u hu =>
    eventuallyEq_of_mem (isOpen_ball.mem_nhds hu) (fun v hv => (hsplit v hv).symm)
  have hIA : AnalyticOnNhd ℝ (Actions hκ) (ball u₀ ρ) := fun u hu =>
    ((finiteActions_analytic hκ S u).add (hTA u hu)).congr (hev u hu)
  refine ⟨ρ, hρ, hIA, N, g, r, hgA, hrA, fun u _ n hn => ?_, fun u hu n hn => ?_, ?_, fun u hu => ?_⟩
  · have hn' : n ∈ S := (memS N n).2 hn
    exact ⟨by rw [hgn]; simp [hn'], by rw [hrn]; simp [hn']⟩
  · have hn' : n ∉ S := fun h => (memS N n).1 h hn
    obtain ⟨h1, -, h3, h4, h5⟩ := htail u (hball u hu) n hn
    rw [hgn, hrn]; simp only [hn', ↓reduceIte]
    exact ⟨h1, h3, h4, h5⟩
  · -- bounded holomorphic extensions
    obtain ⟨R₁, hR₁, M₁, gc, hga, hgb, hge⟩ :=
      QuantumNLS.RB01Head.ext_of_analyticAt (hba u₀ (mem_ball_self hρ)) A
    obtain ⟨R₂, hR₂, hR₂ρ, M₂, rc, hra, hrb, hre⟩ := hGe S
    obtain ⟨R₃, hR₃, M₃, Ic, hI⟩ := QuantumNLS.RB01Head.head_ext hκ u₀ S
    set R := min (min R₁ R₂) (min R₃ ρ) with hRdef
    have hR : 0 < R := lt_min (lt_min hR₁ hR₂) (lt_min hR₃ hρ)
    have hR1 : R ≤ R₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hR2 : R ≤ R₂ := (min_le_left _ _).trans (min_le_right _ _)
    have hR3 : R ≤ R₃ := (min_le_right _ _).trans (min_le_left _ _)
    have hR4 : R ≤ ρ := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨R, hR, hR4, max (max M₁ M₂) M₃, gc, rc, Ic, fun z hz => hga z (ball_subset_ball hR1 hz),
      fun z hz => hra z (ball_subset_ball hR2 hz), fun z hz => ⟨?_, ?_⟩, fun x hx => ⟨?_, ?_⟩, fun n hn => ?_⟩
    · exact (hgb z (ball_subset_ball hR1 hz)).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hrb z (ball_subset_ball hR2 hz)).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact hge x (ball_subset_ball hR1 hx)
    · exact hre x (ball_subset_ball hR2 hx)
    · obtain ⟨h1, h2, h3⟩ := hI n ((memS N n).2 hn)
      exact ⟨fun z hz => h1 z (ball_subset_ball hR3 hz),
        fun z hz => (h2 z (ball_subset_ball hR3 hz)).trans (le_max_right _ _),
        fun x hx => h3 x (ball_subset_ball hR3 hx)⟩
  · -- compactness of `DI(u)`
    have hgD : HasFDerivAt g (fderiv ℝ g u) u := (hgA u hu).differentiableAt.hasFDerivAt
    have hrD : HasFDerivAt r (fderiv ℝ r u) u := (hrA u hu).differentiableAt.hasFDerivAt
    set g' := fderiv ℝ g u
    set r' := fderiv ℝ r u
    have hQD := P22R.hasFDerivAt_of_bilinear hgD hgD
    have hTD := P1R.hasFDerivAt_of_bilinear hQD hrD
    have hHD : HasFDerivAt (finiteActions hκ S)
        (∑ n ∈ S, (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℝ) 1 n).comp
          (fderiv ℝ (actionCoordinate hκ n) u)) u := by
      unfold finiteActions
      exact HasFDerivAt.fun_sum (A := fun n y => lp.single 1 n (actionCoordinate hκ n y)) (fun n _ =>
        (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℝ) 1 n).hasFDerivAt.comp u
          (coordinate_analytic hκ n u).differentiableAt.hasFDerivAt)
    have hAD := (hHD.add hTD).congr_of_eventuallyEq (hev u hu).symm
    rw [hAD.fderiv, FunLike.coe_add]
    refine IsCompactOperator.add ?_ ?_
    · exact isCompact_sum S _ (fun n _ =>
        (isCompactOperator_of_locallyCompactSpace_rng (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℝ) 1 n)).comp_clm _)
    · have hQ' : IsCompactOperator
          ⇑(P22R.precompR (L2T L) (g u) g' + P22R.precompL (L2T L) g' (g u)) := by
        rw [FunLike.coe_add, precompR_eq, precompL_eq]
        exact ((P22R_compact _).comp_clm g').add ((P22R_flip_compact _).comp_clm g')
      rw [FunLike.coe_add, precompR_eq, precompL_eq]
      exact ((P1R_compact _).comp_clm r').add (hQ'.clm_comp (P1R.flip (r u)))

/-- Real analyticity of the actions at every field. -/
theorem analyticAt_actions (hκ : 0 < κ) (u : L2T L) : AnalyticAt ℝ (Actions hκ) u := by
  obtain ⟨ρ, hρ, h, -⟩ := local_form hκ u
  exact h u (mem_ball_self hρ)

/-- `DI(u)` is compact at every field. -/
theorem compact_derivative (hκ : 0 < κ) (u : L2T L) : IsCompactOperator (fderiv ℝ (Actions hκ) u) := by
  obtain ⟨ρ, hρ, -, N, g, r, -, -, -, -, -, h⟩ := local_form hκ u
  exact h u (mem_ball_self hρ)

/-- Every tail of `D²I(0)` has operator norm at least `2`. -/
theorem hessian_tails (hκ : 0 < κ) (S : Finset ℤ)
    (T : L2T L →L[ℝ] L2T L →L[ℝ] lp (fun _ : ℤ => ℝ) 1)
    (hT : ∀ k, k ∉ S → T (QuantumNLS.Fourier.modeLp L k) (QuantumNLS.Fourier.modeLp L k) k =
      fderiv ℝ (fderiv ℝ (Actions hκ)) 0 (QuantumNLS.Fourier.modeLp L k) (QuantumNLS.Fourier.modeLp L k) k) :
    2 ≤ ‖T‖ :=
  QuantumNLS.TerraMultiRound30HessianBridge.hessian_tail_lower_bound_of_derivative_field hκ
    (fderiv ℝ (Actions hκ)) (fderiv ℝ (fderiv ℝ (Actions hκ)) 0) T
    (fun u => (analyticAt_actions hκ u).differentiableAt.hasFDerivAt)
    ((analyticAt_actions hκ 0).fderiv.differentiableAt.hasFDerivAt) S hT

/-- **Theorem `thm:global-B01-actions`** (R-EC25334D). For every `u₀ ∈ L²(𝕋_L;ℂ)` there is an open neighborhood `U`
of `u₀` on which `u ↦ (I_n(u))_{n∈ℤ}` is real analytic into `ℓ¹(ℤ)`. There is an integer `N` and maps
`g : U → ℓ²` and `r : U → ℓ∞`, vanishing at `|n| ≤ N` (so valued in `ℓ²({|n| > N})`, `ℓ∞({|n| > N})`), real analytic,
with `I_n = |g_n|² r_n` for `|n| > N`, `r_n` real with `1/2 < r_n < 3/2`. On a smaller ball `B(u₀, R) ⊆ U`, `g`, `r`
and the finitely many actions `I_n`, `|n| ≤ N`, have bounded holomorphic extensions on `B(ι u₀, R)` in the
complexification `Cx(L²(𝕋_L))`. For each `u`, `DI(u) : L²_ℝ → ℓ¹` is compact. Every tail of `D²I(0)` (an operator
agreeing with `D²I(0)` on the diagonal entries outside a finite set) has norm `≥ 2`, so the tails of `D²I` do not
converge in operator norm, already at zero. -/
theorem global_B01_actions (hκ : 0 < κ) (u₀ : L2T L) :
    (∃ U : Set (L2T L), IsOpen U ∧ u₀ ∈ U ∧ AnalyticOnNhd ℝ (Actions hκ) U ∧
      ∃ N : ℕ, ∃ g : L2T L → lp (fun _ : ℤ => ℂ) 2, ∃ r : L2T L → lp (fun _ : ℤ => ℂ) ∞,
        AnalyticOnNhd ℝ g U ∧ AnalyticOnNhd ℝ r U ∧
        (∀ u ∈ U, ∀ n : ℤ, ¬ (N : ℝ) < |(n : ℝ)| → g u n = 0 ∧ r u n = 0) ∧
        (∀ u ∈ U, ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
          Actions hκ u n = ‖g u n‖ ^ 2 * (r u n).re ∧ (r u n).im = 0 ∧ 1 / 2 < (r u n).re ∧
            (r u n).re < 3 / 2) ∧
        (∃ R > (0 : ℝ), ball u₀ R ⊆ U ∧ ∃ M : ℝ, ∃ gc : Cx (L2T L) → lp (fun _ : ℤ => ℂ) 2,
          ∃ rc : Cx (L2T L) → lp (fun _ : ℤ => ℂ) ∞, ∃ Ic : ℤ → Cx (L2T L) → ℂ,
          AnalyticOnNhd ℂ gc (ball (Cx.ι u₀) R) ∧ AnalyticOnNhd ℂ rc (ball (Cx.ι u₀) R) ∧
          (∀ z ∈ ball (Cx.ι u₀) R, ‖gc z‖ ≤ M ∧ ‖rc z‖ ≤ M) ∧
          (∀ x ∈ ball u₀ R, gc (Cx.ι x) = g x ∧ rc (Cx.ι x) = r x) ∧
          ∀ n : ℤ, ¬ (N : ℝ) < |(n : ℝ)| → AnalyticOnNhd ℂ (Ic n) (ball (Cx.ι u₀) R) ∧
            (∀ z ∈ ball (Cx.ι u₀) R, ‖Ic n z‖ ≤ M) ∧
            ∀ x ∈ ball u₀ R, Ic n (Cx.ι x) = ((Actions hκ x n : ℝ) : ℂ))) ∧
    (∀ u : L2T L, IsCompactOperator (fderiv ℝ (Actions hκ) u)) ∧
    (∀ (S : Finset ℤ) (T : L2T L →L[ℝ] L2T L →L[ℝ] lp (fun _ : ℤ => ℝ) 1),
      (∀ k, k ∉ S → T (QuantumNLS.Fourier.modeLp L k) (QuantumNLS.Fourier.modeLp L k) k =
        fderiv ℝ (fderiv ℝ (Actions hκ)) 0 (QuantumNLS.Fourier.modeLp L k) (QuantumNLS.Fourier.modeLp L k) k) →
      2 ≤ ‖T‖) := by
  obtain ⟨ρ, hρ, hIA, N, g, r, hga, hra, h0, h1, ⟨R, hR, hRρ, M, gc, rc, Ic, hext⟩, -⟩ := local_form hκ u₀
  exact ⟨⟨ball u₀ ρ, isOpen_ball, mem_ball_self hρ, hIA, N, g, r, hga, hra, h0, h1,
    ⟨R, hR, ball_subset_ball hRρ, M, gc, rc, Ic, hext⟩⟩, compact_derivative hκ, hessian_tails hκ⟩

end QuantumNLS.RB01Main

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RB01Main.P22R_compact
#print axioms QuantumNLS.RB01Main.P1R_compact
#print axioms QuantumNLS.RB01Main.local_form
#print axioms QuantumNLS.RB01Main.analyticAt_actions
#print axioms QuantumNLS.RB01Main.compact_derivative
#print axioms QuantumNLS.RB01Main.hessian_tails
#print axioms QuantumNLS.RB01Main.global_B01_actions
