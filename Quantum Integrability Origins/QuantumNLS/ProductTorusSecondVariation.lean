import QuantumNLS.ProductTorusFixedVector
import QuantumNLS.ProductTorusSymplectic

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T5c: twice differentiable flows and the second variational equation

Source: `chapters/global/product_torus.tex`, proof, "The product topology and full initial-point regularity", last
paragraph ("Repeating this argument with the higher variational equations ..."), and "Averaging the primitive"
("... justifies differentiation under the scalar integral"; "Since `d(T_θ^*α) = T_θ^*ω = ω`, ..."). The source
assumes `𝓘` real analytic; this stage uses only `D𝓘 ∈ C²` (`ContDiff ℝ 2 DI`), a consequence.

Route (the same Gronwall pattern as stages T2c/T2d, one order higher):
* the augmented autonomous field `F(x, J) = (X_θ x, DX_θ(x) ∘ J)` on `E × L(E)` is `C¹` (`augF_contDiff`), and
  `Φ^t(x, J) = (φ_θ^t x, Dφ_θ^t(x) ∘ J)` is a family of global solutions (`augΦ_hasDerivAt`, from the T2d
  variational equation); T2c `local_diff` applied to `(F, Φ)` gives short-time differentiability of
  `x ↦ Dφ_θ^t(x)` with an explicit derivative (`local_diff_aug`, `hasFDerivAt_fderiv_flow_short`);
* a finite subcover of the compact fibre gives one short time (`uniform_short2`), and the chain rule along
  `Dφ^{t}(y) = Dφ^{t-m}(φ^m y) ∘ Dφ^m(y)` composes short steps: **`differentiableAt_fderiv_flow`** (every `φ_θ^t`
  is twice Fréchet differentiable at every point);
* `right_deriv2_zero`, `deriv2_zero`: `d/dr|₀ D²φ_θ^r(p) = D²X_θ(p)` (the augmented variational solution at `0`;
  negative times via `−θ`);
* **`hasDerivAt_fderiv2_flow`**, the second variational equation
  `d/dt D²φ^t(x) = DX(φ^t x) ∘ D²φ^t(x) + D²X(φ^t x)[Dφ^t(x)·, Dφ^t(x)·]`
  (`hasDerivAt_fderiv2_flow_apply` for a fixed pair of tangent vectors);
* `fderiv2_flow_symm` (symmetry of `D²φ_θ^t(x)`), `norm_fderiv2_X_le` (`‖D²X_θ‖ ≤ ‖θ‖_∞‖D³𝓘‖/2`), and the
  Gronwall bound **`norm_fderiv2_flow_le`**: `‖D²φ_θ^t(x)‖ ≤ K₂ e^{3Kt}/K` when `‖DX_θ‖ ≤ K`, `‖D²X_θ‖ ≤ K₂` on the
  fibre of `x` (`t ≥ 0`).
GP-04 note: no path-space Picard map is differentiated and no fixed-point theorem is used (as in T2c).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open Filter Topology Set Metric
open scoped InnerProductSpace NNReal

noncomputable section

namespace QuantumNLS.ProductTorusSecondVariation

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusLocalDiff
  QuantumNLS.ProductTorusVariational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-! ## 1. The augmented system -/

/-- The augmented field `F(x, J) = (X_θ x, DX_θ(x) ∘ J)`. -/
def augF (DI : E → (E →L[ℝ] L1 ℝ)) (θ : Linf) (V : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (X DI θ V.1, (fderiv ℝ (X DI θ) V.1).comp V.2)

/-- Its flow `Φ^t(x, J) = (φ_θ^t x, Dφ_θ^t(x) ∘ J)`. -/
def augΦ (DI : E → (E →L[ℝ] L1 ℝ)) (θ : Linf) (t : ℝ) (V : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (flow DI θ t V.1, (fderiv ℝ (flow DI θ t) V.1).comp V.2)

theorem augF_contDiff (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) : ContDiff ℝ 1 (augF DI θ) := by
  have hdX : ContDiff ℝ 1 (fderiv ℝ (X DI θ)) := (X_contDiff h2 θ).fderiv_right (le_of_eq one_add_one_eq_two)
  exact ((X_contDiff h.contDiff θ).comp contDiff_fst).prodMk ((hdX.comp contDiff_fst).clm_comp contDiff_snd)

theorem augΦ_hasDerivAt (h : Hyp I DI) (θ : Linf) (V : E × (E →L[ℝ] E)) (t : ℝ) :
    HasDerivAt (fun t => augΦ DI θ t V) (augF DI θ (augΦ DI θ t V)) t := by
  have h1 := hasDerivAt_flow h θ V.1 t
  have h2 := (hasDerivAt_fderiv_flow h θ V.1 t).clm_comp (hasDerivAt_const t V.2)
  have h3 := h1.prodMk h2
  show HasDerivAt (fun t => (flow DI θ t V.1, (fderiv ℝ (flow DI θ t) V.1).comp V.2)) _ t
  convert h3 using 1
  simp [augF, augΦ, ContinuousLinearMap.comp_assoc]

theorem augΦ_zero (h : Hyp I DI) (θ : Linf) (V : E × (E →L[ℝ] E)) : augΦ DI θ 0 V = V := by
  simp [augΦ, flow_zero h, fderiv_flow_zero h]

/-- T2c `local_diff` for the augmented system, at initial points `(x, id)`. -/
theorem local_diff_aug (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (p : E) :
    ∃ ρ > (0 : ℝ), ∃ τ > (0 : ℝ), ∀ x ∈ ball p ρ,
      ∃ J : ℝ → (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)),
        J 0 = ContinuousLinearMap.id ℝ (E × (E →L[ℝ] E)) ∧
        (∀ s ∈ Icc 0 τ, HasDerivWithinAt J
          ((fderiv ℝ (augF DI θ) (augΦ DI θ s (x, ContinuousLinearMap.id ℝ E))).comp (J s)) (Icc 0 τ) s) ∧
        ∀ t ∈ Icc 0 τ, HasFDerivAt (augΦ DI θ t) (J t) (x, ContinuousLinearMap.id ℝ E) := by
  obtain ⟨ρ, hρ, τ, hτ, H⟩ := local_diff (f := augF DI θ) (φ := augΦ DI θ) (augF_contDiff h h2 θ)
    (fun V t => augΦ_hasDerivAt h θ V t) (augΦ_zero h θ) (p, ContinuousLinearMap.id ℝ E)
  refine ⟨ρ, hρ, τ, hτ, fun x hx => ?_⟩
  have hx' : (x, ContinuousLinearMap.id ℝ E) ∈ ball (p, ContinuousLinearMap.id ℝ E) ρ := by
    rw [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hx
  obtain ⟨J, -, hJ0, hJd, hJt⟩ := H _ hx'
  exact ⟨J, hJ0, hJd, hJt⟩

/-- The embedding derivative `ι' = (id, 0) : E → E × L(E)`. -/
def ιd (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : E →L[ℝ] E × (E →L[ℝ] E) :=
  (ContinuousLinearMap.id ℝ E).prod 0

/-- From a derivative of `Φ^t` at `(x, id)` to a derivative of `y ↦ Dφ^t(y)` at `x`. -/
theorem hasFDerivAt_fderiv_flow_short (θ : Linf) {x : E} {t : ℝ}
    {J' : (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E))}
    (hJ : HasFDerivAt (augΦ DI θ t) J' (x, ContinuousLinearMap.id ℝ E)) :
    HasFDerivAt (fderiv ℝ (flow DI θ t)) ((ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp (J'.comp (ιd E))) x := by
  have hι : HasFDerivAt (fun y : E => (y, ContinuousLinearMap.id ℝ E)) (ιd E) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const _ x)
  have hc := (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp x (hJ.comp x hι)
  refine hc.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [augΦ]

/-! ## 2. Twice differentiable flows -/

/-- One short time for the whole compact fibre (second order). -/
theorem uniform_short2 (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (u : E) :
    ∃ τ > (0 : ℝ), ∀ w ∈ I ⁻¹' {I u}, ∀ t ∈ Icc 0 τ, DifferentiableAt ℝ (fderiv ℝ (flow DI θ t)) w := by
  classical
  have H (x : I ⁻¹' {I u}) := local_diff_aug h h2 θ (x : E)
  choose ρ hρ τ hτ hJ using H
  obtain ⟨s, hs⟩ := (h.fibre_compact u).elim_finite_subcover
    (fun x : I ⁻¹' {I u} => ball (x : E) (ρ x)) (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hρ ⟨x, hx⟩)⟩)
  have huF : u ∈ I ⁻¹' {I u} := Set.mem_singleton (I u)
  have hne : s.Nonempty := by
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp (hs huF)
    exact ⟨i, hi⟩
  refine ⟨s.inf' hne τ, ?_, fun w hw t ht => ?_⟩
  · show (0 : ℝ) < s.inf' hne τ
    rw [Finset.lt_inf'_iff]
    exact fun i _ => hτ i
  obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.mp (hs hw)
  obtain ⟨J, -, -, hJt⟩ := hJ i w hwi
  exact (hasFDerivAt_fderiv_flow_short θ (hJt t ⟨ht.1, ht.2.trans (Finset.inf'_le _ hi)⟩)).differentiableAt

theorem differentiableAt_fderiv_flow_nonneg (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (u : E) {t : ℝ}
    (ht : 0 ≤ t) : DifferentiableAt ℝ (fderiv ℝ (flow DI θ t)) u := by
  obtain ⟨τ, hτ, hshort⟩ := uniform_short2 h h2 θ u
  have key : ∀ n : ℕ, ∀ w ∈ I ⁻¹' {I u}, ∀ t ∈ Icc 0 (n * τ),
      DifferentiableAt ℝ (fderiv ℝ (flow DI θ t)) w := by
    intro n
    induction n with
    | zero =>
      intro w hw t ht
      have ht0 : t = 0 := le_antisymm (by simpa using ht.2) ht.1
      subst ht0
      exact hshort w hw 0 ⟨le_rfl, hτ.le⟩
    | succ n ih =>
      intro w hw t ht
      have ht2 : t ≤ n * τ + τ := by
        have := ht.2
        rw [Nat.cast_succ, add_mul, one_mul] at this
        exact this
      have hs0 : 0 ≤ min t τ := le_min ht.1 hτ.le
      have hsτ : min t τ ≤ τ := min_le_right _ _
      have hts : t - min t τ ∈ Icc 0 (n * τ) := by
        constructor
        · linarith [min_le_left t τ]
        · rcases le_total t τ with h1 | h1
          · rw [min_eq_left h1, sub_self]
            positivity
          · rw [min_eq_right h1]
            linarith
      have hcomp : fderiv ℝ (flow DI θ t) = fun y =>
          (fderiv ℝ (flow DI θ (t - min t τ)) (flow DI θ (min t τ) y)).comp (fderiv ℝ (flow DI θ (min t τ)) y) := by
        funext y
        rw [← fderiv_flow_add h θ (t - min t τ) (min t τ) y, sub_add_cancel]
      rw [hcomp]
      have hA : DifferentiableAt ℝ (fun y => fderiv ℝ (flow DI θ (t - min t τ)) (flow DI θ (min t τ) y)) w :=
        (ih _ (mem_fibre_flow h θ hw _) _ hts).comp w (differentiableAt_flow h θ _ w)
      exact hA.clm_comp (hshort w hw _ ⟨hs0, hsτ⟩)
  obtain ⟨n, hn⟩ := exists_nat_ge (t / τ)
  exact key n u (Set.mem_singleton (I u)) t ⟨ht, by rwa [div_le_iff₀ hτ] at hn⟩

/-- **Every time-`t` map of the flow is twice Fréchet differentiable at every point.** -/
theorem differentiableAt_fderiv_flow (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (t : ℝ) (u : E) :
    DifferentiableAt ℝ (fderiv ℝ (flow DI θ t)) u := by
  rcases le_total 0 t with ht | ht
  · exact differentiableAt_fderiv_flow_nonneg h h2 θ u ht
  · rw [flow_eq_neg h θ t]
    exact differentiableAt_fderiv_flow_nonneg h h2 (-θ) u (by linarith)

/-- Symmetry of the second derivative of the flow. -/
theorem fderiv2_flow_symm (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (t : ℝ) (x a b : E) :
    fderiv ℝ (fderiv ℝ (flow DI θ t)) x a b = fderiv ℝ (fderiv ℝ (flow DI θ t)) x b a :=
  second_derivative_symmetric (f := flow DI θ t) (fun y => (differentiableAt_flow h θ t y).hasFDerivAt)
    (differentiableAt_fderiv_flow h h2 θ t x).hasFDerivAt a b

theorem fderiv2_flow_zero (h : Hyp I DI) (θ : Linf) (x : E) : fderiv ℝ (fderiv ℝ (flow DI θ 0)) x = 0 := by
  have : fderiv ℝ (flow DI θ 0) = fun _ => ContinuousLinearMap.id ℝ E := funext (fderiv_flow_zero h θ)
  rw [this]
  exact fderiv_const_apply _

/-! ## 3. The second variational equation -/

theorem fderiv2_X_neg (θ : Linf) (p : E) :
    fderiv ℝ (fderiv ℝ (X DI (-θ))) p = -fderiv ℝ (fderiv ℝ (X DI θ)) p := by
  have : fderiv ℝ (X DI (-θ)) = fun q => -fderiv ℝ (X DI θ) q := funext (fderiv_X_neg θ)
  rw [this]
  exact fderiv_fun_neg

/-- Right derivative at `0` of `r ↦ D²φ^r(p)`. -/
theorem right_deriv2_zero (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (p : E) :
    HasDerivWithinAt (fun r => fderiv ℝ (fderiv ℝ (flow DI θ r)) p) (fderiv ℝ (fderiv ℝ (X DI θ)) p) (Ici 0) 0 := by
  obtain ⟨ρ, hρ, τ, hτ, H⟩ := local_diff_aug h h2 θ p
  obtain ⟨J, hJ0, hJd, hJt⟩ := H p (mem_ball_self hρ)
  have hval : ∀ r ∈ Icc 0 τ, fderiv ℝ (fderiv ℝ (flow DI θ r)) p =
      (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp ((J r).comp (ιd E)) := fun r hr =>
    (hasFDerivAt_fderiv_flow_short θ (hJt r hr)).fderiv
  have h1 : HasDerivWithinAt J (fderiv ℝ (augF DI θ) (p, ContinuousLinearMap.id ℝ E)) (Icc 0 τ) 0 := by
    have := hJd 0 ⟨le_rfl, hτ.le⟩
    rwa [augΦ_zero h, hJ0, ContinuousLinearMap.comp_id] at this
  have h1' : HasDerivWithinAt (fun r => (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp ((J r).comp (ιd E)))
      ((ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp
        ((fderiv ℝ (augF DI θ) (p, ContinuousLinearMap.id ℝ E)).comp (ιd E))) (Icc 0 τ) 0 := by
    have := (hasDerivWithinAt_const (0 : ℝ) (Icc 0 τ) (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))).clm_comp
      (h1.clm_comp (hasDerivWithinAt_const (0 : ℝ) (Icc 0 τ) (ιd E)))
    convert this using 1
    simp
  have hid : (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp
      ((fderiv ℝ (augF DI θ) (p, ContinuousLinearMap.id ℝ E)).comp (ιd E)) = fderiv ℝ (fderiv ℝ (X DI θ)) p := by
    have hF : HasFDerivAt (augF DI θ) (fderiv ℝ (augF DI θ) (p, ContinuousLinearMap.id ℝ E))
        (p, ContinuousLinearMap.id ℝ E) :=
      ((augF_contDiff h h2 θ).differentiable one_ne_zero _).hasFDerivAt
    have hι : HasFDerivAt (fun y : E => (y, ContinuousLinearMap.id ℝ E)) (ιd E) p :=
      (hasFDerivAt_id p).prodMk (hasFDerivAt_const _ p)
    have hc := (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp p (hF.comp p hι)
    refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).fderiv.symm
    simp [augF]
  rw [hid] at h1'
  have h2' : HasDerivWithinAt (fun r => (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp ((J r).comp (ιd E)))
      (fderiv ℝ (fderiv ℝ (X DI θ)) p) (Ici 0) 0 :=
    (hasDerivWithinAt_inter (Iio_mem_nhds hτ)).1
      (h1'.mono fun x hx => ⟨(mem_Ici.1 hx.1), (mem_Iio.1 hx.2).le⟩)
  refine h2'.congr_of_eventuallyEq ?_ (hval 0 ⟨le_rfl, hτ.le⟩)
  filter_upwards [inter_mem_nhdsWithin (Ici (0 : ℝ)) (Iio_mem_nhds hτ)] with r hr
  exact hval r ⟨mem_Ici.1 hr.1, (mem_Iio.1 hr.2).le⟩

/-- Two-sided derivative at `0` of `r ↦ D²φ^r(p)`. -/
theorem deriv2_zero (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (p : E) :
    HasDerivAt (fun r => fderiv ℝ (fderiv ℝ (flow DI θ r)) p) (fderiv ℝ (fderiv ℝ (X DI θ)) p) 0 := by
  have hR := right_deriv2_zero h h2 θ p
  have hL0 := right_deriv2_zero h h2 (-θ) p
  have hneg : HasDerivWithinAt (fun r : ℝ => -r) (-1) (Iic 0) 0 := (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt
  have hmaps : MapsTo (fun r : ℝ => -r) (Iic 0) (Ici 0) := fun r hr => by
    simp only [mem_Iic, mem_Ici] at hr ⊢
    linarith
  have hL0' : HasDerivWithinAt (fun r => fderiv ℝ (fderiv ℝ (flow DI (-θ) r)) p)
      (fderiv ℝ (fderiv ℝ (X DI (-θ))) p) (Ici 0) ((fun r : ℝ => -r) 0) := by
    simp only [neg_zero]
    exact hL0
  have hL1 := hL0'.scomp 0 hneg hmaps
  have hL : HasDerivWithinAt (fun r => fderiv ℝ (fderiv ℝ (flow DI θ r)) p) (fderiv ℝ (fderiv ℝ (X DI θ)) p)
      (Iic 0) 0 := by
    have he : (fun r => fderiv ℝ (fderiv ℝ (flow DI θ r)) p) =
        (fun r => fderiv ℝ (fderiv ℝ (flow DI (-θ) r)) p) ∘ (fun r : ℝ => -r) := by
      funext r
      show fderiv ℝ (fderiv ℝ (flow DI θ r)) p = fderiv ℝ (fderiv ℝ (flow DI (-θ) (-r))) p
      rw [flow_eq_neg h θ r]
    rw [he]
    convert hL1 using 1
    rw [fderiv2_X_neg, smul_neg, neg_one_smul, neg_neg]
  have hU := hL.union hR
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at hU
  exact hU

/-- Chain rule for the second derivative along the group law. -/
theorem fderiv2_flow_add (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (s t : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (flow DI θ s)) x =
      (ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (flow DI θ (s - t)) (flow DI θ t x))).comp
          (fderiv ℝ (fderiv ℝ (flow DI θ t)) x) +
        ((ContinuousLinearMap.compL ℝ E E E).flip (fderiv ℝ (flow DI θ t) x)).comp
          ((fderiv ℝ (fderiv ℝ (flow DI θ (s - t))) (flow DI θ t x)).comp (fderiv ℝ (flow DI θ t) x)) := by
  have he : fderiv ℝ (flow DI θ s) = fun y =>
      (fderiv ℝ (flow DI θ (s - t)) (flow DI θ t y)).comp (fderiv ℝ (flow DI θ t) y) := by
    funext y
    rw [← fderiv_flow_add h θ (s - t) t y, sub_add_cancel]
  have hc : DifferentiableAt ℝ (fun y => fderiv ℝ (flow DI θ (s - t)) (flow DI θ t y)) x :=
    (differentiableAt_fderiv_flow h h2 θ (s - t) (flow DI θ t x)).comp x (differentiableAt_flow h θ t x)
  have hd : DifferentiableAt ℝ (fderiv ℝ (flow DI θ t)) x := differentiableAt_fderiv_flow h h2 θ t x
  have hcd : fderiv ℝ (fun y => fderiv ℝ (flow DI θ (s - t)) (flow DI θ t y)) x =
      (fderiv ℝ (fderiv ℝ (flow DI θ (s - t))) (flow DI θ t x)).comp (fderiv ℝ (flow DI θ t) x) :=
    fderiv_comp x (differentiableAt_fderiv_flow h h2 θ (s - t) (flow DI θ t x)) (differentiableAt_flow h θ t x)
  rw [he, fderiv_clm_comp hc hd, hcd]

/-- **The second variational equation**
`d/dt D²φ^t(x) = DX(φ^t x) ∘ D²φ^t(x) + D²X(φ^t x)[Dφ^t(x)·] ∘ Dφ^t(x)`. -/
theorem hasDerivAt_fderiv2_flow (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (x : E) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (flow DI θ s)) x)
      ((ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (X DI θ) (flow DI θ t x))).comp
          (fderiv ℝ (fderiv ℝ (flow DI θ t)) x) +
        ((ContinuousLinearMap.compL ℝ E E E).flip (fderiv ℝ (flow DI θ t) x)).comp
          ((fderiv ℝ (fderiv ℝ (X DI θ)) (flow DI θ t x)).comp (fderiv ℝ (flow DI θ t) x))) t := by
  have he : (fun s => fderiv ℝ (fderiv ℝ (flow DI θ s)) x) = fun s =>
      (ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (flow DI θ (s - t)) (flow DI θ t x))).comp
          (fderiv ℝ (fderiv ℝ (flow DI θ t)) x) +
        ((ContinuousLinearMap.compL ℝ E E E).flip (fderiv ℝ (flow DI θ t) x)).comp
          ((fderiv ℝ (fderiv ℝ (flow DI θ (s - t))) (flow DI θ t x)).comp (fderiv ℝ (flow DI θ t) x)) :=
    funext fun s => fderiv2_flow_add h h2 θ s t x
  rw [he]
  have ha : HasDerivAt (fun s => fderiv ℝ (flow DI θ (s - t)) (flow DI θ t x))
      (fderiv ℝ (X DI θ) (flow DI θ t x)) t :=
    HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact deriv_zero h θ (flow DI θ t x))
  have hb : HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (flow DI θ (s - t))) (flow DI θ t x))
      (fderiv ℝ (fderiv ℝ (X DI θ)) (flow DI θ t x)) t :=
    HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact deriv2_zero h h2 θ (flow DI θ t x))
  have h1 := ((ContinuousLinearMap.compL ℝ E E E).hasFDerivAt.comp_hasDerivAt t ha).clm_comp
    (hasDerivAt_const t (fderiv ℝ (fderiv ℝ (flow DI θ t)) x))
  have h3 := (hasDerivAt_const t ((ContinuousLinearMap.compL ℝ E E E).flip (fderiv ℝ (flow DI θ t) x))).clm_comp
    (hb.clm_comp (hasDerivAt_const t (fderiv ℝ (flow DI θ t) x)))
  refine (h1.add h3).congr_deriv ?_
  simp

/-- The fixed-pair second variational equation for `v(t) = D²φ^t(x)[a, b]`. -/
theorem hasDerivAt_fderiv2_flow_apply (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (x a b : E) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (flow DI θ s)) x a b)
      (fderiv ℝ (X DI θ) (flow DI θ t x) (fderiv ℝ (fderiv ℝ (flow DI θ t)) x a b) +
        fderiv ℝ (fderiv ℝ (X DI θ)) (flow DI θ t x) (fderiv ℝ (flow DI θ t) x a) (fderiv ℝ (flow DI θ t) x b)) t := by
  have hc := ((hasDerivAt_fderiv2_flow h h2 θ x t).clm_apply (hasDerivAt_const t a)).clm_apply
    (hasDerivAt_const t b)
  convert hc using 1
  simp

theorem continuous_fderiv2_flow (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (x : E) :
    Continuous (fun s => fderiv ℝ (fderiv ℝ (flow DI θ s)) x) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_fderiv2_flow h h2 θ x s).continuousAt

/-! ## 4. Bounds -/

/-- `X_θ`'s derivative as a bounded linear image of `D𝓘`: `DX_θ(u) = L_θ(D²𝓘(u))`. -/
def Lθ (θ : Linf) : (E →L[ℝ] E →L[ℝ] L1 ℝ) →L[ℝ] (E →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E WinvL).comp
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] L1 ℝ) (E →L[ℝ] ℝ) (ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ)))

theorem Lθ_apply_apply (θ : Linf) (D : E →L[ℝ] E →L[ℝ] L1 ℝ) (b : E) :
    Lθ θ D b = Winv ((pair θ).comp (D b)) := by
  simp only [Lθ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply, WinvL_apply]

theorem fderiv_X_eq_L (h : Hyp I DI) (θ : Linf) : fderiv ℝ (X DI θ) = fun v => Lθ θ (fderiv ℝ DI v) := by
  funext v
  ext b
  rw [Lθ_apply_apply, fderiv_X_apply h]

/-- `‖D²X_θ(u)‖ ≤ ‖θ‖_∞ ‖D³𝓘(u)‖ / 2` (here `D³𝓘 = D²(D𝓘)`). -/
theorem norm_fderiv2_X_le (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (u : E) :
    ‖fderiv ℝ (fderiv ℝ (X DI θ)) u‖ ≤ ‖θ‖ * ‖fderiv ℝ (fderiv ℝ DI) u‖ / 2 := by
  have hDD : HasFDerivAt (fderiv ℝ DI) (fderiv ℝ (fderiv ℝ DI) u) u :=
    (((h2.fderiv_right (le_of_eq one_add_one_eq_two)).differentiable one_ne_zero) u).hasFDerivAt
  have hc : HasFDerivAt (fun v => Lθ θ (fderiv ℝ DI v)) ((Lθ θ).comp (fderiv ℝ (fderiv ℝ DI) u)) u :=
    (Lθ (E := E) θ).hasFDerivAt.comp u hDD
  rw [fderiv_X_eq_L h θ, hc.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b => ?_
  rw [ContinuousLinearMap.comp_apply, Lθ_apply_apply, norm_Winv]
  have h1 : ‖(pair θ).comp (fderiv ℝ (fderiv ℝ DI) u a b)‖ ≤ ‖θ‖ * ‖fderiv ℝ (fderiv ℝ DI) u a b‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (norm_pair_le θ) (norm_nonneg _))
  have h3 : ‖fderiv ℝ (fderiv ℝ DI) u a b‖ ≤ ‖fderiv ℝ (fderiv ℝ DI) u‖ * ‖a‖ * ‖b‖ :=
    ((fderiv ℝ (fderiv ℝ DI) u a).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ DI) u).le_opNorm a) (norm_nonneg _))
  have h4 := mul_le_mul_of_nonneg_left h3 (norm_nonneg θ)
  calc ‖(pair θ).comp (fderiv ℝ (fderiv ℝ DI) u a b)‖ / 2 ≤ ‖θ‖ * ‖fderiv ℝ (fderiv ℝ DI) u a b‖ / 2 := by
        linarith
    _ ≤ ‖θ‖ * (‖fderiv ℝ (fderiv ℝ DI) u‖ * ‖a‖ * ‖b‖) / 2 := by linarith
    _ = ‖θ‖ * ‖fderiv ℝ (fderiv ℝ DI) u‖ / 2 * ‖a‖ * ‖b‖ := by ring

omit [CompleteSpace E] in
theorem norm_Q_le (a : E →L[ℝ] E) (G B : E →L[ℝ] E →L[ℝ] E) (A : E →L[ℝ] E) :
    ‖(ContinuousLinearMap.compL ℝ E E E a).comp G + ((ContinuousLinearMap.compL ℝ E E E).flip A).comp (B.comp A)‖ ≤
      ‖a‖ * ‖G‖ + ‖B‖ * ‖A‖ * ‖A‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
    calc ‖a.comp (G v)‖ ≤ ‖a‖ * ‖G v‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖a‖ * (‖G‖ * ‖v‖) := mul_le_mul_of_nonneg_left (G.le_opNorm v) (norm_nonneg _)
      _ = ‖a‖ * ‖G‖ * ‖v‖ := by ring
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply]
    calc ‖(B (A v)).comp A‖ ≤ ‖B (A v)‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖B‖ * ‖A v‖) * ‖A‖ := mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
      _ ≤ (‖B‖ * (‖A‖ * ‖v‖)) * ‖A‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖B‖ * ‖A‖ * ‖A‖ * ‖v‖ := by ring

/-- **Gronwall bound for the second derivative of the flow** (`t ≥ 0`): if `‖DX_θ‖ ≤ K` and `‖D²X_θ‖ ≤ K₂` on the
fibre of `x`, then `‖D²φ_θ^t(x)‖ ≤ K₂ e^{Kt} e^{Kt} / K · e^{Kt}`. -/
theorem norm_fderiv2_flow_le (h : Hyp I DI) (h2 : ContDiff ℝ 2 DI) (θ : Linf) (x : E) {K K₂ : ℝ} (hK0 : 0 < K)
    (hK : ∀ w ∈ I ⁻¹' {I x}, ‖fderiv ℝ (X DI θ) w‖ ≤ K)
    (hK₂ : ∀ w ∈ I ⁻¹' {I x}, ‖fderiv ℝ (fderiv ℝ (X DI θ)) w‖ ≤ K₂) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (flow DI θ t)) x‖ ≤
      K₂ * Real.exp (K * t) * Real.exp (K * t) / K * Real.exp (K * t) := by
  have hK₂0 : 0 ≤ K₂ := (norm_nonneg _).trans (hK₂ x (Set.mem_singleton (I x)))
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (a := 0) (b := t) (K := K)
    (ε := K₂ * Real.exp (K * t) * Real.exp (K * t)) (δ := 0)
    (f := fun s => fderiv ℝ (fderiv ℝ (flow DI θ s)) x)
    (f' := fun s => (ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (X DI θ) (flow DI θ s x))).comp
          (fderiv ℝ (fderiv ℝ (flow DI θ s)) x) +
        ((ContinuousLinearMap.compL ℝ E E E).flip (fderiv ℝ (flow DI θ s) x)).comp
          ((fderiv ℝ (fderiv ℝ (X DI θ)) (flow DI θ s x)).comp (fderiv ℝ (flow DI θ s) x)))
    (continuous_fderiv2_flow h h2 θ x).continuousOn
    (fun s _ => (hasDerivAt_fderiv2_flow h h2 θ x s).hasDerivWithinAt)
    (by
      show ‖fderiv ℝ (fderiv ℝ (flow DI θ 0)) x‖ ≤ 0
      rw [fderiv2_flow_zero h, norm_zero])
    (fun s hs => by
      have hp := mem_fibre_flow h θ (Set.mem_singleton (I x)) s
      have hA := norm_fderiv_flow_le_nonneg h θ x hK hs.1
      have hA' : ‖fderiv ℝ (flow DI θ s) x‖ ≤ Real.exp (K * t) :=
        hA.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2.le hK0.le))
      refine (norm_Q_le _ _ _ _).trans ?_
      have e1 := mul_le_mul_of_nonneg_right (hK _ hp) (norm_nonneg (fderiv ℝ (fderiv ℝ (flow DI θ s)) x))
      have e2 : ‖fderiv ℝ (fderiv ℝ (X DI θ)) (flow DI θ s x)‖ * ‖fderiv ℝ (flow DI θ s) x‖ *
          ‖fderiv ℝ (flow DI θ s) x‖ ≤ K₂ * Real.exp (K * t) * Real.exp (K * t) :=
        mul_le_mul (mul_le_mul (hK₂ _ hp) hA' (norm_nonneg _) hK₂0) hA' (norm_nonneg _) (by positivity)
      linarith)
    t ⟨ht, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hK0.ne'] at hg
  simp only [sub_zero, zero_mul, zero_add] at hg
  calc ‖fderiv ℝ (fderiv ℝ (flow DI θ t)) x‖
      ≤ K₂ * Real.exp (K * t) * Real.exp (K * t) / K * (Real.exp (K * t) - 1) := hg
    _ ≤ K₂ * Real.exp (K * t) * Real.exp (K * t) / K * Real.exp (K * t) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end QuantumNLS.ProductTorusSecondVariation

#print axioms QuantumNLS.ProductTorusSecondVariation.augF_contDiff
#print axioms QuantumNLS.ProductTorusSecondVariation.local_diff_aug
#print axioms QuantumNLS.ProductTorusSecondVariation.differentiableAt_fderiv_flow
#print axioms QuantumNLS.ProductTorusSecondVariation.fderiv2_flow_symm
#print axioms QuantumNLS.ProductTorusSecondVariation.deriv2_zero
#print axioms QuantumNLS.ProductTorusSecondVariation.hasDerivAt_fderiv2_flow
#print axioms QuantumNLS.ProductTorusSecondVariation.hasDerivAt_fderiv2_flow_apply
#print axioms QuantumNLS.ProductTorusSecondVariation.norm_fderiv2_X_le
#print axioms QuantumNLS.ProductTorusSecondVariation.norm_fderiv2_flow_le
