import QuantumNLS.ProductTorusFlow
import QuantumNLS.ProductTorusLocalDiff

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T2d: differentiable complete flows and the variational equation

Source: `chapters/global/product_torus.tex`, proof, "Bounded angle generators and complete flows", paragraphs 3–5
("Differentiating one transported field along the other and using uniqueness of the linear variational equation";
"For `‖θ‖_∞ ≤ π` and `u ∈ 𝒞`, `‖X_θ(u)‖ ≤ (π/2)A₁(𝒞)`, `‖DX_θ(u)‖ ≤ (π/2)A₂(𝒞)`. All trajectories stay in `𝒞`.
The variational equation gives eq:global-torus-derivative-bound"; "Its inverse and its bounded inverse differential
follow from `T_{-θ}`").

For the complete flows `φ_θ^t = flow DI θ t` of stage T2b (hypotheses `ProductTorusFlow.Hyp`):
* `differentiableAt_flow`: every `φ_θ^t` is Fréchet differentiable at every point. Route: T2c `local_diff` at each
  point of the compact fibre, a finite subcover gives one short time (`uniform_short`), and the group law
  `φ^{t} = φ^{t-s} ∘ φ^{s}` with conservation of the fibre (T2b) composes finitely many short steps; negative times
  use `φ_θ^{-t} = φ_{-θ}^{t}`;
* `hasDerivAt_fderiv_flow`: **the variational equation** `d/dt Dφ^t(u) = DX_θ(φ^t u) ∘ Dφ^t(u)` (two-sided), and its
  fixed-vector form `hasDerivAt_fderiv_flow_apply`;
* `fderiv_flow_neg_comp`: `Dφ^{-t}(φ^t u) ∘ Dφ^t(u) = id` (the bounded inverse differential from `T_{-θ}`);
* `norm_fderiv_X_le`: `‖DX_θ(u)‖ ≤ ‖θ‖_∞ ‖D²𝓘(u)‖ / 2`;
* `norm_fderiv_flow_le`: if `‖DX_θ‖ ≤ K` on the fibre then `‖Dφ^t(u)‖ ≤ exp(K|t|)` (Gronwall);
* `derivative_bound`: eq:global-torus-derivative-bound in the form
  `‖DT_θ(u)‖ + ‖DT_θ(u)⁻¹‖ ≤ 2 exp((‖θ‖_∞/2) A₂)` whenever `‖D²𝓘‖ ≤ A₂` on the fibre of `u` (the source's
  constant `2 exp((π/2)A₂(𝒞))` for `‖θ‖_∞ ≤ π`), with `DT_θ(u)⁻¹ = DT_{-θ}(T_θ u)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology Set Metric
open scoped InnerProductSpace NNReal

noncomputable section

namespace QuantumNLS.ProductTorusVariational

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusLocalDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-! ## 1. Short-time differentiability, uniformly on a fibre -/

theorem local_diff_flow (h : Hyp I DI) (θ : Linf) (p : E) :
    ∃ ρ > (0 : ℝ), ∃ τ > (0 : ℝ), ∀ u ∈ ball p ρ, ∃ J : ℝ → E →L[ℝ] E, Continuous J ∧
      J 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ s ∈ Icc 0 τ, HasDerivWithinAt J ((fderiv ℝ (X DI θ) (flow DI θ s u)).comp (J s)) (Icc 0 τ) s) ∧
      ∀ t ∈ Icc 0 τ, HasFDerivAt (flow DI θ t) (J t) u :=
  local_diff (f := X DI θ) (φ := flow DI θ) (X_contDiff h.contDiff θ) (hasDerivAt_flow h θ) (flow_zero h θ) p

theorem mem_fibre_flow (h : Hyp I DI) (θ : Linf) {u w : E} (hw : w ∈ I ⁻¹' {I u}) (t : ℝ) :
    flow DI θ t w ∈ I ⁻¹' {I u} := by
  show I (flow DI θ t w) ∈ ({I u} : Set (L1 ℝ))
  rw [I_flow h θ w t]
  exact hw

/-- One short time for the whole compact fibre. -/
theorem uniform_short (h : Hyp I DI) (θ : Linf) (u : E) :
    ∃ τ > (0 : ℝ), ∀ w ∈ I ⁻¹' {I u}, ∀ t ∈ Icc 0 τ, DifferentiableAt ℝ (flow DI θ t) w := by
  classical
  have H (x : I ⁻¹' {I u}) := local_diff_flow h θ (x : E)
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
  obtain ⟨J, -, -, -, hJt⟩ := hJ i w hwi
  exact (hJt t ⟨ht.1, ht.2.trans (Finset.inf'_le _ hi)⟩).differentiableAt

/-! ## 2. Differentiability for all times -/

theorem differentiableAt_flow_nonneg (h : Hyp I DI) (θ : Linf) (u : E) {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableAt ℝ (flow DI θ t) u := by
  obtain ⟨τ, hτ, hshort⟩ := uniform_short h θ u
  have key : ∀ n : ℕ, ∀ w ∈ I ⁻¹' {I u}, ∀ t ∈ Icc 0 (n * τ), DifferentiableAt ℝ (flow DI θ t) w := by
    intro n
    induction n with
    | zero =>
      intro w _ t ht
      have ht0 : t = 0 := le_antisymm (by simpa using ht.2) ht.1
      subst ht0
      have : flow DI θ 0 = id := funext (flow_zero h θ)
      rw [this]
      exact differentiableAt_id
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
      have hcomp : flow DI θ t = flow DI θ (t - min t τ) ∘ flow DI θ (min t τ) := by
        funext x
        simp only [Function.comp]
        rw [← flow_add h θ x (t - min t τ) (min t τ), sub_add_cancel]
      rw [hcomp]
      exact (ih _ (mem_fibre_flow h θ hw _) _ hts).comp w (hshort w hw _ ⟨hs0, hsτ⟩)
  obtain ⟨n, hn⟩ := exists_nat_ge (t / τ)
  exact key n u (Set.mem_singleton (I u)) t ⟨ht, by rwa [div_le_iff₀ hτ] at hn⟩

theorem flow_eq_neg (h : Hyp I DI) (θ : Linf) (t : ℝ) : flow DI θ t = flow DI (-θ) (-t) :=
  funext fun x => by rw [flow_neg_angle h, neg_neg]

theorem flow_neg_time (h : Hyp I DI) (θ : Linf) (t : ℝ) : flow DI θ (-t) = flow DI (-θ) t :=
  funext fun x => (flow_neg_angle h θ x t).symm

/-- **Every time-`t` map of the flow is differentiable everywhere.** -/
theorem differentiableAt_flow (h : Hyp I DI) (θ : Linf) (t : ℝ) (u : E) :
    DifferentiableAt ℝ (flow DI θ t) u := by
  rcases le_total 0 t with ht | ht
  · exact differentiableAt_flow_nonneg h θ u ht
  · rw [flow_eq_neg h θ t]
    exact differentiableAt_flow_nonneg h (-θ) u (by linarith)

/-- Chain rule along the group law. -/
theorem fderiv_flow_add (h : Hyp I DI) (θ : Linf) (r t : ℝ) (u : E) :
    fderiv ℝ (flow DI θ (r + t)) u =
      (fderiv ℝ (flow DI θ r) (flow DI θ t u)).comp (fderiv ℝ (flow DI θ t) u) := by
  have hcomp : flow DI θ (r + t) = flow DI θ r ∘ flow DI θ t := funext fun x => flow_add h θ x r t
  rw [hcomp]
  exact fderiv_comp (hg := differentiableAt_flow h θ r _) (hf := differentiableAt_flow h θ t u)

theorem fderiv_flow_zero (h : Hyp I DI) (θ : Linf) (u : E) :
    fderiv ℝ (flow DI θ 0) u = ContinuousLinearMap.id ℝ E := by
  have : flow DI θ 0 = id := funext (flow_zero h θ)
  rw [this, fderiv_id]

/-- `Dφ^{-t}(φ^t u) ∘ Dφ^t(u) = id`. -/
theorem fderiv_flow_neg_comp (h : Hyp I DI) (θ : Linf) (t : ℝ) (u : E) :
    (fderiv ℝ (flow DI θ (-t)) (flow DI θ t u)).comp (fderiv ℝ (flow DI θ t) u) = ContinuousLinearMap.id ℝ E := by
  rw [← fderiv_flow_add h, neg_add_cancel, fderiv_flow_zero h]

/-! ## 3. The variational equation -/

theorem X_neg (θ : Linf) : X DI (-θ) = fun u => -X DI θ u := by
  funext u
  rw [← neg_one_smul ℝ θ, X_smul, neg_one_smul]

theorem fderiv_X_neg (θ : Linf) (p : E) : fderiv ℝ (X DI (-θ)) p = -fderiv ℝ (X DI θ) p := by
  rw [X_neg]
  exact fderiv_fun_neg

/-- Right derivative at `0` of `r ↦ Dφ^r(p)`. -/
theorem right_deriv_zero (h : Hyp I DI) (θ : Linf) (p : E) :
    HasDerivWithinAt (fun r => fderiv ℝ (flow DI θ r) p) (fderiv ℝ (X DI θ) p) (Ici 0) 0 := by
  obtain ⟨ρ, hρ, τ, hτ, H⟩ := local_diff_flow h θ p
  obtain ⟨J, -, hJ0, hJd, hJt⟩ := H p (mem_ball_self hρ)
  have h1 : HasDerivWithinAt J ((fderiv ℝ (X DI θ) (flow DI θ 0 p)).comp (J 0)) (Icc 0 τ) 0 :=
    hJd 0 ⟨le_rfl, hτ.le⟩
  rw [flow_zero h, hJ0, ContinuousLinearMap.comp_id] at h1
  have h2 : HasDerivWithinAt J (fderiv ℝ (X DI θ) p) (Ici 0) 0 :=
    (hasDerivWithinAt_inter (Iio_mem_nhds hτ)).1
      (h1.mono fun x hx => ⟨(mem_Ici.1 hx.1), (mem_Iio.1 hx.2).le⟩)
  refine h2.congr_of_eventuallyEq ?_ (hJt 0 ⟨le_rfl, hτ.le⟩).fderiv
  filter_upwards [inter_mem_nhdsWithin (Ici (0 : ℝ)) (Iio_mem_nhds hτ)] with r hr
  exact (hJt r ⟨mem_Ici.1 hr.1, (mem_Iio.1 hr.2).le⟩).fderiv

/-- Two-sided derivative at `0` of `r ↦ Dφ^r(p)`. -/
theorem deriv_zero (h : Hyp I DI) (θ : Linf) (p : E) :
    HasDerivAt (fun r => fderiv ℝ (flow DI θ r) p) (fderiv ℝ (X DI θ) p) 0 := by
  have hR := right_deriv_zero h θ p
  have hL0 := right_deriv_zero h (-θ) p
  have hneg : HasDerivWithinAt (fun r : ℝ => -r) (-1) (Iic 0) 0 := (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt
  have hmaps : MapsTo (fun r : ℝ => -r) (Iic 0) (Ici 0) := fun r hr => by
    simp only [mem_Iic, mem_Ici] at hr ⊢
    linarith
  have hL0' : HasDerivWithinAt (fun r => fderiv ℝ (flow DI (-θ) r) p) (fderiv ℝ (X DI (-θ)) p) (Ici 0)
      ((fun r : ℝ => -r) 0) := by
    simp only [neg_zero]
    exact hL0
  have hL1 := hL0'.scomp 0 hneg hmaps
  have hL : HasDerivWithinAt (fun r => fderiv ℝ (flow DI θ r) p) (fderiv ℝ (X DI θ) p) (Iic 0) 0 := by
    have he : (fun r => fderiv ℝ (flow DI θ r) p) = (fun r => fderiv ℝ (flow DI (-θ) r) p) ∘ (fun r : ℝ => -r) := by
      funext r
      show fderiv ℝ (flow DI θ r) p = fderiv ℝ (flow DI (-θ) (-r)) p
      rw [flow_eq_neg h θ r]
    rw [he]
    convert hL1 using 1
    rw [fderiv_X_neg, smul_neg, neg_one_smul, neg_neg]
  have hU := hL.union hR
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at hU
  exact hU

/-- **The variational equation** `d/dt Dφ^t(u) = DX_θ(φ^t u) ∘ Dφ^t(u)`. -/
theorem hasDerivAt_fderiv_flow (h : Hyp I DI) (θ : Linf) (u : E) (t : ℝ) :
    HasDerivAt (fun t => fderiv ℝ (flow DI θ t) u)
      ((fderiv ℝ (X DI θ) (flow DI θ t u)).comp (fderiv ℝ (flow DI θ t) u)) t := by
  set p := flow DI θ t u
  set D0 := fderiv ℝ (flow DI θ t) u
  have he : (fun s => fderiv ℝ (flow DI θ s) u) = fun s => (fderiv ℝ (flow DI θ (s - t)) p).comp D0 := by
    funext s
    rw [← fderiv_flow_add h, sub_add_cancel]
  rw [he]
  have hG : HasDerivAt (fun s => fderiv ℝ (flow DI θ (s - t)) p) (fderiv ℝ (X DI θ) p) t :=
    HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact deriv_zero h θ p)
  have hc := hG.clm_comp (hasDerivAt_const t D0)
  convert hc using 1
  simp

/-- The fixed-vector variational equation. -/
theorem hasDerivAt_fderiv_flow_apply (h : Hyp I DI) (θ : Linf) (u k : E) (t : ℝ) :
    HasDerivAt (fun t => fderiv ℝ (flow DI θ t) u k)
      (fderiv ℝ (X DI θ) (flow DI θ t u) (fderiv ℝ (flow DI θ t) u k)) t := by
  have hc := (hasDerivAt_fderiv_flow h θ u t).clm_apply (hasDerivAt_const t k)
  convert hc using 1
  simp

theorem continuous_fderiv_flow (h : Hyp I DI) (θ : Linf) (u : E) :
    Continuous (fun t => fderiv ℝ (flow DI θ t) u) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_fderiv_flow h θ u t).continuousAt

/-! ## 4. Bounds -/

theorem norm_WinvL_le : ‖(WinvL : (E →L[ℝ] ℝ) →L[ℝ] E)‖ ≤ 1 / 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun ℓ => by
    rw [WinvL_apply, norm_Winv]
    linarith

/-- The derivative of `X_θ = W⁻¹ ∘ (pair θ ∘ ·) ∘ D𝓘`. -/
theorem fderiv_X_eq (h : Hyp I DI) (θ : Linf) (u : E) :
    fderiv ℝ (X DI θ) u =
      WinvL.comp ((ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ)).comp (fderiv ℝ DI u)) := by
  have hD : HasFDerivAt DI (fderiv ℝ DI u) u := ((h.contDiff.differentiable one_ne_zero) u).hasFDerivAt
  have hC : HasFDerivAt (fun v => ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ) (DI v))
      ((ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ)).comp (fderiv ℝ DI u)) u :=
    (ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ)).hasFDerivAt.comp u hD
  have hW : HasFDerivAt (fun v => WinvL (ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ) (DI v)))
      (WinvL.comp ((ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ)).comp (fderiv ℝ DI u))) u :=
    WinvL.hasFDerivAt.comp u hC
  rw [X_eq_comp]
  exact hW.fderiv

theorem fderiv_X_apply (h : Hyp I DI) (θ : Linf) (u a : E) :
    fderiv ℝ (X DI θ) u a = Winv ((pair θ).comp (fderiv ℝ DI u a)) := by
  rw [fderiv_X_eq h, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, WinvL_apply]

/-- `‖DX_θ(u)‖ ≤ ‖θ‖_∞ ‖D²𝓘(u)‖ / 2`. -/
theorem norm_fderiv_X_le (h : Hyp I DI) (θ : Linf) (u : E) :
    ‖fderiv ℝ (X DI θ) u‖ ≤ ‖θ‖ * ‖fderiv ℝ DI u‖ / 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
  rw [fderiv_X_apply h, norm_Winv]
  have h1 : ‖(pair θ).comp (fderiv ℝ DI u a)‖ ≤ ‖θ‖ * ‖fderiv ℝ DI u a‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (norm_pair_le θ) (norm_nonneg _))
  have h3 : ‖θ‖ * ‖fderiv ℝ DI u a‖ ≤ ‖θ‖ * (‖fderiv ℝ DI u‖ * ‖a‖) :=
    mul_le_mul_of_nonneg_left ((fderiv ℝ DI u).le_opNorm a) (norm_nonneg θ)
  calc ‖(pair θ).comp (fderiv ℝ DI u a)‖ / 2 ≤ ‖θ‖ * ‖fderiv ℝ DI u a‖ / 2 := by linarith
    _ ≤ ‖θ‖ * (‖fderiv ℝ DI u‖ * ‖a‖) / 2 := by linarith
    _ = ‖θ‖ * ‖fderiv ℝ DI u‖ / 2 * ‖a‖ := by ring

theorem norm_fderiv_flow_le_nonneg (h : Hyp I DI) (θ : Linf) (u : E) {K : ℝ}
    (hK : ∀ w ∈ I ⁻¹' {I u}, ‖fderiv ℝ (X DI θ) w‖ ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (flow DI θ t) u‖ ≤ Real.exp (K * t) := by
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (a := 0) (b := t) (K := K) (ε := 0) (δ := 1)
    (f := fun t => fderiv ℝ (flow DI θ t) u)
    (f' := fun t => (fderiv ℝ (X DI θ) (flow DI θ t u)).comp (fderiv ℝ (flow DI θ t) u))
    (continuous_fderiv_flow h θ u).continuousOn
    (fun s _ => (hasDerivAt_fderiv_flow h θ u s).hasDerivWithinAt)
    (by
      show ‖fderiv ℝ (flow DI θ 0) u‖ ≤ 1
      rw [fderiv_flow_zero h]
      exact ContinuousLinearMap.norm_id_le)
    (fun s _ => by
      show ‖(fderiv ℝ (X DI θ) (flow DI θ s u)).comp (fderiv ℝ (flow DI θ s) u)‖ ≤
        K * ‖fderiv ℝ (flow DI θ s) u‖ + 0
      rw [add_zero]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hK _ (mem_fibre_flow h θ (Set.mem_singleton (I u)) s)) (norm_nonneg _)))
    t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0, one_mul, sub_zero] at hg
  exact hg

/-- **Gronwall bound for the derivative of the flow**: `‖Dφ^t(u)‖ ≤ exp(K|t|)` when `‖DX_θ‖ ≤ K` on the fibre. -/
theorem norm_fderiv_flow_le (h : Hyp I DI) (θ : Linf) (u : E) {K : ℝ}
    (hK : ∀ w ∈ I ⁻¹' {I u}, ‖fderiv ℝ (X DI θ) w‖ ≤ K) (t : ℝ) :
    ‖fderiv ℝ (flow DI θ t) u‖ ≤ Real.exp (K * |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact norm_fderiv_flow_le_nonneg h θ u hK ht
  · rw [abs_of_nonpos ht, flow_eq_neg h θ t]
    refine norm_fderiv_flow_le_nonneg h (-θ) u (fun w hw => ?_) (by linarith)
    rw [fderiv_X_neg, norm_neg]
    exact hK w hw

/-- **eq:global-torus-derivative-bound.** If `‖D²𝓘‖ ≤ A₂` on the fibre of `u`, then
`‖DT_θ(u)‖ + ‖DT_{-θ}(T_θ u)‖ ≤ 2 exp((‖θ‖_∞/2) A₂)`, where `DT_{-θ}(T_θ u) ∘ DT_θ(u) = id = DT_θ(u) ∘ DT_{-θ}(T_θ u)`
(the bounded inverse differential). For `‖θ‖_∞ ≤ π` this is the source's `2 exp((π/2) A₂(𝒞))`. -/
theorem derivative_bound (h : Hyp I DI) (θ : Linf) (u : E) {A₂ : ℝ}
    (hA : ∀ w ∈ I ⁻¹' {I u}, ‖fderiv ℝ DI w‖ ≤ A₂) :
    ‖fderiv ℝ (T DI θ) u‖ + ‖fderiv ℝ (T DI (-θ)) (T DI θ u)‖ ≤ 2 * Real.exp (‖θ‖ / 2 * A₂) ∧
      (fderiv ℝ (T DI (-θ)) (T DI θ u)).comp (fderiv ℝ (T DI θ) u) = ContinuousLinearMap.id ℝ E ∧
      (fderiv ℝ (T DI θ) u).comp (fderiv ℝ (T DI (-θ)) (T DI θ u)) = ContinuousLinearMap.id ℝ E := by
  have hKθ : ∀ (η : Linf), ‖η‖ = ‖θ‖ → ∀ w ∈ I ⁻¹' {I u}, ‖fderiv ℝ (X DI η) w‖ ≤ ‖θ‖ / 2 * A₂ := by
    intro η hη w hw
    refine (norm_fderiv_X_le h η w).trans ?_
    rw [hη]
    have := mul_le_mul_of_nonneg_left (hA w hw) (norm_nonneg θ)
    linarith
  have hTu : T DI θ u ∈ I ⁻¹' {I u} := mem_fibre_flow h θ (Set.mem_singleton (I u)) 1
  have hfib : I ⁻¹' {I (T DI θ u)} = I ⁻¹' {I u} := by rw [I_T h θ u]
  have h1 : ‖fderiv ℝ (T DI θ) u‖ ≤ Real.exp (‖θ‖ / 2 * A₂) := by
    have := norm_fderiv_flow_le h θ u (hKθ θ rfl) 1
    rwa [abs_one, mul_one] at this
  have h2 : ‖fderiv ℝ (T DI (-θ)) (T DI θ u)‖ ≤ Real.exp (‖θ‖ / 2 * A₂) := by
    have := norm_fderiv_flow_le h (-θ) (T DI θ u)
      (by rw [hfib]; exact hKθ (-θ) (norm_neg θ)) 1
    rwa [abs_one, mul_one] at this
  refine ⟨by linarith, ?_, ?_⟩
  · have := fderiv_flow_neg_comp h θ 1 u
    unfold T
    rwa [flow_neg_time h θ 1] at this
  · have := fderiv_flow_neg_comp h (-θ) 1 (T DI θ u)
    unfold T at this ⊢
    rw [flow_neg_time h (-θ) 1, neg_neg] at this
    have hTT : flow DI (-θ) 1 (flow DI θ 1 u) = u := T_neg_T h θ u
    rwa [hTT] at this

end QuantumNLS.ProductTorusVariational

#print axioms QuantumNLS.ProductTorusVariational.uniform_short
#print axioms QuantumNLS.ProductTorusVariational.differentiableAt_flow
#print axioms QuantumNLS.ProductTorusVariational.fderiv_flow_add
#print axioms QuantumNLS.ProductTorusVariational.fderiv_flow_neg_comp
#print axioms QuantumNLS.ProductTorusVariational.deriv_zero
#print axioms QuantumNLS.ProductTorusVariational.hasDerivAt_fderiv_flow
#print axioms QuantumNLS.ProductTorusVariational.hasDerivAt_fderiv_flow_apply
#print axioms QuantumNLS.ProductTorusVariational.norm_fderiv_X_le
#print axioms QuantumNLS.ProductTorusVariational.norm_fderiv_flow_le
#print axioms QuantumNLS.ProductTorusVariational.derivative_bound
