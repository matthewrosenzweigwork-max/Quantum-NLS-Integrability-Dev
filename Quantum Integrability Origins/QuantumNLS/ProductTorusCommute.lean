import QuantumNLS.ProductTorusVariational

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T3: commuting flows and the group law

Source: `chapters/global/product_torus.tex`, proof, "Bounded angle generators and complete flows", third paragraph:
"For two bounded sequences, `dH_θ[X_η] = 0`, since all the coordinates `dI_j[X_η]` vanish. The two analytic Hamiltonian
vector fields commute. Differentiating one transported field along the other and using uniqueness of the linear
variational equation shows that their complete flows commute. Differentiating `φ_θ^t φ_η^t u` then identifies it with
the solution of `X_{θ+η} = X_θ + X_η`. Consequently `T_θ := φ_θ^1`, `T_θT_η = T_{θ+η}`, `T_θ^{-1} = T_{-θ}`.
For finitely supported `θ`, this agrees with the finite composition of the individual flows at their prescribed
times."

Proved (hypotheses `ProductTorusFlow.Hyp`):
* `omega_nondeg`: `ω(v,·) = 0 ⇒ v = 0`;
* `symm2`: the second derivative `D²𝓘(u)` is symmetric (`𝓘` is `C²`);
* `deriv_DI_X`: differentiating `D𝓘(u)X_θ(u) = 0` (T1) gives `D²𝓘(u)[k, X_θ u] + D𝓘(u)DX_θ(u)k = 0`;
* **`bracket`**: `DX_η(u)X_θ(u) = DX_θ(u)X_η(u)` (the vector fields commute), from `ω(DX_θ a, b) = d²H_θ[a,b]`,
  symmetry of the Hessian and nondegeneracy of `ω`;
* **`push`**: `Dφ_θ^t(v) X_η(v) = X_η(φ_θ^t v)` ("differentiating one transported field along the other"): the
  difference solves the linear variational equation with zero initial value, hence vanishes (Gronwall uniqueness);
* **`commute`**: `φ_θ^t ∘ φ_η^s = φ_η^s ∘ φ_θ^t`;
* `increment`, `hasDerivAt_flow_moving`: `d/dr|₀ φ_θ^r(z(r)) = X_θ(z(0)) + z'(0)`;
* **`flow_add_angle`**: `φ_{θ+η}^t = φ_θ^t ∘ φ_η^t`, and **`T_add`**: `T_{θ+η} = T_θ ∘ T_η`;
* `X_single`: the generator of the unit sequence `e_n` is the individual Hamiltonian field `X_{I_n}`;
  **`T_list`/`T_finset`**: for finitely supported `θ = Σ_{n∈S} c_n e_n`, `T_θ` is the composition of the individual
  flows `φ_{I_n}^{c_n}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology Set Metric
open scoped InnerProductSpace NNReal

noncomputable section

namespace QuantumNLS.ProductTorusCommute

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusLocalDiff
  QuantumNLS.ProductTorusVariational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-! ## 1. The symplectic form -/

omit [CompleteSpace E] in
theorem omega_sub_left (a b k : E) : omega (a - b) k = omega a k - omega b k := by
  unfold omega
  rw [inner_sub_left, Complex.sub_im]
  ring

/-- `ω` is nondegenerate (GP-06: `v ↦ ω(v,·)` is a real-linear isomorphism). -/
theorem omega_nondeg {v : E} (hv : ∀ k, omega v k = 0) : v = 0 := by
  obtain ⟨J, hJ, -⟩ := QuantumNLS.Ext025A.gp06_strong_symplectic_identification (E := E)
  have hJv : J v = 0 := by
    refine ContinuousLinearMap.ext fun k => ?_
    rw [hJ, zero_apply]
    exact hv k
  exact J.injective (hJv.trans (map_zero J).symm)

theorem omega_X (θ : Linf) (u k : E) : omega (X DI θ u) k = pair θ (DI u k) := by
  unfold X
  rw [omega_Winv]
  rfl

/-! ## 2. Second derivatives and the bracket -/

/-- `ω(DX_θ(u)a, k) = d²H_θ(u)[a,k]`. -/
theorem omega_fderiv_X (h : Hyp I DI) (θ : Linf) (u a k : E) :
    omega (fderiv ℝ (X DI θ) u a) k = pair θ (fderiv ℝ DI u a k) := by
  rw [fderiv_X_apply h, omega_Winv]
  rfl

theorem fderiv_I_eq (h : Hyp I DI) : fderiv ℝ I = DI := funext fun u => (h.hasFDerivAt u).fderiv

/-- Symmetry of `D²𝓘(u)`. -/
theorem symm2 (h : Hyp I DI) (u a b : E) : fderiv ℝ DI u a b = fderiv ℝ DI u b a := by
  have h11 : ContDiff ℝ (1 + 1) I := by
    refine contDiff_succ_iff_fderiv.2 ⟨fun u => (h.hasFDerivAt u).differentiableAt, fun h1 => by simp at h1, ?_⟩
    rw [fderiv_I_eq h]
    exact h.contDiff
  rw [one_add_one_eq_two] at h11
  have hs := h11.contDiffAt.isSymmSndFDerivAt (x := u) (by simp)
  have := hs a b
  rwa [fderiv_I_eq h] at this

/-- Differentiating `D𝓘(u)X_θ(u) = 0`. -/
theorem deriv_DI_X (h : Hyp I DI) (θ : Linf) (u k : E) :
    fderiv ℝ DI u k (X DI θ u) + DI u (fderiv ℝ (X DI θ) u k) = 0 := by
  have hz : (fun v => DI v (X DI θ v)) = fun _ => (0 : L1 ℝ) := funext fun v => DI_X_zero h.involutive θ v
  have hc : HasFDerivAt DI (fderiv ℝ DI u) u := ((h.contDiff.differentiable one_ne_zero) u).hasFDerivAt
  have hx : HasFDerivAt (X DI θ) (fderiv ℝ (X DI θ) u) u :=
    ((X_contDiff h.contDiff θ).differentiable one_ne_zero u).hasFDerivAt
  have hd := hc.clm_apply hx
  rw [hz] at hd
  have h0 := hd.unique (hasFDerivAt_const (0 : L1 ℝ) u)
  have := congrArg (fun L : E →L[ℝ] L1 ℝ => L k) h0
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply] at this
  first
  | exact this
  | (rw [add_comm]; exact this)

/-- **The vector fields commute**: `DX_η(u)X_θ(u) = DX_θ(u)X_η(u)`. -/
theorem bracket (h : Hyp I DI) (θ η : Linf) (u : E) :
    fderiv ℝ (X DI η) u (X DI θ u) = fderiv ℝ (X DI θ) u (X DI η u) := by
  rw [← sub_eq_zero]
  apply omega_nondeg
  intro k
  rw [omega_sub_left, sub_eq_zero]
  have e1 : omega (fderiv ℝ (X DI η) u (X DI θ u)) k = -omega (X DI η u) (fderiv ℝ (X DI θ) u k) := by
    rw [omega_fderiv_X h, symm2 h, omega_X]
    have := congrArg (pair η) (deriv_DI_X h θ u k)
    rw [map_add, map_zero] at this
    linarith
  have e2 : omega (fderiv ℝ (X DI θ) u (X DI η u)) k = -omega (X DI η u) (fderiv ℝ (X DI θ) u k) := by
    rw [omega_fderiv_X h, symm2 h, omega_antisymm (X DI η u), neg_neg, omega_fderiv_X h]
  rw [e1, e2]

/-! ## 3. Transport of one field along the other flow -/

theorem push_nonneg (h : Hyp I DI) (θ η : Linf) (v : E) {t : ℝ} (ht : 0 ≤ t) :
    fderiv ℝ (flow DI θ t) v (X DI η v) = X DI η (flow DI θ t v) := by
  obtain ⟨K, hK⟩ := (h.fibre_compact v).exists_bound_of_continuousOn
    ((X_contDiff h.contDiff θ).continuous_fderiv one_ne_zero).continuousOn
  have hXη : ∀ p : E, HasFDerivAt (X DI η) (fderiv ℝ (X DI η) p) p := fun p =>
    ((X_contDiff h.contDiff η).differentiable one_ne_zero p).hasFDerivAt
  have hcont : ContinuousOn (fun s => fderiv ℝ (flow DI θ s) v (X DI η v) - X DI η (flow DI θ s v)) (Icc 0 t) :=
    (((continuous_fderiv_flow h θ v).clm_apply continuous_const).sub
      ((X_contDiff h.contDiff η).continuous.comp (continuous_flow_time h θ v))).continuousOn
  have hder : ∀ s ∈ Ico (0 : ℝ) t, HasDerivWithinAt
      (fun s => fderiv ℝ (flow DI θ s) v (X DI η v) - X DI η (flow DI θ s v))
      (fderiv ℝ (X DI θ) (flow DI θ s v) (fderiv ℝ (flow DI θ s) v (X DI η v)) -
        fderiv ℝ (X DI η) (flow DI θ s v) (X DI θ (flow DI θ s v))) (Ici s) s := fun s _ =>
    ((hasDerivAt_fderiv_flow_apply h θ v (X DI η v) s).sub
      ((hXη _).comp_hasDerivAt s (hasDerivAt_flow h θ v s))).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) t,
      ‖fderiv ℝ (X DI θ) (flow DI θ s v) (fderiv ℝ (flow DI θ s) v (X DI η v)) -
        fderiv ℝ (X DI η) (flow DI θ s v) (X DI θ (flow DI θ s v))‖ ≤
      K * ‖fderiv ℝ (flow DI θ s) v (X DI η v) - X DI η (flow DI θ s v)‖ := by
    intro s _
    rw [bracket h θ η, ← map_sub]
    exact ((fderiv ℝ (X DI θ) (flow DI θ s v)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hK _ (mem_fibre_flow h θ (Set.mem_singleton (I v)) s)) (norm_nonneg _))
  have hw := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (a := 0) (b := t) (K := K)
    (f := fun s => fderiv ℝ (flow DI θ s) v (X DI η v) - X DI η (flow DI θ s v))
    (f' := fun s => fderiv ℝ (X DI θ) (flow DI θ s v) (fderiv ℝ (flow DI θ s) v (X DI η v)) -
        fderiv ℝ (X DI η) (flow DI θ s v) (X DI θ (flow DI θ s v)))
    hcont hder (by
      show fderiv ℝ (flow DI θ 0) v (X DI η v) - X DI η (flow DI θ 0 v) = 0
      rw [fderiv_flow_zero h, flow_zero h, ContinuousLinearMap.id_apply, sub_self])
    hbound t ⟨ht, le_rfl⟩
  exact sub_eq_zero.1 hw

/-- **Transport**: `Dφ_θ^t(v) X_η(v) = X_η(φ_θ^t v)` for all `t`. -/
theorem push (h : Hyp I DI) (θ η : Linf) (v : E) (t : ℝ) :
    fderiv ℝ (flow DI θ t) v (X DI η v) = X DI η (flow DI θ t v) := by
  rcases le_total 0 t with ht | ht
  · exact push_nonneg h θ η v ht
  · rw [flow_eq_neg h θ t]
    exact push_nonneg h (-θ) η v (by linarith)

/-- **The complete flows commute.** -/
theorem commute (h : Hyp I DI) (θ η : Linf) (t s : ℝ) (u : E) :
    flow DI θ t (flow DI η s u) = flow DI η s (flow DI θ t u) := by
  have hd : ∀ r, HasDerivAt (fun r => flow DI θ t (flow DI η r u)) (X DI η (flow DI θ t (flow DI η r u))) r := by
    intro r
    have := (differentiableAt_flow h θ t (flow DI η r u)).hasFDerivAt.comp_hasDerivAt r (hasDerivAt_flow h η u r)
    rw [push h θ η] at this
    exact this
  exact (flow_eq_of_sol h η (α := fun r => flow DI θ t (flow DI η r u))
    (by show flow DI θ t (flow DI η 0 u) = flow DI θ t u; rw [flow_zero h]) hd s).symm

/-! ## 4. The group law -/

/-- Short increments: `‖φ_θ^r z − z − r X_θ(p)‖ ≤ C r (r + ‖z − p‖)` near `p`. -/
theorem increment (h : Hyp I DI) (θ : Linf) (p : E) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ z ∈ closedBall p δ, ∀ r ∈ Icc 0 δ,
      ‖flow DI θ r z - z - r • X DI θ p‖ ≤ C * r * (r + ‖z - p‖) := by
  have hf : ContDiff ℝ 1 (X DI θ) := X_contDiff h.contDiff θ
  obtain ⟨a, ha, hloc⟩ := local_constants hf p
  set K : ℝ := ‖fderiv ℝ (X DI θ) p‖ + 1 with hK
  set L : ℝ := ‖X DI θ p‖ + 1 with hL
  have hK0 : 0 ≤ K := by positivity
  have hL0 : 0 ≤ L := by positivity
  set τ : ℝ := a / (2 * (L + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτL : (L + 1) * τ ≤ a / 2 := by
    have : (L + 1) * τ = a / 2 := by rw [hτ]; field_simp
    linarith
  refine ⟨min (a / 2) τ, lt_min (by positivity) hτ0, K * (L + 1), by positivity, fun z hz r hr => ?_⟩
  have hz2 : z ∈ closedBall p (a / 2) := closedBall_subset_closedBall (min_le_left _ _) hz
  have hrτ : r ≤ τ := hr.2.trans (min_le_right _ _)
  have hin : ∀ s ∈ Icc 0 r, flow DI θ s z ∈ closedBall p a := fun s hs =>
    stays (f := X DI θ) (φ := flow DI θ) (hasDerivAt_flow h θ) (flow_zero h θ) hL0 (fun w hw => (hloc w hw).2)
      hτL hz2 ⟨hs.1, hs.2.trans hrτ⟩
  have hp : p ∈ closedBall p a := mem_closedBall_self ha.le
  -- speed bound
  have hspeed : ∀ s ∈ Icc 0 r, ‖flow DI θ s z - z‖ ≤ L * s := by
    have := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := r) (C := L)
      (f := fun s => flow DI θ s z) (f' := fun s => X DI θ (flow DI θ s z))
      (fun s _ => (hasDerivAt_flow h θ z s).hasDerivWithinAt)
      (fun s hs => (hloc _ (hin s (Ico_subset_Icc_self hs))).2)
    intro s hs
    have h1 := this s hs
    simp only [flow_zero h, sub_zero] at h1
    exact h1
  -- Lipschitz bound of `X_θ` on the ball, against the centre
  have hlip : ∀ y ∈ closedBall p a, ‖X DI θ y - X DI θ p‖ ≤ K * ‖y - p‖ := fun y hy =>
    Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun x _ => hf.differentiable one_ne_zero x)
      (fun x hx => (hloc x hx).1) (convex_closedBall p a) hp hy
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := r)
    (C := K * (L * r + ‖z - p‖))
    (f := fun s => flow DI θ s z - s • X DI θ p) (f' := fun s => X DI θ (flow DI θ s z) - X DI θ p)
    (fun s _ => by
      have h1 := (hasDerivAt_flow h θ z s).sub ((hasDerivAt_id' s).smul_const (X DI θ p))
      rw [one_smul] at h1
      exact h1.hasDerivWithinAt)
    (fun s hs => by
      have hs' : s ∈ Icc 0 r := Ico_subset_Icc_self hs
      refine (hlip _ (hin s hs')).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      calc ‖flow DI θ s z - p‖ = ‖(flow DI θ s z - z) + (z - p)‖ := by congr 1; abel
        _ ≤ ‖flow DI θ s z - z‖ + ‖z - p‖ := norm_add_le _ _
        _ ≤ L * s + ‖z - p‖ := by linarith [hspeed s hs']
        _ ≤ L * r + ‖z - p‖ := by have := mul_le_mul_of_nonneg_left hs'.2 hL0; linarith)
    r ⟨hr.1, le_rfl⟩
  simp only [flow_zero h, zero_smul, sub_zero] at hmain
  have heq : flow DI θ r z - r • X DI θ p - z = flow DI θ r z - z - r • X DI θ p := by abel
  rw [heq] at hmain
  refine hmain.trans ?_
  have hd : 0 ≤ ‖z - p‖ := norm_nonneg _
  nlinarith [mul_nonneg (mul_nonneg hK0 hr.1) hr.1, mul_nonneg (mul_nonneg (mul_nonneg hK0 hL0) hr.1) hd]

/-- Moving-point derivative at time `0`: `d/dr|₀ φ_θ^r(z(r)) = X_θ(z(0)) + z'(0)`. -/
theorem hasDerivAt_flow_moving (h : Hyp I DI) (θ : Linf) {z : ℝ → E} {z' : E} (hz : HasDerivAt z z' 0) :
    HasDerivAt (fun r => flow DI θ r (z r)) (X DI θ (z 0) + z') 0 := by
  suffices hG : HasDerivAt (fun r => flow DI θ r (z r) - z r) (X DI θ (z 0)) 0 by
    exact (hG.add hz).congr_of_eventuallyEq (Eventually.of_forall fun r => by simp)
  obtain ⟨δ₁, hδ₁, C₁, hC₁, H₁⟩ := increment h θ (z 0)
  obtain ⟨δ₂, hδ₂, C₂, hC₂, H₂⟩ := increment h (-θ) (z 0)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set C : ℝ := C₁ + C₂ + 1 with hC
  have hC0 : 0 < C := by positivity
  set δ : ℝ := min (min δ₁ δ₂) (c / (2 * C)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (by positivity)
  have hδc : δ ≤ c / (2 * C) := min_le_right _ _
  have hδ1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hzc : ∀ᶠ r in 𝓝 (0 : ℝ), z r ∈ ball (z 0) δ :=
    hz.continuousAt.tendsto.eventually (ball_mem_nhds (z 0) hδ0)
  have hr : ∀ᶠ r in 𝓝 (0 : ℝ), r ∈ Ioo (-δ) δ := Ioo_mem_nhds (by linarith) hδ0
  filter_upwards [hzc, hr] with r hzr hrr
  rw [mem_ball, dist_eq_norm] at hzr
  simp only [flow_zero h, sub_self, sub_zero, Real.norm_eq_abs]
  have hsum : ∀ ρ, 0 ≤ ρ → ρ < δ → ∀ C' : ℝ, 0 ≤ C' → C' ≤ C →
      C' * ρ * (ρ + ‖z r - z 0‖) ≤ c * ρ := by
    intro ρ hρ0 hρ C' hC'0 hC'
    have h1 : ρ + ‖z r - z 0‖ ≤ c / C := by
      have : c / (2 * C) + c / (2 * C) = c / C := by ring
      linarith
    have h2 : C' * (ρ + ‖z r - z 0‖) ≤ C * (c / C) :=
      mul_le_mul hC' h1 (by positivity) hC0.le
    have h3 : C * (c / C) = c := by field_simp
    calc C' * ρ * (ρ + ‖z r - z 0‖) = ρ * (C' * (ρ + ‖z r - z 0‖)) := by ring
      _ ≤ ρ * c := mul_le_mul_of_nonneg_left (h2.trans h3.le) hρ0
      _ = c * ρ := by ring
  rcases le_total 0 r with h0 | h0
  · have := H₁ (z r) (by rw [mem_closedBall, dist_eq_norm]; linarith) r ⟨h0, by linarith [hrr.2]⟩
    rw [abs_of_nonneg h0]
    exact this.trans (hsum r h0 hrr.2 C₁ hC₁ (by linarith))
  · have hfl : flow DI θ r (z r) = flow DI (-θ) (-r) (z r) := by rw [flow_neg_angle h, neg_neg]
    have := H₂ (z r) (by rw [mem_closedBall, dist_eq_norm]; linarith) (-r) ⟨by linarith, by linarith [hrr.1]⟩
    simp only [X_neg, smul_neg, neg_smul, neg_neg] at this
    rw [← hfl] at this
    rw [abs_of_nonpos h0]
    exact this.trans (hsum (-r) (by linarith) (by linarith [hrr.1]) C₂ hC₂ (by linarith))

/-- **Group law of the flows**: `φ_{θ+η}^t = φ_θ^t ∘ φ_η^t`. -/
theorem flow_add_angle (h : Hyp I DI) (θ η : Linf) (t : ℝ) (u : E) :
    flow DI (θ + η) t u = flow DI θ t (flow DI η t u) := by
  have hd : ∀ t, HasDerivAt (fun t => flow DI θ t (flow DI η t u))
      (X DI (θ + η) (flow DI θ t (flow DI η t u))) t := by
    intro t
    have hshift : (fun s => flow DI θ s (flow DI η s u)) =
        fun s => flow DI θ (s - t) (flow DI η (s - t) (flow DI θ t (flow DI η t u))) := by
      funext s
      rw [← commute h θ η t (s - t) (flow DI η t u), ← flow_add h η u (s - t) t,
        ← flow_add h θ _ (s - t) t, sub_add_cancel]
    rw [hshift]
    have hM := hasDerivAt_flow_moving h θ (z := fun r => flow DI η r (flow DI θ t (flow DI η t u)))
      (hasDerivAt_flow h η (flow DI θ t (flow DI η t u)) 0)
    simp only [flow_zero h, ← X_add] at hM
    exact HasDerivAt.comp_sub_const (f := fun r => flow DI θ r (flow DI η r (flow DI θ t (flow DI η t u)))) t t
      (by rw [sub_self]; exact hM)
  exact flow_eq_of_sol h (θ + η) (α := fun t => flow DI θ t (flow DI η t u))
    (by show flow DI θ 0 (flow DI η 0 u) = u; rw [flow_zero h, flow_zero h]) hd t

/-- **`T_θ T_η = T_{θ+η}`.** -/
theorem T_add (h : Hyp I DI) (θ η : Linf) (u : E) : T DI (θ + η) u = T DI θ (T DI η u) :=
  flow_add_angle h θ η 1 u

theorem T_comm (h : Hyp I DI) (θ η : Linf) (u : E) : T DI θ (T DI η u) = T DI η (T DI θ u) :=
  commute h θ η 1 1 u

/-! ## 5. Finitely supported angles -/

/-- The unit sequence `e_n ∈ ℓ^∞`. -/
def e (n : ℤ) : Linf := lp.single ⊤ n (1 : ℝ)

theorem pair_e (n : ℤ) : pair (e n) = coord n := by
  ext x
  show ∑' m, ((e n : Linf) : ℤ → ℝ) m * x m = x n
  rw [tsum_eq_single n (fun m hm => by rw [e, lp.single_apply, Pi.single_eq_of_ne hm, zero_mul]),
    e, lp.single_apply, Pi.single_eq_same, one_mul]

/-- The generator of `e_n` is the individual Hamiltonian field `X_{I_n}`. -/
theorem X_e (n : ℤ) : X DI (e n) = Xn DI n := funext fun u => by unfold X Xn; rw [pair_e]

/-- **Finite compositions** (lists of indices). -/
theorem T_list (h : Hyp I DI) (c : ℤ → ℝ) (l : List ℤ) (u : E) :
    T DI (l.map fun n => c n • e n).sum u = (l.map fun n => flow DI (e n) (c n)).foldr (· ∘ ·) id u := by
  induction l generalizing u with
  | nil => simp [T_zero h]
  | cons n l ih =>
    simp only [List.map_cons, List.sum_cons, List.foldr_cons, Function.comp_apply]
    rw [T_add h, ih, flow_eq_T h]

/-- **Finitely supported angles**: `T_{Σ_{n∈S} c_n e_n}` is the composition of the individual flows `φ_{I_n}^{c_n}`
(the generator of `e_n` being `X_{I_n}`, `X_e`). -/
theorem T_finset (h : Hyp I DI) (c : ℤ → ℝ) (S : Finset ℤ) (u : E) :
    T DI (∑ n ∈ S, c n • e n) u = (S.toList.map fun n => flow DI (e n) (c n)).foldr (· ∘ ·) id u := by
  rw [← Finset.sum_map_toList]
  exact T_list h c S.toList u

end QuantumNLS.ProductTorusCommute

#print axioms QuantumNLS.ProductTorusCommute.omega_nondeg
#print axioms QuantumNLS.ProductTorusCommute.symm2
#print axioms QuantumNLS.ProductTorusCommute.bracket
#print axioms QuantumNLS.ProductTorusCommute.push
#print axioms QuantumNLS.ProductTorusCommute.commute
#print axioms QuantumNLS.ProductTorusCommute.hasDerivAt_flow_moving
#print axioms QuantumNLS.ProductTorusCommute.flow_add_angle
#print axioms QuantumNLS.ProductTorusCommute.T_add
#print axioms QuantumNLS.ProductTorusCommute.X_e
#print axioms QuantumNLS.ProductTorusCommute.T_finset
