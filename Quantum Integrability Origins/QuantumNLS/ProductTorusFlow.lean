import QuantumNLS.ProductTorusConservation
import QuantumNLS.Ext025A6CompactFlow
import QuantumNLS.Ext025A8Global

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T2b: complete bounded-angle flows

Source: `chapters/global/product_torus.tex`, proof, "Bounded angle generators and complete flows", second paragraph:
"Along every local solution of `X_θ`, all `I_j` are consequently constant. Its trajectory lies in the compact fibre
`𝓘⁻¹({𝓘(u)})`. Continuity bounds `X_θ` there. At a finite maximal endpoint the integral equation therefore has a
strong Hilbert limit, and the local analytic ODE through that limit extends the solution. The flow `φ_θ^t` is
complete. The same argument proves conservation of mass ..."; and the third paragraph's
"`T_θ := φ_θ^1`, ..., `T_θ^{-1} = T_{-θ}`" (only the one-generator part: the group law for two different angles needs
the commuting-flow argument of stage T3).

Hypotheses (`Hyp I DI`), all source hypotheses or consequences of them:
* `D𝓘` is the Fréchet derivative of `𝓘 : H → ℓ¹` and is `C¹` (the source assumes `𝓘` real analytic);
* `Involutive D𝓘` (source hypothesis 2);
* every fibre `𝓘⁻¹{𝓘 u}` is norm compact (source hypothesis 3 applied to the compact set `{𝓘 u} ⊂ ℓ¹_+`, the
  positivity being source hypothesis 1; see `fibre_compact_of_source`).

Route (the printed one, with the endpoint argument replaced by an equivalent uniform-time continuation):
* `X_θ` is `C¹` (`X_contDiff`), hence Lipschitz on the compact fibre (`lipschitzOn_fibre`);
* GP-04 A6 `compact_common_local_solutions` (accepted at its displayed hypotheses) gives one positive local existence
  time for all initial points of the fibre; T2a `mem_fibre` keeps these local solutions in the fibre;
* EXT-025 A8 `uniform_invariant_global` glues such uniform local solutions in a set on which the field is Lipschitz
  into a global solution, by uniqueness on overlaps;
* uniqueness of global solutions: both stay in one compact fibre (T2a), where `X_θ` is Lipschitz.

Then `flow DI θ t u` is the complete flow `φ_θ^t(u)` and:
`flow_zero`, `hasDerivAt_flow`, `flow_eq_of_sol` (every global solution is the flow), `I_flow` (conservation),
`norm_flow` (mass conservation), `flow_add` (`φ^{t+s} = φ^t ∘ φ^s`), `flow_smul` (`φ_{cθ}^t = φ_θ^{ct}`),
`flow_neg_left`/`flow_neg_right` (`φ^{-t} ∘ φ^t = id = φ^t ∘ φ^{-t}`), and for `T_θ := φ_θ^1`:
`T_neg_T`, `T_T_neg` (`T_θ^{-1} = T_{-θ}`), `flow_eq_T` (`φ_θ^t = T_{tθ}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology Set Metric
open scoped InnerProductSpace NNReal

noncomputable section

namespace QuantumNLS.ProductTorusFlow

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusConservation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-! ## 1. `W⁻¹` as a bounded real-linear map; regularity of `X_θ` -/

/-- `W⁻¹` as a bounded real-linear map (norm `≤ 1/2`). -/
def WinvL : (E →L[ℝ] ℝ) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := Winv
      map_add' := Winv_add
      map_smul' := fun c ℓ => Winv_smul c ℓ }
    (1 / 2) (fun ℓ => by
      show ‖Winv ℓ‖ ≤ 1 / 2 * ‖ℓ‖
      rw [norm_Winv]; linarith)

lemma WinvL_apply (ℓ : E →L[ℝ] ℝ) : WinvL ℓ = Winv ℓ := rfl

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

lemma X_eq_comp (DI : E → (E →L[ℝ] L1 ℝ)) (θ : Linf) :
    X DI θ = fun u => WinvL (ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ) (DI u)) := by
  funext u
  rw [WinvL_apply, ContinuousLinearMap.compL_apply]
  rfl

/-- `X_θ` is as regular as `D𝓘`. -/
theorem X_contDiff {n : WithTop ℕ∞} (hDI : ContDiff ℝ n DI) (θ : Linf) : ContDiff ℝ n (X DI θ) := by
  rw [X_eq_comp]
  exact WinvL.contDiff.comp ((ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ)).contDiff.comp hDI)

/-- A `C¹` field is Lipschitz on every compact set. -/
theorem lipschitzOn_compact (hDI : ContDiff ℝ 1 DI) (θ : Linf) {K : Set E} (hK : IsCompact K) :
    ∃ L : ℝ≥0, LipschitzOnWith L (X DI θ) K :=
  ((X_contDiff hDI θ).locallyLipschitz).locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK

/-! ## 2. Hypotheses -/

/-- The hypotheses used for the complete flows. -/
structure Hyp (I : E → L1 ℝ) (DI : E → (E →L[ℝ] L1 ℝ)) : Prop where
  hasFDerivAt : ∀ u, HasFDerivAt I (DI u) u
  contDiff : ContDiff ℝ 1 DI
  involutive : Involutive DI
  fibre_compact : ∀ u, IsCompact (I ⁻¹' {I u})

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- Source hypotheses 1 (positivity) and 3 (properness on compact subsets of `ℓ¹_+`) give compact fibres. -/
theorem fibre_compact_of_source (hpos : ∀ u n, 0 ≤ (I u : ℤ → ℝ) n)
    (hprop : ∀ K : Set (L1 ℝ), IsCompact K → (∀ x ∈ K, ∀ n, 0 ≤ (x : ℤ → ℝ) n) → IsCompact (I ⁻¹' K))
    (u : E) : IsCompact (I ⁻¹' {I u}) :=
  hprop {I u} isCompact_singleton (by rintro x rfl; exact hpos u)

/-! ## 3. Global solutions: conservation, existence, uniqueness -/

/-- Conservation along a global solution. -/
theorem conserved_global (hI : ∀ u, HasFDerivAt I (DI u) u) (hinv : Involutive DI) (θ : Linf) {α : ℝ → E}
    (hα : ∀ t, HasDerivAt α (X DI θ (α t)) t) (s t : ℝ) : I (α t) = I (α s) :=
  conserved hI hinv θ (a := min s t - 1) (b := max s t + 1) (fun r _ => hα r)
    ⟨by linarith [min_le_left s t], by linarith [le_max_left s t]⟩
    ⟨by linarith [min_le_right s t], by linarith [le_max_right s t]⟩

/-- **Existence of a global solution** in the fibre of the initial point. -/
theorem exists_global (h : Hyp I DI) (θ : Linf) (u : E) :
    ∃ α : ℝ → E, α 0 = u ∧ ∀ t, HasDerivAt α (X DI θ (α t)) t ∧ α t ∈ I ⁻¹' {I u} := by
  set K : Set E := I ⁻¹' {I u} with hKdef
  have hK : IsCompact K := h.fibre_compact u
  have huK : u ∈ K := Set.mem_singleton (I u)
  obtain ⟨L, hL⟩ := lipschitzOn_compact h.contDiff θ hK
  obtain ⟨r, hr, δ, hδ, hloc⟩ := Ext025A6.compact_common_local_solutions hK ⟨u, huK⟩
    (fun x _ => (X_contDiff h.contDiff θ).contDiffAt) 0
  refine Ext025A8.uniform_invariant_global hL hδ ?_ huK
  intro x hx
  obtain ⟨γ, hγ0, hγ⟩ := hloc x hx x (mem_closedBall_self hr.le)
  have hγ' : ∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (X DI θ (γ t)) t := fun t ht =>
    hγ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  refine ⟨γ, hγ0, fun t ht => ⟨hγ' t ht, ?_⟩⟩
  have hm := mem_fibre h.hasFDerivAt h.involutive θ hγ' h0 t ht
  rw [hγ0] at hm
  have hx' : I x = I u := hx
  show I (γ t) ∈ ({I u} : Set (L1 ℝ))
  rw [← hx']
  exact hm

/-- **Uniqueness of global solutions.** -/
theorem global_unique (h : Hyp I DI) (θ : Linf) {α β : ℝ → E}
    (hα : ∀ t, HasDerivAt α (X DI θ (α t)) t) (hβ : ∀ t, HasDerivAt β (X DI θ (β t)) t) {t₀ : ℝ}
    (heq : α t₀ = β t₀) : α = β := by
  set K : Set E := I ⁻¹' {I (α t₀)} with hKdef
  obtain ⟨L, hL⟩ := lipschitzOn_compact h.contDiff θ (h.fibre_compact (α t₀))
  have hαK : ∀ t, α t ∈ K := fun t => conserved_global h.hasFDerivAt h.involutive θ hα t₀ t
  have hβK : ∀ t, β t ∈ K := fun t => by
    show I (β t) ∈ ({I (α t₀)} : Set (L1 ℝ))
    rw [heq]
    exact conserved_global h.hasFDerivAt h.involutive θ hβ t₀ t
  exact ODE_solution_unique_univ (v := fun _ => X DI θ) (s := fun _ => K) (fun _ => hL)
    (fun t => ⟨hα t, hαK t⟩) (fun t => ⟨hβ t, hβK t⟩) heq

/-! ## 4. The complete flow `φ_θ^t` -/

open Classical in
/-- The complete flow `φ_θ^t(u)` of `X_θ` (the chosen global solution through `u`; by `flow_eq_of_sol` it is the
unique one). -/
def flow (DI : E → (E →L[ℝ] L1 ℝ)) (θ : Linf) (t : ℝ) (u : E) : E :=
  if h : ∃ α : ℝ → E, α 0 = u ∧ ∀ s, HasDerivAt α (X DI θ (α s)) s then h.choose t else u

/-- Every global solution through `u` at time `0` is the flow. -/
theorem flow_eq_of_sol (h : Hyp I DI) (θ : Linf) {u : E} {α : ℝ → E} (hα0 : α 0 = u)
    (hα : ∀ t, HasDerivAt α (X DI θ (α t)) t) (t : ℝ) : flow DI θ t u = α t := by
  have hex : ∃ α : ℝ → E, α 0 = u ∧ ∀ s, HasDerivAt α (X DI θ (α s)) s := ⟨α, hα0, hα⟩
  have hc := hex.choose_spec
  have hu := global_unique h θ hc.2 hα (t₀ := 0) (by rw [hc.1, hα0])
  rw [flow, dite_eq_left hex, hu]

theorem flow_spec (h : Hyp I DI) (θ : Linf) (u : E) :
    flow DI θ 0 u = u ∧ ∀ t, HasDerivAt (fun t => flow DI θ t u) (X DI θ (flow DI θ t u)) t := by
  obtain ⟨α, hα0, hα⟩ := exists_global h θ u
  have he : (fun t => flow DI θ t u) = α := funext (flow_eq_of_sol h θ hα0 fun t => (hα t).1)
  refine ⟨by rw [flow_eq_of_sol h θ hα0 (fun t => (hα t).1), hα0], fun t => ?_⟩
  rw [he, flow_eq_of_sol h θ hα0 (fun t => (hα t).1) t]
  exact (hα t).1

theorem flow_zero (h : Hyp I DI) (θ : Linf) (u : E) : flow DI θ 0 u = u := (flow_spec h θ u).1

theorem hasDerivAt_flow (h : Hyp I DI) (θ : Linf) (u : E) (t : ℝ) :
    HasDerivAt (fun t => flow DI θ t u) (X DI θ (flow DI θ t u)) t := (flow_spec h θ u).2 t

theorem continuous_flow_time (h : Hyp I DI) (θ : Linf) (u : E) : Continuous (fun t => flow DI θ t u) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_flow h θ u t).continuousAt

/-- **Conservation of every action along the flow.** -/
theorem I_flow (h : Hyp I DI) (θ : Linf) (u : E) (t : ℝ) : I (flow DI θ t u) = I u := by
  have := conserved_global h.hasFDerivAt h.involutive θ (hasDerivAt_flow h θ u) 0 t
  rwa [flow_zero h θ u] at this

/-- **Mass conservation** (source hypothesis 1). -/
theorem norm_flow (h : Hyp I DI) (hmass : ∀ u, ∑' n, (I u : ℤ → ℝ) n = ‖u‖ ^ 2) (θ : Linf) (u : E) (t : ℝ) :
    ‖flow DI θ t u‖ = ‖u‖ := by
  have h2 : ‖flow DI θ t u‖ ^ 2 = ‖u‖ ^ 2 := by rw [← hmass, ← hmass, I_flow h θ u t]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The one-parameter group law `φ^{t+s} = φ^t ∘ φ^s`. -/
theorem flow_add (h : Hyp I DI) (θ : Linf) (u : E) (t s : ℝ) :
    flow DI θ (t + s) u = flow DI θ t (flow DI θ s u) := by
  have hd : ∀ r, HasDerivAt (fun r => flow DI θ (r + s) u) (X DI θ (flow DI θ (r + s) u)) r :=
    fun r => HasDerivAt.comp_add_const r s (hasDerivAt_flow h θ u (r + s))
  exact (flow_eq_of_sol h θ (α := fun r => flow DI θ (r + s) u) (by simp only [zero_add]) hd t).symm

/-- Rescaling the angle rescales time: `φ_{cθ}^t = φ_θ^{ct}`. -/
theorem flow_smul (h : Hyp I DI) (c : ℝ) (θ : Linf) (u : E) (t : ℝ) :
    flow DI (c • θ) t u = flow DI θ (c * t) u := by
  have hd : ∀ r, HasDerivAt (fun r => flow DI θ (c * r) u) (X DI (c • θ) (flow DI θ (c * r) u)) r := by
    intro r
    have h1 : HasDerivAt (fun y : ℝ => c * y) c r := by simpa using (hasDerivAt_id r).const_mul c
    have h2 := (hasDerivAt_flow h θ u (c * r)).scomp r h1
    rw [X_smul]
    exact h2
  exact flow_eq_of_sol h (c • θ) (α := fun r => flow DI θ (c * r) u) (by simp only [mul_zero]; exact flow_zero h θ u)
    hd t

theorem flow_neg_left (h : Hyp I DI) (θ : Linf) (u : E) (t : ℝ) : flow DI θ (-t) (flow DI θ t u) = u := by
  rw [← flow_add h, neg_add_cancel, flow_zero h]

theorem flow_neg_right (h : Hyp I DI) (θ : Linf) (u : E) (t : ℝ) : flow DI θ t (flow DI θ (-t) u) = u := by
  rw [← flow_add h, add_neg_cancel, flow_zero h]

/-! ## 5. The time-one maps `T_θ := φ_θ^1` -/

/-- `T_θ := φ_θ^1`. -/
def T (DI : E → (E →L[ℝ] L1 ℝ)) (θ : Linf) (u : E) : E := flow DI θ 1 u

theorem flow_neg_angle (h : Hyp I DI) (θ : Linf) (u : E) (t : ℝ) : flow DI (-θ) t u = flow DI θ (-t) u := by
  rw [← neg_one_smul ℝ θ, flow_smul h, neg_one_mul]

/-- `T_{-θ} ∘ T_θ = id`. -/
theorem T_neg_T (h : Hyp I DI) (θ : Linf) (u : E) : T DI (-θ) (T DI θ u) = u := by
  unfold T
  rw [flow_neg_angle h, flow_neg_left h]

/-- `T_θ ∘ T_{-θ} = id`. -/
theorem T_T_neg (h : Hyp I DI) (θ : Linf) (u : E) : T DI θ (T DI (-θ) u) = u := by
  unfold T
  rw [flow_neg_angle h, flow_neg_right h]

/-- `φ_θ^t = T_{tθ}`. -/
theorem flow_eq_T (h : Hyp I DI) (θ : Linf) (t : ℝ) (u : E) : flow DI θ t u = T DI (t • θ) u := by
  unfold T
  rw [flow_smul h, mul_one]

theorem I_T (h : Hyp I DI) (θ : Linf) (u : E) : I (T DI θ u) = I u := I_flow h θ u 1

theorem T_zero (h : Hyp I DI) (u : E) : T DI 0 u = u := by
  rw [← zero_smul ℝ (0 : Linf), ← flow_eq_T h, flow_zero h]

end QuantumNLS.ProductTorusFlow

#print axioms QuantumNLS.ProductTorusFlow.X_contDiff
#print axioms QuantumNLS.ProductTorusFlow.fibre_compact_of_source
#print axioms QuantumNLS.ProductTorusFlow.exists_global
#print axioms QuantumNLS.ProductTorusFlow.global_unique
#print axioms QuantumNLS.ProductTorusFlow.flow_eq_of_sol
#print axioms QuantumNLS.ProductTorusFlow.hasDerivAt_flow
#print axioms QuantumNLS.ProductTorusFlow.I_flow
#print axioms QuantumNLS.ProductTorusFlow.norm_flow
#print axioms QuantumNLS.ProductTorusFlow.flow_add
#print axioms QuantumNLS.ProductTorusFlow.flow_smul
#print axioms QuantumNLS.ProductTorusFlow.T_neg_T
#print axioms QuantumNLS.ProductTorusFlow.T_T_neg
#print axioms QuantumNLS.ProductTorusFlow.flow_eq_T
#print axioms QuantumNLS.ProductTorusFlow.T_zero
