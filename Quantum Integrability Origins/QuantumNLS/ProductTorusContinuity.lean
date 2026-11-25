import QuantumNLS.ProductTorusCommute

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T4a: product-topology continuity and the integer periods

Source: `chapters/global/product_torus.tex`, proof, "The product topology and full initial-point regularity",
paragraphs 1–3: "Suppose `θ^j → θ` coordinatewise, with `sup_j ‖θ^j‖_∞ ≤ R < ∞`. ...
`sup_{u∈𝒞} ‖X_{θ^j}(u) − X_θ(u)‖ → 0`. ... Comparing integral equations, a finite-interval Gronwall argument yields
convergence of the flows ... Joint continuity with the initial point follows by the same argument. If `u_j → u`,
continuity of `𝓘` makes `K = {𝓘(u_j)} ∪ {𝓘(u)}` compact. All the trajectories in the comparison lie in the single
compact set `𝓘⁻¹(K)`. ... For a bounded integer sequence `m`, its finite truncations give `T_{2πP_N m} = Id` by the
individual periods. The just proved convergence gives `T_{2πm} = Id`."

Hypotheses beyond `ProductTorusFlow.Hyp`: source hypothesis 1 (nonnegativity, `Nonneg`), source hypothesis 3
(`Proper`: `𝓘⁻¹(K)` compact for compact `K ⊂ ℓ¹_+`), and, for the periods, source hypothesis 4 in the form
`flow DI (e n) (2π) = id` (the complete flow of `I_n`, whose generator is `X_{I_n}` by T3 `X_e`).

Route for the comparison: both trajectories stay in the compact set `𝒞 = 𝓘⁻¹(K)` (T2b conservation), the `C¹` field
`X_θ` is Lipschitz on the compact set `𝒞` (mathlib: locally Lipschitz on a compact set ⇒ Lipschitz there, so no
convex neighbourhood or covering-ball subdivision is needed), the forcing `‖X_{θ^j} − X_θ‖ ≤ ε_j` on `𝒞` comes from T1
`X_tendsto_uniform`, and mathlib's approximate-trajectory Gronwall inequality compares them.

Proved:
* **`flow_tendsto`**: `θ^j → θ` coordinatewise and bounded, `u_j → u` ⇒ `φ_{θ^j}^t(u_j) → φ_θ^t(u)` for every `t`;
  `T_tendsto` (time one);
* `flow_e_int`: `φ_{I_n}^{2πk} = id` for every integer `k`;
* `T_finite_period`: `T_{Σ_{n∈S} 2π m_n e_n} = id`;
* **`T_period`**: `T_{2πm} = id` for every bounded integer sequence `m`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology Set Metric
open scoped InnerProductSpace NNReal

noncomputable section

namespace QuantumNLS.ProductTorusContinuity

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusVariational
  QuantumNLS.ProductTorusCommute

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-- Source hypothesis 1, nonnegativity. -/
def Nonneg (I : E → L1 ℝ) : Prop := ∀ u n, 0 ≤ (I u : ℤ → ℝ) n

/-- Source hypothesis 3: `𝓘⁻¹(K)` is norm compact whenever `K ⊂ ℓ¹_+` is norm compact. -/
def Proper (I : E → L1 ℝ) : Prop :=
  ∀ K : Set (L1 ℝ), IsCompact K → (∀ x ∈ K, ∀ n, 0 ≤ (x : ℤ → ℝ) n) → IsCompact (I ⁻¹' K)

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem compact_preimage (hpos : Nonneg I) (hprop : Proper I) (hIc : Continuous I) {us : ℕ → E} {u : E}
    (hu : Tendsto us atTop (𝓝 u)) : IsCompact (I ⁻¹' insert (I u) (range fun j => I (us j))) :=
  hprop _ (((hIc.tendsto u).comp hu).isCompact_insert_range) (by
    rintro x hx n
    rcases hx with rfl | ⟨j, rfl⟩
    · exact hpos u n
    · exact hpos (us j) n)

/-- Convergence of the flows for nonnegative times. -/
theorem flow_tendsto_nonneg (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) {θs : ℕ → Linf} {θ : Linf}
    {R : ℝ} (hR : ∀ j, ‖θs j‖ ≤ R) (hθR : ‖θ‖ ≤ R) (hcoord : ∀ n, Tendsto (fun j => θs j n) atTop (𝓝 (θ n)))
    {us : ℕ → E} {u : E} (hu : Tendsto us atTop (𝓝 u)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun j => flow DI (θs j) t (us j)) atTop (𝓝 (flow DI θ t u)) := by
  have hIc : Continuous I := continuous_iff_continuousAt.2 fun v => (h.hasFDerivAt v).continuousAt
  have hC : IsCompact (I ⁻¹' insert (I u) (range fun j => I (us j))) := compact_preimage hpos hprop hIc hu
  have huC : ∀ s, flow DI θ s u ∈ I ⁻¹' insert (I u) (range fun j => I (us j)) := fun s => by
    show I (flow DI θ s u) ∈ insert (I u) (range fun j => I (us j))
    rw [I_flow h]
    exact mem_insert _ _
  have husC : ∀ j s, flow DI (θs j) s (us j) ∈ I ⁻¹' insert (I u) (range fun j => I (us j)) := fun j s => by
    show I (flow DI (θs j) s (us j)) ∈ insert (I u) (range fun j => I (us j))
    rw [I_flow h]
    exact mem_insert_of_mem _ ⟨j, rfl⟩
  obtain ⟨L, hL⟩ := lipschitzOn_compact h.contDiff θ hC
  have hunif := X_tendsto_uniform DI _ hC h.contDiff.continuous.continuousOn θs θ hR hθR hcoord
  have hK0 : (0 : ℝ) < ((L + 1 : ℝ≥0) : ℝ) := by positivity
  obtain ⟨A, hA⟩ : ∃ A, A = Real.exp (((L + 1 : ℝ≥0) : ℝ) * t) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; exact Real.exp_pos _
  set M : ℝ := A * (1 + 1 / ((L + 1 : ℝ≥0) : ℝ)) with hM
  have hM0 : 0 < M := by positivity
  have hAM : A ≤ M := by
    have : (1 : ℝ) ≤ 1 + 1 / ((L + 1 : ℝ≥0) : ℝ) := by
      have : 0 ≤ 1 / ((L + 1 : ℝ≥0) : ℝ) := by positivity
      linarith
    calc A = A * 1 := (mul_one A).symm
      _ ≤ M := mul_le_mul_of_nonneg_left this hA0.le
  have hAL : A / ((L + 1 : ℝ≥0) : ℝ) ≤ M := by
    have : 1 / ((L + 1 : ℝ≥0) : ℝ) ≤ 1 + 1 / ((L + 1 : ℝ≥0) : ℝ) := by linarith
    calc A / ((L + 1 : ℝ≥0) : ℝ) = A * (1 / ((L + 1 : ℝ≥0) : ℝ)) := by ring
      _ ≤ M := mul_le_mul_of_nonneg_left this hA0.le
  refine Metric.tendsto_nhds.2 fun η hη => ?_
  have hδ : ∀ᶠ j in atTop, dist (us j) u < η / (2 * M) := Metric.tendsto_nhds.1 hu _ (by positivity)
  filter_upwards [hδ, hunif (η / (2 * M)) (by positivity)] with j hj hX
  have hg := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => X DI θ)
    (s := fun _ => I ⁻¹' insert (I u) (range fun j => I (us j))) (K := L + 1)
    (f := fun s => flow DI (θs j) s (us j)) (g := fun s => flow DI θ s u) (a := 0) (b := t)
    (f' := fun s => X DI (θs j) (flow DI (θs j) s (us j))) (g' := fun s => X DI θ (flow DI θ s u))
    (εf := η / (2 * M)) (εg := 0) (δ := dist (us j) u)
    (fun _ _ => hL.weaken le_self_add) (continuous_flow_time h _ _).continuousOn
    (fun s _ => (hasDerivAt_flow h _ _ s).hasDerivWithinAt)
    (fun s _ => by rw [dist_eq_norm]; exact hX _ (husC j s))
    (fun s _ => husC j s) (continuous_flow_time h _ _).continuousOn
    (fun s _ => (hasDerivAt_flow h _ _ s).hasDerivWithinAt) (fun s _ => by simp)
    (fun s _ => huC s)
    (by show dist (flow DI (θs j) 0 (us j)) (flow DI θ 0 u) ≤ dist (us j) u; rw [flow_zero h, flow_zero h])
    t ⟨ht, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hK0.ne'] at hg
  simp only [sub_zero, add_zero, ← hA] at hg
  have hd0 : 0 ≤ dist (us j) u := dist_nonneg
  have h1 : dist (us j) u * A ≤ dist (us j) u * M := mul_le_mul_of_nonneg_left hAM hd0
  have h2 : η / (2 * M) / ((L + 1 : ℝ≥0) : ℝ) * (A - 1) ≤ η / (2 * M) * M := by
    calc η / (2 * M) / ((L + 1 : ℝ≥0) : ℝ) * (A - 1) ≤ η / (2 * M) / ((L + 1 : ℝ≥0) : ℝ) * A :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = η / (2 * M) * (A / ((L + 1 : ℝ≥0) : ℝ)) := by ring
      _ ≤ η / (2 * M) * M := mul_le_mul_of_nonneg_left hAL (by positivity)
  have h3 : dist (us j) u * M < η / 2 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * M)).1 hj
    linarith
  have h4 : η / (2 * M) * M = η / 2 := by field_simp
  linarith

theorem neg_coord {θs : ℕ → Linf} {θ : Linf} (hcoord : ∀ n, Tendsto (fun j => θs j n) atTop (𝓝 (θ n))) :
    ∀ n, Tendsto (fun j => (-θs j) n) atTop (𝓝 ((-θ) n)) := fun n => by
  simp only [lp.coeFn_neg, Pi.neg_apply]
  exact (hcoord n).neg

/-- **Joint continuity of the flows in the product topology of bounded angles and the initial point.** -/
theorem flow_tendsto (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) {θs : ℕ → Linf} {θ : Linf}
    {R : ℝ} (hR : ∀ j, ‖θs j‖ ≤ R) (hθR : ‖θ‖ ≤ R) (hcoord : ∀ n, Tendsto (fun j => θs j n) atTop (𝓝 (θ n)))
    {us : ℕ → E} {u : E} (hu : Tendsto us atTop (𝓝 u)) (t : ℝ) :
    Tendsto (fun j => flow DI (θs j) t (us j)) atTop (𝓝 (flow DI θ t u)) := by
  rcases le_total 0 t with ht | ht
  · exact flow_tendsto_nonneg h hpos hprop hR hθR hcoord hu ht
  · have e1 : (fun j => flow DI (θs j) t (us j)) = fun j => flow DI (-θs j) (-t) (us j) :=
      funext fun j => by rw [flow_eq_neg h]
    rw [e1, flow_eq_neg h θ t]
    exact flow_tendsto_nonneg h hpos hprop (θs := fun j => -θs j) (θ := -θ) (R := R)
      (fun j => by rw [norm_neg]; exact hR j) (by rw [norm_neg]; exact hθR) (neg_coord hcoord) hu
      (by linarith)

theorem T_tendsto (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) {θs : ℕ → Linf} {θ : Linf}
    {R : ℝ} (hR : ∀ j, ‖θs j‖ ≤ R) (hθR : ‖θ‖ ≤ R) (hcoord : ∀ n, Tendsto (fun j => θs j n) atTop (𝓝 (θ n)))
    {us : ℕ → E} {u : E} (hu : Tendsto us atTop (𝓝 u)) :
    Tendsto (fun j => T DI (θs j) (us j)) atTop (𝓝 (T DI θ u)) :=
  flow_tendsto h hpos hprop hR hθR hcoord hu 1

/-! ## The integer periods -/

/-- Source hypothesis 4: the complete flow of each `I_n` has time `2π` equal to the identity. -/
def Periodic (DI : E → (E →L[ℝ] L1 ℝ)) : Prop := ∀ n u, flow DI (e n) (2 * Real.pi) u = u

theorem flow_e_nat (h : Hyp I DI) (hper : Periodic DI) (n : ℤ) (k : ℕ) (u : E) :
    flow DI (e n) (2 * Real.pi * k) u = u := by
  induction k generalizing u with
  | zero => simp [flow_zero h]
  | succ k ih =>
    rw [Nat.cast_succ, mul_add, mul_one, add_comm, flow_add h, ih, hper]

theorem flow_e_int (h : Hyp I DI) (hper : Periodic DI) (n k : ℤ) (u : E) :
    flow DI (e n) (2 * Real.pi * k) u = u := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · exact_mod_cast flow_e_nat h hper n m u
  · have h1 := flow_neg_left h (e n) u (2 * Real.pi * m)
    rw [flow_e_nat h hper n m u] at h1
    simp only [Int.cast_neg, Int.cast_natCast, mul_neg]
    exact h1

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem foldr_id {l : List ℤ} {F : ℤ → E → E} (hF : ∀ n u, F n u = u) (u : E) :
    (l.map F).foldr (· ∘ ·) id u = u := by
  induction l with
  | nil => rfl
  | cons n l ih => simp only [List.map_cons, List.foldr_cons, Function.comp_apply, ih, hF]

/-- Finite truncations: `T_{Σ_{n∈S} 2π m_n e_n} = id`. -/
theorem T_finite_period (h : Hyp I DI) (hper : Periodic DI) (m : ℤ → ℤ) (S : Finset ℤ) (u : E) :
    T DI (∑ n ∈ S, (2 * Real.pi * m n) • e n) u = u := by
  rw [T_finset h (fun n => 2 * Real.pi * m n)]
  exact foldr_id (F := fun n => flow DI (e n) (2 * Real.pi * m n)) (fun n v => flow_e_int h hper n (m n) v) u

theorem coe_finset_sum_e (c : ℤ → ℝ) (S : Finset ℤ) (k : ℤ) :
    ((∑ n ∈ S, c n • e n : Linf) : ℤ → ℝ) k = if k ∈ S then c k else 0 := by
  classical
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, e, lp.single_apply, smul_eq_mul]
  by_cases hk : k ∈ S
  · rw [ite_eq_left hk, Finset.sum_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb.symm, mul_zero])
      (fun h => absurd hk h), Pi.single_eq_same, mul_one]
  · rw [ite_eq_right hk]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hkb : k ≠ b := fun he => hk (he ▸ hb)
    rw [Pi.single_eq_of_ne hkb, mul_zero]

/-- **`T_{2πm} = id` for every bounded integer sequence `m`.** -/
theorem T_period (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) (hper : Periodic DI) (m : ℤ → ℤ) {B : ℝ}
    (hB : ∀ n, |(m n : ℝ)| ≤ B) (θ : Linf) (hθ : ∀ n, θ n = 2 * Real.pi * m n) (u : E) : T DI θ u = u := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set θs : ℕ → Linf := fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (2 * Real.pi * m n) • e n with hθs
  have hcoord : ∀ k, Tendsto (fun N => θs N k) atTop (𝓝 (θ k)) := by
    intro k
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k.natAbs] with N hN
    show θ k = ((∑ n ∈ Finset.Icc (-(N : ℤ)) N, (2 * Real.pi * m n) • e n : Linf) : ℤ → ℝ) k
    rw [coe_finset_sum_e, ite_eq_left (Finset.mem_Icc.2 ⟨by omega, by omega⟩), hθ]
  have hbound : ∀ k : ℤ, |2 * Real.pi * (m k : ℝ)| ≤ 2 * Real.pi * B := fun k => by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left (hB k) (by positivity)
  have hR : ∀ N, ‖θs N‖ ≤ 2 * Real.pi * B := fun N => by
    refine lp.norm_le_of_forall_le (by positivity) fun k => ?_
    show ‖((∑ n ∈ Finset.Icc (-(N : ℤ)) N, (2 * Real.pi * m n) • e n : Linf) : ℤ → ℝ) k‖ ≤ _
    rw [coe_finset_sum_e, Real.norm_eq_abs]
    split_ifs
    · exact hbound k
    · rw [abs_zero]; positivity
  have hθR : ‖θ‖ ≤ 2 * Real.pi * B := lp.norm_le_of_forall_le (by positivity) fun k => by
    rw [Real.norm_eq_abs, hθ]; exact hbound k
  have hlim : Tendsto (fun N => T DI (θs N) u) atTop (𝓝 (T DI θ u)) :=
    T_tendsto h hpos hprop hR hθR hcoord (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u))
  have hconst : (fun N => T DI (θs N) u) = fun _ => u := funext fun N => T_finite_period h hper m _ u
  rw [hconst] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

end QuantumNLS.ProductTorusContinuity

#print axioms QuantumNLS.ProductTorusContinuity.flow_tendsto_nonneg
#print axioms QuantumNLS.ProductTorusContinuity.flow_tendsto
#print axioms QuantumNLS.ProductTorusContinuity.T_tendsto
#print axioms QuantumNLS.ProductTorusContinuity.flow_e_int
#print axioms QuantumNLS.ProductTorusContinuity.T_finite_period
#print axioms QuantumNLS.ProductTorusContinuity.T_period
