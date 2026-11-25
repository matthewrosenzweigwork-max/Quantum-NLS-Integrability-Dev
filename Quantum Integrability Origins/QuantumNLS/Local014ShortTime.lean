import QuantumNLS.Local014StateLimits

/-!
# LOCAL-014 stage E6: the short-time Egorov limit

Source: `source-text/chapters/local/quantum_periods.tex:214-260` (proof of LOCAL-014):
"... a uniformly norm-convergent Heisenberg series for `|t| < (eK)^{-1}` ... Apply this observation
to each term in the Heisenberg series. The uniform majorant (reset:dyson-bound) justifies
interchanging the limit and the series. The resulting classical series equals `b(phi^t v)` ...
This proves (reset:egorov-limit) for short time."

Assembly of the frozen stages: E3 (Heisenberg series at fixed `N`, termwise majorant), E1/E2
(iterated commutator lists and their symbols), E4a (self-adjoint parts, `h` real on the sphere),
E4c (condensed states evaluate symbols), E5 (classical series along a solution curve).

* `fderiv_tangent_eq`, `fderiv_hamField_eq`: if two real functions agree on the unit sphere and are
  differentiable at a unit `u`, their Hamiltonian fields differ at `u` by a real multiple of `iu`,
  a vector tangent to the gauge orbit; every gauge-invariant differentiable `g` therefore has
  `dg(u)[X_F(u)] = dg(u)[X_G(u)]`. Consequently the Poisson brackets `{g, F}` and `{g, Re h}` agree
  on the unit sphere (`pbC_eq_of_sphere`) for every real `F` that coincides with the symbol `h`
  there: the classical series, hence the limit, does not depend on how `h` is extended off the
  sphere (the integrator's fidelity point about the flow of `h` versus that of `Re h`).
* `short_time`: for `e K |t| < 1`, normal states condensed at `phi 0` (`Tr(ρ_N Q_{N,1}(P)) → 1`) and
  any solution curve `phi` on the unit sphere of the Hamiltonian field of such an `F`,
  `Tr(ρ_N e^{itNH_N} Q_{N,q}(B) e^{−itNH_N}) → ⟨(phi t)^{⊗q}, B (phi t)^{⊗q}⟩`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators ENNReal Nat
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.TraceClass QuantumNLS.Ext025B11TracePairing
  QuantumNLS.Ext025A12Trace QuantumNLS.Ext025A12Normal QuantumNLS.KernelDefinition
  QuantumNLS.KernelConvergence QuantumNLS.SymplecticBracket QuantumNLS.Local014Dyson
  QuantumNLS.Local014Heisenberg QuantumNLS.Local014IteratedSymbol
  QuantumNLS.Local014ClassicalSeries QuantumNLS.Local014RealSymbol QuantumNLS.Local014OneBody
  QuantumNLS.Local014StateLimits

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.Local014ShortTime

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "REP" => QuantumNLS.RadiusBound.represented
local notation "RB" => QuantumNLS.RadiusBound.radiusBound

/-! ## 1. Extensions of `h` off the unit sphere -/

/-- A tangent vector at a unit `u` (`Re⟨u, y⟩ = 0`) is the velocity of a curve on the sphere,
so derivatives of functions agreeing on the sphere agree on it. -/
theorem fderiv_tangent_eq {F G : H → ℝ} {u : H} (hu : ‖u‖ = 1) (hF : DifferentiableAt ℝ F u)
    (hG : DifferentiableAt ℝ G u) (hFG : ∀ v : H, ‖v‖ = 1 → F v = G v) (y : H)
    (hy : (⟪u, y⟫_ℂ).re = 0) : fderiv ℝ F u y = fderiv ℝ G u y := by
  by_cases hy0 : y = 0
  · simp [hy0]
  set a := ‖y‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hy0
  set c : ℝ → H := fun s => ((Real.cos (s * a) : ℝ) : ℂ) • u + ((Real.sin (s * a) / a : ℝ) : ℂ) • y
    with hc
  have hc0 : c 0 = u := by simp [hc]
  have hcn : ∀ s, ‖c s‖ = 1 := by
    intro s
    have h2 : ‖c s‖ ^ 2 = 1 := by
      rw [hc]
      simp only
      rw [norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, inner_smul_left, inner_smul_right,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, hu]
      have hre : (((starRingEnd ℂ) ((Real.cos (s * a) : ℝ) : ℂ)) *
          (((Real.sin (s * a) / a : ℝ) : ℂ) * ⟪u, y⟫_ℂ)).re = 0 := by
        rw [Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul, hy,
          mul_zero]
      simp only [RCLike.re_to_complex]
      rw [hre, abs_div, abs_of_pos ha0, ← ha, div_mul_cancel₀ _ ha0.ne', mul_one, sq_abs, sq_abs,
        mul_zero, add_zero]
      linarith [Real.sin_sq_add_cos_sq (s * a)]
    have := norm_nonneg (c s)
    nlinarith
  have hcd : HasDerivAt c y 0 := by
    have h1 : HasDerivAt (fun s : ℝ => Real.cos (s * a)) (-Real.sin (0 * a) * (1 * a)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).mul_const a).cos
    have h2 : HasDerivAt (fun s : ℝ => Real.sin (s * a) / a) (Real.cos (0 * a) * (1 * a) / a) 0 :=
      (((hasDerivAt_id (0 : ℝ)).mul_const a).sin).div_const a
    have h := (h1.ofReal_comp.smul_const u).add (h2.ofReal_comp.smul_const y)
    convert h using 1
    simp [ha0.ne']
  have hFc : HasDerivAt (fun s => F (c s)) (fderiv ℝ F u y) 0 := by
    have h : HasFDerivAt F (fderiv ℝ F u) (c 0) := by rw [hc0]; exact hF.hasFDerivAt
    exact h.comp_hasDerivAt (0 : ℝ) hcd
  have hGc : HasDerivAt (fun s => G (c s)) (fderiv ℝ G u y) 0 := by
    have h : HasFDerivAt G (fderiv ℝ G u) (c 0) := by rw [hc0]; exact hG.hasFDerivAt
    exact h.comp_hasDerivAt (0 : ℝ) hcd
  have heq : (fun s => F (c s)) = fun s => G (c s) := funext fun s => hFG _ (hcn s)
  rw [heq] at hFc
  exact hFc.unique hGc

/-- Derivative of a gauge-invariant function along the gauge orbit vanishes. -/
theorem fderiv_gauge (g : H → ℂ) (hg : ∀ (c : ℂ), ‖c‖ = 1 → ∀ v, g (c • v) = g v) {u : H}
    (hd : DifferentiableAt ℝ g u) : fderiv ℝ g u (Complex.I • u) = 0 := by
  have hγ : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I) • u) (Complex.I • u) 0 := by
    have he : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I))
        (Complex.exp ((0 : ℝ) * Complex.I) * Complex.I) 0 :=
      ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp.congr_deriv (by simp)
    have := he.smul_const u
    simpa using this
  have hcomp : HasDerivAt (fun θ : ℝ => g (Complex.exp (θ * Complex.I) • u))
      (fderiv ℝ g u (Complex.I • u)) 0 := by
    have h : HasFDerivAt g (fderiv ℝ g u) (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) • u) := by
      simpa using hd.hasFDerivAt
    exact h.comp_hasDerivAt (0 : ℝ) hγ
  have hconst : HasDerivAt (fun θ : ℝ => g (Complex.exp (θ * Complex.I) • u)) 0 0 := by
    have : (fun θ : ℝ => g (Complex.exp (θ * Complex.I) • u)) = fun _ => g u :=
      funext fun θ => hg _ (by rw [Complex.norm_exp_ofReal_mul_I]) u
    rw [this]; exact hasDerivAt_const _ _
  exact hcomp.unique hconst

/-- **Hamiltonian fields of two extensions differ along the gauge orbit**: if real `F`, `G` agree
on the unit sphere and are differentiable at a unit `u`, then every gauge-invariant `g`
differentiable at `u` has `dg(u)[X_F(u)] = dg(u)[X_G(u)]`. -/
theorem fderiv_hamField_eq {F G : H → ℝ} {u : H} (hu : ‖u‖ = 1) (hF : DifferentiableAt ℝ F u)
    (hG : DifferentiableAt ℝ G u) (hFG : ∀ v : H, ‖v‖ = 1 → F v = G v) (g : H → ℂ)
    (hg : ∀ (c : ℂ), ‖c‖ = 1 → ∀ v, g (c • v) = g v) (hd : DifferentiableAt ℝ g u) :
    fderiv ℝ g u (hamField F u) = fderiv ℝ g u (hamField G u) := by
  set z := SymplecticBracket.gradient F u - SymplecticBracket.gradient G u with hz
  have hD : ∀ y : H, (⟪u, y⟫_ℂ).re = 0 → (⟪z, y⟫_ℂ).re = 0 := by
    intro y hy
    have h := fderiv_tangent_eq hu hF hG hFG y hy
    rw [fderiv_eq_two_inner_gradient, fderiv_eq_two_inner_gradient, real_inner_eq_re_inner,
      real_inner_eq_re_inner] at h
    rw [hz, inner_sub_left, Complex.sub_re]
    simp only [RCLike.re_to_complex] at h
    linarith
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
  set c : ℝ := (⟪u, z⟫_ℂ).re with hcdef
  set y := z - (c : ℂ) • u with hydef
  have hyt : (⟪u, y⟫_ℂ).re = 0 := by
    rw [hydef, inner_sub_right, inner_smul_right, huu, mul_one, Complex.sub_re, Complex.ofReal_re]
    simp [hcdef]
  have hzy := hD y hyt
  have hyy : (⟪y, y⟫_ℂ).re = 0 := by
    have : ⟪y, y⟫_ℂ = ⟪z, y⟫_ℂ - (c : ℂ) * ⟪u, y⟫_ℂ := by
      rw [hydef, inner_sub_left, inner_smul_left, Complex.conj_ofReal]
    rw [this, Complex.sub_re, Complex.re_ofReal_mul, hzy, hyt, mul_zero, sub_zero]
  have hy0 : y = 0 := by
    have h2 : ‖y‖ ^ 2 = 0 := by
      have hn : ⟪y, y⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
      rw [hn, Complex.ofReal_re] at hyy
      exact hyy
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  have hzc : z = (c : ℂ) • u := by
    rw [hydef] at hy0
    exact sub_eq_zero.mp hy0
  have hdiff : hamField F u = hamField G u + c • ((-Complex.I) • u) := by
    have : hamField F u - hamField G u = c • ((-Complex.I) • u) := by
      rw [hamField, hamField, ← smul_sub, ← hz, hzc, smul_comm, Complex.coe_smul]
    rw [← this]; abel
  rw [hdiff, map_add, map_smul, neg_smul, map_neg, fderiv_gauge g hg hd, neg_zero, smul_zero,
    add_zero]

theorem pbC_congr_right (g : H → ℂ) {F G : H → ℂ} {u : H} (h : F =ᶠ[𝓝 u] G) :
    pbC g F u = pbC g G u := by
  have hre : (fun v => (F v).re) =ᶠ[𝓝 u] (fun v => (G v).re) := h.mono fun v hv => by simp [hv]
  have him : (fun v => (F v).im) =ᶠ[𝓝 u] (fun v => (G v).im) := h.mono fun v hv => by simp [hv]
  simp only [pbC, pbR, hamField, SymplecticBracket.gradient, hre.fderiv_eq, him.fderiv_eq]

/-- `{g, F} = {g, Re h}` on the unit sphere for gauge-invariant differentiable `g`, whenever the
real `F` coincides with the symbol `h` on the unit sphere and is differentiable there. -/
theorem pbC_eq_of_sphere {F G : H → ℝ} {u : H} (hu : ‖u‖ = 1) (hF : DifferentiableAt ℝ F u)
    (hG : DifferentiableAt ℝ G u) (hFG : ∀ v : H, ‖v‖ = 1 → F v = G v) (g : H → ℂ)
    (hg : ∀ (c : ℂ), ‖c‖ = 1 → ∀ v, g (c • v) = g v) (hd : DifferentiableAt ℝ g u) :
    pbC g (fun v => (F v : ℂ)) u = pbC g (fun v => (G v : ℂ)) u := by
  rw [pbC_ofReal g F hd, pbC_ofReal g G hd, fderiv_hamField_eq hu hF hG hFG g hg hd]

/-! ## 2. The short-time limit -/

/-- `e^{itNA} X e^{−itNA}` (E3's `opExp`). -/
def heis (N : ℕ) (A X : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (t : ℝ) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  opExp ((Complex.I * (t : ℂ) * (N : ℂ)) • A) * X *
    opExp (-((Complex.I * (t : ℂ) * (N : ℂ)) • A))

theorem tr_mul_smul {N : ℕ} (ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (a : ℂ)
    (Y : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) : tr (ρ * (a • Y)) = a * tr (ρ * Y) := by
  have h : ρ * (a • Y) = a • (ρ * Y) := by
    ext x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul]
  rw [h]
  exact trace_smul _ a _

theorem tr_mul_sub {N : ℕ} {ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N} (ht : IsTraceClass ρ)
    (Y Z : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) : tr (ρ * (Y - Z)) = tr (ρ * Y) - tr (ρ * Z) := by
  rw [mul_sub]
  exact trace_sub _ _ _ (finite_right Y ρ ht).ne (finite_right Z ρ ht).ne

/-- **Short-time Egorov limit** (source 214-260). `K` bounds the radius-`8` norms of the
self-adjoint-part expansion (E4a) of `H_N`; `F` is any real function differentiable on the unit
sphere and equal there to the symbol `h` of `H_N`; `phi` is a solution curve on the unit sphere of
the Hamiltonian field of `F`; `ρ_N` are normal states condensed at `phi 0`. Then for `e K |t| < 1`,
`Tr(ρ_N e^{itNH_N} Q_{N,q}(B) e^{−itNH_N}) → ⟨(phi t)^{⊗q}, B (phi t)^{⊗q}⟩`. -/
theorem short_time {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hH : ConvergesOnRadius 8 Hk Hlim)
    (hsa : ∀ N, IsSelfAdjoint (REP (Hk N))) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ N, RB 8 (saList Hk N) ≤ K) (F : H → ℝ)
    (hFd : ∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ F u)
    (hF : ∀ u : H, ‖u‖ = 1 → (F u : ℂ) = symbol Hlim u) {phi : ℝ → H}
    (hphi : ∀ s, HasDerivAt phi (hamField F (phi s)) s) (hn : ∀ s, ‖phi s‖ = 1)
    (ρ : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (hρ : ∀ N, IsNormalState (ρ N))
    (h1 : Tendsto (fun N => qexp (ρ N) 1 (P (phi 0) 1)) atTop (𝓝 1)) {t : ℝ}
    (ht : Real.exp 1 * K * |t| < 1) (q : ℕ) (B : BoundedSymmetricKernel H q) :
    Tendsto (fun N => tr (ρ N * heis N (REP (Hk N)) (REP (testList q B N)) t)) atTop
      (𝓝 (kernelProductSymbol B (phi t))) := by
  set S := saList Hk with hSdef
  have hS : ConvergesOnRadius 8 S (saLim Hlim) := saList_converges (by norm_num) hH
  have hSrep : ∀ N, REP (S N) = REP (Hk N) := fun N => represented_saList Hk N (hsa N)
  have hX : ConvergesOnRadius 4 (testList q B) (testLim q B) := test_converges (by norm_num) B
  set g : ℕ → H → ℂ := fun k => symbol (iterLim (saLim Hlim) (testLim q B) k) with hgdef
  set c : ℕ → ℕ → ℂ := fun N k =>
    ((t : ℂ) ^ k / (k ! : ℂ)) * tr (ρ N * REP (dysonList S (testList q B) k N)) with hcdef
  set Cq : ℝ := 4 ^ q * ‖B‖ with hCq
  have hCq0 : 0 ≤ Cq := by positivity
  -- termwise limits (E4c applied to the iterated commutator families, E2)
  have hterm : ∀ k, Tendsto (fun N => c N k) atTop (𝓝 (((t : ℂ) ^ k / (k ! : ℂ)) * g k (phi 0))) := by
    intro k
    have hR : (1 : ℝ) < 2 + 2 / ((k : ℝ) + 1) := by have := radius_pos k; linarith
    exact (tendsto_tr_represented hR (iter_converges hS hX k) (hn 0) ρ hρ h1).const_mul _
  -- the uniform Dyson majorant (E3), for `N ≥ q`
  have hrepk : ∀ N k, REP (dysonList S (testList q B) k N) =
      (deltaOp N (REP (Hk N)))^[k] (REP (testList q B N)) := by
    intro N k
    rw [represented_dysonList, hSrep]
  have hbound : ∀ᶠ N in atTop, ∀ k, ‖c N k‖ ≤ (Real.exp 1 * K * |t|) ^ k * Cq := by
    filter_upwards [eventually_ge_atTop q] with N hqN k
    have hb := norm_heisenberg_term_le hK hqN B t k
    rw [hSrep] at hb
    have hc : c N k = tr (ρ N * (((t : ℂ) ^ k / (k ! : ℂ)) •
        (deltaOp N (REP (Hk N)))^[k] (RadiusBound.Q N q hqN B))) := by
      rw [tr_mul_smul, hcdef]
      beta_reduce
      rw [hrepk, represented_testList hqN]
    rw [hc]
    exact (norm_tr_mul_le (hρ N) _).trans hb
  have hsumm : Summable fun k : ℕ => (Real.exp 1 * K * |t|) ^ k * Cq :=
    (summable_geometric_of_lt_one (by positivity) ht).mul_right Cq
  -- the Heisenberg series evaluated in the state (E3), for `N ≥ q`
  have hid : ∀ᶠ N in atTop,
      tr (ρ N * heis N (REP (Hk N)) (REP (testList q B N)) t) = ∑' k, c N k := by
    filter_upwards [hbound] with N hb
    have hs : Summable (c N) := Summable.of_norm_bounded hsumm hb
    have hpart : Tendsto (fun n => ∑ k ∈ range n, c N k) atTop
        (𝓝 (tr (ρ N * heis N (REP (Hk N)) (REP (testList q B N)) t))) := by
      have hHe := heisenberg_tendsto N (REP (Hk N)) (REP (testList q B N)) t
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hHe
      have hsum : ∑ k ∈ range n, c N k = tr (ρ N * ∑ k ∈ range n,
          ((t : ℂ) ^ k / (k ! : ℂ)) • (deltaOp N (REP (Hk N)))^[k] (REP (testList q B N))) := by
        rw [Finset.mul_sum, tr_sum _ _ (fun k => finite_right _ _ (hρ N).2.1)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [tr_mul_smul, hcdef]
        beta_reduce
        rw [hrepk]
      rw [hsum, ← tr_mul_sub (hρ N).2.1]
      exact norm_tr_mul_le (hρ N) _
    exact tendsto_nhds_unique hpart hs.hasSum.tendsto_sum_nat
  -- interchange of limit and series (dominated convergence)
  have hlim : Tendsto (fun N => ∑' k, c N k) atTop
      (𝓝 (∑' k, ((t : ℂ) ^ k / (k ! : ℂ)) * g k (phi 0))) :=
    tendsto_tsum_of_dominated_convergence hsumm hterm hbound
  -- the classical series (E5), with the chain of brackets with `F`
  have hdiff : ∀ k (u : H), ‖u‖ = 1 → DifferentiableAt ℝ (g k) u := by
    intro k u hu
    have hR := radius_pos k
    exact differentiableAt_symbol (summable_of_converges (by linarith) (iter_converges hS hX k))
      (by rw [hu]; linarith)
  have hhR : ∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ (hReal Hlim) u := by
    intro u hu
    exact Complex.reCLM.differentiableAt.comp u
      (differentiableAt_symbol (summable_of_converges (by norm_num) hH) (by rw [hu]; norm_num))
  have hsucc : ∀ k (u : H), ‖u‖ = 1 → g (k + 1) u = pbC (g k) (fun v => (F v : ℂ)) u := by
    intro k u hu
    have h2 : ‖u‖ ^ 2 < 2 := by rw [hu]; norm_num
    have hev : symbol (saLim Hlim) =ᶠ[𝓝 u] fun v => ((hReal Hlim v : ℝ) : ℂ) :=
      Filter.eventuallyEq_of_mem (isOpen_ball2.mem_nhds h2) fun v hv =>
        symbol_saLim (by norm_num) hH v (by have : ‖v‖ ^ 2 < 2 := hv; linarith)
    rw [show g (k + 1) u = pbC (g k) (symbol (saLim Hlim)) u from
      symbol_iterLim_succ hS hX k u h2, pbC_congr_right _ hev]
    refine pbC_eq_of_sphere hu (hhR u hu) (hFd u hu) (fun v hv => ?_) (g k)
      (fun c hc v => symbol_phase _ hc v) (hdiff k u hu)
    have := congrArg Complex.re (hF v hv)
    simp only [Complex.ofReal_re] at this
    simp [hReal, this]
  have hbd : ∀ k (u : H), ‖u‖ = 1 → ‖g k u‖ ≤ (K * k) ^ k * Cq :=
    fun k u hu => norm_symbol_iterLim_le hS hK B k u hu.le
  have hcl := classical_hasSum F g hK0 hCq0 hphi hn hdiff hsucc hbd ht
  have heq : ∑' k, ((t : ℂ) ^ k / (k ! : ℂ)) * g k (phi 0) = kernelProductSymbol B (phi t) := by
    have h0 : g 0 (phi t) = kernelProductSymbol B (phi t) := symbol_testLim B (phi t)
    rw [← h0, ← hcl.tsum_eq]
    congr 1
    funext k
    push_cast
    ring
  rw [← heq]
  exact hlim.congr' (hid.mono fun N h => h.symm)

end QuantumNLS.Local014ShortTime

#print axioms QuantumNLS.Local014ShortTime.fderiv_tangent_eq
#print axioms QuantumNLS.Local014ShortTime.fderiv_gauge
#print axioms QuantumNLS.Local014ShortTime.fderiv_hamField_eq
#print axioms QuantumNLS.Local014ShortTime.pbC_congr_right
#print axioms QuantumNLS.Local014ShortTime.pbC_eq_of_sphere
#print axioms QuantumNLS.Local014ShortTime.tr_mul_smul
#print axioms QuantumNLS.Local014ShortTime.tr_mul_sub
#print axioms QuantumNLS.Local014ShortTime.short_time
