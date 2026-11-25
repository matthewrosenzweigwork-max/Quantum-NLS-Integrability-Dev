import QuantumNLS.Local014Main

/-!
# LOCAL-014 `reset:analytic-egorov` for a flow on an interval (new module)

Source: `source-text/chapters/local/quantum_periods.tex:186-267` (statement 186-203, proof
204-267). The source assumes "the Hamiltonian flow `phi^t` of `h` exists on the unit sphere for all
times under consideration". The frozen theorem `Local014Main.local014_analytic_egorov` instead
assumes a solution curve for all real times (Terra r183 hold). This module restates the theorem
with the flow given only on an interval `I`.

Reading adopted (the source names no endpoint convention):
* `I : Set ℝ` is an interval, `I.OrdConnected` (equivalently convex in `ℝ`), with `0 ∈ I`; `I`
  may be open, closed, half-open, bounded or unbounded;
* `hphi : ∀ s ∈ I, HasDerivWithinAt phi (hamField F (phi s)) I s`, which is `HasDerivAt` at interior
  points of `I` (`HasDerivAt.hasDerivWithinAt`) and a one-sided derivative inside `I` at endpoints;
* `hn : ∀ s ∈ I, ‖phi s‖ = 1`;
* the conclusions (ii) and (iii) hold for every `t ∈ I`; part (i) and the sphere hypotheses on `F`
  and `h` are unchanged from the frozen theorem.

Why local copies of the frozen E5/E6 lemmas are needed (the obstacle, stated exactly): the frozen
`Local014ClassicalSeries.classical_hasSum` and `Local014ShortTime.short_time` take the hypothesis
`∀ s, HasDerivAt phi (hamField F (phi s)) s` on all of `ℝ`, and the frozen `taylor_bound` uses
`HasDerivAt` on all of `ℝ`. A curve defined only on `I` admits no legitimate global extension:
constant or reflected continuation fails to be differentiable at a finite endpoint of `I` unless
`hamField F` vanishes there, and an open `I` admits no continuation at all. The frozen lemmas are
therefore not applied to an extension. Instead the proofs of the E5 classical series and the E6
short-time limit are repeated verbatim, except that every use of the flow is restricted to the
segment `Set.uIcc 0 t ⊆ I` and derivatives are taken within that segment (`taylor_bound_on`,
`classical_hasSum_on`, `short_time_on`). The restart induction is repeated on `I` with the
shift `s' ↦ t₀ + s'` (`restart_split_mem`, `hasDerivWithinAt_shift`). Frozen lemmas that do not
use the global flow are reused by name: `Local014Main.evolve`, `evolve_isNormalState`,
`tr_evolve_heis`, `kps_P_self`, `heis_zero`, `represented_testList`, `symbol_im_eq_zero`,
`differentiableAt_symbol`, `pbC_ofReal`, `taylorPoly`, `hasDerivAt_taylorPoly`,
`taylorPoly_zero_point`, `pow_div_factorial_le`, `heisenberg_tendsto`, `norm_heisenberg_term_le`,
`norm_symbol_iterLim_le`, `iter_converges`, `test_converges`, `tendsto_tr_represented`, and the
symbol and state lemmas of the E1-E4 stages.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators ENNReal Nat ComplexOrder
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.TraceClass QuantumNLS.Ext025B11TracePairing
  QuantumNLS.Ext025A12Trace QuantumNLS.Ext025A12Normal QuantumNLS.KernelDefinition
  QuantumNLS.KernelConvergence QuantumNLS.SymplecticBracket QuantumNLS.Local014Dyson
  QuantumNLS.Local014Heisenberg QuantumNLS.Local014IteratedSymbol
  QuantumNLS.Local014ClassicalSeries QuantumNLS.Local014RealSymbol QuantumNLS.Local014OneBody
  QuantumNLS.Local014StateLimits QuantumNLS.Local014ShortTime QuantumNLS.Local014Main

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.Local014Interval

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "REP" => QuantumNLS.RadiusBound.represented
local notation "RB" => QuantumNLS.RadiusBound.radiusBound

/-! ## 1. Taylor remainder on a segment (local form of the frozen E5 remainder) -/

/-- A derivative within a segment `[a, t]`, at a point `x < t`, is a derivative within `[x, ∞)`. -/
theorem hasDerivWithinAt_Ici_of_Icc {f : ℝ → ℂ} {f' : ℂ} {a t x : ℝ} (hx : x ∈ Set.Ico a t)
    (h : HasDerivWithinAt f f' (Set.Icc a t) x) : HasDerivWithinAt f f' (Set.Ici x) x := by
  refine h.mono_of_mem_nhdsWithin (Filter.mem_of_superset (Ico_mem_nhdsGE hx.2) ?_)
  intro y hy
  exact ⟨hx.1.trans hy.1, hy.2.le⟩

/-- **Taylor remainder on `[0, t]`**, `0 ≤ t` (local form of `taylor_bound_nonneg`). -/
theorem taylor_bound_nonneg_on (n : ℕ) :
    ∀ (G : ℕ → ℝ → ℂ) (M : ℕ → ℝ) (t : ℝ), 0 ≤ t →
      (∀ k x, x ∈ Set.Icc 0 t → HasDerivWithinAt (G k) (G (k + 1) x) (Set.Icc 0 t) x) →
      (∀ k x, x ∈ Set.Icc 0 t → ‖G k x‖ ≤ M k) →
      ‖G 0 t - taylorPoly (fun k => G k 0) n t‖ ≤ M n * t ^ n / (n ! : ℝ) := by
  induction n with
  | zero =>
    intro G M t ht _ hb
    simpa [taylorPoly] using hb 0 t ⟨ht, le_rfl⟩
  | succ n ih =>
    intro G M t ht hd hb
    set f : ℝ → ℂ := fun s => G 0 s - taylorPoly (fun k => G k 0) (n + 1) s with hf
    set f' : ℝ → ℂ := fun s => G 1 s - taylorPoly (fun k => G (k + 1) 0) n s with hf'
    have hfd : ∀ s ∈ Set.Icc 0 t, HasDerivWithinAt f (f' s) (Set.Icc 0 t) s := fun s hs =>
      (hd 0 s hs).sub (hasDerivAt_taylorPoly (fun k => G k 0) n s).hasDerivWithinAt
    have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hfac1 : (0 : ℝ) < ((n + 1) ! : ℝ) := by exact_mod_cast Nat.factorial_pos (n + 1)
    set B : ℝ → ℝ := fun s => M (n + 1) * s ^ (n + 1) / ((n + 1) ! : ℝ) with hB
    set B' : ℝ → ℝ := fun s => M (n + 1) * s ^ n / (n ! : ℝ) with hB'
    have hBd : ∀ s, HasDerivAt B (B' s) s := by
      intro s
      have h := ((hasDerivAt_pow (n + 1) s).const_mul (M (n + 1))).div_const ((n + 1) ! : ℝ)
      refine h.congr_deriv ?_
      simp only [hB', Nat.factorial_succ]
      push_cast
      field_simp
      try ring
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := t)
      (f := f) (f' := f') (B := B) (B' := B')
      (fun s hs => (hfd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hfd s ⟨hs.1, hs.2.le⟩))
      (by simp [hf, hB, taylorPoly_zero_point])
      hBd
      (fun s hs => by
        have h := ih (fun k => G (k + 1)) (fun k => M (k + 1)) s hs.1
          (fun k x hx => (hd (k + 1) x ⟨hx.1, hx.2.trans hs.2.le⟩).mono
            (Set.Icc_subset_Icc le_rfl hs.2.le))
          (fun k x hx => hb (k + 1) x ⟨hx.1, hx.2.trans hs.2.le⟩)
        simpa [hf'] using h)
    have := key ⟨ht, le_rfl⟩
    simpa [hf, hB] using this

/-- **Taylor remainder on the segment `[[0, t]]`**, both signs of `t` (local form of
`taylor_bound`). -/
theorem taylor_bound_on (n : ℕ) (G : ℕ → ℝ → ℂ) (M : ℕ → ℝ) (t : ℝ)
    (hd : ∀ k x, x ∈ Set.uIcc 0 t → HasDerivWithinAt (G k) (G (k + 1) x) (Set.uIcc 0 t) x)
    (hb : ∀ k x, x ∈ Set.uIcc 0 t → ‖G k x‖ ≤ M k) :
    ‖G 0 t - taylorPoly (fun k => G k 0) n t‖ ≤ M n * |t| ^ n / (n ! : ℝ) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    rw [Set.uIcc_of_le ht] at hd hb
    exact taylor_bound_nonneg_on n G M t ht hd hb
  · rw [abs_of_neg ht]
    have hu : Set.uIcc 0 t = Set.Icc t 0 := Set.uIcc_of_ge ht.le
    have hmaps : Set.MapsTo (fun s : ℝ => -s) (Set.Icc 0 (-t)) (Set.uIcc 0 t) := by
      intro y hy
      rw [hu]
      show t ≤ -y ∧ -y ≤ 0
      exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    set G' : ℕ → ℝ → ℂ := fun k s => ((-1 : ℂ) ^ k) * G k (-s) with hG'
    have hd' : ∀ k x, x ∈ Set.Icc 0 (-t) →
        HasDerivWithinAt (G' k) (G' (k + 1) x) (Set.Icc 0 (-t)) x := by
      intro k x hx
      have hg : HasDerivWithinAt (G k) (G (k + 1) (-x)) (Set.uIcc 0 t) (-x) :=
        hd k (-x) (hmaps hx)
      have hneg : HasDerivWithinAt (fun s : ℝ => -s) (-1) (Set.Icc 0 (-t)) x :=
        hasDerivWithinAt_neg x _
      have hc : HasDerivWithinAt (G k ∘ fun s : ℝ => -s) ((-1 : ℝ) • G (k + 1) (-x))
          (Set.Icc 0 (-t)) x := HasDerivWithinAt.scomp x hg hneg hmaps
      have h1 := hc.const_mul ((-1 : ℂ) ^ k)
      refine h1.congr_deriv ?_
      simp only [hG', pow_succ]
      simp [Function.comp_def]
    have hb' : ∀ k x, x ∈ Set.Icc 0 (-t) → ‖G' k x‖ ≤ M k := by
      intro k x hx
      simp only [hG', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact hb k (-x) (hmaps hx)
    have h := taylor_bound_nonneg_on n G' M (-t) (by linarith) hd' hb'
    have hpoly : taylorPoly (fun k => G' k 0) n (-t) = taylorPoly (fun k => G k 0) n t := by
      unfold taylorPoly
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hG', neg_zero]
      rw [neg_pow t k]
      push_cast
      rw [← mul_assoc]
      congr 1
      rw [mul_div_assoc, mul_comm ((-1 : ℂ) ^ k), mul_assoc, ← mul_pow]
      norm_num
    rw [hpoly] at h
    simpa [hG'] using h

/-! ## 2. Classical series along a flow on an interval (local form of the frozen E5 lemma) -/

/-- Chain rule along a curve solving `phi' = X_hr(phi)` within a set `S`. -/
theorem hasDerivWithinAt_comp_flow (g : H → ℂ) (hr : H → ℝ) {phi : ℝ → H} {s : ℝ} {S : Set ℝ}
    (hphi : HasDerivWithinAt phi (hamField hr (phi s)) S s) (hg : DifferentiableAt ℝ g (phi s)) :
    HasDerivWithinAt (fun τ => g (phi τ)) (pbC g (fun v => (hr v : ℂ)) (phi s)) S s := by
  rw [QuantumNLS.Local014ClassicalSeries.pbC_ofReal g hr hg]
  exact hg.hasFDerivAt.comp_hasDerivWithinAt s hphi

/-- **Classical series on an interval** (local form of `classical_hasSum`): if the curve solves the
flow within the interval `I ∋ 0`, `t ∈ I` and `eK|t| < 1`, then the series along the flow sums to
`g_0(phi t)`. -/
theorem classical_hasSum_on (hr : H → ℝ) (g : ℕ → H → ℂ) {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    {I : Set ℝ} (hI : I.OrdConnected) (hI0 : (0 : ℝ) ∈ I) {phi : ℝ → H}
    (hphi : ∀ s ∈ I, HasDerivWithinAt phi (hamField hr (phi s)) I s)
    (hn : ∀ s ∈ I, ‖phi s‖ = 1)
    (hdiff : ∀ k (u : H), ‖u‖ = 1 → DifferentiableAt ℝ (g k) u)
    (hsucc : ∀ k (u : H), ‖u‖ = 1 → g (k + 1) u = pbC (g k) (fun v => (hr v : ℂ)) u)
    (hbd : ∀ k (u : H), ‖u‖ = 1 → ‖g k u‖ ≤ (K * k) ^ k * C) {t : ℝ} (htI : t ∈ I)
    (ht : Real.exp 1 * K * |t| < 1) :
    HasSum (fun k : ℕ => (((t ^ k / (k ! : ℝ)) : ℝ) : ℂ) * g k (phi 0)) (g 0 (phi t)) := by
  have hsub : Set.uIcc 0 t ⊆ I := hI.uIcc_subset hI0 htI
  set G : ℕ → ℝ → ℂ := fun k s => g k (phi s) with hG
  have hd : ∀ k s, s ∈ Set.uIcc 0 t → HasDerivWithinAt (G k) (G (k + 1) s) (Set.uIcc 0 t) s := by
    intro k s hs
    have h := hasDerivWithinAt_comp_flow (g k) hr (hphi s (hsub hs))
      (hdiff k (phi s) (hn s (hsub hs)))
    rw [← hsucc k (phi s) (hn s (hsub hs))] at h
    exact h.mono hsub
  set r : ℝ := Real.exp 1 * K * |t| with hr_def
  have hr0 : 0 ≤ r := by positivity
  -- the remainder bound
  have hrem : ∀ n : ℕ, ‖G 0 t - taylorPoly (fun k => G k 0) n t‖ ≤ r ^ n * C := by
    intro n
    refine (taylor_bound_on n G (fun k => (K * k) ^ k * C) t hd
      (fun k s hs => hbd k (phi s) (hn s (hsub hs)))).trans ?_
    have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hkey : (n : ℝ) ^ n / (n ! : ℝ) ≤ Real.exp 1 ^ n :=
      QuantumNLS.Local014Heisenberg.pow_div_factorial_le n
    calc (K * n) ^ n * C * |t| ^ n / (n ! : ℝ)
        = (K * |t|) ^ n * ((n : ℝ) ^ n / (n ! : ℝ)) * C := by
          rw [mul_pow, mul_pow]; field_simp
      _ ≤ (K * |t|) ^ n * Real.exp 1 ^ n * C := by gcongr
      _ = r ^ n * C := by rw [hr_def, mul_assoc (Real.exp 1), mul_pow (Real.exp 1)]; ring
  have htend : Tendsto (fun n : ℕ => taylorPoly (fun k => G k 0) n t) atTop (𝓝 (G 0 t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => r ^ n * C) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 ht).mul_const C
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    rw [norm_sub_rev]
    exact hrem n
  -- absolute summability of the series
  have hterm : ∀ k : ℕ, ‖(((t ^ k / (k ! : ℝ)) : ℝ) : ℂ) * g k (phi 0)‖ ≤ r ^ k * C := by
    intro k
    have hfac : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hkey : (k : ℝ) ^ k / (k ! : ℝ) ≤ Real.exp 1 ^ k :=
      QuantumNLS.Local014Heisenberg.pow_div_factorial_le k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos hfac]
    calc |t| ^ k / (k ! : ℝ) * ‖g k (phi 0)‖ ≤ |t| ^ k / (k ! : ℝ) * ((K * k) ^ k * C) :=
          mul_le_mul_of_nonneg_left (hbd k (phi 0) (hn 0 hI0)) (by positivity)
      _ = (K * |t|) ^ k * ((k : ℝ) ^ k / (k ! : ℝ)) * C := by
          rw [mul_pow, mul_pow]; field_simp
      _ ≤ (K * |t|) ^ k * Real.exp 1 ^ k * C := by gcongr
      _ = r ^ k * C := by rw [hr_def, mul_assoc (Real.exp 1), mul_pow (Real.exp 1)]; ring
  have hsum : Summable fun k : ℕ => ‖(((t ^ k / (k ! : ℝ)) : ℝ) : ℂ) * g k (phi 0)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
      ((summable_geometric_of_lt_one hr0 ht).mul_right C)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
  exact htend

/-! ## 3. Short-time limit on an interval (local form of the frozen E6 `short_time`) -/

/-- Shift of a within-derivative: `s ↦ phi (t₀ + s)` has the within-derivative on the preimage of `I`. -/
theorem hasDerivWithinAt_shift {phi : ℝ → H} {f' : H} {I : Set ℝ} {t₀ s : ℝ}
    (h : HasDerivWithinAt phi f' I (t₀ + s)) :
    HasDerivWithinAt (fun x => phi (t₀ + x)) f' ((fun x : ℝ => t₀ + x) ⁻¹' I) s := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 s := hasDerivAt_id' s
  have hT : HasDerivWithinAt (fun x : ℝ => t₀ + x) 1 ((fun x : ℝ => t₀ + x) ⁻¹' I) s :=
    (hid.const_add t₀).hasDerivWithinAt
  have hc : HasDerivWithinAt (phi ∘ fun x : ℝ => t₀ + x) ((1 : ℝ) • f')
      ((fun x : ℝ => t₀ + x) ⁻¹' I) s := HasDerivWithinAt.scomp s h hT (fun y hy => hy)
  rw [one_smul] at hc
  exact hc

/-- **Short-time Egorov limit on an interval** (local form of `short_time`): for `eK|t| < 1`, `t ∈ I`,
normal states condensed at `phi 0`, and a flow on `I`, the expectation converges to the classical
value at `phi t`. -/
theorem short_time_on {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hH : ConvergesOnRadius 8 Hk Hlim)
    (hsa : ∀ N, IsSelfAdjoint (REP (Hk N))) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ N, RB 8 (saList Hk N) ≤ K) (F : H → ℝ)
    (hFd : ∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ F u)
    (hF : ∀ u : H, ‖u‖ = 1 → (F u : ℂ) = symbol Hlim u) {I : Set ℝ} (hI : I.OrdConnected)
    (hI0 : (0 : ℝ) ∈ I) {phi : ℝ → H}
    (hphi : ∀ s ∈ I, HasDerivWithinAt phi (hamField F (phi s)) I s)
    (hn : ∀ s ∈ I, ‖phi s‖ = 1)
    (ρ : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (hρ : ∀ N, IsNormalState (ρ N))
    (h1 : Tendsto (fun N => qexp (ρ N) 1 (P (phi 0) 1)) atTop (𝓝 1)) {t : ℝ} (htI : t ∈ I)
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
  have hterm : ∀ k, Tendsto (fun N => c N k) atTop
      (𝓝 (((t : ℂ) ^ k / (k ! : ℂ)) * g k (phi 0))) := by
    intro k
    have hR : (1 : ℝ) < 2 + 2 / ((k : ℝ) + 1) := by have := radius_pos k; linarith
    exact (tendsto_tr_represented hR (iter_converges hS hX k) (hn 0 hI0) ρ hρ h1).const_mul _
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
  -- the classical series (E5), with the chain of brackets with `F`, on `I`
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
  have hCq0' : 0 ≤ Cq := hCq0
  have hcl := classical_hasSum_on F g hK0 hCq0' hI hI0 hphi hn hdiff hsucc hbd htI ht
  have heq : ∑' k, ((t : ℂ) ^ k / (k ! : ℂ)) * g k (phi 0) = kernelProductSymbol B (phi t) := by
    have h0 : g 0 (phi t) = kernelProductSymbol B (phi t) := symbol_testLim B (phi t)
    rw [← h0, ← hcl.tsum_eq]
    congr 1
    funext k
    push_cast
    ring
  rw [← heq]
  exact hlim.congr' (hid.mono fun N h => h.symm)

/-! ## 4. Restarts on an interval -/

/-- Restart splitting with the intermediate time in the segment `[[0, t]]`. -/
theorem restart_split_mem {τ t : ℝ} (hτ : 0 < τ) (n : ℕ) (ht : |t| ≤ (n + 1 : ℕ) * τ) :
    ∃ t₀ s : ℝ, t = t₀ + s ∧ |s| ≤ τ ∧ |t₀| ≤ n * τ ∧ t₀ ∈ Set.uIcc 0 t := by
  by_cases h1 : |t| ≤ τ
  · exact ⟨0, t, by ring, h1, by rw [abs_zero]; positivity, Set.left_mem_uIcc⟩
  · push_cast at ht
    rcases le_or_gt 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at ht h1
      refine ⟨t - τ, τ, by ring, by rw [abs_of_pos hτ], ?_, ?_⟩
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [Set.mem_uIcc]
        left
        constructor <;> linarith
    · rw [abs_of_neg h0] at ht h1
      refine ⟨t + τ, -τ, by ring, by rw [abs_neg, abs_of_pos hτ], ?_, ?_⟩
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [Set.mem_uIcc]
        right
        constructor <;> linarith

/-! ## 5. The main theorem on an interval -/

/-- **LOCAL-014 `reset:analytic-egorov` for a flow on an interval** (`quantum_periods.tex:186-203`).

Hypotheses as in `Local014Main.local014_analytic_egorov`, except for the flow: `I` is an interval
(`Set.OrdConnected`) containing `0`, `phi` solves the Hamiltonian field of `F` within `I`
(`HasDerivWithinAt phi (hamField F (phi s)) I s` for `s ∈ I`; at interior points this is `HasDerivAt`),
`phi 0 = v` with `‖v‖ = 1`, and `‖phi s‖ = 1` for `s ∈ I`.

Conclusions: (i) as in the frozen theorem (`h` is real on the unit sphere and `Re h` is admissible);
(ii) for every `t ∈ I`, every `q` and bounded `B`, the expectation of `Q_{N,q}(B)` in the evolved
state converges to `⟨(phi t)^{⊗q}, B (phi t)^{⊗q}⟩` (zero for `N < q`); (iii) for every `t ∈ I`,
the evolved one-body matrices converge in trace norm to `|phi t⟩⟨phi t|`. -/
theorem local014_analytic_egorov_interval {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (HN : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (hsa : ∀ N, IsSelfAdjoint (HN N))
    (hexp : ∀ N, RadiusBound.IsExpansion (HN N) (Hk N)) (hH : ConvergesOnRadius 8 Hk Hlim)
    (F : H → ℝ) (hFd : ∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ F u)
    (hF : ∀ u : H, ‖u‖ = 1 → (F u : ℂ) = symbol Hlim u)
    {v : H} (hv : ‖v‖ = 1) {I : Set ℝ} (hI : I.OrdConnected) (hI0 : (0 : ℝ) ∈ I)
    {phi : ℝ → H} (hphi0 : phi 0 = v)
    (hphi : ∀ s ∈ I, HasDerivWithinAt phi (hamField F (phi s)) I s)
    (hn : ∀ s ∈ I, ‖phi s‖ = 1)
    (ρ : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (hρ : ∀ N, IsNormalState (ρ N))
    (hcond : Tendsto (fun N => traceNorm (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v))
      atTop (𝓝 0)) :
    ((∀ u : H, ‖u‖ = 1 → (symbol Hlim u).im = 0) ∧
      (∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ (hReal Hlim) u ∧
        ((hReal Hlim u : ℝ) : ℂ) = symbol Hlim u)) ∧
    (∀ t ∈ I, ∀ (q : ℕ) (B : BoundedSymmetricKernel H q),
      Tendsto (fun N => if h : q ≤ N then
          tr (ρ N * (opExp ((Complex.I * (t : ℂ) * (N : ℂ)) • HN N) * RadiusBound.Q N q h B *
            opExp (-((Complex.I * (t : ℂ) * (N : ℂ)) • HN N)))) else 0) atTop
        (𝓝 (kernelProductSymbol B (phi t)))) ∧
    (∀ t ∈ I, Tendsto (fun N => traceNorm (oneBody N (evolve N (HN N) (ρ N) t) -
        InnerProductSpace.rankOne ℂ (phi t) (phi t))) atTop (𝓝 0)) := by
  have hrepN : ∀ N, REP (Hk N) = HN N := fun N => (hexp N).symm
  have hsaR : ∀ N, IsSelfAdjoint (REP (Hk N)) := fun N => by rw [hrepN]; exact hsa N
  -- realness and admissibility of `Re h`
  have hreal : ∀ u : H, ‖u‖ = 1 → (symbol Hlim u).im = 0 :=
    fun u hu => symbol_im_eq_zero (by norm_num) hH hsaR u hu
  have hhR : ∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ (hReal Hlim) u := by
    intro u hu
    exact Complex.reCLM.differentiableAt.comp u
      (differentiableAt_symbol (summable_of_converges (by norm_num) hH) (by rw [hu]; norm_num))
  have hadm : ∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ (hReal Hlim) u ∧
      ((hReal Hlim u : ℝ) : ℂ) = symbol Hlim u := by
    intro u hu
    refine ⟨hhR u hu, Complex.ext (by simp [hReal]) (by simp [hReal, hreal u hu])⟩
  -- the constant `K` and the short time `τ`
  obtain ⟨C, hC⟩ := (saList_converges (R := 8) (by norm_num) hH).1
  set K := max C 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ N, RB 8 (saList Hk N) ≤ K := fun N => (hC N).trans (le_max_left _ _)
  set τ := 1 / (Real.exp 1 * K + 1) with hτdef
  have hEK : 0 ≤ Real.exp 1 * K := mul_nonneg (Real.exp_pos 1).le hK0
  have hτ0 : 0 < τ := by positivity
  have hτ : ∀ s : ℝ, |s| ≤ τ → Real.exp 1 * K * |s| < 1 := by
    intro s hs
    calc Real.exp 1 * K * |s| ≤ Real.exp 1 * K * τ := mul_le_mul_of_nonneg_left hs hEK
      _ < 1 := by
        rw [hτdef, mul_one_div, div_lt_one (by linarith)]
        linarith
  -- one-body condensation as an expectation
  have hqexp_one : ∀ {N : ℕ} (hN : 1 ≤ N) (σ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
      (hσ : IsNormalState σ) (w : H),
      ⟪w, oneBody N σ w⟫_ℂ = qexp σ 1 (P w 1) := by
    intro N hN σ hσ w
    rw [inner_oneBody_eq hN hσ.1 hσ.2.1, toSym1_rankOne, qexp, dif_pos hN]
  have h1 : Tendsto (fun N => qexp (ρ N) 1 (P (phi 0) 1)) atTop (𝓝 1) := by
    rw [hphi0]
    have hreal' : Tendsto (fun N => (traceNorm (oneBody N (ρ N) -
        InnerProductSpace.rankOne ℂ v v)).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcond
      rw [ENNReal.toReal_zero] at this
      exact this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hreal'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hγ := oneBody_isNormalState hN (hρ N)
    rw [← hqexp_one hN (ρ N) (hρ N) v]
    have hvv : ⟪v, InnerProductSpace.rankOne ℂ v v v⟫_ℂ = 1 := by
      rw [InnerProductSpace.rankOne_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
      simp
    have hdiff : ⟪v, oneBody N (ρ N) v⟫_ℂ - 1 =
        ⟪v, (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v) v⟫_ℂ := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_right, hvv]
    rw [hdiff]
    have hD : IsTraceClass (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v) :=
      finite_sub hγ.2.1 (lt_of_le_of_lt (Fidelity.traceNorm_rankOne_le _ _) ENNReal.ofReal_lt_top)
    calc ‖⟪v, (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v) v⟫_ℂ‖
        ≤ ‖oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v‖ := by
          refine (norm_inner_le_norm _ _).trans ?_
          rw [hv, one_mul]
          refine ((oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v).le_opNorm v).trans ?_
          rw [hv, mul_one]
      _ ≤ (traceNorm (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v)).toReal := by
          have := norm_le_traceNorm (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v)
          rw [← ENNReal.ofReal_toReal hD.ne] at this
          exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp this
  -- the restart induction, with every time in `I`
  have hmain : ∀ n : ℕ, ∀ t ∈ I, |t| ≤ n * τ → ∀ (q : ℕ) (B : BoundedSymmetricKernel H q),
      Tendsto (fun N => tr (ρ N * heis N (REP (Hk N)) (REP (testList q B N)) t)) atTop
        (𝓝 (kernelProductSymbol B (phi t))) := by
    intro n
    induction n with
    | zero =>
      intro t htI ht q B
      have ht0 : t = 0 := by simpa using ht
      subst ht0
      exact short_time_on hH hsaR hK0 hK F hFd hF hI hI0 hphi hn ρ hρ h1 htI (by simp) q B
    | succ n ih =>
      intro t htI ht q B
      obtain ⟨t₀, s, hts, hs, ht₀, ht₀mem⟩ := restart_split_mem hτ0 n ht
      have ht₀I : t₀ ∈ I := hI.uIcc_subset hI0 htI ht₀mem
      subst hts
      set ρ' : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
        fun N => evolve N (REP (Hk N)) (ρ N) t₀ with hρ'def
      have hρ' : ∀ N, IsNormalState (ρ' N) := fun N => evolve_isNormalState (hsaR N) (hρ N) t₀
      have hshift : ∀ (N : ℕ) (X : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (s' : ℝ),
          tr (ρ' N * heis N (REP (Hk N)) X s') = tr (ρ N * heis N (REP (Hk N)) X (t₀ + s')) :=
        fun N X s' => tr_evolve_heis (hρ N).2.1 X t₀ s'
      set J : Set ℝ := (fun x : ℝ => t₀ + x) ⁻¹' I with hJ
      have hJord : J.OrdConnected := by
        refine ⟨fun a ha b hb c hc => ?_⟩
        have ha' : t₀ + a ∈ I := ha
        have hb' : t₀ + b ∈ I := hb
        exact hI.out ha' hb' (show t₀ + c ∈ Set.Icc (t₀ + a) (t₀ + b) from
          ⟨by linarith [hc.1], by linarith [hc.2]⟩)
      have hJ0 : (0 : ℝ) ∈ J := by
        show t₀ + 0 ∈ I
        rw [add_zero]
        exact ht₀I
      have hsJ : s ∈ J := htI
      set ψ : ℝ → H := fun s' => phi (t₀ + s') with hψ
      have hψd : ∀ s' ∈ J, HasDerivWithinAt ψ (hamField F (ψ s')) J s' := fun s' hs' =>
        hasDerivWithinAt_shift (hphi (t₀ + s') hs')
      have hψn : ∀ s' ∈ J, ‖ψ s'‖ = 1 := fun s' hs' => hn (t₀ + s') hs'
      have h1' : Tendsto (fun N => qexp (ρ' N) 1 (P (ψ 0) 1)) atTop (𝓝 1) := by
        have hψ0 : ψ 0 = phi t₀ := by simp [hψ]
        rw [hψ0]
        have hIH := ih t₀ ht₀I ht₀ 1 (P (phi t₀) 1)
        rw [kps_P_self (hn t₀ ht₀I)] at hIH
        refine hIH.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hT := tr_evolve_heis (A := REP (Hk N)) (hρ N).2.1
          (REP (testList 1 (P (phi t₀) 1) N)) t₀ 0
        rw [heis_zero, add_zero] at hT
        rw [qexp, dif_pos hN, ← represented_testList hN]
        exact hT.symm
      have hst := short_time_on hH hsaR hK0 hK F hFd hF hJord hJ0 hψd hψn ρ' hρ' h1' hsJ
        (hτ s hs) q B
      have hψs : ψ s = phi (t₀ + s) := rfl
      rw [hψs] at hst
      exact hst.congr fun N => hshift N _ s
  have hall : ∀ t ∈ I, ∀ (q : ℕ) (B : BoundedSymmetricKernel H q),
      Tendsto (fun N => tr (ρ N * heis N (REP (Hk N)) (REP (testList q B N)) t)) atTop
        (𝓝 (kernelProductSymbol B (phi t))) := by
    intro t htI q B
    obtain ⟨n, hn'⟩ := exists_nat_ge (|t| / τ)
    exact hmain n t htI (by rwa [div_le_iff₀ hτ0] at hn') q B
  refine ⟨⟨hreal, hadm⟩, ?_, ?_⟩
  · intro t htI q B
    refine (hall t htI q B).congr' ?_
    filter_upwards [eventually_ge_atTop q] with N hqN
    rw [dif_pos hqN, represented_testList hqN, heis, hrepN]
  · intro t htI
    have hlimP := hall t htI 1 (P (phi t) 1)
    rw [kps_P_self (hn t htI)] at hlimP
    have hre : Tendsto (fun N => 1 - (tr (ρ N * heis N (REP (Hk N))
        (REP (testList 1 (P (phi t) 1) N)) t)).re) atTop (𝓝 0) := by
      have := ((Complex.continuous_re.tendsto (1 : ℂ)).comp hlimP).const_sub 1
      simpa using this
    have hup : Tendsto (fun N => ENNReal.ofReal (2 * √(1 - (tr (ρ N * heis N (REP (Hk N))
        (REP (testList 1 (P (phi t) 1) N)) t)).re))) atTop (𝓝 0) := by
      have hc : Continuous fun x : ℝ => 2 * √x := by fun_prop
      have := ENNReal.tendsto_ofReal ((hc.tendsto 0).comp hre)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hσ := evolve_isNormalState (hsa N) (hρ N) t
    have hγ := oneBody_isNormalState hN hσ
    have hkey : ⟪phi t, oneBody N (evolve N (HN N) (ρ N) t) (phi t)⟫_ℂ =
        tr (ρ N * heis N (REP (Hk N)) (REP (testList 1 (P (phi t) 1) N)) t) := by
      have hT := tr_evolve_heis (A := REP (Hk N)) (hρ N).2.1
        (REP (testList 1 (P (phi t) 1) N)) t 0
      rw [heis_zero, add_zero] at hT
      rw [hqexp_one hN _ hσ, qexp, dif_pos hN, ← represented_testList hN, ← hrepN, hT]
    refine (traceNorm_sub_rankOne_le hγ (phi t) (hn t htI)).trans (le_of_eq ?_)
    rw [RCLike.re_to_complex, hkey]

end QuantumNLS.Local014Interval

#print axioms QuantumNLS.Local014Interval.local014_analytic_egorov_interval
