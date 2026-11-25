import QuantumNLS.Local014Heisenberg

/-!
# LOCAL-014 stage E2: iterated commutators converge, with iterated Poisson brackets as symbols

Source: `source-text/chapters/local/quantum_periods.tex:220-222` (proof of LOCAL-014): "The
principal-calculus lemma, iterated with strictly decreasing radii, shows that the symbol of each
iterated commutator is the corresponding iterated Poisson bracket with `h`."

Realization (LOCAL-013, frozen, read-only: `Local013CommutatorLimit.commutator_converges`,
`commLim`, `Local013CommutatorSeries.symbol_commLim`):
* `iterLim Hlim Blim k`: the `k`-fold iterated limiting commutator kernels;
* `iter_converges`: if `H` converges on radius `8` and `X` on radius `4`, the iterated lists
  `δ_N^k X_N` (E1 `dysonList`) converge on the strictly decreasing radii `2 + 2/(k+1)`;
* `symbol_iterLim_succ`, `symbol_iterLim_eq`: on `‖v‖² < 2` (an open set containing the unit
  sphere) the symbol of `δ^k X` is `ad_h^k b`, `ad_h g = {g, h}` (DEF-015 `pbC`), `h` the symbol of
  `H` and `b` the symbol of `X`;
* `testLim`, `test_converges`, `symbol_testLim`: the fixed test `Q_{N,q}(B)` converges (every
  radius) with symbol `b(v) = ⟨v^{⊗q}, B v^{⊗q}⟩`;
* `norm_symbol_iterLim_le`: on the closed unit ball, `|ad_h^k b| ≤ (Kk)^k 4^q ‖B‖` (Dyson bound of
  E1 passed to the limiting kernels).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators Nat
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.KernelConvergence
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly QuantumNLS.SymplecticBracket
  QuantumNLS.Local013CommutatorLimit QuantumNLS.Local013CommutatorSeries QuantumNLS.Local014Dyson

namespace QuantumNLS.Local014IteratedSymbol

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "RB" => QuantumNLS.RadiusBound.radiusBound

/-- Iterated limiting commutator kernels. -/
def iterLim (Hlim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) :
    ℕ → ∀ p : ℕ, BoundedSymmetricKernel H p
  | 0 => Blim
  | k + 1 => commLim Hlim (iterLim Hlim Blim k)

/-- `ad_h g = {g, h}` (DEF-015 complex bracket). -/
def adh (h : H → ℂ) (g : H → ℂ) : H → ℂ := pbC g h

theorem converges_reduce {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    {A : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hA : ConvergesOnRadius R A Alim) :
    ConvergesOnRadius r A Alim := by
  obtain ⟨⟨C, hC⟩, hl⟩ := hA
  exact ⟨⟨C, fun N => (QuantumNLS.RadiusBound.radiusBound_mono hr hrR (A N)).trans (hC N)⟩, hl⟩

theorem radius_pos (k : ℕ) : (2 : ℝ) < 2 + 2 / ((k : ℝ) + 1) := by
  have : (0 : ℝ) < 2 / ((k : ℝ) + 1) := by positivity
  linarith

theorem radius_le_four (k : ℕ) : 2 + 2 / ((k : ℝ) + 1) ≤ 4 := by
  have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := (Nat.cast_nonneg (α := ℝ) k); linarith
  have : 2 / ((k : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

theorem radius_anti (k : ℕ) :
    2 + 2 / (((k + 1 : ℕ) : ℝ) + 1) < 2 + 2 / ((k : ℝ) + 1) := by
  push_cast
  have h0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have : 2 / ((k : ℝ) + 1 + 1) < 2 / ((k : ℝ) + 1) :=
    div_lt_div_of_pos_left (by norm_num) h0 (by linarith)
  linarith

/-- **Iterated commutators converge** on the decreasing radii `2 + 2/(k+1)`. -/
theorem iter_converges {Hk X : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hH : ConvergesOnRadius 8 Hk Hlim) (hX : ConvergesOnRadius 4 X Blim) (k : ℕ) :
    ConvergesOnRadius (2 + 2 / ((k : ℝ) + 1)) (dysonList Hk X k) (iterLim Hlim Blim k) := by
  induction k with
  | zero =>
    have : (2 : ℝ) + 2 / (((0 : ℕ) : ℝ) + 1) = 4 := by norm_num
    rw [this]; exact hX
  | succ k ih =>
    have hR := radius_le_four k
    have hrR := radius_anti k
    have hr1 : (1 : ℝ) ≤ 2 + 2 / (((k + 1 : ℕ) : ℝ) + 1) := (radius_pos (k + 1)).le.trans' (by norm_num)
    have hH' := converges_reduce (by linarith [radius_pos k]) (hR.trans (by norm_num)) hH
    exact (commutator_converges hr1 hrR hH' ih).1

/-- Summability of the radius series of a convergent family. -/
theorem summable_of_converges {R : ℝ} (hR : 0 ≤ R)
    {A : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hA : ConvergesOnRadius R A Alim) :
    Summable (fun p : ℕ => R ^ p * ‖Alim p‖) := by
  obtain ⟨⟨C, hC⟩, hl⟩ := hA
  exact radius_summable hR hC hl

/-- The symbol of `δ^{k+1} X` is `{a_k, h}` on `‖v‖² < 2`. -/
theorem symbol_iterLim_succ {Hk X : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hH : ConvergesOnRadius 8 Hk Hlim) (hX : ConvergesOnRadius 4 X Blim) (k : ℕ) (v : H)
    (hv : ‖v‖ ^ 2 < 2) :
    symbol (iterLim Hlim Blim (k + 1)) v =
      pbC (symbol (iterLim Hlim Blim k)) (symbol Hlim) v := by
  have hR := radius_pos k
  have hR4 := radius_le_four k
  have hHs := summable_of_converges (by linarith)
    (converges_reduce (by linarith) (hR4.trans (by norm_num)) hH)
  have hXs := summable_of_converges (by linarith) (iter_converges hH hX k)
  exact symbol_commLim (by linarith) hHs hXs v (by linarith)

/-- Brackets only see a neighbourhood: functions equal near `u` have equal brackets at `u`. -/
theorem pbC_congr_left {F G : H → ℂ} (h : H → ℂ) {u : H} (hFG : F =ᶠ[𝓝 u] G) :
    pbC F h u = pbC G h u := by
  have hre : (fun v => (F v).re) =ᶠ[𝓝 u] (fun v => (G v).re) := hFG.mono fun v hv => by dsimp only; rw [hv]
  have him : (fun v => (F v).im) =ᶠ[𝓝 u] (fun v => (G v).im) := hFG.mono fun v hv => by dsimp only; rw [hv]
  unfold pbC pbR
  rw [hre.fderiv_eq, him.fderiv_eq]

theorem isOpen_ball2 : IsOpen {v : H | ‖v‖ ^ 2 < 2} :=
  isOpen_lt (continuous_norm.pow 2) continuous_const

/-- **Iterated symbols**: on `‖v‖² < 2`, `symbol (δ^k X) = ad_h^k b`. -/
theorem symbol_iterLim_eq {Hk X : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hH : ConvergesOnRadius 8 Hk Hlim) (hX : ConvergesOnRadius 4 X Blim) (k : ℕ) :
    ∀ v : H, ‖v‖ ^ 2 < 2 →
      symbol (iterLim Hlim Blim k) v = (adh (symbol Hlim))^[k] (symbol Blim) v := by
  induction k with
  | zero => intro v _; rfl
  | succ k ih =>
    intro v hv
    rw [symbol_iterLim_succ hH hX k v hv, Function.iterate_succ_apply', adh]
    apply pbC_congr_left
    filter_upwards [isOpen_ball2.mem_nhds hv] with w hw
    exact ih w hw

/-! ## The fixed test -/

/-- Limiting kernels of the test: `B` in degree `q`. -/
def testLim (q : ℕ) (B : BoundedSymmetricKernel H q) (p : ℕ) : BoundedSymmetricKernel H p :=
  if h : p = q then castSymSectorOperator h.symm B else 0

theorem coeffAt_testList {q : ℕ} (B : BoundedSymmetricKernel H q) {N p : ℕ} (hp : p ≤ N) :
    coeffAt (testList q B) N p = testLim q B p := by
  unfold coeffAt
  rw [dif_pos hp]
  rfl

theorem test_converges {R : ℝ} (hR : 0 ≤ R) {q : ℕ} (B : BoundedSymmetricKernel H q) :
    ConvergesOnRadius R (testList q B) (testLim q B) := by
  refine ⟨⟨R ^ q * ‖B‖, fun N => radiusBound_testList_le N hR B⟩, fun p => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop p] with N hN
  rw [coeffAt_testList B hN, sub_self]
  exact (norm_zero (E := SymSector ℂ H p →L[ℂ] SymSector ℂ H p)).symm

theorem kps_zero {p : ℕ} (v : H) :
    kernelProductSymbol (0 : BoundedSymmetricKernel H p) v = 0 := by
  simp [kernelProductSymbol]

/-- The test symbol `b(v) = ⟨v^{⊗q}, B v^{⊗q}⟩`. -/
theorem symbol_testLim {q : ℕ} (B : BoundedSymmetricKernel H q) (v : H) :
    symbol (testLim q B) v = kernelProductSymbol B v := by
  unfold symbol
  rw [tsum_eq_single q]
  · simp [testLim, castSymSectorOperator]
  · intro p hp
    simp only [testLim, dif_neg hp]
    exact kps_zero v

/-- **Bound for the iterated symbols** on the closed unit ball: `|ad_h^k b(u)| ≤ (Kk)^k 4^q ‖B‖`. -/
theorem norm_symbol_iterLim_le {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p} {K : ℝ}
    (hH : ConvergesOnRadius 8 Hk Hlim) (hK : ∀ N, RB 8 (Hk N) ≤ K) {q : ℕ}
    (B : BoundedSymmetricKernel H q) (k : ℕ) (u : H) (hu : ‖u‖ ≤ 1) :
    ‖symbol (iterLim Hlim (testLim q B) k) u‖ ≤ (K * k) ^ k * (4 ^ q * ‖B‖) := by
  have hconv := converges_reduce (r := 2) (by norm_num) (radius_pos k).le
    (iter_converges hH (test_converges (by norm_num) B) k)
  obtain ⟨_, hl⟩ := hconv
  set L := iterLim Hlim (testLim q B) k
  have hC : ∀ N, RB 2 (dysonList Hk (testList q B) k N) ≤ (K * k) ^ k * (4 ^ q * ‖B‖) :=
    fun N => dyson_bound_test hK B k N
  have hsum2 : Summable (fun p : ℕ => (2 : ℝ) ^ p * ‖L p‖) := radius_summable (by norm_num) hC hl
  have hterm : ∀ p : ℕ, ‖kernelProductSymbol (L p) u‖ ≤ (2 : ℝ) ^ p * ‖L p‖ := by
    intro p
    refine (norm_kernelProductSymbol_le (L p) u).trans ?_
    have h1 : ‖u‖ ^ (2 * p) ≤ 1 := pow_le_one₀ (norm_nonneg u) hu
    have h2 : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    nlinarith [norm_nonneg (L p)]
  have hsumk : Summable (fun p : ℕ => ‖kernelProductSymbol (L p) u‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hterm hsum2
  calc ‖symbol L u‖ ≤ ∑' p : ℕ, ‖kernelProductSymbol (L p) u‖ := norm_tsum_le_tsum_norm hsumk
    _ ≤ ∑' p : ℕ, (2 : ℝ) ^ p * ‖L p‖ := hsumk.tsum_le_tsum hterm hsum2
    _ ≤ (K * k) ^ k * (4 ^ q * ‖B‖) :=
        hsum2.tsum_le_of_sum_range_le fun n => partial_sums_le (by norm_num) hC hl n

end QuantumNLS.Local014IteratedSymbol

/-! Axiom audit. -/
#print axioms QuantumNLS.Local014IteratedSymbol.iter_converges
#print axioms QuantumNLS.Local014IteratedSymbol.symbol_iterLim_succ
#print axioms QuantumNLS.Local014IteratedSymbol.pbC_congr_left
#print axioms QuantumNLS.Local014IteratedSymbol.symbol_iterLim_eq
#print axioms QuantumNLS.Local014IteratedSymbol.test_converges
#print axioms QuantumNLS.Local014IteratedSymbol.symbol_testLim
#print axioms QuantumNLS.Local014IteratedSymbol.norm_symbol_iterLim_le
