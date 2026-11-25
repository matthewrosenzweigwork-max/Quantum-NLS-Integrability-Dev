import NlsGge.GK38.GradFundamentalSpectralODE
import NlsGge.GK38.GradFundamentalSpectralGauge
import NlsGge.GK38.GradFundamentalStar
import NlsGge.GK38.PairAnalytic
import NlsGge.Atomic.G1.G1104ODE
import NlsGge.Atomic.G1.G1104Ker

/-!
# G1-104 supporting module G1104Jor (M4: Jordan chains versus Taylor-coefficient chains)

Target file `NlsGge/Atomic/G1/G1104Jor.lean`, namespace `NlsGge.Atomic.G1104Jor`.
Lands after `G1104Host`, `G1104Sup`, `G1104ODE`, `G1104Ker`.

Fix `φ : PotPair`, `bc`, `z0`.  Write `M(t,z) = fundPair φ z t`.

* Taylor coefficients (no calculus of iterated derivatives): `T = (1 - 𝒱_{z0})⁻¹ 𝒮_{z0}` on
  `C([0,1], M₂)`, `tayCoeff φ z0 j = T^j M(·,z0)`.  `hasSum_tayCoeff`/`hasSum_tayEntry`:
  `M(·, z0 + w) = ∑ w^j M_j` for `‖w‖ < r`.  `tayM_ac`, `tayM_ae`, `tayM_zero_time`:
  `M_j` is AC, `M_j' = Q_{z0} M_j + R̂ M_{j-1}` a.e. (`R̂ = ∂_z Q = spectralCoeff38`),
  `M_j(0) = δ_{j0} I`.
* `tayD bc φ z0 a`: Taylor coefficients of `D(z) = B0 + B1 M(1,z)` (`hasSum_tayD`).
* `chainFun φ z0 c k = ∑_{i ≤ k} M_i c_{k-i}`; `tayKer bc φ z0 N` is `K_N`: the
  `c : Fin N → ℂ²` with `∑_{a ≤ m} D_a c_{m-a} = 0` for `m < N`.
* `IsAcChain`, `tay_chain_correspondence` (AC level; hypothesis `PairUniq`, discharged by
  `pairUniq` from `G1104Ker.pairSolution_eq_Mext`).
* `IsOpChain A z N W` (ascending Jordan chain `(A - z) W_k = W_{k-1}`), `opChain_iff`
  (operator chain iff AC chain with `bcRelation`), `opChain_iff_tayKer` (M4, set level),
  `tayChainEquiv : K_N ≃ₗ opChainSpace` (M4, linear equivalence), `finrank_tayKer_eq`,
  `rootVector_iff_opChain` (relation to the head's descending `rootVector`).

Component convention: `Bool.true` is index `0` of `Fin 2` (`pairIdx`).
No hypothesis is added to any statement; no Jordan chain is assumed finite or of bounded length.
-/

set_option autoImplicit false

open NlsGge.Atomic.Interval
open NlsGge.Pilot NlsGge.GK38 MeasureTheory Set Filter Topology
open NlsGge.GKDefinitionDesign NlsGge.Atomic.G1104ODE NlsGge.Atomic.G1104Ker
open scoped ENNReal
open NlsGge.Schur NlsGge.Atomic.LIB026 NlsGge.Atomic.LIB033

namespace NlsGge.Atomic.G1104Jor
noncomputable section

/-! ### A.1  Forced Volterra equation `F = 𝒮 H + 𝒱 F` gives the forced ZS ODE -/

/-- The gauge integrand of the forced equation `F = 𝒮 H + 𝒱 F`. -/
def forcedGauge (φ : PotPair) (z : ℂ) (F H : PairCont38) (s : ℝ) : PairMat38 :=
  Matrix.of fun i j => spectralGaugeSource38 z H s i j +
    (freeE z (-s) * potCoeff38 φ s * ext38 F s) i j

theorem intervalIntegrable_forcedGauge (φ : PotPair) (z : ℂ) (F H : PairCont38) (i j : Fin 2) :
    IntervalIntegrable (fun s => forcedGauge φ z F H s i j) volume 0 1 :=
  (intervalIntegrable_spectralGaugeSource38 z H i j).add
    (intervalIntegrable_triple_entry φ ((continuous_freeE z).comp continuous_neg)
      (continuous_ext38 F) i j)

theorem forced_gauge (φ : PotPair) (z : ℂ) (F H : PairCont38)
    (hF : F = spectralForcingCLM38 z H + volterraP φ z F)
    (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    F t i j = freeE z t i i *
      ((0 : PairMat38) i j + ∫ s in (0 : ℝ)..(t : ℝ), forcedGauge φ z F H s i j) := by
  have heq := congrArg (fun F : PairCont38 => F t i j) hF
  simp only [ContinuousMap.add_apply, Pi.add_apply] at heq
  rw [heq, spectralForcingCLM38_apply, volterraP_apply, volterraFun_eq, freeE_mul_apply,
    Matrix.zero_apply, zero_add]
  simp only [forcedGauge, Matrix.of_apply, volterraKer]
  have hi1 := (intervalIntegrable_spectralGaugeSource38 z H i j).mono_set
    (uIcc_zero_subset t.2)
  have hi2 : IntervalIntegrable (fun s =>
      (freeE z (-s) * potCoeff38 φ s * ext38 F s) i j)
      volume 0 (t : ℝ) := by
    simpa only [Function.comp_def] using
      (intervalIntegrable_triple_entry φ ((continuous_freeE z).comp continuous_neg)
        (continuous_ext38 F) i j).mono_set (uIcc_zero_subset t.2)
  exact k1WeightedIntegralAdd38 _ _ _ _ hi1 hi2

theorem forced_ac (φ : PotPair) (z : ℂ) (F H : PairCont38)
    (hF : F = spectralForcingCLM38 z H + volterraP φ z F) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => ext38 F s i j) 0 1 :=
  ac_gaugePrimitive38 F z 0 (forcedGauge φ z F H)
    (intervalIntegrable_forcedGauge φ z F H) (forced_gauge φ z F H hF) i j

theorem forced_zero_time (φ : PotPair) (z : ℂ) (F H : PairCont38)
    (hF : F = spectralForcingCLM38 z H + volterraP φ z F) :
    F ⟨0, le_rfl, zero_le_one⟩ = 0 := by
  ext i j
  rw [forced_gauge φ z F H hF]
  simp

theorem forced_ae (φ : PotPair) (z : ℂ) (F H : PairCont38)
    (hF : F = spectralForcingCLM38 z H + volterraP φ z F) (i j : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => ext38 F r i j)
        ((zsCoeffPot38 φ z s * ext38 F s + spectralCoeff38 * ext38 H s) i j) s := by
  filter_upwards [ae_hasDerivAt_gaugePrimitive38 F z 0
    (forcedGauge φ z F H) (intervalIntegrable_forcedGauge φ z F H)
    (forced_gauge φ z F H hF) i j] with s hs hm
  apply (hs hm).congr_deriv
  have hφ := gaugeDeriv_coeff38 φ z s (ext38 F s) i j
  have hZ := spectralGauge_cancel38 z H s i j
  simp only [forcedGauge, Matrix.of_apply, Matrix.add_apply]
  linear_combination hφ + hZ

/-! ### A.2  The Taylor coefficients `M_j` of `z ↦ M(·, z)` at `z0` -/

/-- `T = (1 - 𝒱_{z0})⁻¹ 𝒮_{z0}`, the recursion operator of the Taylor coefficients. -/
def tayStep (φ : PotPair) (z0 : ℂ) : PairCont38 →L[ℂ] PairCont38 :=
  Ring.inverse (1 - volterraP φ z0) * spectralForcingCLM38 z0

/-- `M_j = T^j M_0`, `M_0 = fundContP φ z0`. These are the Taylor coefficients of
`w ↦ fundContP φ (z0 + w)` at `w = 0` (`hasSum_tayCoeff`). -/
def tayCoeff (φ : PotPair) (z0 : ℂ) (j : ℕ) : PairCont38 :=
  (tayStep φ z0 ^ j) (fundContP φ z0)

theorem tayCoeff_zero (φ : PotPair) (z0 : ℂ) : tayCoeff φ z0 0 = fundContP φ z0 := by
  simp [tayCoeff]

theorem tayCoeff_succ (φ : PotPair) (z0 : ℂ) (j : ℕ) :
    tayCoeff φ z0 (j + 1) = tayStep φ z0 (tayCoeff φ z0 j) := by
  simp only [tayCoeff, pow_succ']
  rfl

theorem invOne_apply_sub (φ : PotPair) (z0 : ℂ) (X : PairCont38) :
    Ring.inverse (1 - volterraP φ z0) X - volterraP φ z0 (Ring.inverse (1 - volterraP φ z0) X)
      = X := by
  have hu := isUnit_one_sub_volterraP φ z0
  have h := congrArg (fun T => T X) (Ring.mul_inverse_cancel _ hu)
  exact h

theorem invOne_apply_cancel (φ : PotPair) (z0 : ℂ) (X : PairCont38) :
    Ring.inverse (1 - volterraP φ z0) (X - volterraP φ z0 X) = X := by
  have hu := isUnit_one_sub_volterraP φ z0
  have h := congrArg (fun T => T X) (Ring.inverse_mul_cancel _ hu)
  exact h

theorem tayCoeff_succ_forced (φ : PotPair) (z0 : ℂ) (j : ℕ) :
    tayCoeff φ z0 (j + 1) = spectralForcingCLM38 z0 (tayCoeff φ z0 j) +
      volterraP φ z0 (tayCoeff φ z0 (j + 1)) := by
  rw [tayCoeff_succ]
  exact sub_eq_iff_eq_add.mp (invOne_apply_sub φ z0 _)

/-- The shifted equation: `M(z0 + w) = M_0 + w T M(z0 + w)`. -/
theorem shifted_eq (φ : PotPair) (z0 w : ℂ) :
    fundContP φ (z0 + w) = tayCoeff φ z0 0 + w • tayStep φ z0 (fundContP φ (z0 + w)) := by
  have hs := fundContP_shiftedVolterra38 φ z0 w
  set G := fundContP φ (z0 + w) with hG
  have h1 : G - volterraP φ z0 G = freeFundP z0 + w • spectralForcingCLM38 z0 G :=
    sub_eq_of_eq_add (hs.trans (by abel))
  calc G = Ring.inverse (1 - volterraP φ z0) (G - volterraP φ z0 G) :=
        (invOne_apply_cancel φ z0 G).symm
    _ = Ring.inverse (1 - volterraP φ z0) (freeFundP z0) +
        w • Ring.inverse (1 - volterraP φ z0) (spectralForcingCLM38 z0 G) := by
        rw [h1, map_add, map_smul]
    _ = tayCoeff φ z0 0 + w • tayStep φ z0 G := by
        rw [tayCoeff_zero]
        rfl

/-! ### A.3  The Taylor series of `w ↦ M(·, z0 + w)` -/

theorem norm_pow_apply_le (T : PairCont38 →L[ℂ] PairCont38) (n : ℕ) (x : PairCont38) :
    ‖(T ^ n) x‖ ≤ ‖T‖ ^ n * ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    calc ‖(T ^ (n + 1)) x‖ = ‖(T ^ n) (T x)‖ := by rw [pow_succ]; rfl
      _ ≤ ‖T‖ ^ n * ‖T x‖ := ih _
      _ ≤ ‖T‖ ^ n * (‖T‖ * ‖x‖) := by
          gcongr
          exact T.le_opNorm x
      _ = ‖T‖ ^ (n + 1) * ‖x‖ := by ring

theorem partial_sum_identity (φ : PotPair) (z0 w : ℂ) (n : ℕ) :
    fundContP φ (z0 + w) - ∑ j ∈ Finset.range n, w ^ j • tayCoeff φ z0 j =
      w ^ n • (tayStep φ z0 ^ n) (fundContP φ (z0 + w)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    have hG := shifted_eq φ z0 w
    have h' : fundContP φ (z0 + w) - tayCoeff φ z0 0 =
        w • tayStep φ z0 (fundContP φ (z0 + w)) := sub_eq_of_eq_add' hG
    have h2 : (tayStep φ z0 ^ n) (fundContP φ (z0 + w)) - tayCoeff φ z0 n =
        w • (tayStep φ z0 ^ (n + 1)) (fundContP φ (z0 + w)) := by
      have h3 : tayCoeff φ z0 n = (tayStep φ z0 ^ n) (tayCoeff φ z0 0) := by
        rw [tayCoeff_zero]; rfl
      rw [h3, ← map_sub, h', map_smul]
      rw [pow_succ]
      rfl
    have h3 : w ^ n • (tayStep φ z0 ^ n) (fundContP φ (z0 + w)) - w ^ n • tayCoeff φ z0 n =
        w ^ n • ((tayStep φ z0 ^ n) (fundContP φ (z0 + w)) - tayCoeff φ z0 n) :=
      (smul_sub _ _ _).symm
    rw [h3, h2, smul_smul, ← pow_succ]

theorem hasSum_tayCoeff (φ : PotPair) (z0 : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w‖ < r →
      HasSum (fun j : ℕ => w ^ j • tayCoeff φ z0 j) (fundContP φ (z0 + w)) := by
  refine ⟨(‖tayStep φ z0‖ + 1)⁻¹, by positivity, fun w hw => ?_⟩
  set T := tayStep φ z0 with hT
  have hq : ‖w‖ * ‖T‖ < 1 := by
    have h1 : ‖w‖ * (‖T‖ + 1) < 1 := by
      have := mul_lt_mul_of_pos_right hw (by positivity : 0 < ‖T‖ + 1)
      rwa [inv_mul_cancel₀ (by positivity)] at this
    nlinarith [norm_nonneg w, norm_nonneg T]
  have hq0 : 0 ≤ ‖w‖ * ‖T‖ := by positivity
  have hbd : ∀ j : ℕ, ‖w ^ j • tayCoeff φ z0 j‖ ≤
      ‖fundContP φ z0‖ * (‖w‖ * ‖T‖) ^ j := by
    intro j
    rw [norm_smul, norm_pow]
    have h1 : ‖tayCoeff φ z0 j‖ ≤ ‖T‖ ^ j * ‖fundContP φ z0‖ :=
      norm_pow_apply_le T j (fundContP φ z0)
    calc ‖w‖ ^ j * ‖tayCoeff φ z0 j‖ ≤ ‖w‖ ^ j * (‖T‖ ^ j * ‖fundContP φ z0‖) := by gcongr
      _ = ‖fundContP φ z0‖ * (‖w‖ * ‖T‖) ^ j := by rw [mul_pow]; ring
  have hsum : Summable (fun j : ℕ => w ^ j • tayCoeff φ z0 j) :=
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hq0 hq).mul_left ‖fundContP φ z0‖) hbd
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, w ^ j • tayCoeff φ z0 j) atTop
      (𝓝 (fundContP φ (z0 + w))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ n : ℕ, ‖(∑ j ∈ Finset.range n, w ^ j • tayCoeff φ z0 j) -
        fundContP φ (z0 + w)‖ ≤ ‖fundContP φ (z0 + w)‖ * (‖w‖ * ‖T‖) ^ n := by
      intro n
      rw [norm_sub_rev, partial_sum_identity, norm_smul, norm_pow]
      have := norm_pow_apply_le T n (fundContP φ (z0 + w))
      calc ‖w‖ ^ n * ‖(T ^ n) (fundContP φ (z0 + w))‖
          ≤ ‖w‖ ^ n * (‖T‖ ^ n * ‖fundContP φ (z0 + w)‖) := by gcongr
        _ = ‖fundContP φ (z0 + w)‖ * (‖w‖ * ‖T‖) ^ n := by rw [mul_pow]; ring
    refine squeeze_zero (fun n => norm_nonneg _) hb ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul
      ‖fundContP φ (z0 + w)‖
  have := tendsto_nhds_unique h1 h2
  rw [← this]
  exact hsum.hasSum

theorem hasSum_tayEntry (φ : PotPair) (z0 : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w‖ < r → ∀ (t : Icc (0 : ℝ) 1) (i j : Fin 2),
      HasSum (fun n : ℕ => w ^ n * tayCoeff φ z0 n t i j) (fundPair φ (z0 + w) t i j) := by
  obtain ⟨r, hr, h⟩ := hasSum_tayCoeff φ z0
  refine ⟨r, hr, fun w hw t i j => ?_⟩
  have h1 := (fundEntryL38 t i j).hasSum (h w hw)
  have e : (fun n : ℕ => fundEntryL38 t i j (w ^ n • tayCoeff φ z0 n)) =
      fun n : ℕ => w ^ n * tayCoeff φ z0 n t i j := by
    funext n
    simp [fundEntryL38]
  rw [e] at h1
  exact h1

/-! ### A.4  Time regularity of the Taylor coefficients -/

/-- `M_j` on the real line (constant extension from `[0,1]`). -/
def tayM (φ : PotPair) (z0 : ℂ) (j : ℕ) : ℝ → PairMat38 := ext38 (tayCoeff φ z0 j)

/-- `M_{j-1}`, with `M_{-1} = 0`. -/
def tayPrevM (φ : PotPair) (z0 : ℂ) : ℕ → ℝ → PairMat38
  | 0 => fun _ => 0
  | j + 1 => tayM φ z0 j

theorem tayM_ac (φ : PotPair) (z0 : ℂ) (j : ℕ) (i k : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => tayM φ z0 j s i k) 0 1 := by
  cases j with
  | zero =>
    simp only [tayM, tayCoeff_zero]
    exact ac_fundContP_entry38 φ z0 i k
  | succ j => exact forced_ac φ z0 _ _ (tayCoeff_succ_forced φ z0 j) i k

theorem tayM_ae (φ : PotPair) (z0 : ℂ) (j : ℕ) (i k : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => tayM φ z0 j r i k)
        ((zsCoeffPot38 φ z0 s * tayM φ z0 j s + spectralCoeff38 * tayPrevM φ z0 j s) i k) s := by
  cases j with
  | zero =>
    filter_upwards [ae_hasDerivAt_fundContP_entry38 φ z0 i k] with s hs hm
    have := hs hm
    simpa [tayM, tayCoeff_zero, tayPrevM] using this
  | succ j =>
    exact forced_ae φ z0 _ _ (tayCoeff_succ_forced φ z0 j) i k

theorem tayM_zero_time (φ : PotPair) (z0 : ℂ) (j : ℕ) :
    tayM φ z0 j 0 = if j = 0 then 1 else 0 := by
  cases j with
  | zero =>
    simp only [tayM, tayCoeff_zero, if_true]
    rw [ext38_of_mem _ ⟨le_rfl, zero_le_one⟩]
    exact fundPair_zero φ z0
  | succ j =>
    simp only [tayM, Nat.succ_ne_zero, if_false]
    rw [ext38_of_mem _ ⟨le_rfl, zero_le_one⟩]
    exact forced_zero_time φ z0 _ _ (tayCoeff_succ_forced φ z0 j)

/-! ### B  Vector chains `W_k = ∑_{i ≤ k} M_i c_{k-i}` -/

/-- A pair function with `f' = Q_z f + R̂ g` a.e. on `[0,1]` (`R̂ = ∂_z Q_z`), `f` AC. -/
def IsForcedSolution (φ : PotPair) (z : ℂ) (f g : ℝ → PairVec38) : Prop :=
  (∀ i, AbsolutelyContinuousOnInterval (fun s => f s i) 0 1) ∧
  ∀ i, ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
    HasDerivAt (fun r => f r i)
      ((zsCoeffPot38 φ z s).mulVec (f s) i + (spectralCoeff38.mulVec (g s)) i) s

theorem isPairSolution38_of_forced (φ : PotPair) (z : ℂ) (f : ℝ → PairVec38)
    (hf : IsForcedSolution φ z f (fun _ => 0)) : IsPairSolution38 φ z f := by
  refine ⟨hf.1, fun i => ?_⟩
  filter_upwards [hf.2 i] with s hs hm
  simpa using hs hm

theorem forced_of_isPairSolution38 (φ : PotPair) (z : ℂ) (f : ℝ → PairVec38)
    (hf : IsPairSolution38 φ z f) : IsForcedSolution φ z f (fun _ => 0) := by
  refine ⟨hf.1, fun i => ?_⟩
  filter_upwards [hf.2 i] with s hs hm
  simpa using hs hm

/-- The previous element of a chain; `0` before the first. -/
def prevOf (V : ℕ → ℝ → PairVec38) : ℕ → ℝ → PairVec38
  | 0 => fun _ => 0
  | k + 1 => V k

/-- Padded coefficient access: `c j = 0` for `j ≥ N`. -/
def cget {N : ℕ} (c : Fin N → PairVec38) (j : ℕ) : PairVec38 :=
  if h : j < N then c ⟨j, h⟩ else 0

theorem cget_add {N : ℕ} (c d : Fin N → PairVec38) (j : ℕ) :
    cget (c + d) j = cget c j + cget d j := by
  unfold cget; split_ifs <;> simp

theorem cget_smul {N : ℕ} (r : ℂ) (c : Fin N → PairVec38) (j : ℕ) :
    cget (r • c) j = r • cget c j := by
  unfold cget; split_ifs <;> simp

theorem cget_of_lt {N : ℕ} (c : Fin N → PairVec38) {j : ℕ} (hj : j < N) :
    cget c j = c ⟨j, hj⟩ := by
  simp [cget, hj]

/-- `W_k(s) = ∑_{i ≤ k} M_i(s) c_{k-i}`, the `k`-th Taylor chain function of `c`. -/
def chainFun (φ : PotPair) (z0 : ℂ) {N : ℕ} (c : Fin N → PairVec38) (k : ℕ) (s : ℝ) :
    PairVec38 :=
  ∑ i ∈ Finset.range (k + 1), (tayM φ z0 i s).mulVec (cget c (k - i))

theorem chainFun_add (φ : PotPair) (z0 : ℂ) {N : ℕ} (c d : Fin N → PairVec38) (k : ℕ)
    (s : ℝ) : chainFun φ z0 (c + d) k s = chainFun φ z0 c k s + chainFun φ z0 d k s := by
  simp only [chainFun, cget_add, Matrix.mulVec_add, Finset.sum_add_distrib]

theorem chainFun_smul (φ : PotPair) (z0 : ℂ) {N : ℕ} (r : ℂ) (c : Fin N → PairVec38) (k : ℕ)
    (s : ℝ) : chainFun φ z0 (r • c) k s = r • chainFun φ z0 c k s := by
  simp only [chainFun, cget_smul, Matrix.mulVec_smul, Finset.smul_sum]

theorem chainFun_zero_time (φ : PotPair) (z0 : ℂ) {N : ℕ} (c : Fin N → PairVec38) (k : ℕ) :
    chainFun φ z0 c k 0 = cget c k := by
  unfold chainFun
  rw [Finset.sum_eq_single 0]
  · simp [tayM_zero_time]
  · intro a _ ha
    simp [tayM_zero_time, ha]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos k)) h

theorem sum_prev_chain (φ : PotPair) (z0 : ℂ) {N : ℕ} (c : Fin N → PairVec38) (k : ℕ)
    (s : ℝ) :
    ∑ a ∈ Finset.range (k + 1), (tayPrevM φ z0 a s).mulVec (cget c (k - a)) =
      prevOf (chainFun φ z0 c) k s := by
  cases k with
  | zero => simp [tayPrevM, prevOf]
  | succ k =>
    rw [Finset.sum_range_succ']
    simp only [tayPrevM, prevOf, chainFun, Matrix.zero_mulVec, add_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.add_sub_add_right]

theorem chain_deriv_alg (φ : PotPair) (z0 : ℂ) {N : ℕ} (c : Fin N → PairVec38) (k : ℕ)
    (s : ℝ) (i : Fin 2) :
    ∑ a ∈ Finset.range (k + 1),
      ((zsCoeffPot38 φ z0 s * tayM φ z0 a s + spectralCoeff38 * tayPrevM φ z0 a s).mulVec
        (cget c (k - a))) i =
      (zsCoeffPot38 φ z0 s).mulVec (chainFun φ z0 c k s) i +
        (spectralCoeff38.mulVec (prevOf (chainFun φ z0 c) k s)) i := by
  rw [← sum_prev_chain, ← Finset.sum_apply]
  have h1 : ∑ a ∈ Finset.range (k + 1),
      (zsCoeffPot38 φ z0 s * tayM φ z0 a s + spectralCoeff38 * tayPrevM φ z0 a s).mulVec
        (cget c (k - a)) =
      (zsCoeffPot38 φ z0 s).mulVec (chainFun φ z0 c k s) +
        spectralCoeff38.mulVec (∑ a ∈ Finset.range (k + 1),
          (tayPrevM φ z0 a s).mulVec (cget c (k - a))) := by
    simp only [chainFun, Matrix.mulVec_sum, Matrix.add_mulVec, Matrix.mulVec_mulVec,
      Finset.sum_add_distrib]
  rw [h1]
  simp [Pi.add_apply]

theorem ac_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (h : ∀ a ∈ S, AbsolutelyContinuousOnInterval (f a) 0 1) :
    AbsolutelyContinuousOnInterval (fun x => ∑ a ∈ S, f a x) 0 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using absolutelyContinuousOnInterval_const38 0 0 1
  | insert a S ha ih =>
    have := (h a (Finset.mem_insert_self a S)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    simp only [Finset.sum_insert ha]
    exact this

theorem chainFun_forced (φ : PotPair) (z0 : ℂ) {N : ℕ} (c : Fin N → PairVec38) (k : ℕ) :
    IsForcedSolution φ z0 (chainFun φ z0 c k) (prevOf (chainFun φ z0 c) k) := by
  have hfun : ∀ i : Fin 2, (fun r => chainFun φ z0 c k r i) = fun r =>
      ∑ a ∈ Finset.range (k + 1), (cget c (k - a) 0 * tayM φ z0 a r i 0 +
        cget c (k - a) 1 * tayM φ z0 a r i 1) := by
    intro i
    funext r
    simp only [chainFun, Finset.sum_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [hfun i]
    refine ac_finset_sum _ _ fun a _ => ?_
    have h0 := (tayM_ac φ z0 a i 0).const_smul (cget c (k - a) 0)
    have h1 := (tayM_ac φ z0 a i 1).const_smul (cget c (k - a) 1)
    have h2 := h0.add h1
    simp only [smul_eq_mul] at h2
    exact h2
  · have hae : ∀ᵐ s : ℝ, ∀ a ∈ Finset.range (k + 1), ∀ m : Fin 2, s ∈ Icc (0 : ℝ) 1 →
        HasDerivAt (fun r => tayM φ z0 a r i m)
          ((zsCoeffPot38 φ z0 s * tayM φ z0 a s + spectralCoeff38 * tayPrevM φ z0 a s) i m) s :=
      (Filter.eventually_all_finset _).2 fun a _ =>
        Filter.eventually_all.2 fun m => tayM_ae φ z0 a i m
    filter_upwards [hae] with s hs hm
    rw [hfun i]
    have hd : HasDerivAt (fun r => ∑ a ∈ Finset.range (k + 1),
        (cget c (k - a) 0 * tayM φ z0 a r i 0 + cget c (k - a) 1 * tayM φ z0 a r i 1))
        (∑ a ∈ Finset.range (k + 1), (cget c (k - a) 0 *
          (zsCoeffPot38 φ z0 s * tayM φ z0 a s + spectralCoeff38 * tayPrevM φ z0 a s) i 0 +
          cget c (k - a) 1 *
          (zsCoeffPot38 φ z0 s * tayM φ z0 a s + spectralCoeff38 * tayPrevM φ z0 a s) i 1)) s :=
      HasDerivAt.fun_sum fun a ha =>
        (((hs a ha 0 hm).const_mul (cget c (k - a) 0)).add
          ((hs a ha 1 hm).const_mul (cget c (k - a) 1)))
    refine hd.congr_deriv ?_
    rw [← chain_deriv_alg φ z0 c k s i]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-! ### C  The constraint system `K_N` and the boundary relations -/

/-- Taylor coefficients of the characteristic matrix `D(z) = B0 + B1 M(1,z)` at `z0`. -/
def tayD (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) (a : ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (if a = 0 then charB0 bc else 0) + charB1 bc * tayM φ z0 a 1

/-- `m`-th constraint `∑_{a ≤ m} D_a c_{m-a}`. -/
def tayConstraintFun (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) {N : ℕ}
    (c : Fin N → PairVec38) (m : ℕ) : PairVec38 :=
  ∑ a ∈ Finset.range (m + 1), (tayD bc φ z0 a).mulVec (cget c (m - a))

/-- The linear constraint map `c ↦ (∑_{a ≤ m} D_a c_{m-a})_{m < N}`. -/
def tayConstraint (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) (N : ℕ) :
    (Fin N → PairVec38) →ₗ[ℂ] (Fin N → PairVec38) where
  toFun c := fun m => tayConstraintFun bc φ z0 c m.val
  map_add' c d := by
    funext m
    simp only [tayConstraintFun, cget_add, Matrix.mulVec_add, Finset.sum_add_distrib,
      Pi.add_apply]
  map_smul' r c := by
    funext m
    simp only [tayConstraintFun, cget_smul, Matrix.mulVec_smul, Finset.smul_sum,
      Pi.smul_apply, RingHom.id_apply]

/-- `K_N`: the Taylor-coefficient chains of length `N` satisfying the boundary relations. -/
def tayKer (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) (N : ℕ) :
    Submodule ℂ (Fin N → PairVec38) :=
  LinearMap.ker (tayConstraint bc φ z0 N)

theorem mem_tayKer_iff (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) {N : ℕ}
    (c : Fin N → PairVec38) :
    c ∈ tayKer bc φ z0 N ↔ ∀ m : Fin N, tayConstraintFun bc φ z0 c m.val = 0 := by
  simp only [tayKer, LinearMap.mem_ker, tayConstraint, LinearMap.coe_mk, AddHom.coe_mk]
  exact ⟨fun h m => congrFun h m, fun h => funext h⟩

theorem tayConstraintFun_eq (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) {N : ℕ}
    (c : Fin N → PairVec38) (k : ℕ) :
    tayConstraintFun bc φ z0 c k =
      (charB0 bc).mulVec (chainFun φ z0 c k 0) + (charB1 bc).mulVec (chainFun φ z0 c k 1) := by
  rw [chainFun_zero_time]
  unfold tayConstraintFun chainFun tayD
  simp only [Matrix.add_mulVec, Finset.sum_add_distrib, Matrix.mulVec_sum, Matrix.mulVec_mulVec]
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro a _ ha; simp [ha]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos k)) h

theorem bcRelation_chain_iff (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) {N : ℕ}
    (c : Fin N → PairVec38) (k : ℕ) :
    bcRelation bc (chainFun φ z0 c k 0) (chainFun φ z0 c k 1) ↔
      tayConstraintFun bc φ z0 c k = 0 := by
  rw [bcRelation_iff_charB, tayConstraintFun_eq]

/-! ### D  The correspondence at the level of absolutely continuous solutions -/

                                                                                             
                                                                                     
                                                                         
def PairUniq (φ : PotPair) (z : ℂ) : Prop :=
  ∀ f : ℝ → PairVec38, IsPairSolution38 φ z f → ∀ t ∈ Icc (0 : ℝ) 1,
    f t = (Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fundPair φ z) t).mulVec (f 0)

/-- A chain of AC pair functions: `V_k' = Q_{z0} V_k + R̂ V_{k-1}` a.e. (with `V_{-1} = 0`),
satisfying the boundary relation `bcRelation bc (V_k 0) (V_k 1)` for `k < N`. -/
def IsAcChain (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) (N : ℕ)
    (V : ℕ → ℝ → PairVec38) : Prop :=
  ∀ k < N, IsForcedSolution φ z0 (V k) (prevOf V k) ∧ bcRelation bc (V k 0) (V k 1)

theorem chainFun_isAcChain (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) {N : ℕ}
    (c : Fin N → PairVec38) (hc : c ∈ tayKer bc φ z0 N) :
    IsAcChain bc φ z0 N (chainFun φ z0 c) := by
  intro k hk
  refine ⟨chainFun_forced φ z0 c k, ?_⟩
  rw [bcRelation_chain_iff]
  exact (mem_tayKer_iff bc φ z0 c).1 hc ⟨k, hk⟩

theorem chain_unique (φ : PotPair) (z0 : ℂ) (hU : PairUniq φ z0) {N : ℕ}
    (V : ℕ → ℝ → PairVec38) (hV : ∀ k < N, IsForcedSolution φ z0 (V k) (prevOf V k))
    (c : Fin N → PairVec38) (hc : ∀ k : Fin N, V k 0 = c k) :
    ∀ k, k < N → ∀ t ∈ Icc (0 : ℝ) 1, V k t = chainFun φ z0 c k t := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk t ht
    have hpair : IsPairSolution38 φ z0 (fun s => V k s - chainFun φ z0 c k s) := by
      refine ⟨fun i => ((hV k hk).1 i).sub ((chainFun_forced φ z0 c k).1 i), fun i => ?_⟩
      filter_upwards [(hV k hk).2 i, (chainFun_forced φ z0 c k).2 i] with s h1 h2 hm
      have h3 := (h1 hm).sub (h2 hm)
      refine h3.congr_deriv ?_
      have hprev : prevOf V k s = prevOf (chainFun φ z0 c) k s := by
        cases k with
        | zero => rfl
        | succ k' => exact ih k' (by omega) (by omega) s hm
      rw [hprev, Matrix.mulVec_sub]
      simp only [Pi.sub_apply]
      ring
    have h0 : V k 0 - chainFun φ z0 c k 0 = 0 := by
      rw [chainFun_zero_time, cget_of_lt c hk, hc ⟨k, hk⟩, sub_self]
    have := hU _ hpair t ht
    simp only [h0, Matrix.mulVec_zero] at this
    exact sub_eq_zero.1 this

theorem tayKer_of_isAcChain (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ)
    (hU : PairUniq φ z0) {N : ℕ} (V : ℕ → ℝ → PairVec38) (hV : IsAcChain bc φ z0 N V) :
    (fun k : Fin N => V k 0) ∈ tayKer bc φ z0 N ∧
      ∀ k, k < N → ∀ t ∈ Icc (0 : ℝ) 1,
        V k t = chainFun φ z0 (fun k : Fin N => V k 0) k t := by
  have huniq := chain_unique φ z0 hU V (fun k hk => (hV k hk).1) (fun k : Fin N => V k 0)
    (fun k => rfl)
  refine ⟨?_, huniq⟩
  rw [mem_tayKer_iff]
  intro m
  rw [← bcRelation_chain_iff]
  have h0 := huniq m m.2 0 ⟨le_rfl, zero_le_one⟩
  have h1 := huniq m m.2 1 ⟨zero_le_one, le_rfl⟩
  rw [← h0, ← h1]
  exact (hV m m.2).2

/-- **M4 at the level of AC solutions.** For `N : ℕ`, with hypothesis `U1` (`PairUniq`):
(a) every `c ∈ K_N` gives the AC chain `W_k = ∑_{i ≤ k} M_i c_{k-i}` with the boundary
relations, initial values `W_k(0) = c_k`; (b) every AC chain with the boundary relations is of
this form with `c_k = V_k(0)` (on `[0,1]`), and `c ∈ K_N`. -/
theorem tay_chain_correspondence (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ)
    (hU : PairUniq φ z0) (N : ℕ) :
    (∀ c ∈ tayKer bc φ z0 N, IsAcChain bc φ z0 N (chainFun φ z0 c) ∧
      ∀ k : Fin N, chainFun φ z0 c k 0 = c k) ∧
    (∀ V : ℕ → ℝ → PairVec38, IsAcChain bc φ z0 N V →
      ∃ c ∈ tayKer bc φ z0 N, (∀ k : Fin N, V k 0 = c k) ∧
        ∀ k, k < N → ∀ t ∈ Icc (0 : ℝ) 1, V k t = chainFun φ z0 c k t) := by
  refine ⟨fun c hc => ⟨chainFun_isAcChain bc φ z0 c hc, fun k => ?_⟩, fun V hV => ?_⟩
  · rw [chainFun_zero_time, cget_of_lt c k.2]
  · obtain ⟨h1, h2⟩ := tayKer_of_isAcChain bc φ z0 hU V hV
    exact ⟨_, h1, fun k => rfl, h2⟩

/-! ### E  `tayD` are the Taylor coefficients of the characteristic matrix -/

theorem tayM_one (φ : PotPair) (z0 : ℂ) (a : ℕ) :
    tayM φ z0 a 1 = tayCoeff φ z0 a ⟨1, zero_le_one, le_rfl⟩ := by
  simp only [tayM]
  exact ext38_of_mem _ ⟨zero_le_one, le_rfl⟩

/-- `D(z0 + w) = ∑_a w^a D_a` entrywise, for `‖w‖ < r`, where `D(z) = B0 + B1 M(1, z)`
(`charMatrix bc (fundPair φ z 1)`). -/
theorem hasSum_tayD (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w‖ < r → ∀ i j : Fin 2,
      HasSum (fun a : ℕ => w ^ a * tayD bc φ z0 a i j)
        (charMatrix bc (fundPair φ (z0 + w) ⟨1, zero_le_one, le_rfl⟩) i j) := by
  obtain ⟨r, hr, h⟩ := hasSum_tayEntry φ z0
  refine ⟨r, hr, fun w hw i j => ?_⟩
  have hB1 : HasSum (fun a : ℕ => ∑ l : Fin 2,
      charB1 bc i l * (w ^ a * tayCoeff φ z0 a ⟨1, zero_le_one, le_rfl⟩ l j))
      (∑ l : Fin 2, charB1 bc i l * fundPair φ (z0 + w) ⟨1, zero_le_one, le_rfl⟩ l j) :=
    hasSum_sum fun l _ => (h w hw ⟨1, zero_le_one, le_rfl⟩ l j).mul_left (charB1 bc i l)
  have hB0 : HasSum (fun a : ℕ => if a = 0 then charB0 bc i j else 0) (charB0 bc i j) :=
    hasSum_ite_eq 0 (charB0 bc i j)
  have h2 := hB0.add hB1
  have e1 : charMatrix bc (fundPair φ (z0 + w) ⟨1, zero_le_one, le_rfl⟩) i j =
      charB0 bc i j + ∑ l : Fin 2,
        charB1 bc i l * fundPair φ (z0 + w) ⟨1, zero_le_one, le_rfl⟩ l j := by
    simp [charMatrix, Matrix.add_apply, Matrix.mul_apply]
  rw [e1]
  convert h2 using 1
  funext a
  have h' : ∀ l : Fin 2, tayM φ z0 a 1 l j = tayCoeff φ z0 a ⟨1, zero_le_one, le_rfl⟩ l j :=
    fun l => by rw [tayM_one]
  simp only [tayD, Matrix.add_apply, Matrix.mul_apply, h']
  by_cases ha : a = 0
  · subst ha
    simp [Finset.mul_sum, mul_add, mul_left_comm]
  · simp [ha, Fin.sum_univ_two, mul_add]
    ring

/-! ### F  Operator chains: `(A - z0) W_k = W_{k-1}` versus AC chains -/

theorem continuousOn_Icc_of_ac {F : ℝ → ℂ} (hF : AbsolutelyContinuousOnInterval F 0 1) :
    ContinuousOn F (Icc (0 : ℝ) 1) := by
  simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hF.continuousOn

theorem exists_bound_Icc {F : ℝ → ℂ} (hc : ContinuousOn F (Icc (0 : ℝ) 1)) :
    ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ‖F s‖ ≤ C :=
  isCompact_Icc.exists_bound_of_continuousOn hc

theorem memLp_two_of_continuousOn {F : ℝ → ℂ} (hc : ContinuousOn F (Icc (0 : ℝ) 1)) :
    MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  obtain ⟨C, hC⟩ := exists_bound_Icc hc
  refine MemLp.of_bound ((hc.aestronglyMeasurable measurableSet_Icc).mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hC s ⟨hs.1.le, hs.2⟩

theorem memLp_top_of_continuousOn {F : ℝ → ℂ} (hc : ContinuousOn F (Icc (0 : ℝ) 1)) :
    MemLp F ∞ (volume.restrict (Ioc (0 : ℝ) 1)) := by
  obtain ⟨C, hC⟩ := exists_bound_Icc hc
  refine memLp_top_of_bound ((hc.aestronglyMeasurable measurableSet_Icc).mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hC s ⟨hs.1.le, hs.2⟩

theorem zsApply_eq_smul_add_iff (φ : SourcePairL2) (f : H1Pair) (z : ℂ) (w : SourcePairL2) :
    zsApply φ f = z • h1PairValue f + w ↔
      ∀ b : Bool, ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        zsExpression φ (fun c x => (f c).value x) (fun c x => (f c).derivative x) b x =
          z * (f b).value x + w b x := by
  constructor
  · intro h b
    have hb : (zsApply φ f) b = z • (f b).value + w b :=
      congrArg (fun v : SourcePairL2 => v b) h
    filter_upwards [zsApply_ae φ f b, Lp.coeFn_add (z • (f b).value) (w b),
      Lp.coeFn_smul z (f b).value] with x h1 h2 h3
    rw [← h1, hb, h2]
    simp only [Pi.add_apply, h3]
    rfl
  · intro h
    refine PiLp.ext fun b => Lp.ext ?_
    filter_upwards [zsApply_ae φ f b, Lp.coeFn_add (z • (f b).value) (w b),
      Lp.coeFn_smul z (f b).value, h b] with x h1 h2 h3 h4
    change (zsApply φ f b) x = (z • (f b).value + w b) x
    rw [h1, h2, h4]
    simp only [Pi.add_apply, h3]
    rfl

/-- Forward bridge: an H1 pair with `zsApply f = z f + w` gives a forced AC solution. -/
theorem isForced_repVec (φ : PotPair) (z : ℂ) (f : H1Pair) (w : SourcePairL2)
    (gf : ℝ → PairVec38)
    (h : zsApply (intervalPotential φ) f = z • h1PairValue f + w)
    (hw : ∀ b : Bool, (fun t => w b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun t => gf t (pairIdx b)) :
    IsForcedSolution φ z (repVec f) gf := by
  have hz := (zsApply_eq_smul_add_iff _ f z w).1 h
  have hP := intervalPotential_ae φ
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · exact (representative_spec (f true)).1
    · exact (representative_spec (f false)).1
  · have hrt := representative_spec (f true)
    have hrf := representative_spec (f false)
    have hzt : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 →
        zsExpression (intervalPotential φ) (fun c x => (f c).value x)
          (fun c x => (f c).derivative x) true x = z * (f true).value x + w true x :=
      (ae_restrict_iff' measurableSet_Ioc).1 (hz true)
    have hzf : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 →
        zsExpression (intervalPotential φ) (fun c x => (f c).value x)
          (fun c x => (f c).derivative x) false x = z * (f false).value x + w false x :=
      (ae_restrict_iff' measurableSet_Ioc).1 (hz false)
    have hVt : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → Fext (f true) x = (f true).value x :=
      (ae_restrict_iff' measurableSet_Ioc).1 (representative_ae (f true))
    have hVf : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → Fext (f false) x = (f false).value x :=
      (ae_restrict_iff' measurableSet_Ioc).1 (representative_ae (f false))
    have hPt : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → intervalPotential φ true x = potRepFst38 φ x :=
      (ae_restrict_iff' measurableSet_Ioc).1 hP.1
    have hPf : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → intervalPotential φ false x = potRepSnd38 φ x :=
      (ae_restrict_iff' measurableSet_Ioc).1 hP.2
    have hWt : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → w true x = gf x 0 :=
      (ae_restrict_iff' measurableSet_Ioc).1 (hw true)
    have hWf : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → w false x = gf x 1 :=
      (ae_restrict_iff' measurableSet_Ioc).1 (hw false)
    have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by simp [ae_iff]
    intro i
    filter_upwards [hrt.2, hrf.2, hzt, hzf, hVt, hVf, hPt, hPf, hWt, hWf, h0]
      with x dt df ezt ezf vt vf pt pf wt wf hx0 hx
    have hxI : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩
    have hxu : x ∈ uIcc (0 : ℝ) 1 := by rwa [uIcc_of_le zero_le_one]
    have ezt' := ezt hxI
    have ezf' := ezf hxI
    simp only [zsExpression, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at ezt' ezf'
    rw [pt hxI, ← vf hxI, ← vt hxI, wt hxI] at ezt'
    rw [pf hxI, ← vf hxI, ← vt hxI, wf hxI] at ezf'
    obtain ⟨e00, e01, e10, e11⟩ := zsCoeffPot_entries φ z x
    fin_cases i
    · have mv : (zsCoeffPot38 φ z x).mulVec (repVec f x) 0 =
          -(Complex.I * z) * Fext (f true) x +
            Complex.I * potRepFst38 φ x * Fext (f false) x := by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e00, e01]
        rfl
      have mw : spectralCoeff38.mulVec (gf x) 0 = -Complex.I * gf x 0 := by
        simp [spectralCoeff38, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have hd := dt hxu
      change HasDerivAt (Fext (f true))
        ((zsCoeffPot38 φ z x).mulVec (repVec f x) 0 + spectralCoeff38.mulVec (gf x) 0) x
      rw [mv, mw]
      refine hd.congr_deriv ?_
      linear_combination (-Complex.I) * ezt' + ((f true).derivative x) * Complex.I_mul_I
    · have mv : (zsCoeffPot38 φ z x).mulVec (repVec f x) 1 =
          -(Complex.I * potRepSnd38 φ x) * Fext (f true) x +
            Complex.I * z * Fext (f false) x := by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e10, e11]
        rfl
      have mw : spectralCoeff38.mulVec (gf x) 1 = Complex.I * gf x 1 := by
        simp [spectralCoeff38, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have hd := df hxu
      change HasDerivAt (Fext (f false))
        ((zsCoeffPot38 φ z x).mulVec (repVec f x) 1 + spectralCoeff38.mulVec (gf x) 1) x
      rw [mv, mw]
      refine hd.congr_deriv ?_
      linear_combination Complex.I * ezf' + ((f false).derivative x) * Complex.I_mul_I

theorem pairIdx_true : pairIdx true = 0 := rfl

theorem pairIdx_false : pairIdx false = 1 := rfl

/-- The forced derivative expression, component `b`. -/
def Gc (φ : PotPair) (z : ℂ) (v p : ℝ → PairVec38) (b : Bool) (s : ℝ) : ℂ :=
  ((zsCoeffPot38 φ z s).mulVec (v s) + spectralCoeff38.mulVec (p s)) (pairIdx b)

theorem Gc_true (φ : PotPair) (z : ℂ) (v p : ℝ → PairVec38) (s : ℝ) :
    Gc φ z v p true s = -(Complex.I * z) * v s 0 +
      Complex.I * (potRepFst38 φ s * v s 1) + -Complex.I * p s 0 := by
  simp only [Gc, pairIdx, if_true, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    zsCoeffPot38, zsCoeffPair, spectralCoeff38]
  simp
  ring

theorem Gc_false (φ : PotPair) (z : ℂ) (v p : ℝ → PairVec38) (s : ℝ) :
    Gc φ z v p false s = -(Complex.I * potRepSnd38 φ s) * v s 0 +
      Complex.I * z * v s 1 + Complex.I * p s 1 := by
  simp only [Gc, pairIdx, Bool.false_eq_true, if_false, Pi.add_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, zsCoeffPot38, zsCoeffPair, spectralCoeff38]
  simp

theorem memLp_Gc (φ : PotPair) (z : ℂ) (v p : ℝ → PairVec38)
    (hv : ∀ i, ContinuousOn (fun s => v s i) (Icc (0 : ℝ) 1))
    (hp : ∀ i, ContinuousOn (fun s => p s i) (Icc (0 : ℝ) 1)) (b : Bool) :
    MemLp (Gc φ z v p b) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hφ1 : MemLp (potRepFst38 φ) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (NlsGge.Atomic.G1104Sup.sourceIntervalClass_spec φ.1).1
  have hφ2 : MemLp (potRepSnd38 φ) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (NlsGge.Atomic.G1104Sup.sourceIntervalClass_spec φ.2).1
  cases b
  · have e : Gc φ z v p false = fun s => -Complex.I * (potRepSnd38 φ s * v s 0) +
        Complex.I * z * v s 1 + Complex.I * p s 1 := by
      funext s
      rw [Gc_false]
      ring
    rw [e]
    have h1 : MemLp (fun s => potRepSnd38 φ s * v s 0) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
      hφ2.mul (memLp_top_of_continuousOn (hv 0))
    exact ((h1.const_mul (-Complex.I)).add
      ((memLp_two_of_continuousOn (hv 1)).const_mul (Complex.I * z))).add
      ((memLp_two_of_continuousOn (hp 1)).const_mul Complex.I)
  · have e : Gc φ z v p true = fun s => -(Complex.I * z) * v s 0 +
        Complex.I * (potRepFst38 φ s * v s 1) + -Complex.I * p s 0 := by
      funext s
      rw [Gc_true]
    rw [e]
    have h1 : MemLp (fun s => potRepFst38 φ s * v s 1) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
      hφ1.mul (memLp_top_of_continuousOn (hv 1))
    exact (((memLp_two_of_continuousOn (hv 0)).const_mul (-(Complex.I * z))).add
      (h1.const_mul Complex.I)).add
      ((memLp_two_of_continuousOn (hp 0)).const_mul (-Complex.I))


theorem forced_hd {φ : PotPair} {z : ℂ} {v p : ℝ → PairVec38}
    (hf : IsForcedSolution φ z v p) (b : Bool) :
    ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (fun s => v s (pairIdx b)) (Gc φ z v p b x) x := by
  filter_upwards [hf.2 (pairIdx b)] with x hx hxu
  exact hx (by rwa [uIcc_of_le zero_le_one] at hxu)

/-- The H1 pair with value `v` (components `pairIdx`) and derivative `Gc`. -/
def mkH1 (φ : PotPair) (z : ℂ) (v p : ℝ → PairVec38) (hf : IsForcedSolution φ z v p)
    (hv : ∀ i, ContinuousOn (fun s => v s i) (Icc (0 : ℝ) 1))
    (hp : ∀ i, ContinuousOn (fun s => p s i) (Icc (0 : ℝ) 1)) : H1Pair := fun b =>
  acH1 (memLp_two_of_continuousOn (hv (pairIdx b))) (memLp_Gc φ z v p hv hp b)
    (hf.1 (pairIdx b)) (forced_hd hf b)

section mk
variable (φ : PotPair) (z : ℂ) (v p : ℝ → PairVec38) (hf : IsForcedSolution φ z v p)
  (hv : ∀ i, ContinuousOn (fun s => v s i) (Icc (0 : ℝ) 1))
  (hp : ∀ i, ContinuousOn (fun s => p s i) (Icc (0 : ℝ) 1))

theorem mkH1_value_ae (b : Bool) :
    (fun x => (mkH1 φ z v p hf hv hp b).value x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x => v x (pairIdx b) :=
  (memLp_two_of_continuousOn (hv (pairIdx b))).coeFn_toLp

theorem mkH1_derivative_ae (b : Bool) :
    (fun x => (mkH1 φ z v p hf hv hp b).derivative x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      Gc φ z v p b :=
  (memLp_Gc φ z v p hv hp b).coeFn_toLp

theorem mkH1_traceLeft (b : Bool) : traceLeft (mkH1 φ z v p hf hv hp b) = v 0 (pairIdx b) :=
  acH1_traceLeft _ _ _ _

theorem mkH1_traceRight (b : Bool) : traceRight (mkH1 φ z v p hf hv hp b) = v 1 (pairIdx b) :=
  acH1_traceRight _ _ _ _

theorem mkH1_zsApply (w : SourcePairL2)
    (hw : ∀ b : Bool, (fun t => w b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun t => p t (pairIdx b)) :
    zsApply (intervalPotential φ) (mkH1 φ z v p hf hv hp) =
      z • h1PairValue (mkH1 φ z v p hf hv hp) + w := by
  rw [zsApply_eq_smul_add_iff]
  have hP := intervalPotential_ae φ
  intro b
  cases b
  · filter_upwards [hP.2, mkH1_value_ae φ z v p hf hv hp false,
      mkH1_value_ae φ z v p hf hv hp true, mkH1_derivative_ae φ z v p hf hv hp false,
      hw false] with x pf vf vt df ww
    simp only [zsExpression, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    rw [pf, df, vf, vt, ww, Gc_false]
    simp only [pairIdx_true, pairIdx_false]
    linear_combination (potRepSnd38 φ x * v x 0 - z * v x 1 - p x 1) * Complex.I_mul_I
  · filter_upwards [hP.1, mkH1_value_ae φ z v p hf hv hp false,
      mkH1_value_ae φ z v p hf hv hp true, mkH1_derivative_ae φ z v p hf hv hp true,
      hw true] with x pt vf vt dt ww
    simp only [zsExpression, Bool.not_true, ↓reduceIte]
    rw [pt, dt, vf, vt, ww, Gc_true]
    simp only [pairIdx_true, pairIdx_false]
    linear_combination (potRepFst38 φ x * v x 1 - z * v x 0 - p x 0) * Complex.I_mul_I

end mk

/-! ### G  The operator chain and the bridge theorem -/

/-- The previous chain element; `0` before the first. -/
def prevSP (W : ℕ → SourcePairL2) : ℕ → SourcePairL2
  | 0 => 0
  | k + 1 => W k

/-- Ascending Jordan chain of length `N` for `A - z`: `W_k ∈ dom A`, `(A - z) W_k = W_{k-1}`,
`W_{-1} = 0` (so `W_0` is an eigenvector or zero). -/
def IsOpChain (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ) (N : ℕ)
    (W : ℕ → SourcePairL2) : Prop :=
  ∀ k < N, ∃ hk : W k ∈ A.domain, A ⟨W k, hk⟩ - z • W k = prevSP W k

theorem exists_h1_of_dom (φ : PotPair) (bc : ZSBoundaryCondition) (z : ℂ)
    (u w : SourcePairL2) (hu : u ∈ (zsRealization (intervalPotential φ) bc).domain)
    (hA : zsRealization (intervalPotential φ) bc ⟨u, hu⟩ - z • u = w) :
    ∃ f : H1Pair, HasZSBoundaryCondition bc f ∧ h1PairValue f = u ∧
      zsApply (intervalPotential φ) f = z • u + w := by
  obtain ⟨f, hf, hfu⟩ : u ∈ zsBoundaryDomain bc := hu
  subst hfu
  refine ⟨f, hf, rfl, ?_⟩
  have h := zsRealization_apply (intervalPotential φ) bc f hf
  have h2 : zsApply (intervalPotential φ) f - z • h1PairValue f = w := h ▸ hA
  exact sub_eq_iff_eq_add'.1 h2

theorem opStep_of_h1 (φ : PotPair) (bc : ZSBoundaryCondition) (z : ℂ)
    (u w : SourcePairL2) (F : H1Pair) (hF : HasZSBoundaryCondition bc F)
    (hFu : h1PairValue F = u) (hA : zsApply (intervalPotential φ) F = z • u + w) :
    ∃ hu : u ∈ (zsRealization (intervalPotential φ) bc).domain,
      zsRealization (intervalPotential φ) bc ⟨u, hu⟩ - z • u = w := by
  subst hFu
  refine ⟨⟨F, hF, rfl⟩, ?_⟩
  rw [zsRealization_apply (intervalPotential φ) bc F hF, hA]
  abel


theorem prevSP_zero_ae (V : ℕ → ℝ → PairVec38) (W : ℕ → SourcePairL2) (b : Bool) :
    (fun t => (prevSP W 0) b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun t => prevOf V 0 t (pairIdx b) := by
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))] with t ht
  simpa [prevSP, prevOf] using ht

/-- **Operator side of M4.** `W` is an ascending Jordan chain of the `bc`-realization at `z`
iff its components are a.e. equal to those of an AC chain `V` with the boundary relations. -/
theorem opChain_iff (φ : PotPair) (bc : ZSBoundaryCondition) (z : ℂ) (N : ℕ)
    (W : ℕ → SourcePairL2) :
    IsOpChain (zsRealization (intervalPotential φ) bc) z N W ↔
      ∃ V : ℕ → ℝ → PairVec38, IsAcChain bc φ z N V ∧
        ∀ k < N, ∀ b : Bool, (fun t => W k b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
          fun t => V k t (pairIdx b) := by
  constructor
  · intro h
    have hex : ∀ k, ∃ f : H1Pair, k < N → (HasZSBoundaryCondition bc f ∧
        h1PairValue f = W k ∧ zsApply (intervalPotential φ) f = z • W k + prevSP W k) := by
      intro k
      by_cases hk : k < N
      · obtain ⟨hk', hA⟩ := h k hk
        obtain ⟨f, hf, hfu, hfa⟩ := exists_h1_of_dom φ bc z (W k) (prevSP W k) hk' hA
        exact ⟨f, fun _ => ⟨hf, hfu, hfa⟩⟩
      · exact ⟨fun _ => h1Zero, fun h' => absurd h' hk⟩
    choose f hf using hex
    have hval : ∀ k, k < N → ∀ b : Bool,
        (fun t => W k b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
          fun t => repVec (f k) t (pairIdx b) := by
      intro k hk b
      have e : (W k).ofLp b = (f k b).value := by
        have := congrArg (fun u : SourcePairL2 => u.ofLp b) (hf k hk).2.1
        exact this.symm
      filter_upwards [representative_ae (f k b)] with t ht
      rw [e, repVec_pairIdx]
      exact ht.symm
    refine ⟨fun k => repVec (f k), fun k hk => ⟨?_, ?_⟩, hval⟩
    · have hA := (hf k hk).2.2
      rw [← (hf k hk).2.1] at hA
      refine isForced_repVec φ z (f k) (prevSP W k) (prevOf (fun j => repVec (f j)) k) hA ?_
      intro b
      cases k with
      | zero => exact prevSP_zero_ae _ W b
      | succ k' => exact hval k' (by omega) b
    · have hL : ∀ b : Bool, traceLeft (f k b) = repVec (f k) 0 (pairIdx b) := by
        intro b
        rw [repVec_pairIdx]
        exact (IccExtend_left zero_le_one (representative (f k b))).symm
      have hR : ∀ b : Bool, traceRight (f k b) = repVec (f k) 1 (pairIdx b) := by
        intro b
        rw [repVec_pairIdx]
        exact (IccExtend_right zero_le_one (representative (f k b))).symm
      exact (hasZS_iff_bcRelation bc (f k) (repVec (f k) 0) (repVec (f k) 1) hL hR).1
        (hf k hk).1
  · rintro ⟨V, hV, hW⟩ k hk
    obtain ⟨hforced, hbc⟩ := hV k hk
    have hv : ∀ i, ContinuousOn (fun s => V k s i) (Icc (0 : ℝ) 1) :=
      fun i => continuousOn_Icc_of_ac (hforced.1 i)
    have hp : ∀ i, ContinuousOn (fun s => prevOf V k s i) (Icc (0 : ℝ) 1) := by
      cases k with
      | zero => intro i; exact continuousOn_const
      | succ k' => intro i; exact continuousOn_Icc_of_ac ((hV k' (by omega)).1.1 i)
    have hpw : ∀ b : Bool, (fun t => (prevSP W k) b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        fun t => prevOf V k t (pairIdx b) := by
      intro b
      cases k with
      | zero => exact prevSP_zero_ae V W b
      | succ k' => exact hW k' (by omega) b
    have hFbc : HasZSBoundaryCondition bc (mkH1 φ z (V k) (prevOf V k) hforced hv hp) :=
      (hasZS_iff_bcRelation bc _ (V k 0) (V k 1)
        (fun b => mkH1_traceLeft φ z (V k) (prevOf V k) hforced hv hp b)
        (fun b => mkH1_traceRight φ z (V k) (prevOf V k) hforced hv hp b)).2 hbc
    have hFu : h1PairValue (mkH1 φ z (V k) (prevOf V k) hforced hv hp) = W k := by
      refine PiLp.ext fun b => Lp.ext ?_
      filter_upwards [mkH1_value_ae φ z (V k) (prevOf V k) hforced hv hp b, hW k hk b]
        with t h1 h2
      change (mkH1 φ z (V k) (prevOf V k) hforced hv hp b).value t = (W k).ofLp b t
      rw [h1, h2]
    have hA := mkH1_zsApply φ z (V k) (prevOf V k) hforced hv hp (prevSP W k) hpw
    rw [hFu] at hA
    exact opStep_of_h1 φ bc z (W k) (prevSP W k) _ hFbc hFu hA


/-! ### H  M4: the Jordan-chain / Taylor-chain correspondence -/

theorem pairUniq (φ : PotPair) (z : ℂ) : PairUniq φ z :=
  fun _ hf _ ht => pairSolution_eq_Mext hf ht

/-- **M4 (set level).** `W` is an ascending Jordan chain of length `N` of the `bc`-realization
at `z0` iff there is `c ∈ K_N` with `W_k = [t ↦ ∑_{i ≤ k} M_i(t) c_{k-i}]` a.e., `k < N`. -/
theorem opChain_iff_tayKer (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ)
    (W : ℕ → SourcePairL2) :
    IsOpChain (zsRealization (intervalPotential φ) bc) z0 N W ↔
      ∃ c ∈ tayKer bc φ z0 N, ∀ k < N, ∀ b : Bool,
        (fun t => W k b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
          fun t => chainFun φ z0 c k t (pairIdx b) := by
  rw [opChain_iff]
  constructor
  · rintro ⟨V, hV, hW⟩
    obtain ⟨c, hc, -, hVc⟩ := (tay_chain_correspondence bc φ z0 (pairUniq φ z0) N).2 V hV
    refine ⟨c, hc, fun k hk b => ?_⟩
    filter_upwards [hW k hk b, ae_restrict_mem measurableSet_Ioc] with t h1 hmem
    rw [h1, hVc k hk t ⟨hmem.1.le, hmem.2⟩]
  · rintro ⟨c, hc, hW⟩
    exact ⟨chainFun φ z0 c, ((tay_chain_correspondence bc φ z0 (pairUniq φ z0) N).1 c hc).1, hW⟩

/-- The class of `t ↦ W_k(t)` for the chain function of `c`. -/
def chainClass (φ : PotPair) (z0 : ℂ) {N : ℕ} (c : Fin N → PairVec38) (k : ℕ) : SourcePairL2 :=
  WithLp.toLp 2 (fun b : Bool =>
    (memLp_two_of_continuousOn
      (continuousOn_Icc_of_ac ((chainFun_forced φ z0 c k).1 (pairIdx b)))).toLp
      (fun t => chainFun φ z0 c k t (pairIdx b)))

theorem chainClass_ae (φ : PotPair) (z0 : ℂ) {N : ℕ} (c : Fin N → PairVec38) (k : ℕ)
    (b : Bool) :
    (fun t => chainClass φ z0 c k b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun t => chainFun φ z0 c k t (pairIdx b) :=
  (memLp_two_of_continuousOn
    (continuousOn_Icc_of_ac ((chainFun_forced φ z0 c k).1 (pairIdx b)))).coeFn_toLp

/-- `c ↦ (chainClass c k)_{k<N}`. -/
def chainMap (φ : PotPair) (z0 : ℂ) (N : ℕ) :
    (Fin N → PairVec38) →ₗ[ℂ] (Fin N → SourcePairL2) where
  toFun c := fun k => chainClass φ z0 c k.val
  map_add' c d := by
    funext k
    refine PiLp.ext fun b => Lp.ext ?_
    filter_upwards [chainClass_ae φ z0 (c + d) k b, chainClass_ae φ z0 c k b,
      chainClass_ae φ z0 d k b,
      Lp.coeFn_add (chainClass φ z0 c k b) (chainClass φ z0 d k b)] with t h1 h2 h3 h4
    change chainClass φ z0 (c + d) k b t =
      (chainClass φ z0 c k b + chainClass φ z0 d k b) t
    rw [h1, h4, Pi.add_apply, h2, h3, chainFun_add]
    rfl
  map_smul' r c := by
    funext k
    refine PiLp.ext fun b => Lp.ext ?_
    filter_upwards [chainClass_ae φ z0 (r • c) k b, chainClass_ae φ z0 c k b,
      Lp.coeFn_smul r (chainClass φ z0 c k b)] with t h1 h2 h4
    change chainClass φ z0 (r • c) k b t = (r • chainClass φ z0 c k b) t
    rw [h1, h4, Pi.smul_apply, h2, chainFun_smul]
    rfl

theorem chainMap_injective (φ : PotPair) (z0 : ℂ) (N : ℕ) :
    Function.Injective (chainMap φ z0 N) := by
  intro c c' h
  funext k
  have hk : chainClass φ z0 c k.val = chainClass φ z0 c' k.val := congrFun h k
  have key : ∀ b : Bool, ∀ t ∈ Icc (0 : ℝ) 1,
      chainFun φ z0 c k t (pairIdx b) = chainFun φ z0 c' k t (pairIdx b) := by
    intro b
    have hae : (fun t => chainFun φ z0 c k t (pairIdx b)) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
        (fun t => chainFun φ z0 c' k t (pairIdx b)) := by
      rw [← restrict_Ioc_eq_restrict_Icc]
      filter_upwards [chainClass_ae φ z0 c k b, chainClass_ae φ z0 c' k b] with t h1 h2
      rw [← h1, ← h2, hk]
    exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hae
      (continuousOn_Icc_of_ac ((chainFun_forced φ z0 c k).1 (pairIdx b)))
      (continuousOn_Icc_of_ac ((chainFun_forced φ z0 c' k).1 (pairIdx b)))
  have h0 : chainFun φ z0 c k 0 = chainFun φ z0 c' k 0 := by
    funext i
    fin_cases i
    · exact key true 0 ⟨le_rfl, zero_le_one⟩
    · exact key false 0 ⟨le_rfl, zero_le_one⟩
  rw [chainFun_zero_time, chainFun_zero_time, cget_of_lt c k.2, cget_of_lt c' k.2] at h0
  exact h0

/-- Padded access to a finite chain. -/
def fget {N : ℕ} (W : Fin N → SourcePairL2) (j : ℕ) : SourcePairL2 :=
  if h : j < N then W ⟨j, h⟩ else 0

theorem fget_of_lt {N : ℕ} (W : Fin N → SourcePairL2) {j : ℕ} (hj : j < N) :
    fget W j = W ⟨j, hj⟩ := by
  simp [fget, hj]

theorem chainMap_mem_iff (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ)
    (W : Fin N → SourcePairL2) :
    W ∈ LinearMap.range ((chainMap φ z0 N).comp (tayKer bc φ z0 N).subtype) ↔
      IsOpChain (zsRealization (intervalPotential φ) bc) z0 N (fget W) := by
  rw [opChain_iff_tayKer]
  constructor
  · rintro ⟨⟨c, hc⟩, rfl⟩
    refine ⟨c, hc, fun k hk b => ?_⟩
    rw [fget_of_lt _ hk]
    exact chainClass_ae φ z0 c k b
  · rintro ⟨c, hc, hW⟩
    refine ⟨⟨c, hc⟩, ?_⟩
    funext k
    refine PiLp.ext fun b => Lp.ext ?_
    filter_upwards [chainClass_ae φ z0 c k b, hW k k.2 b] with t h1 h2
    rw [fget_of_lt _ k.2] at h2
    change chainClass φ z0 c k b t = W k b t
    rw [h1, h2]

/-- The space of ascending Jordan chains of length `N` (in `Fin N → SourcePairL2`), defined
intrinsically by `IsOpChain`; it is a submodule by `chainMap_mem_iff`. -/
def opChainSpace (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ) :
    Submodule ℂ (Fin N → SourcePairL2) :=
  (LinearMap.range ((chainMap φ z0 N).comp (tayKer bc φ z0 N).subtype)).copy
    {W | IsOpChain (zsRealization (intervalPotential φ) bc) z0 N (fget W)}
    (by ext W; exact (chainMap_mem_iff φ bc z0 N W).symm)

theorem mem_opChainSpace (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ)
    (W : Fin N → SourcePairL2) :
    W ∈ opChainSpace φ bc z0 N ↔
      IsOpChain (zsRealization (intervalPotential φ) bc) z0 N (fget W) := Iff.rfl

/-- **M4 (linear equivalence).** `K_N ≃ₗ` the space of Jordan chains of length `N`
(`c ↦ (t ↦ ∑_{i ≤ k} M_i(t) c_{k-i})_k`). -/
def tayChainEquiv (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ) :
    tayKer bc φ z0 N ≃ₗ[ℂ] opChainSpace φ bc z0 N :=
  (LinearEquiv.ofInjective ((chainMap φ z0 N).comp (tayKer bc φ z0 N).subtype)
    (fun _ _ h => Subtype.ext (chainMap_injective φ z0 N h))).trans
    (LinearEquiv.ofEq _ _ (Submodule.copy_eq _ _ _).symm)

theorem finrank_tayKer_eq (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ) :
    Module.finrank ℂ (tayKer bc φ z0 N) = Module.finrank ℂ (opChainSpace φ bc z0 N) :=
  (tayChainEquiv φ bc z0 N).finrank_eq


/-! ### I  Ascending chains versus the descending `rootVector` of the head -/

theorem rootVector_iff_opChain (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ)
    (v : SourcePairL2) :
    rootVector A z v ↔
      ∃ (N : ℕ) (W : ℕ → SourcePairL2), IsOpChain A z N W ∧
        v = if N = 0 then 0 else W (N - 1) := by
  constructor
  · rintro ⟨N, w, h0, hN, hstep⟩
    refine ⟨N, fun k => w (N - 1 - k), fun k hk => ?_, ?_⟩
    · obtain ⟨hj, hA⟩ := hstep (N - 1 - k) (by omega)
      refine ⟨hj, ?_⟩
      rw [hA]
      cases k with
      | zero =>
        have : N - 1 - 0 + 1 = N := by omega
        rw [this, hN]
        rfl
      | succ k' =>
        have : N - 1 - (k' + 1) + 1 = N - 1 - k' := by omega
        rw [this]
        rfl
    · by_cases hN0 : N = 0
      · subst hN0
        simp [← h0, hN]
      · simp only [hN0, if_false]
        have : N - 1 - (N - 1) = 0 := by omega
        rw [this, h0]
  · rintro ⟨N, W, hW, hv⟩
    by_cases hN0 : N = 0
    · subst hN0
      refine ⟨0, fun _ => 0, ?_, rfl, fun j hj => absurd hj (by omega)⟩
      simpa using hv.symm
    · refine ⟨N, fun j => if j < N then W (N - 1 - j) else 0, ?_, ?_, ?_⟩
      · simp only [Nat.pos_of_ne_zero hN0, if_true, hN0, if_false] at hv ⊢
        rw [hv, Nat.sub_zero]
      · simp
      · intro j hj
        obtain ⟨hk, hA⟩ := hW (N - 1 - j) (by omega)
        simp only [hj, if_true]
        refine ⟨hk, ?_⟩
        rw [hA]
        by_cases hj1 : j + 1 < N
        · simp only [hj1, if_true]
          have : N - 1 - j = (N - 1 - (j + 1)) + 1 := by omega
          rw [this]
          rfl
        · have h1 : N - 1 - j = 0 := by omega
          simp only [hj1, if_false]
          rw [h1]
          rfl

end
end NlsGge.Atomic.G1104Jor
