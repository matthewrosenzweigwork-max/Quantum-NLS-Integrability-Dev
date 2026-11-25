import Mathlib
import QuantumNLS.LossSeries

/-!
# R-8C922B25 `lem:loss` — Differentiability with loss of Sobolev order (`chapters/core/DYNAMICS_LEMMAS.tex:13`)

Printed statement.  Let `X` be a Banach space and `(Y^s)_{s≥0}` a Hilbert scale with continuous injective embeddings and the interpolation inequality
`‖y‖_{Y^q} ≤ ‖y‖_{Y^0}^{1−q/S} ‖y‖_{Y^S}^{q/S}` (`0 < q < S`).  Let `U ⊂ X` be open, `k ≥ 1`, `S > (k+1)q > 0`, `f : U → Y^0` of class `C^{k+1}` with values in
`Y^S` of locally bounded `Y^S` norm.  Then `f : U → Y^q` is `C^k`, its derivatives are the same derivatives as in `Y^0` now taking values in `Y^q`, and every
derivative of order `≤ k` has locally bounded multilinear operator norm in this stronger target; the bounds are uniform near a compact subset of `U`.

Formalization (all real: "all derivatives and multilinear spaces below are real"):
* `InterpScale`: levels `Y s` (`s : ℝ≥0`) real Banach spaces (every Hilbert scale is one; completeness is the only use of the Hilbert structure), continuous linear
  embeddings `emb s t : Y s → Y t` (`t ≤ s`), injective, compatible, with the printed interpolation inequality;
* `loss`: `ContDiffOn ℝ k (emb S q ∘ g) U`; `emb q 0 (D^j (emb S q ∘ g)(x) v) = D^j f (x) v` for `j ≤ k`; local bounds of `‖D^j (emb S q ∘ g)‖`;
* `loss_uniform`: the bounds are uniform on a neighbourhood of every compact `K ⊆ U`.
Proof: the finite-difference route of the printed proof (parts 1-5: `LossDifference`, `LossLift`, `LossDyadic`, `LossMult`, `LossSeries`), mixed differences so that no
polarization is needed; the intermediate level `p = (q + S/(k+1))/2` plays the role of the printed `q'`.  The only external fact is the printed interpolation
inequality (hypothesis of the scale); no EXT-025 contract is used by the abstract lemma, and the complex-Banach holomorphic clause C2 of DEF-017 is not needed
(the lemma is a `C^{k+1}` statement; real analytic maps are `C^∞`).
-/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
open scoped ContDiff NNReal
open Filter Topology Set Metric
noncomputable section
namespace QuantumNLS.Loss

theorem nn_zero_le (s : ℝ≥0) : (0 : ℝ≥0) ≤ s := bot_le

/-- A scale with continuous injective embeddings and the interpolation inequality. -/
structure InterpScale where
  Y : ℝ≥0 → Type
  [instN : ∀ s, NormedAddCommGroup (Y s)]
  [instS : ∀ s, NormedSpace ℝ (Y s)]
  [instC : ∀ s, CompleteSpace (Y s)]
  emb : ∀ s t : ℝ≥0, t ≤ s → (Y s →L[ℝ] Y t)
  emb_inj : ∀ (s t : ℝ≥0) (h : t ≤ s), Function.Injective (emb s t h)
  emb_comp : ∀ (s t r : ℝ≥0) (h1 : t ≤ s) (h2 : r ≤ t) (y : Y s),
    emb t r h2 (emb s t h1 y) = emb s r (h2.trans h1) y
  interp : ∀ (q S : ℝ≥0) (hq : 0 < q) (hqS : q < S) (y : Y S),
    ‖emb S q hqS.le y‖ ≤ ‖emb S 0 (nn_zero_le S) y‖ ^ (1 - (q : ℝ) / S) * ‖y‖ ^ ((q : ℝ) / S)

attribute [instance] InterpScale.instN InterpScale.instS InterpScale.instC

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **`lem:loss`** (differentiability with loss of Sobolev order). -/
theorem loss (𝒴 : InterpScale) [CompleteSpace X] {U : Set X} (hU : IsOpen U) {k : ℕ} (hk : 1 ≤ k)
    {q S : ℝ≥0} (hq : 0 < q) (hS : ((k : ℝ) + 1) * q < S) (hqS : q ≤ S)
    (f : X → 𝒴.Y 0) (hf : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) f U)
    (g : X → 𝒴.Y S) (hfg : ∀ x ∈ U, f x = 𝒴.emb S 0 (nn_zero_le S) (g x))
    (hg : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ y ∈ U, dist y x < r → ‖g y‖ ≤ M) :
    ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (fun x => 𝒴.emb S q hqS (g x)) U ∧
      (∀ j ≤ k, ∀ x ∈ U, ∀ v : Fin j → X,
        𝒴.emb q 0 (nn_zero_le q) (iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x v) =
          iteratedFDeriv ℝ j f x v) ∧
      (∀ x0 ∈ U, ∃ r > 0, ∃ B : ℝ, ∀ x ∈ ball x0 r, ∀ j ≤ k,
        ‖iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x‖ ≤ B) := by
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hSr : (0 : ℝ) < S := by
    have : (0 : ℝ) < ((k : ℝ) + 1) * q := by positivity
    linarith
  -- the intermediate level p = (q + S/(k+1))/2
  have hqlt : (q : ℝ) < (S : ℝ) / ((k : ℝ) + 1) := by rw [lt_div_iff₀ hkpos]; linarith
  let pr : ℝ := ((q : ℝ) + (S : ℝ) / ((k : ℝ) + 1)) / 2
  have hpr0 : 0 ≤ pr := by positivity
  let p : ℝ≥0 := ⟨pr, hpr0⟩
  have hpR : (p : ℝ) = pr := rfl
  have hqp_r : (q : ℝ) < p := by rw [hpR]; simp only [pr]; linarith
  have hqp : q < p := by exact_mod_cast hqp_r
  have hpS_r : ((k : ℝ) + 1) * p < S := by
    rw [hpR]; simp only [pr]
    have : ((k : ℝ) + 1) * (((q : ℝ) + (S : ℝ) / ((k : ℝ) + 1)) / 2) =
        (((k : ℝ) + 1) * q + S) / 2 := by field_simp
    rw [this]; linarith
  have hpS : p ≤ S := by
    have : (p : ℝ) ≤ S := by nlinarith [hpS_r, NNReal.coe_nonneg p, Nat.cast_nonneg (α := ℝ) k]
    exact_mod_cast this
  have hp0r : (0 : ℝ) < p := hqr.trans hqp_r
  have hp0 : 0 < p := by exact_mod_cast hp0r
  have hpSlt : p < S := by
    have : (p : ℝ) < S := by nlinarith [hpS_r, Nat.cast_nonneg (α := ℝ) k]
    exact_mod_cast this
  set θ : ℝ := (p : ℝ) / S with hθ
  set θ' : ℝ := (q : ℝ) / p with hθ'
  have hθ0 : 0 < θ := by positivity
  have hθ'0 : 0 < θ' := by positivity
  have hθ'1 : θ' < 1 := by rw [hθ', div_lt_one hp0r]; exact hqp_r
  have hkθ : ((k : ℝ) + 1) * θ < 1 := by
    rw [hθ, ← mul_div_assoc, div_lt_one hSr]; exact hpS_r
  -- the embeddings
  let ιSp := 𝒴.emb S p hpS
  let ιp0 := 𝒴.emb p 0 (nn_zero_le p)
  let ιpq := 𝒴.emb p q hqp.le
  let ιq0 := 𝒴.emb q 0 (nn_zero_le q)
  have hcomp : ∀ z, ιq0 (ιpq z) = ιp0 z := fun z => 𝒴.emb_comp p q 0 hqp.le (nn_zero_le q) z
  have hS0 : ∀ y, ιp0 (ιSp y) = 𝒴.emb S 0 (nn_zero_le S) y := fun y => 𝒴.emb_comp S p 0 hpS (nn_zero_le p) y
  have hSq : ∀ y, ιpq (ιSp y) = 𝒴.emb S q hqS y := fun y => 𝒴.emb_comp S p q hpS hqp.le y
  have hint1 : ∀ y : 𝒴.Y S, ‖ιSp y‖ ≤ ‖ιp0 (ιSp y)‖ ^ (1 - θ) * ‖y‖ ^ θ := by
    intro y
    rw [hS0]
    exact 𝒴.interp p S hp0 hpSlt y
  have hint2 : ∀ z : 𝒴.Y p, ‖ιpq z‖ ≤ ‖ιp0 z‖ ^ (1 - θ') * ‖z‖ ^ θ' := fun z => 𝒴.interp q p hq hqp z
  have hM : ∀ x0 ∈ U, ∃ r > 0, ball x0 r ⊆ U ∧ ∃ M : ℝ, ∀ y ∈ ball x0 r, ‖g y‖ ≤ M := by
    intro x0 hx0
    obtain ⟨r1, hr1, M, hM⟩ := hg x0 hx0
    obtain ⟨r2, hr2, hb2⟩ := Metric.isOpen_iff.1 hU x0 hx0
    refine ⟨min r1 r2, lt_min hr1 hr2, (Metric.ball_subset_ball (min_le_right _ _)).trans hb2, M, fun y hy => ?_⟩
    have hy2 : y ∈ ball x0 r2 := Metric.ball_subset_ball (min_le_right _ _) hy
    exact hM y (hb2 hy2) (lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _))
  have hP0 := hf.ftaylorSeriesWithin hU.uniqueDiffOn
  have hP : HasFTaylorSeriesUpToOn ((k + 1 : ℕ) : ℕ∞ω) (fun x => ιp0 (ιSp (g x))) (ftaylorSeriesWithin ℝ f U) U :=
    hP0.congr (fun x hx => by rw [hS0, hfg x hx])
  obtain ⟨V, hVt, hVv, hVb⟩ := loss_taylor ιSp ιp0 ιpq ιq0 (𝒴.emb_inj p 0 _) (𝒴.emb_inj q 0 _) hcomp hθ0 hθ'0 hθ'1 hkθ
    hint1 hint2 hU g hM (ftaylorSeriesWithin ℝ f U) hP
  have hVt' : HasFTaylorSeriesUpToOn ((k : ℕ) : ℕ∞ω) (fun x => 𝒴.emb S q hqS (g x)) V U :=
    hVt.congr (fun x hx => (hSq (g x)).symm)
  have hVeq : ∀ j ≤ k, ∀ x ∈ U, V x j = iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x := fun j hj x hx => by
    rw [hVt'.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hj) hU.uniqueDiffOn hx]
    exact iteratedFDerivWithin_of_isOpen j hU hx
  refine ⟨hVt'.contDiffOn, ?_, ?_⟩
  · intro j hj x hx v
    rw [← hVeq j hj x hx, hVv x hx j hj v]
    exact congrArg (fun T => T v) (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) j hU hx)
  · intro x0 hx0
    obtain ⟨r, hr, hb, B, hB⟩ := hVb x0 hx0
    refine ⟨r, hr, B, fun x hx j hj => ?_⟩
    rw [← hVeq j hj x (hb hx)]
    exact hB x hx j hj

/-- Local bounds on a compact set are uniform on a neighbourhood of it (finite subcover). -/
theorem uniform_of_local {Φ : X → ℝ} {K : Set X} (hK : IsCompact K)
    (hloc : ∀ x0 ∈ K, ∃ r > 0, ∃ B : ℝ, ∀ x ∈ ball x0 r, Φ x ≤ B) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∃ B : ℝ, ∀ x ∈ V, Φ x ≤ B := by
  choose! r hr B hB using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => ball x (r x))
    (fun x hx => Metric.ball_mem_nhds x (hr x hx))
  refine ⟨⋃ x ∈ t, ball x (r x), isOpen_biUnion (fun x _ => Metric.isOpen_ball), hcov, ∑ x ∈ t, |B x|, ?_⟩
  intro z hz
  obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.1 hz
  exact (hB x (htK x hxt) z hzx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |B x|) (fun i _ => abs_nonneg _) hxt))

/-- **`lem:loss`, uniform version** ("all bounds can be chosen uniformly near a fixed compact subset"). -/
theorem loss_uniform (𝒴 : InterpScale) [CompleteSpace X] {U : Set X} (hU : IsOpen U) {k : ℕ} (hk : 1 ≤ k)
    {q S : ℝ≥0} (hq : 0 < q) (hS : ((k : ℝ) + 1) * q < S) (hqS : q ≤ S)
    (f : X → 𝒴.Y 0) (hf : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) f U)
    (g : X → 𝒴.Y S) (hfg : ∀ x ∈ U, f x = 𝒴.emb S 0 (nn_zero_le S) (g x))
    (hg : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ y ∈ U, dist y x < r → ‖g y‖ ≤ M)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∃ B : ℝ, ∀ x ∈ V, ∀ j ≤ k,
      ‖iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x‖ ≤ B := by
  obtain ⟨-, -, hb⟩ := loss 𝒴 hU hk hq hS hqS f hf g hfg hg
  obtain ⟨V, hVo, hKV, B, hB⟩ := uniform_of_local (Φ := fun x => ∑ j ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x‖) hK (fun x0 hx0 => by
    obtain ⟨r, hr, B, hB⟩ := hb x0 (hKU hx0)
    refine ⟨r, hr, (k + 1) * B, fun x hx => ?_⟩
    calc ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x‖
        ≤ ∑ _j ∈ Finset.range (k + 1), B :=
          Finset.sum_le_sum (fun j hj => hB x hx j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
      _ = (k + 1) * B := by simp)
  refine ⟨V, hVo, hKV, B, fun x hx j hj => ?_⟩
  exact (Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x‖)
    (fun i _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))).trans (hB x hx)

end QuantumNLS.Loss

#print axioms QuantumNLS.Loss.loss
#print axioms QuantumNLS.Loss.loss_uniform
