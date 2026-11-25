import Mathlib
import QuantumNLS.LossMult
import QuantumNLS.LossLift

/-!
# R-8C922B25 `lem:loss` (`DYNAMICS_LEMMAS.tex:13`), part 5: the `Y^q`-valued Taylor series

Abstract form of the printed proof on four levels `W = Y^S`, `Z = Y^p`, `Zq = Y^q`, `F = Y^0` (`q < p`, `(k+1)p < S`), with continuous injective embeddings
`ιp0, ιq0` into `F`, `ιSp : W → Z`, `ιpq : Z → Zq`, and `ιq0 ∘ ιpq = ιp0`.  Given `g : X → W` locally bounded in `W` with `f = ιp0 ∘ ιSp ∘ g` carrying a Taylor series `P`
up to order `k+1` on the open set `U` (`f ∈ C^{k+1}` into `Y^0`), `loss_taylor` produces a Taylor series `V` up to order `k` of `ιpq ∘ ιSp ∘ g` into `Zq`
(so `f ∈ C^k` into `Y^q`), whose coefficients are those of `P` (`ιq0 (V x j v) = P x j v`) with local operator-norm bounds:
* local data: bounds of `g` and of `P x m` (`m ≤ k+1`) on a ball (continuity of the low-regularity derivatives);
* `dyadic_lift` (part 3) and `lift_multilinear` (part 4): the coefficient `P x j` lifts uniquely to `T0 x j` in `L^j(X; Z)` with a local bound;
* continuity of `x ↦ V x j` in `L^j(X; Zq)` by `mult_interp` (printed: "interpolation ... the right side tends to zero as `y → x`");
* `lift_hasFDerivAt` (part 2) turns the `Y^0`-derivative relation into the `Zq`-derivative relation (printed: FTC in `Y^0`, integral in `Y^q`, injectivity).
Mathlib only; no EXT-025 contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
open scoped ContDiff
open Filter Topology Set Metric
noncomputable section
namespace QuantumNLS.Loss

variable {X F Z Zq W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z] [NormedAddCommGroup Zq] [NormedSpace ℝ Zq]
  [CompleteSpace Zq] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem loss_taylor (ιSp : W →L[ℝ] Z) (ιp0 : Z →L[ℝ] F) (ιpq : Z →L[ℝ] Zq) (ιq0 : Zq →L[ℝ] F)
    (hp0 : Function.Injective ιp0) (hq0 : Function.Injective ιq0) (hcomp : ∀ z, ιq0 (ιpq z) = ιp0 z)
    {θ θ' : ℝ} (hθ0 : 0 < θ) (hθ'0 : 0 < θ') (hθ'1 : θ' < 1) {k : ℕ} (hkθ : ((k : ℝ) + 1) * θ < 1)
    (hint1 : ∀ y : W, ‖ιSp y‖ ≤ ‖ιp0 (ιSp y)‖ ^ (1 - θ) * ‖y‖ ^ θ)
    (hint2 : ∀ z : Z, ‖ιpq z‖ ≤ ‖ιp0 z‖ ^ (1 - θ') * ‖z‖ ^ θ')
    {U : Set X} (hU : IsOpen U) (g : X → W)
    (hM : ∀ x0 ∈ U, ∃ r > 0, ball x0 r ⊆ U ∧ ∃ M, ∀ y ∈ ball x0 r, ‖g y‖ ≤ M)
    (P : X → FormalMultilinearSeries ℝ X F)
    (hP : HasFTaylorSeriesUpToOn ((k + 1 : ℕ) : ℕ∞ω) (fun x => ιp0 (ιSp (g x))) P U) :
    ∃ V : X → FormalMultilinearSeries ℝ X Zq,
      HasFTaylorSeriesUpToOn ((k : ℕ) : ℕ∞ω) (fun x => ιpq (ιSp (g x))) V U ∧
      (∀ x ∈ U, ∀ j ≤ k, ∀ v, ιq0 (V x j v) = P x j v) ∧
      ∀ x0 ∈ U, ∃ r > 0, ball x0 r ⊆ U ∧ ∃ B : ℝ, ∀ x ∈ ball x0 r, ∀ j ≤ k, ‖V x j‖ ≤ B := by
  have hθ1 : θ < 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  -- Step 1: local lifts
  have hloc : ∀ x0 ∈ U, ∃ r > 0, ball x0 r ⊆ U ∧ ∃ B : ℝ, ∀ x ∈ ball x0 r, ∀ j ≤ k,
      ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) Z, (∀ v, ιp0 (T v) = P x j v) ∧ ‖T‖ ≤ B := by
    intro x0 hx0
    obtain ⟨r1, hr1, hball1, M, hMb⟩ := hM x0 hx0
    have hev : ∀ᶠ y in 𝓝 x0, ∀ m ∈ Finset.range (k + 2), ‖P y m‖ < ‖P x0 m‖ + 1 := by
      refine (Filter.eventually_all_finset (Finset.range (k + 2))).2 (fun m hm => ?_)
      have hmk : (m : ℕ∞ω) ≤ ((k + 1 : ℕ) : ℕ∞ω) := by
        have := Finset.mem_range.1 hm
        exact_mod_cast (by omega : m ≤ k + 1)
      have hc := (hP.cont m hmk).continuousAt (hU.mem_nhds hx0)
      exact hc.norm.eventually (gt_mem_nhds (by linarith))
    obtain ⟨r2, hr2, hr2b⟩ := Metric.eventually_nhds_iff.1 hev
    set r := min r1 r2 with hr
    have hrpos : 0 < r := lt_min hr1 hr2
    have hrb1 : ball x0 r ⊆ ball x0 r1 := Metric.ball_subset_ball (min_le_left _ _)
    set C : ℝ := ∑ m ∈ Finset.range (k + 2), (‖P x0 m‖ + 1) with hC
    have hCb : ∀ y ∈ ball x0 r, ∀ m ≤ k + 1, ‖P y m‖ ≤ C := by
      intro y hy m hm
      have hy2 : dist y x0 < r2 := lt_of_lt_of_le (mem_ball.1 hy) (min_le_right _ _)
      have h1 := hr2b hy2 m (Finset.mem_range.2 (by omega))
      have h2 : ‖P x0 m‖ + 1 ≤ C := Finset.single_le_sum (f := fun m => ‖P x0 m‖ + 1)
        (fun i _ => by positivity) (Finset.mem_range.2 (by omega))
      linarith
    have hMb' : ∀ y ∈ ball x0 r, ‖g y‖ ≤ M := fun y hy => hMb y (hrb1 hy)
    have hlift : ∀ j : Fin (k + 1), ∃ B : ℝ, ∀ x ∈ ball x0 (r / 2), ∀ v : Fin j → X, (∀ i, ‖v i‖ ≤ 1) →
        ∃ L : Z, ιp0 L = P x j v ∧ ‖L‖ ≤ B := fun j => by
      have hj : (j : ℕ) ≤ k := Nat.lt_succ_iff.1 j.2
      have hjθ : (((j : ℕ) : ℝ) + 1) * θ < 1 := by
        have : ((j : ℕ) : ℝ) ≤ k := by exact_mod_cast hj
        nlinarith
      exact dyadic_lift ιSp ιp0 hθ0 hθ1 hint1 g P hP hrpos (hrb1.trans hball1) hMb' (j : ℕ) hj hjθ
        (A := C) (C := C) (fun y hy => hCb y hy ((j : ℕ) + 1) (by omega))
        (fun y hy => hCb y hy (j : ℕ) (by omega))
    choose Bj hBj using hlift
    refine ⟨r / 2, by positivity, (Metric.ball_subset_ball (by linarith)).trans (hrb1.trans hball1),
      ∑ j, |Bj j|, fun x hx j hj => ?_⟩
    have hjj : j < k + 1 := Nat.lt_succ_of_le hj
    obtain ⟨T, hT1, hT2⟩ := lift_multilinear ιp0 hp0 (P x j) (Bj ⟨j, hjj⟩) (hBj ⟨j, hjj⟩ x hx)
    refine ⟨T, hT1, hT2.trans ?_⟩
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Bj j|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ (⟨j, hjj⟩ : Fin (k + 1))))
  -- Step 2: the unique lifts
  classical
  let T0 : (x : X) → (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => X) Z := fun x j =>
    if h : ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) Z, ∀ v, ιp0 (T v) = P x j v then h.choose else 0
  have hT0spec : ∀ x j (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) Z),
      (∀ v, ιp0 (T v) = P x j v) → T0 x j = T := by
    intro x j T hT
    have hex : ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) Z, ∀ v, ιp0 (T v) = P x j v := ⟨T, hT⟩
    simp only [T0, dif_pos hex]
    ext v
    apply hp0
    rw [hex.choose_spec v, hT v]
  have hT0lift : ∀ x ∈ U, ∀ j ≤ k, ∀ v, ιp0 (T0 x j v) = P x j v := by
    intro x hx j hj v
    obtain ⟨r, hr, -, B, hB⟩ := hloc x hx
    obtain ⟨T, hT1, -⟩ := hB x (mem_ball_self hr) j hj
    rw [hT0spec x j T hT1]; exact hT1 v
  have hT0bound : ∀ x0 ∈ U, ∃ r > 0, ball x0 r ⊆ U ∧ ∃ B : ℝ, ∀ x ∈ ball x0 r, ∀ j ≤ k, ‖T0 x j‖ ≤ B := by
    intro x0 hx0
    obtain ⟨r, hr, hb, B, hB⟩ := hloc x0 hx0
    refine ⟨r, hr, hb, B, fun x hx j hj => ?_⟩
    obtain ⟨T, hT1, hT2⟩ := hB x hx j hj
    rw [hT0spec x j T hT1]; exact hT2
  let V : X → FormalMultilinearSeries ℝ X Zq := fun x j => ιpq.compContinuousMultilinearMap (T0 x j)
  have hV : ∀ x ∈ U, ∀ j ≤ k, ∀ v, ιq0 (V x j v) = P x j v := by
    intro x hx j hj v
    show ιq0 (ιpq (T0 x j v)) = _
    rw [hcomp, hT0lift x hx j hj v]
  -- continuity
  have hcont : ∀ m ≤ k, ContinuousOn (fun x => V x m) U := by
    intro m hm x0 hx0
    apply ContinuousAt.continuousWithinAt
    obtain ⟨r, hr, hb, B, hB⟩ := hT0bound x0 hx0
    have hPc : ContinuousAt (fun y => P y m) x0 :=
      (hP.cont m (by exact_mod_cast (by omega : m ≤ k + 1))).continuousAt (hU.mem_nhds hx0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x0 (mem_ball_self hr) m hm)
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hP0 : Tendsto (fun y => ‖P y m - P x0 m‖) (𝓝 x0) (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hPc
    have hrp : Tendsto (fun y => ‖P y m - P x0 m‖ ^ (1 - θ') * (2 * B) ^ θ') (𝓝 x0) (𝓝 0) := by
      have h1 := ((Real.continuous_rpow_const (by linarith : 0 ≤ 1 - θ')).tendsto 0).comp hP0
      rw [Real.zero_rpow (by linarith : (1 - θ') ≠ 0)] at h1
      simpa using h1.mul_const ((2 * B) ^ θ')
    refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ hrp
    filter_upwards [Metric.ball_mem_nhds x0 hr] with y hy
    have hyU : y ∈ U := hb hy
    have hdiff : V y m - V x0 m = ιpq.compContinuousMultilinearMap (T0 y m - T0 x0 m) := by
      ext v; simp [V]
    have hp0eq : ιp0.compContinuousMultilinearMap (T0 y m - T0 x0 m) = P y m - P x0 m := by
      ext v
      simp [hT0lift y hyU m hm v, hT0lift x0 hx0 m hm v]
    have hmi := mult_interp ιpq ιp0 hθ'0 hθ'1 hint2 (T0 y m - T0 x0 m)
    rw [hp0eq] at hmi
    rw [hdiff]
    refine hmi.trans ?_
    have hD2 : ‖T0 y m - T0 x0 m‖ ≤ 2 * B := by
      calc _ ≤ ‖T0 y m‖ + ‖T0 x0 m‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hB y hy m hm) (hB x0 (mem_ball_self hr) m hm)
        _ = 2 * B := by ring
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hD2 hθ'0.le) (by positivity)
  -- derivatives
  have hfd : ∀ m < k, ∀ x ∈ U, HasFDerivWithinAt (fun y => V y m) ((V x (m + 1)).curryLeft) U x := by
    intro m hm x hx
    let ι : ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Zq →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin m => X) F :=
      ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => X) Zq F ιq0
    have hιapp : ∀ (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Zq) v, ι T v = ιq0 (T v) :=
      fun T v => rfl
    have hιinj : Function.Injective ι := by
      intro a b hab
      ext v
      apply hq0
      have := congrArg (fun T => T v) hab
      simpa [hιapp] using this
    have hAc : ContinuousOn (fun y => (V y (m + 1)).curryLeft) U := by
      have h1 := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) Zq).continuous.comp_continuousOn
        (hcont (m + 1) (by omega))
      refine h1.congr (fun y hy => ?_)
      ext u v
      simp [continuousMultilinearCurryLeftEquiv_apply, ContinuousMultilinearMap.curryLeft_apply]
    have hG : ∀ y ∈ U, HasFDerivAt (fun y => ι (V y m)) (ι.comp ((V y (m + 1)).curryLeft)) y := by
      intro y hy
      have h1 := (hP.fderivWithin m (by exact_mod_cast (by omega : m < k + 1)) y hy).hasFDerivAt
        (hU.mem_nhds hy)
      have hev : (fun z => P z m) =ᶠ[𝓝 y] (fun z => ι (V z m)) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz => by
          ext v; rw [hιapp]; exact (hV z hz m (by omega) v).symm)
      have h2 := h1.congr_of_eventuallyEq hev.symm
      refine h2.congr_fderiv ?_
      ext u v
      simp [hιapp, ContinuousMultilinearMap.curryLeft_apply, hV y hy (m + 1) (by omega)]
    exact (lift_hasFDerivAt ι hιinj hU (fun y => V y m) (fun y => (V y (m + 1)).curryLeft) hAc hG x hx).hasFDerivWithinAt
  have hzero : ∀ x ∈ U, (V x 0).curry0 = ιpq (ιSp (g x)) := by
    intro x hx
    have hT : T0 x 0 = ContinuousMultilinearMap.uncurry0 ℝ X (ιSp (g x)) := by
      apply hT0spec
      intro v
      have h0 := hP.zero_eq x hx
      have : P x 0 v = (P x 0).curry0 := by
        rw [ContinuousMultilinearMap.curry0_apply]; congr 1; exact Subsingleton.elim _ _
      rw [this, h0]
      simp
    simp [V, hT, ContinuousMultilinearMap.curry0_apply]
  refine ⟨V, ⟨hzero, fun m hm x hx => hfd m (by exact_mod_cast hm) x hx,
    fun m hm => hcont m (by exact_mod_cast hm)⟩, hV, ?_⟩
  intro x0 hx0
  obtain ⟨r, hr, hb, B, hB⟩ := hT0bound x0 hx0
  refine ⟨r, hr, hb, ‖ιpq‖ * B, fun x hx j hj => ?_⟩
  calc ‖V x j‖ ≤ ‖ιpq‖ * ‖T0 x j‖ := ιpq.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖ιpq‖ * B := mul_le_mul_of_nonneg_left (hB x hx j hj) (norm_nonneg _)

end QuantumNLS.Loss

#print axioms QuantumNLS.Loss.loss_taylor
