import Mathlib
import QuantumNLS.SmoothJ
import QuantumNLS.JLower
import QuantumNLS.IBridge
import QuantumNLS.WeakSubseq

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (I): compactness, identification of the limit and strong convergence

Source (F03.tex, end of the proof of `CC:F03:deterministic`): "The bound (CC:F03:finite-bound) makes the minimizers weakly precompact. The lower bound and a recovery sequence for the unique limiting minimizer imply that every weak limit is `F`
and `𝒥_N(F_N) → 𝒥(F)`. If `v_N` is that recovery sequence, quadratic completion at the finite minimizer gives `𝒥_N(v_N) − 𝒥_N(F_N) = (L/2)‖v_N − F_N‖² + (κ/2)ℰ_N(v_N − F_N) ≥ (L/2)‖v_N − F_N‖²`.
Its left side tends to zero, proving (CC:F03:bulk-limit). Finally (CC:F03:finite-bound), strong convergence of both `Q_N` and `F_N`, and (CC:F03:limit-bound) give convergence of the nonlocal energies as well."

Formal statement `strong_limit`: for measurable `Q ∈ L²(0,1)` with `{Q t = Q s}` null, the response `F` (`IsBulkResponse L κ Q F`), a core `S ⊆ {pullbacks of bounded Lipschitz functions}` (`IsFormCore`; the smooth pullbacks of `QuantileCore.isFormCore_bulk` qualify),
step quantiles `Q_N = stepF N q` with `‖Q_N − Q‖₂ → 0` and `F_N` the step function of the solution of `B_N v = q` (`Bop L (κ/N) q v = q`):
`‖F_N − F‖₂ → 0` and `ℰ_N(F_N) → 𝓔(F)` (`ENint`, the double integral).
(Only the printed route is used: weak compactness `WeakSubseq`, lower bound `JLower`, smooth recovery `SmoothJ` + core density at `F` instead of an explicit diagonal sequence, quadratic completion `IBridge`/`FiniteResponse.JN_sub_JN`.)
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace QuantumNLS.StrongLimit

open QuantumNLS.BulkResponseRiesz (mu2 ae_fst ae_snd inner_eq_integral ae_subseq)
open QuantumNLS.QuantileForm (uI formEnergy_congr)
open QuantumNLS.BulkResponseForm (L2Unit formEnergy IsBulkResponse IsFormCore formDomain bulkForm)
open QuantumNLS.GLowerBound (ENint)
open QuantumNLS.StepIntegrals (stepF stepL2 stepL2_ae measurable_stepF norm_sq_step inner_step ENint_step
  JN_step stepL2_sub)
open QuantumNLS.FiniteResponse (Bop L2N EN ipN JN response_bounds JN_sub_JN)
open QuantumNLS.SmoothJ (compL2 compL2_ae norm_compL2_sub_le smooth_J_tendsto stepL2_comp JN_comp ENint_congr_ae)
open QuantumNLS.IBridge (Jfun J_sub_J core_small)

theorem EN_nonneg (N : ℕ) (c : ℝ) (q v : Fin N → ℝ) : 0 ≤ EN N c q v := by
  unfold EN
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)

theorem L2N_nonneg (N : ℕ) (v : Fin N → ℝ) : 0 ≤ L2N N v := by
  unfold L2N
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem Fe_facts {N : ℕ} (hN : 0 < N) {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {q Fv : Fin N → ℝ}
    (hF : Bop L (κ / N) q Fv = q) :
    L * ‖stepL2 Fv‖ ≤ ‖stepL2 q‖ ∧
      κ * EN N (κ / N) q Fv = inner ℝ (stepL2 q) (stepL2 Fv) - L * ‖stepL2 Fv‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := response_bounds hL hκ hN hF
  have n1 := norm_sq_step hN Fv
  have n2 := norm_sq_step hN q
  have i := inner_step hN q Fv
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    have : ‖stepL2 q‖ ^ 2 < (L * ‖stepL2 Fv‖) ^ 2 :=
      pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
    rw [mul_pow, n1, n2] at this
    linarith
  · rw [i, n1]
    linarith

theorem ENint_Fe {N : ℕ} (hN : 0 < N) (c : ℝ) (q Fv : Fin N → ℝ) :
    ENint c (stepF N q) (stepL2 Fv : ℝ → ℝ) = ENNReal.ofReal (EN N c q Fv) :=
  (ENint_congr_ae (stepL2_ae Fv)).trans (ENint_step hN c q Fv)

theorem JN_Fe {N : ℕ} (hN : 0 < N) (L κ : ℝ) (q Fv : Fin N → ℝ) :
    JN L κ N q Fv = (L / 2) * ‖stepL2 Fv‖ ^ 2 + (κ / 2) * EN N (κ / N) q Fv -
      inner ℝ (stepL2 q) (stepL2 Fv) := by
  rw [JN_step hN, ENint_step hN, ENNReal.toReal_ofReal (EN_nonneg _ _ _ _)]

/-- Quadratic completion for the step functions. -/
theorem Jcompare {N : ℕ} (hN : 0 < N) {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {q Fv : Fin N → ℝ}
    (hF : Bop L (κ / N) q Fv = q) {h : ℝ → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) :
    (L / 2) * ‖compL2 hm hB (measurable_stepF q) - stepL2 Fv‖ ^ 2 ≤
      JN L κ N q (fun i => h (q i)) - JN L κ N q Fv := by
  rw [JN_sub_JN hL hκ hN hF, ← stepL2_comp hN hm hB q, ← stepL2_sub, norm_sq_step hN]
  have := EN_nonneg N (κ / N) q (fun i => h (q i) - Fv i)
  have h2 : (0 : ℝ) ≤ (κ / 2) * EN N (κ / N) q ((fun i => h (q i)) - Fv) := by
    apply mul_nonneg (by positivity)
    exact EN_nonneg _ _ _ _
  unfold L2N
  linarith

/-- Subsequence extraction: weak, norms/energies, almost-everywhere convergence. -/
theorem good_subseq {Fe : ℕ → L2Unit} {yy : ℕ → ℝ} {M Y : ℝ} (hM : ∀ n, ‖Fe n‖ ≤ M)
    (hY : ∀ n, 0 ≤ yy n ∧ yy n ≤ Y) {Qe : ℕ → L2Unit} {Q0 : L2Unit}
    (hQs : Tendsto Qe atTop (𝓝 Q0)) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, Tendsto ms atTop atTop ∧ ∃ (F' : L2Unit) (x y0 : ℝ),
      (∀ ψ : L2Unit, Tendsto (fun k => inner ℝ (Fe (ns (ms k))) ψ) atTop (𝓝 (inner ℝ F' ψ))) ∧
      Tendsto (fun k => ‖Fe (ns (ms k))‖ ^ 2) atTop (𝓝 x) ∧
      Tendsto (fun k => yy (ns (ms k))) atTop (𝓝 y0) ∧
      ∀ᵐ t ∂uI, Tendsto (fun k => (Qe (ns (ms k)) : ℝ → ℝ) t) atTop (𝓝 (Q0 t)) := by
  obtain ⟨φ1, hφ1, F', hw1⟩ :=
    QuantumNLS.WeakSubseq.exists_weak_subseq (fun k => Fe (ns k)) (M := M) (fun k => hM _)
  let r : ℕ → ℝ × ℝ := fun k => (‖Fe (ns (φ1 k))‖ ^ 2, yy (ns (φ1 k)))
  have hr : ∀ k, r k ∈ Metric.closedBall (0 : ℝ × ℝ) (max (M ^ 2) Y) := by
    intro k
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    have ha : ‖(r k).1‖ ≤ M ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hM _) 2
    have hb : ‖(r k).2‖ ≤ Y := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hY _).1]
      exact (hY _).2
    exact max_le_max ha hb
  obtain ⟨a, -, φ2, hφ2, hra⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hr
  have hQs2 : Tendsto (fun k => Qe (ns (φ1 (φ2 k)))) atTop (𝓝 Q0) :=
    hQs.comp (hns.comp (hφ1.tendsto_atTop.comp hφ2.tendsto_atTop))
  obtain ⟨φ3, hφ3, hae⟩ := ae_subseq hQs2
  refine ⟨fun k => φ1 (φ2 (φ3 k)),
    hφ1.tendsto_atTop.comp (hφ2.tendsto_atTop.comp hφ3.tendsto_atTop), F', a.1, a.2,
    fun ψ => (hw1 ψ).comp (hφ2.comp hφ3).tendsto_atTop, ?_, ?_, hae⟩
  · exact ((continuous_fst.tendsto a).comp hra).comp hφ3.tendsto_atTop
  · exact ((continuous_snd.tendsto a).comp hra).comp hφ3.tendsto_atTop

section
variable {L κ : ℝ}

/-- **Strong convergence of the bulk response** (`CC:F03:bulk-limit`) and of the nonlocal energies. -/
theorem strong_limit (hL : 0 < L) (hκ : 0 < κ)
    {Q : ℝ → ℝ} (hQm : Measurable Q) (hQ2 : MemLp Q 2 uI) (hna : ∀ᵐ p ∂mu2, Q p.1 ≠ Q p.2)
    {F : L2Unit} (hF : IsBulkResponse L κ Q F)
    {S : Set L2Unit} (hS : IsFormCore L κ Q S)
    (hSp : ∀ G ∈ S, ∃ (h : ℝ → ℝ) (K : ℝ≥0) (B : ℝ), LipschitzWith K h ∧ (∀ x, |h x| ≤ B) ∧
      (G : ℝ → ℝ) =ᵐ[uI] fun t => h (Q t))
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (q : ∀ n, Fin (N n) → ℝ) (Fv : ∀ n, Fin (N n) → ℝ)
    (hFv : ∀ n, Bop L (κ / N n) (q n) (Fv n) = q n)
    (hQc : Tendsto (fun n => ‖stepL2 (q n) - hQ2.toLp Q‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖stepL2 (Fv n) - F‖) atTop (𝓝 0) ∧
    Tendsto (fun n => (ENint (κ / N n) (stepF (N n) (q n)) (stepF (N n) (Fv n))).toReal) atTop
      (𝓝 (formEnergy Q F).toReal) := by
  set Q0 : L2Unit := hQ2.toLp Q with hQ0def
  have hQ0 : (Q0 : ℝ → ℝ) =ᵐ[uI] Q := hQ2.coeFn_toLp
  have hFd : F ∈ formDomain Q := hF.1
  have hfacts := fun n => Fe_facts (hN n) hL hκ (hFv n)
  have hQs : Tendsto (fun n => stepL2 (q n)) atTop (𝓝 Q0) := tendsto_iff_norm_sub_tendsto_zero.2 hQc
  obtain ⟨C, hC⟩ := hQs.norm.bddAbove_range
  have hCn : ∀ n, ‖stepL2 (q n)‖ ≤ C := fun n => hC (mem_range_self n)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hCn 0)
  have hFeM : ∀ n, ‖stepL2 (Fv n)‖ ≤ C / L := fun n => by
    rw [le_div_iff₀ hL]
    nlinarith [(hfacts n).1, hCn n]
  have hyb : ∀ n, 0 ≤ EN (N n) (κ / N n) (q n) (Fv n) ∧
      EN (N n) (κ / N n) (q n) (Fv n) ≤ C * (C / L) / κ := fun n => by
    refine ⟨EN_nonneg _ _ _ _, ?_⟩
    rw [le_div_iff₀ hκ, mul_comm]
    have h1 := (hfacts n).2
    have h2 : inner ℝ (stepL2 (q n)) (stepL2 (Fv n)) ≤ ‖stepL2 (q n)‖ * ‖stepL2 (Fv n)‖ :=
      real_inner_le_norm _ _
    have h3 : ‖stepL2 (q n)‖ * ‖stepL2 (Fv n)‖ ≤ C * (C / L) :=
      mul_le_mul (hCn n) (hFeM n) (norm_nonneg _) hC0
    nlinarith [sq_nonneg ‖stepL2 (Fv n)‖]
  have hstrong : Tendsto (fun n => ‖stepL2 (Fv n) - F‖) atTop (𝓝 0) := by
    refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨ms, hms, F', x, y0, hwu, hxu, hyu, hae⟩ := good_subseq
      (Fe := fun n => stepL2 (Fv n)) (yy := fun n => EN (N n) (κ / N n) (q n) (Fv n))
      (M := C / L) (Y := C * (C / L) / κ) hFeM hyb hQs hns
    refine ⟨ms, ?_⟩
    let u : ℕ → ℕ := fun k => ns (ms k)
    have hu : Tendsto u atTop atTop := hns.comp hms
    have hcc : Tendsto (fun k => κ / (N (u k) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (hNt.comp hu))
    have hQu : Tendsto (fun k => ‖stepL2 (q (u k)) - Q0‖) atTop (𝓝 0) := hQc.comp hu
    have hQl : ∀ᵐ t ∂uI, Tendsto (fun k => stepF (N (u k)) (q (u k)) t) atTop (𝓝 (Q t)) := by
      filter_upwards [hae, ae_all_iff.2 (fun n => stepL2_ae (q n)), hQ0] with t h1 h2 h3
      rw [← h3]
      exact h1.congr fun k => h2 (u k)
    have hyE : ∀ k, ENint (κ / (N (u k) : ℝ)) (stepF (N (u k)) (q (u k)))
        (stepL2 (Fv (u k)) : ℝ → ℝ) = ENNReal.ofReal (EN (N (u k)) (κ / N (u k)) (q (u k)) (Fv (u k))) :=
      fun k => ENint_Fe (hN _) _ _ _
    obtain ⟨hfin, hlow, hJlim⟩ := QuantumNLS.JLower.J_lower_conv (Q := Q)
      (Qn := fun k => stepF (N (u k)) (q (u k))) (cn := fun k => κ / (N (u k) : ℝ))
      (v := fun k => stepL2 (Fv (u k))) (v0 := F') (M := C / L)
      L κ hL.le hκ.le hQm (fun k => measurable_stepF (q (u k))) hcc hQl (fun k => hFeM _) hwu
      (Qe := fun k => stepL2 (q (u k))) (Q0 := Q0) hQu hxu
      (y := fun k => EN (N (u k)) (κ / N (u k)) (q (u k)) (Fv (u k))) hyE
      (fun k => EN_nonneg _ _ _ _) hyu
    have hF'd : F' ∈ formDomain Q := hfin
    -- the sequence of values of `𝒥_N(F_N)`
    have hJseq : ∀ k, (L / 2) * ‖stepL2 (Fv (u k))‖ ^ 2 +
        (κ / 2) * EN (N (u k)) (κ / N (u k)) (q (u k)) (Fv (u k)) -
        inner ℝ (stepL2 (q (u k))) (stepL2 (Fv (u k))) = JN L κ (N (u k)) (q (u k)) (Fv (u k)) :=
      fun k => (JN_Fe (hN _) L κ _ _).symm
    set ℓ : ℝ := (L / 2) * x + (κ / 2) * y0 - inner ℝ Q0 F' with hℓ
    have hJF' : Jfun L κ Q Q0 F' ≤ ℓ := hlow
    -- upper bound through the core
    have hupper : ∀ ε : ℝ, 0 < ε → ∃ (G : L2Unit) (h : ℝ → ℝ) (K : ℝ≥0) (B : ℝ)
        (hh : LipschitzWith K h) (hB : ∀ x, |h x| ≤ B),
        compL2 hh.continuous.measurable hB hQm = G ∧
        Jfun L κ Q Q0 G - Jfun L κ Q Q0 F < ε ∧
        (L / 2) * ‖G - F‖ ^ 2 + (κ / 2) * (formEnergy Q ((G - F : L2Unit) : ℝ → ℝ)).toReal < ε ∧
        Tendsto (fun k => JN L κ (N (u k)) (q (u k)) (fun i => h (q (u k) i))) atTop
          (𝓝 (Jfun L κ Q Q0 G)) := by
      intro ε hε
      obtain ⟨G, hGS, hGd, hlt⟩ := core_small hL hκ hS hFd hε
      obtain ⟨h, K, B, hh, hB, hGae⟩ := hSp G hGS
      have hm := hh.continuous.measurable
      have hG0 : compL2 hm hB hQm = G := by
        apply Lp.ext
        filter_upwards [compL2_ae hm hB hQm, hGae] with t h1 h2
        rw [h1, h2]
      have hJh := smooth_J_tendsto hh hB hQm (fun k => measurable_stepF (q (u k))) hcc hna hQu
        (fun k => stepL2_ae (q (u k))) hQ0 L κ (Qe := fun k => stepL2 (q (u k)))
      have hE : formEnergy Q (fun t => h (Q t)) = formEnergy Q G :=
        (formEnergy_congr (Filter.EventuallyEq.refl _ _) hGae).symm
      rw [hG0, hE] at hJh
      refine ⟨G, h, K, B, hh, hB, hG0, ?_, hlt, ?_⟩
      · have := J_sub_J hL.le hκ.le hQm hQ0 hF hGd
        linarith
      · refine hJh.congr fun k => ?_
        exact (JN_comp (hN _) hm hB L κ (q (u k))).symm
    have hℓle : ∀ ε : ℝ, 0 < ε → ℓ < Jfun L κ Q Q0 F + ε := by
      intro ε hε
      obtain ⟨G, h, K, B, hh, hB, hG0, hGF, -, hJh⟩ := hupper ε hε
      have hm := hh.continuous.measurable
      have hle : ℓ ≤ Jfun L κ Q Q0 G := by
        refine le_of_tendsto_of_tendsto hJlim hJh (Eventually.of_forall fun k => ?_)
        beta_reduce
        rw [hJseq k]
        have h1 := Jcompare (hN (u k)) hL hκ (hFv (u k)) hm hB
        have h0 : (0 : ℝ) ≤ (L / 2) * ‖compL2 hm hB (measurable_stepF (q (u k))) -
            stepL2 (Fv (u k))‖ ^ 2 := by positivity
        linarith
      linarith
    have hℓF : ℓ ≤ Jfun L κ Q Q0 F := le_of_forall_pos_lt_add hℓle
    -- identification of the weak limit
    have hdiff := J_sub_J hL.le hκ.le hQm hQ0 hF hF'd
    have hE' : 0 ≤ (formEnergy Q ((F' - F : L2Unit) : ℝ → ℝ)).toReal := ENNReal.toReal_nonneg
    have hnorm : ‖F' - F‖ ^ 2 ≤ 0 := by
      have h1 : Jfun L κ Q Q0 F' - Jfun L κ Q Q0 F ≤ 0 := by linarith
      have h2 : 0 ≤ (κ / 2) * (formEnergy Q ((F' - F : L2Unit) : ℝ → ℝ)).toReal := by positivity
      nlinarith [sq_nonneg ‖F' - F‖]
    have hF'F : F' = F := by
      have : ‖F' - F‖ = 0 := by
        have := sq_nonneg ‖F' - F‖
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm hnorm this)
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    have hℓeq : ℓ = Jfun L κ Q Q0 F := by
      refine le_antisymm hℓF ?_
      rw [← hF'F]; exact hJF'
    -- strong convergence along the subsequence
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k => ?_, fun δ hδ => ?_⟩
    · exact lt_of_lt_of_le ha (norm_nonneg _)
    · set ε : ℝ := L * (δ / 3) ^ 2 / 2 with hε
      have hεpos : 0 < ε := by positivity
      obtain ⟨G, h, K, B, hh, hB, hG0, hGF, hGFn, hJh⟩ := hupper ε hεpos
      have hm := hh.continuous.measurable
      have hGsmall : ‖G - F‖ < δ / 3 := by
        have h1 : 0 ≤ (κ / 2) * (formEnergy Q ((G - F : L2Unit) : ℝ → ℝ)).toReal := by positivity
        have h2 : (L / 2) * ‖G - F‖ ^ 2 < (L / 2) * (δ / 3) ^ 2 := by rw [hε] at hGFn; nlinarith
        have h3 : ‖G - F‖ ^ 2 < (δ / 3) ^ 2 := lt_of_mul_lt_mul_left h2 (by positivity)
        exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h3
      -- eventually `𝒥_N(v_N) − 𝒥_N(F_N) < ε`
      have hdiffseq : Tendsto (fun k => JN L κ (N (u k)) (q (u k)) (fun i => h (q (u k) i)) -
          JN L κ (N (u k)) (q (u k)) (Fv (u k))) atTop
          (𝓝 (Jfun L κ Q Q0 G - Jfun L κ Q Q0 F)) := by
        refine hJh.sub ?_
        rw [← hℓeq]
        refine hJlim.congr fun k => hJseq k
      have hA := hdiffseq.eventually (eventually_lt_nhds hGF)
      -- `h(Q_N) → h(Q) = G` strongly
      have hconv : Tendsto (fun k => ‖compL2 hm hB (measurable_stepF (q (u k))) - G‖) atTop (𝓝 0) := by
        rw [← hG0]
        refine squeeze_zero (fun k => norm_nonneg _)
          (fun k => norm_compL2_sub_le hh hB (measurable_stepF (q (u k))) hQm
            (stepL2_ae (q (u k))) hQ0) ?_
        simpa using hQu.const_mul (K : ℝ)
      have hB' := hconv.eventually (eventually_lt_nhds (show (0 : ℝ) < δ / 3 by positivity))
      filter_upwards [hA, hB'] with k hk1 hk2
      have h1 := Jcompare (hN (u k)) hL hκ (hFv (u k)) hm hB
      have h2 : ‖compL2 hm hB (measurable_stepF (q (u k))) - stepL2 (Fv (u k))‖ < δ / 3 := by
        have h3 : (L / 2) * ‖compL2 hm hB (measurable_stepF (q (u k))) - stepL2 (Fv (u k))‖ ^ 2 <
            (L / 2) * (δ / 3) ^ 2 := by rw [hε] at hk1; nlinarith
        have h4 := lt_of_mul_lt_mul_left h3 (by positivity)
        exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h4
      calc ‖stepL2 (Fv (u k)) - F‖
          = ‖(stepL2 (Fv (u k)) - compL2 hm hB (measurable_stepF (q (u k)))) +
              (compL2 hm hB (measurable_stepF (q (u k))) - G) + (G - F)‖ := by
            congr 1; abel
        _ ≤ ‖stepL2 (Fv (u k)) - compL2 hm hB (measurable_stepF (q (u k)))‖ +
              ‖compL2 hm hB (measurable_stepF (q (u k))) - G‖ + ‖G - F‖ :=
            norm_add₃_le
        _ < δ := by
            rw [norm_sub_rev] at h2
            linarith
  refine ⟨hstrong, ?_⟩
  -- energies
  have hFeq : L * ‖F‖ ^ 2 + κ * (formEnergy Q F).toReal = inner ℝ Q0 F := by
    have h1 := QuantumNLS.IBridge.bulkForm_self (L := L) (κ := κ) hQm F hFd
    have h2 := hF.2 F hFd
    rw [h1, QuantumNLS.IBridge.inner_Q0 hQ0] at h2
    exact h2
  have hFs : Tendsto (fun n => stepL2 (Fv n)) atTop (𝓝 F) := tendsto_iff_norm_sub_tendsto_zero.2 hstrong
  have hlim : Tendsto (fun n => (inner ℝ (stepL2 (q n)) (stepL2 (Fv n)) - L * ‖stepL2 (Fv n)‖ ^ 2) / κ)
      atTop (𝓝 ((inner ℝ Q0 F - L * ‖F‖ ^ 2) / κ)) :=
    ((hQs.inner hFs).sub ((hFs.norm.pow 2).const_mul L)).div_const κ
  have hval : (inner ℝ Q0 F - L * ‖F‖ ^ 2) / κ = (formEnergy Q F).toReal := by
    field_simp
    linarith
  rw [hval] at hlim
  refine hlim.congr fun n => ?_
  rw [ENint_step (hN n), ENNReal.toReal_ofReal (EN_nonneg _ _ _ _), ← (hfacts n).2]
  field_simp

end

end QuantumNLS.StrongLimit

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.StrongLimit.Jcompare
#print axioms QuantumNLS.StrongLimit.good_subseq
#print axioms QuantumNLS.StrongLimit.strong_limit
