import Mathlib
import QuantumNLS.GLowerKernel
import QuantumNLS.GLowerWeak

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (G), part 3: the weak lower bound `liminf ℰ_N(v_N) ≥ ℰ(v)`

Source (F03.tex, "Here is the weak lower bound, including the dependence of the kernels on `N`"): for `v_N ⇀ v` in `L²(0,1)`, `Q_N → Q` almost everywhere,
`A_{m,N} v_N ⇀ A_m v` (module `GLowerWeak`), hence `liminf ℰ_N(v_N) ≥ ‖A_m v‖²`, and letting `m → ∞` by monotone convergence `liminf ℰ_N(v_N) ≥ ℰ(v)`.

Formal statement (`weak_liminf`): sequences `Q_n` (measurable), `c_n → 0`, `Q_n → Q` a.e. on `(0,1)`, `v_n ⇀ v_0` weakly with `‖v_n‖ ≤ M` (a weakly convergent sequence is bounded);
`ℰ_n(w) = ∬ (w(t)-w(s))²/(c_n² + (Q_n(t)-Q_n(s))²) dt ds` (`ENint`, in `[0,∞]`); then
`BulkResponseForm.formEnergy Q v_0 ≤ liminf_n ENint c_n Q_n v_n`.
No atomlessness is used: `quot` is `0` where `Q t = Q s` (as is `a_m`, since `χ_m(0) = 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QuantumNLS.GLowerBound

open QuantumNLS.BulkResponseRiesz (mu2 inner_eq_integral quot_congr ae_fst ae_snd)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.BulkResponseForm (quot formEnergy L2Unit)
open QuantumNLS.GLowerKernel (coef coef_nonneg coef_symm coef_le coef_sq_le coef_mono tendsto_coef
  coef_sq_eventually coef_zero_of_eq continuous_chi)
open QuantumNLS.GLowerWeak (weak_pair_tendsto)

/-- The discrete-kernel energy `ℰ_n(w) = ∬ (w(t)-w(s))²/(c² + (Q_n(t)-Q_n(s))²) dt ds ∈ [0,∞]`. -/
def ENint (c : ℝ) (Qn : ℝ → ℝ) (w : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((w p.1 - w p.2) ^ 2 / (c ^ 2 + (Qn p.1 - Qn p.2) ^ 2)) ∂mu2

theorem measurable_coef (m : ℝ) : Measurable (fun z : ℝ × ℝ × ℝ => coef m z.1 z.2.1 z.2.2) := by
  unfold coef
  exact (Real.continuous_sqrt.measurable.comp ((continuous_chi m).measurable.comp
      (measurable_snd.fst.sub measurable_snd.snd))).div
    (Real.continuous_sqrt.measurable.comp ((measurable_fst.pow_const 2).add
      ((measurable_snd.fst.sub measurable_snd.snd).pow_const 2)))

theorem measurable_K (m c : ℝ) {Qa : ℝ → ℝ} (hQ : Measurable Qa) :
    Measurable (fun p : ℝ × ℝ => coef m c (Qa p.1) (Qa p.2)) :=
  (measurable_coef m).comp (measurable_const.prodMk
    ((hQ.comp measurable_fst).prodMk (hQ.comp measurable_snd)))

theorem abs_coef_le {m : ℝ} (hm : 0 < m) (c x y : ℝ) : |coef m c x y| ≤ 2 * m := by
  rw [abs_of_nonneg (coef_nonneg _ _ _ _)]; exact coef_le hm _ _ _

theorem memLp_mul {K g : ℝ × ℝ → ℝ} (hKm : Measurable K) {C : ℝ} (hKb : ∀ p, |K p| ≤ C)
    (hg : MemLp g 2 mu2) : MemLp (fun p => K p * g p) 2 mu2 := by
  have hK : MemLp K ⊤ mu2 :=
    memLp_top_of_bound hKm.aestronglyMeasurable C (Eventually.of_forall fun p => by simpa using hKb p)
  exact hK.mul hg

theorem memLp_fst (f : L2Unit) : MemLp (fun p : ℝ × ℝ => (f : ℝ → ℝ) p.1) 2 mu2 :=
  (Lp.memLp f).comp_fst uI

theorem memLp_snd (f : L2Unit) : MemLp (fun p : ℝ × ℝ => (f : ℝ → ℝ) p.2) 2 mu2 :=
  (Lp.memLp f).comp_snd uI

theorem integrable_Kg {K g ψ : ℝ × ℝ → ℝ} (hKm : Measurable K) {C : ℝ} (hKb : ∀ p, |K p| ≤ C)
    (hg : MemLp g 2 mu2) (hψ : MemLp ψ 2 mu2) : Integrable (fun p => K p * g p * ψ p) mu2 :=
  (memLp_mul hKm hKb hg).integrable_mul hψ

/-- For symmetric `K` and antisymmetric `Φ`: `∬ K (f(t)-f(s)) Φ = 2 ∬ K f(t) Φ`. -/
theorem pair_split {K Φ : ℝ × ℝ → ℝ} (hKm : Measurable K) {C : ℝ} (hKb : ∀ p, |K p| ≤ C)
    (hKs : ∀ p : ℝ × ℝ, K p.swap = K p) (hΦ : MemLp Φ 2 mu2) (hΦa : ∀ p : ℝ × ℝ, Φ p.swap = - Φ p)
    (f : L2Unit) :
    ∫ p, K p * ((f : ℝ → ℝ) p.1 - (f : ℝ → ℝ) p.2) * Φ p ∂mu2 =
      2 * ∫ p, K p * (f : ℝ → ℝ) p.1 * Φ p ∂mu2 := by
  have i1 := integrable_Kg hKm hKb (memLp_fst f) hΦ
  have i2 := integrable_Kg hKm hKb (memLp_snd f) hΦ
  have hs : ∫ p, K p * (f : ℝ → ℝ) p.2 * Φ p ∂mu2 = - ∫ p, K p * (f : ℝ → ℝ) p.1 * Φ p ∂mu2 := by
    rw [← integral_prod_swap (fun p : ℝ × ℝ => K p * (f : ℝ → ℝ) p.2 * Φ p), ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Prod.snd_swap, hKs, hΦa]
    ring
  have : (fun p : ℝ × ℝ => K p * ((f : ℝ → ℝ) p.1 - (f : ℝ → ℝ) p.2) * Φ p) =
      fun p => K p * (f : ℝ → ℝ) p.1 * Φ p - K p * (f : ℝ → ℝ) p.2 * Φ p := by
    funext p; ring
  rw [this, integral_sub i1 i2, hs]; ring

theorem norm_sq_toLp {A : ℝ × ℝ → ℝ} (hA : MemLp A 2 mu2) :
    ‖hA.toLp A‖ ^ 2 = ∫ p, A p ^ 2 ∂mu2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hA.coeFn_toLp] with p h
  have h' : (hA.toLp A : ℝ × ℝ → ℝ) p = A p := h
  rw [h', sq]

theorem inner_toLp {A B : ℝ × ℝ → ℝ} (hA : MemLp A 2 mu2) (hB : MemLp B 2 mu2) :
    inner ℝ (hA.toLp A) (hB.toLp B) = ∫ p, A p * B p ∂mu2 := by
  rw [inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with p h1 h2
  have h1' : (hA.toLp A : ℝ × ℝ → ℝ) p = A p := h1
  have h2' : (hB.toLp B : ℝ × ℝ → ℝ) p = B p := h2
  rw [h1', h2']

/-- Cauchy-Schwarz in `L²((0,1)²)`. -/
theorem integral_mul_le {A Φ : ℝ × ℝ → ℝ} (hA : MemLp A 2 mu2) (hΦ : MemLp Φ 2 mu2) :
    ∫ p, A p * Φ p ∂mu2 ≤
      Real.sqrt (∫ p, A p ^ 2 ∂mu2) * Real.sqrt (∫ p, Φ p ^ 2 ∂mu2) := by
  have h := real_inner_le_norm (hA.toLp A) (hΦ.toLp Φ)
  rw [inner_toLp] at h
  refine h.trans (le_of_eq ?_)
  rw [← norm_sq_toLp hA, ← norm_sq_toLp hΦ, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- `‖A_{m,n} v‖² ≤ ℰ_n(v)`, in `[0,∞]`. -/
theorem ofReal_le_ENint {c : ℝ} {Qn : ℝ → ℝ} {A : ℝ × ℝ → ℝ} (hA : MemLp A 2 mu2) (w : ℝ → ℝ)
    (hle : ∀ p : ℝ × ℝ, A p ^ 2 ≤ (w p.1 - w p.2) ^ 2 / (c ^ 2 + (Qn p.1 - Qn p.2) ^ 2)) :
    ENNReal.ofReal (∫ p, A p ^ 2 ∂mu2) ≤ ENint c Qn w := by
  rw [ofReal_integral_eq_lintegral_ofReal hA.integrable_sq (Eventually.of_forall fun p => sq_nonneg _)]
  exact lintegral_mono fun p => ENNReal.ofReal_le_ofReal (hle p)

/-! ### The measurable representative of `v_0` and the truncated limit integrand `A_m v_0` -/

/-- A measurable representative of `v₀`. -/
def v0m (v0 : L2Unit) : ℝ → ℝ := (Lp.aestronglyMeasurable v0).mk _

theorem v0m_meas (v0 : L2Unit) : Measurable (v0m v0) :=
  (Lp.aestronglyMeasurable v0).stronglyMeasurable_mk.measurable

theorem v0m_ae (v0 : L2Unit) : (v0 : ℝ → ℝ) =ᵐ[uI] v0m v0 :=
  (Lp.aestronglyMeasurable v0).ae_eq_mk

theorem v0m_memLp (v0 : L2Unit) : MemLp (v0m v0) 2 uI := (Lp.memLp v0).ae_eq (v0m_ae v0)

/-- `Φ_m = a_m (v₀(t) - v₀(s))`, `a_m = coef (m+1) 0 (Q t) (Q s)`. -/
def Phi (Q : ℝ → ℝ) (v0 : L2Unit) (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  coef ((m : ℝ) + 1) 0 (Q p.1) (Q p.2) * (v0m v0 p.1 - v0m v0 p.2)

theorem Phi_meas {Q : ℝ → ℝ} (hQ : Measurable Q) (v0 : L2Unit) (m : ℕ) : Measurable (Phi Q v0 m) := by
  unfold Phi
  exact (measurable_K _ _ hQ).mul (((v0m_meas v0).comp measurable_fst).sub ((v0m_meas v0).comp measurable_snd))

theorem memLp_diff (v0 : L2Unit) :
    MemLp (fun p : ℝ × ℝ => v0m v0 p.1 - v0m v0 p.2) 2 mu2 :=
  ((v0m_memLp v0).comp_fst uI).sub ((v0m_memLp v0).comp_snd uI)

theorem Phi_memLp {Q : ℝ → ℝ} (hQ : Measurable Q) (v0 : L2Unit) (m : ℕ) :
    MemLp (Phi Q v0 m) 2 mu2 := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have := memLp_mul (K := fun p : ℝ × ℝ => coef ((m : ℝ) + 1) 0 (Q p.1) (Q p.2))
    (measurable_K _ _ hQ) (fun p => abs_coef_le hm 0 (Q p.1) (Q p.2)) (memLp_diff v0)
  exact this

theorem Phi_swap {Q : ℝ → ℝ} (v0 : L2Unit) (m : ℕ) (p : ℝ × ℝ) :
    Phi Q v0 m p.swap = - Phi Q v0 m p := by
  unfold Phi
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [coef_symm _ _ (Q p.2) (Q p.1)]
  ring

/-! ### Fixed truncation level `m` -/

section
variable {Q : ℝ → ℝ} {Qn : ℕ → ℝ → ℝ} {cn : ℕ → ℝ}
  {v : ℕ → L2Unit} {v0 : L2Unit} {M : ℝ}

theorem fixed_m (hQm : Measurable Q) (hQnm : ∀ n, Measurable (Qn n))
    (hc : Tendsto cn atTop (𝓝 0))
    (hQl : ∀ᵐ t ∂uI, Tendsto (fun n => Qn n t) atTop (𝓝 (Q t)))
    (hM : ∀ n, ‖v n‖ ≤ M)
    (hw : ∀ φ : L2Unit, Tendsto (fun n => inner ℝ (v n) φ) atTop (𝓝 (inner ℝ v0 φ))) (m : ℕ) :
    ENNReal.ofReal (∫ p, Phi Q v0 m p ^ 2 ∂mu2) ≤
      liminf (fun n => ENint (cn n) (Qn n) (v n)) atTop := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  let K : ℕ → ℝ × ℝ → ℝ := fun n p => coef ((m : ℝ) + 1) (cn n) (Qn n p.1) (Qn n p.2)
  let K0 : ℝ × ℝ → ℝ := fun p => coef ((m : ℝ) + 1) 0 (Q p.1) (Q p.2)
  have hKm : ∀ n, Measurable (K n) := fun n => measurable_K _ _ (hQnm n)
  have hK0m : Measurable K0 := measurable_K _ _ hQm
  have hKb : ∀ n p, |K n p| ≤ 2 * ((m : ℝ) + 1) := fun n p => abs_coef_le hm _ _ _
  have hK0b : ∀ p, |K0 p| ≤ 2 * ((m : ℝ) + 1) := fun p => abs_coef_le hm _ _ _
  have hKs : ∀ n (p : ℝ × ℝ), K n p.swap = K n p := fun n p => coef_symm _ _ _ _
  have hK0s : ∀ p : ℝ × ℝ, K0 p.swap = K0 p := fun p => coef_symm _ _ _ _
  have hKl : ∀ᵐ p ∂mu2, Tendsto (fun n => K n p) atTop (𝓝 (K0 p)) := by
    filter_upwards [ae_fst (P := fun t => Tendsto (fun n => Qn n t) atTop (𝓝 (Q t))) hQl,
      ae_snd (P := fun t => Tendsto (fun n => Qn n t) atTop (𝓝 (Q t))) hQl] with p h1 h2
    exact tendsto_coef hm hc h1 h2
  have hΦm := Phi_meas hQm v0 m
  have hΦ := Phi_memLp hQm v0 m
  have hΦs := Phi_swap (Q := Q) v0 m
  have hT := weak_pair_tendsto hΦm hΦ hKm hK0m hKb hK0b hKl hM hw
  have hP : Tendsto (fun n => ∫ p, K n p * ((v n : ℝ → ℝ) p.1 - (v n : ℝ → ℝ) p.2) * Phi Q v0 m p ∂mu2)
      atTop (𝓝 (∫ p, Phi Q v0 m p ^ 2 ∂mu2)) := by
    have hlim : ∫ p, Phi Q v0 m p ^ 2 ∂mu2 =
        2 * ∫ p, K0 p * (v0 : ℝ → ℝ) p.1 * Phi Q v0 m p ∂mu2 := by
      rw [← pair_split hK0m hK0b hK0s hΦ hΦs v0]
      refine integral_congr_ae ?_
      filter_upwards [ae_fst (v0m_ae v0), ae_snd (v0m_ae v0)] with p h1 h2
      rw [h1, h2]
      simp only [Phi, K0]
      ring
    rw [hlim]
    refine (hT.const_mul 2).congr fun n => ?_
    rw [pair_split (hKm n) (hKb n) (hKs n) hΦ hΦs (v n)]
  by_contra hlt
  push_neg at hlt
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hlt
  obtain ⟨hrS, hS⟩ := (ENNReal.ofReal_lt_ofReal_iff'.1 hr2)
  have hfreq : ∃ᶠ n in atTop, ENint (cn n) (Qn n) (v n) < ENNReal.ofReal r :=
    Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hr1
  have hsqrt : Real.sqrt r * Real.sqrt (∫ p, Phi Q v0 m p ^ 2 ∂mu2) <
      ∫ p, Phi Q v0 m p ^ 2 ∂mu2 := by
    set S := ∫ p, Phi Q v0 m p ^ 2 ∂mu2
    have h1 : Real.sqrt r < Real.sqrt S := Real.sqrt_lt_sqrt hr0 hrS
    have h2 : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
    calc Real.sqrt r * Real.sqrt S < Real.sqrt S * Real.sqrt S := mul_lt_mul_of_pos_right h1 h2
      _ = S := Real.mul_self_sqrt hS.le
  have hev := hP.eventually (lt_mem_nhds hsqrt)
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hev).exists
  have hg : MemLp (fun p : ℝ × ℝ => (v n : ℝ → ℝ) p.1 - (v n : ℝ → ℝ) p.2) 2 mu2 :=
    (memLp_fst (v n)).sub (memLp_snd (v n))
  have hA := memLp_mul (hKm n) (hKb n) hg
  have hAE : ENNReal.ofReal (∫ p, (K n p * ((v n : ℝ → ℝ) p.1 - (v n : ℝ → ℝ) p.2)) ^ 2 ∂mu2) ≤
      ENint (cn n) (Qn n) (v n) := by
    refine ofReal_le_ENint hA (v n) fun p => ?_
    beta_reduce
    rw [mul_pow]
    have := coef_sq_le ((m : ℝ) + 1) (cn n) (Qn n p.1) (Qn n p.2)
    calc (K n p) ^ 2 * ((v n : ℝ → ℝ) p.1 - (v n : ℝ → ℝ) p.2) ^ 2
        ≤ 1 / (cn n ^ 2 + (Qn n p.1 - Qn n p.2) ^ 2) * ((v n : ℝ → ℝ) p.1 - (v n : ℝ → ℝ) p.2) ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = _ := by ring
  have hlt2 := (ENNReal.ofReal_lt_ofReal_iff'.1 (lt_of_le_of_lt hAE hn1)).1
  have hcs := integral_mul_le hA hΦ
  have hsq : Real.sqrt (∫ p, (K n p * ((v n : ℝ → ℝ) p.1 - (v n : ℝ → ℝ) p.2)) ^ 2 ∂mu2) ≤ Real.sqrt r :=
    Real.sqrt_le_sqrt hlt2.le
  have : ∫ p, K n p * ((v n : ℝ → ℝ) p.1 - (v n : ℝ → ℝ) p.2) * Phi Q v0 m p ∂mu2 ≤
      Real.sqrt r * Real.sqrt (∫ p, Phi Q v0 m p ^ 2 ∂mu2) :=
    hcs.trans (mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _))
  linarith

end

/-! ### The limit `m → ∞` -/

section
variable {Q : ℝ → ℝ} {Qn : ℕ → ℝ → ℝ} {cn : ℕ → ℝ}
  {v : ℕ → L2Unit} {v0 : L2Unit} {M : ℝ}

/-- **Weak lower bound** (`CC:F03:deterministic`, proof, "weak lower bound"): `liminf ℰ_N(v_N) ≥ ℰ(v)`. -/
theorem weak_liminf (hQm : Measurable Q) (hQnm : ∀ n, Measurable (Qn n))
    (hc : Tendsto cn atTop (𝓝 0))
    (hQl : ∀ᵐ t ∂uI, Tendsto (fun n => Qn n t) atTop (𝓝 (Q t)))
    (hM : ∀ n, ‖v n‖ ≤ M)
    (hw : ∀ φ : L2Unit, Tendsto (fun n => inner ℝ (v n) φ) atTop (𝓝 (inner ℝ v0 φ))) :
    formEnergy Q v0 ≤ liminf (fun n => ENint (cn n) (Qn n) (v n)) atTop := by
  let f : ℕ → ℝ × ℝ → ℝ≥0∞ := fun m p => ENNReal.ofReal (Phi Q v0 m p ^ 2)
  have hfm : ∀ m, Measurable (f m) := fun m =>
    ENNReal.measurable_ofReal.comp ((Phi_meas hQm v0 m).pow_const 2)
  have hmono : ∀ p, Monotone (fun m => f m p) := fun p => by
    refine monotone_nat_of_le_succ fun m => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : coef ((m : ℝ) + 1) 0 (Q p.1) (Q p.2) ≤ coef (((m + 1 : ℕ) : ℝ) + 1) 0 (Q p.1) (Q p.2) :=
      coef_mono (by positivity) (by push_cast; linarith) _ _ _
    have h0 := coef_nonneg ((m : ℝ) + 1) 0 (Q p.1) (Q p.2)
    simp only [Phi, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (sq_nonneg _)
  have hle : formEnergy Q v0 ≤ ∫⁻ p, ⨆ m, f m p ∂mu2 := by
    unfold formEnergy
    refine lintegral_mono_ae ?_
    filter_upwards [ae_fst (v0m_ae v0), ae_snd (v0m_ae v0)] with p h1 h2
    by_cases hq : Q p.1 = Q p.2
    · have : quot Q (v0 : ℝ → ℝ) p.1 p.2 = 0 := by
        unfold quot; rw [hq, sub_self, div_zero]
      rw [this]; simp
    · obtain ⟨m, hm⟩ := (coef_sq_eventually hq).exists
      refine le_trans (le_of_eq ?_) (le_iSup (fun m => f m p) m)
      simp only [f, Phi]
      congr 1
      unfold quot
      rw [mul_pow, hm, h1, h2, div_pow]
      ring
  refine hle.trans ?_
  rw [lintegral_iSup (fun m => hfm m) (fun m n hmn p => hmono p hmn)]
  refine iSup_le fun m => ?_
  have hΦ := Phi_memLp hQm v0 m
  show ∫⁻ p, ENNReal.ofReal (Phi Q v0 m p ^ 2) ∂mu2 ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hΦ.integrable_sq (Eventually.of_forall fun p => sq_nonneg _)]
  exact fixed_m hQm hQnm hc hQl hM hw m

end

end QuantumNLS.GLowerBound

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.GLowerBound.pair_split
#print axioms QuantumNLS.GLowerBound.fixed_m
#print axioms QuantumNLS.GLowerBound.weak_liminf
