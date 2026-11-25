import NlsGge.Analysis.AnalyticTsum38
import NlsGge.Hierarchy.ALComplexExteriorLog38
import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.ALPoissonLiouville38

/-! # Batch 38, L02b-3: real analyticity of the AL full energy `E_{W,h}`
(paper/v2.tex D:thm:ALfinite, proof l.1969).

Route: `C_k(a,b)` = `ζ^{2k}` Taylor coefficient of `alComplexLog38 a b` at `0` (analytic in `(a,b)` as an
iterated `ζ`-derivative of a jointly analytic function; equal to `alC38` on the real slice);
Cauchy bound `‖C_k‖ ≤ S ρ^{-2k}` on a closed ball; `‖K_j(a,b)‖ ≤ 2S(8R)^j`; normal convergence of
`Σ_j β_j h^{-2j-1} K_j` and analyticity of the sum by `analyticAt_tsum_of_bound38`; finally
`E(α) = Re F(α, conj α)` with `F` complex analytic, composed with the `ℝ`-linear map
`α ↦ (α, conj α)` (`AnalyticAt.restrictScalars`).  Main result:
`analyticOnNhd_alEnergy38 : AnalyticOnNhd ℝ (alEnergy38 c h) (alDisk38 L)`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Filter Topology Metric Set
open scoped Nat

section Slice

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Partial derivative in the first (`ζ`) variable. -/
def dzeta38 (G : ℂ × P → ℂ) : ℂ × P → ℂ := fun q => fderiv ℂ G q ((1 : ℂ), (0 : P))

theorem analyticOnNhd_dzeta38 {G : ℂ × P → ℂ} {W : Set (ℂ × P)} (hG : AnalyticOnNhd ℂ G W) :
    AnalyticOnNhd ℂ (dzeta38 G) W := fun q hq =>
  ((ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : P))).analyticAt _).comp (hG.fderiv q hq)

theorem analyticOnNhd_dzeta_iter38 {G : ℂ × P → ℂ} {W : Set (ℂ × P)} (hG : AnalyticOnNhd ℂ G W)
    (n : ℕ) : AnalyticOnNhd ℂ ((dzeta38)^[n] G) W := by
  induction n with
  | zero => simpa using hG
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact analyticOnNhd_dzeta38 ih

theorem hasDerivAt_slice38 {G : ℂ × P → ℂ} {ζ : ℂ} {p : P} (h : AnalyticAt ℂ G (ζ, p)) :
    HasDerivAt (fun t => G (t, p)) (dzeta38 G (ζ, p)) ζ := by
  have h1 := h.differentiableAt.hasFDerivAt
  have h2 : HasDerivAt (fun t : ℂ => (t, p)) ((1 : ℂ), (0 : P)) ζ :=
    (hasDerivAt_id ζ).prodMk (hasDerivAt_const ζ p)
  exact h1.comp_hasDerivAt ζ h2

theorem iteratedDeriv_slice38 {G : ℂ × P → ℂ} {W : Set (ℂ × P)} (hW : IsOpen W)
    (hG : AnalyticOnNhd ℂ G W) (p : P) :
    ∀ n : ℕ, ∀ ζ : ℂ, (ζ, p) ∈ W →
      iteratedDeriv n (fun t => G (t, p)) ζ = ((dzeta38)^[n] G) (ζ, p) := by
  intro n
  induction n with
  | zero => intro ζ _; simp
  | succ n ih =>
    intro ζ hζ
    rw [iteratedDeriv_succ, Function.iterate_succ_apply']
    have hev : iteratedDeriv n (fun t => G (t, p)) =ᶠ[𝓝 ζ] fun t => ((dzeta38)^[n] G) (t, p) := by
      filter_upwards [(hW.preimage (by fun_prop : Continuous fun t : ℂ => (t, p))).mem_nhds hζ]
        with t ht using ih t ht
    rw [hev.deriv_eq]
    exact (hasDerivAt_slice38 (analyticOnNhd_dzeta_iter38 hG n _ hζ)).deriv

end Slice

variable {L : ℕ} [NeZero L]

/-- `ζ^{2k}` Taylor coefficient of the complexified exterior log. -/
def alCc38 (p : (ZMod L → ℂ) × (ZMod L → ℂ)) (k : ℕ) : ℂ :=
  iteratedDeriv (2 * k) (alComplexLog38 p.1 p.2) 0 / ((2 * k)! : ℂ)

theorem analyticAt_alCc38 {U : Set ((ZMod L → ℂ) × (ZMod L → ℂ))} {ρ₁ : ℝ} (hρ : 0 < ρ₁)
    (hU : IsOpen U)
    (hlog : ∀ ζ ∈ ball (0 : ℂ) ρ₁, ∀ p ∈ U,
        AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) =>
          alComplexLog38 r.2.1 r.2.2 r.1) (ζ, p)) (k : ℕ) {p : (ZMod L → ℂ) × (ZMod L → ℂ)}
    (hp : p ∈ U) : AnalyticAt ℂ (fun p' => alCc38 p' k) p := by
  set G : ℂ × ((ZMod L → ℂ) × (ZMod L → ℂ)) → ℂ :=
    fun r => alComplexLog38 r.2.1 r.2.2 r.1 with hG
  have hW : IsOpen (ball (0 : ℂ) ρ₁ ×ˢ U) := isOpen_ball.prod hU
  have hGW : AnalyticOnNhd ℂ G (ball (0 : ℂ) ρ₁ ×ˢ U) := fun q hq =>
    hlog q.1 hq.1 q.2 hq.2
  have hH := analyticOnNhd_dzeta_iter38 hGW (2 * k)
  have h0 : ((0 : ℂ), p) ∈ ball (0 : ℂ) ρ₁ ×ˢ U := ⟨mem_ball_self hρ, hp⟩
  have han : AnalyticAt ℂ (fun p' => (((dzeta38)^[2 * k] G) ((0 : ℂ), p')) / ((2 * k)! : ℂ)) p :=
    ((hH _ h0).comp (AnalyticAt.prod analyticAt_const analyticAt_id)).div_const
  refine han.congr ?_
  filter_upwards [hU.mem_nhds hp] with p' hp'
  unfold alCc38
  rw [← iteratedDeriv_slice38 hW hGW p' (2 * k) 0 ⟨mem_ball_self hρ, hp'⟩]

theorem alCc38_real {α : ZMod L → ℂ} {ρ₁ : ℝ} (hρ : 0 < ρ₁)
    (h : ∀ ζ ∈ ball (0 : ℂ) ρ₁, alComplexLog38 α (fun j => star (α j)) ζ = alLog38 α ζ) (k : ℕ) :
    alCc38 (α, fun j => star (α j)) k = alC38 α k := by
  unfold alCc38 alC38
  have : alComplexLog38 α (fun j => star (α j)) =ᶠ[𝓝 (0 : ℂ)] alLog38 α := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with z hz using h z hz
  simp only
  rw [this.iteratedDeriv_eq]

theorem exists_alCc_bound38 {U : Set ((ZMod L → ℂ) × (ZMod L → ℂ))} {ρ₁ : ℝ} (hρ : 0 < ρ₁)
    (hU : IsOpen U)
    (hlog : ∀ ζ ∈ ball (0 : ℂ) ρ₁, ∀ p ∈ U,
        AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) =>
          alComplexLog38 r.2.1 r.2.2 r.1) (ζ, p))
    {p0 : (ZMod L → ℂ) × (ZMod L → ℂ)} (hp0 : p0 ∈ U) :
    ∃ s : ℝ, 0 < s ∧ closedBall p0 s ⊆ U ∧ ∃ ρ S : ℝ, 0 < ρ ∧ 0 ≤ S ∧
      ∀ p ∈ closedBall p0 s, ∀ k : ℕ, ‖alCc38 p k‖ ≤ S * ((ρ ^ 2)⁻¹) ^ k := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU p0 hp0
  set s : ℝ := ε / 2 with hs
  have hspos : 0 < s := by positivity
  have hsU : closedBall p0 s ⊆ U := fun p hp =>
    hball (lt_of_le_of_lt (mem_closedBall.1 hp) (by rw [hs]; linarith))
  set ρ : ℝ := ρ₁ / 2 with hρdef
  have hρpos : 0 < ρ := by positivity
  set G : ℂ × ((ZMod L → ℂ) × (ZMod L → ℂ)) → ℂ :=
    fun r => alComplexLog38 r.2.1 r.2.2 r.1 with hG
  have hGW : AnalyticOnNhd ℂ G (ball (0 : ℂ) ρ₁ ×ˢ U) := fun q hq => hlog q.1 hq.1 q.2 hq.2
  have hK : IsCompact (closedBall (0 : ℂ) ρ ×ˢ closedBall p0 s) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKW : closedBall (0 : ℂ) ρ ×ˢ closedBall p0 s ⊆ ball (0 : ℂ) ρ₁ ×ˢ U := by
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    refine ⟨?_, hsU hp⟩
    rw [mem_ball_zero_iff]; rw [mem_closedBall_zero_iff] at ht
    rw [hρdef] at ht; linarith
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hGW.continuousOn.mono hKW)
  refine ⟨s, hspos, hsU, ρ, max C 0, hρpos, le_max_right _ _, ?_⟩
  intro p hp k
  have hdiff : DiffContOnCl ℂ (alComplexLog38 p.1 p.2) (ball (0 : ℂ) ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hρpos.ne']
    intro t ht
    have : AnalyticAt ℂ G (t, p) := hGW (t, p) (hKW ⟨ht, hp⟩)
    exact (hasDerivAt_slice38 this).differentiableAt.differentiableWithinAt
  have hsph : ∀ t ∈ sphere (0 : ℂ) ρ, ‖alComplexLog38 p.1 p.2 t‖ ≤ max C 0 := by
    intro t ht
    exact (hC (t, p) ⟨sphere_subset_closedBall ht, hp⟩).trans (le_max_left _ _)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (2 * k) hρpos hdiff hsph
  have hfac : (0 : ℝ) < ((2 * k)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  unfold alCc38
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hfac]
  calc ‖iteratedDeriv (2 * k) (alComplexLog38 p.1 p.2) 0‖
      ≤ ((2 * k)! : ℝ) * max C 0 / ρ ^ (2 * k) := h
    _ = max C 0 * ((ρ ^ 2)⁻¹) ^ k * ((2 * k)! : ℝ) := by
        rw [pow_mul, inv_pow]; field_simp

/-- Complexified moment `K_j(a,b) = 2 C(2j,j) C_0 + 2 Σ_{k=1}^j (-1)^k C(2j,j-k) C_k`. -/
def alKc38 (j : ℕ) (p : (ZMod L → ℂ) × (ZMod L → ℂ)) : ℂ :=
  2 * (Nat.choose (2 * j) j : ℂ) * alCc38 p 0 +
    2 * ∑ k ∈ Finset.Icc 1 j, (-1 : ℂ) ^ k * (Nat.choose (2 * j) (j - k) : ℂ) * alCc38 p k

theorem analyticAt_alKc38 {U : Set ((ZMod L → ℂ) × (ZMod L → ℂ))} {ρ₁ : ℝ} (hρ : 0 < ρ₁)
    (hU : IsOpen U)
    (hlog : ∀ ζ ∈ ball (0 : ℂ) ρ₁, ∀ p ∈ U,
        AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) =>
          alComplexLog38 r.2.1 r.2.2 r.1) (ζ, p)) (j : ℕ)
    {p : (ZMod L → ℂ) × (ZMod L → ℂ)} (hp : p ∈ U) : AnalyticAt ℂ (alKc38 j) p := by
  unfold alKc38
  exact (analyticAt_const.mul (analyticAt_alCc38 hρ hU hlog 0 hp)).add
    (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun k _ =>
      analyticAt_const.mul (analyticAt_alCc38 hρ hU hlog k hp)))

omit [NeZero L] in
/-- Cauchy bound for `K_j`: `‖K_j‖ ≤ 2 S (8R)^j`. -/
theorem norm_alKc38_le {S q : ℝ} (hS : 0 ≤ S) (hq : 0 ≤ q) {p : (ZMod L → ℂ) × (ZMod L → ℂ)}
    (hC : ∀ k : ℕ, ‖alCc38 p k‖ ≤ S * q ^ k) (j : ℕ) :
    ‖alKc38 j p‖ ≤ 2 * S * (8 * max 1 q) ^ j := by
  set R : ℝ := max 1 q with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := by linarith
  have hCk : ∀ k ≤ j, ‖alCc38 p k‖ ≤ S * R ^ j := by
    intro k hk
    calc ‖alCc38 p k‖ ≤ S * q ^ k := hC k
      _ ≤ S * R ^ k := by gcongr; exact le_max_right _ _
      _ ≤ S * R ^ j := by gcongr
  have hchoose : ∀ m : ℕ, ‖(Nat.choose (2 * j) m : ℂ)‖ ≤ 4 ^ j := by
    intro m
    rw [Complex.norm_natCast]
    have := Nat.choose_le_two_pow (2 * j) m
    have h2 : ((Nat.choose (2 * j) m : ℕ) : ℝ) ≤ ((2 ^ (2 * j) : ℕ) : ℝ) := by exact_mod_cast this
    calc _ ≤ ((2 ^ (2 * j) : ℕ) : ℝ) := h2
      _ = 4 ^ j := by push_cast; rw [pow_mul]; norm_num
  have hterm : ∀ k ∈ Finset.Icc 1 j,
      ‖(-1 : ℂ) ^ k * (Nat.choose (2 * j) (j - k) : ℂ) * alCc38 p k‖ ≤ 4 ^ j * (S * R ^ j) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact mul_le_mul (hchoose _) (hCk k hk.2) (norm_nonneg _) (by positivity)
  have hsum : ‖∑ k ∈ Finset.Icc 1 j, (-1 : ℂ) ^ k * (Nat.choose (2 * j) (j - k) : ℂ) * alCc38 p k‖
      ≤ j * (4 ^ j * (S * R ^ j)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    simp
  have h0 : ‖2 * (Nat.choose (2 * j) j : ℂ) * alCc38 p 0‖ ≤ 2 * (4 ^ j * (S * R ^ j)) := by
    rw [norm_mul, norm_mul]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    have := mul_le_mul_of_nonneg_left (mul_le_mul (hchoose j) (hCk 0 (Nat.zero_le _))
      (norm_nonneg _) (by positivity)) (by norm_num : (0:ℝ) ≤ 2)
    rw [mul_assoc]; exact this
  have hj : (j : ℝ) + 1 ≤ 2 ^ j := by
    have := Nat.lt_two_pow_self (n := j)
    exact_mod_cast this
  unfold alKc38
  calc ‖2 * (Nat.choose (2 * j) j : ℂ) * alCc38 p 0 +
        2 * ∑ k ∈ Finset.Icc 1 j, (-1 : ℂ) ^ k * (Nat.choose (2 * j) (j - k) : ℂ) * alCc38 p k‖
      ≤ ‖2 * (Nat.choose (2 * j) j : ℂ) * alCc38 p 0‖ + ‖2 * ∑ k ∈ Finset.Icc 1 j,
          (-1 : ℂ) ^ k * (Nat.choose (2 * j) (j - k) : ℂ) * alCc38 p k‖ := norm_add_le _ _
    _ ≤ 2 * (4 ^ j * (S * R ^ j)) + 2 * (j * (4 ^ j * (S * R ^ j))) := by
        gcongr
        rw [norm_mul]
        have : ‖(2 : ℂ)‖ = 2 := by simp
        rw [this]; gcongr
    _ = 2 * ((j + 1) * (4 ^ j * (S * R ^ j))) := by ring
    _ ≤ 2 * (2 ^ j * (4 ^ j * (S * R ^ j))) := by gcongr
    _ = 2 * S * (8 * R) ^ j := by
        rw [mul_pow, show (8:ℝ) = 2 * 4 by norm_num, mul_pow]; ring

theorem alKc38_re {α : ZMod L → ℂ} (hα : IsALField38 α) {ρ₁ : ℝ} (hρ : 0 < ρ₁)
    (h : ∀ ζ ∈ ball (0 : ℂ) ρ₁, alComplexLog38 α (fun j => star (α j)) ζ = alLog38 α ζ) (j : ℕ) :
    (alKc38 j (α, fun j => star (α j))).re = alMomentK38 α j := by
  unfold alKc38
  simp only [alCc38_real hρ h]
  have h0 : alC38 α 0 = ((alMass38 L α / 2 : ℝ) : ℂ) := by
    have := (alLog38_spec hα).2.2.1
    simpa [alC38] using this
  rw [h0]
  unfold alMomentK38
  have e1 : (2 * (Nat.choose (2 * j) j : ℂ) * ((alMass38 L α / 2 : ℝ) : ℂ)) =
      (((Nat.choose (2 * j) j : ℝ) * alMass38 L α : ℝ) : ℂ) := by push_cast; ring
  have e2 : ∀ k : ℕ, (-1 : ℂ) ^ k * (Nat.choose (2 * j) (j - k) : ℂ) * alC38 α k =
      (((-1 : ℝ) ^ k * (Nat.choose (2 * j) (j - k) : ℝ) : ℝ) : ℂ) * alC38 α k := by
    intro k; push_cast; ring
  simp only [e2]
  rw [Complex.add_re, e1, Complex.ofReal_re]
  have : (2 : ℂ) * ∑ k ∈ Finset.Icc 1 j, (((-1 : ℝ) ^ k * (Nat.choose (2 * j) (j - k) : ℝ) : ℝ) : ℂ)
      * alC38 α k = (((2 : ℝ)) : ℂ) * ∑ k ∈ Finset.Icc 1 j,
        (((-1 : ℝ) ^ k * (Nat.choose (2 * j) (j - k) : ℝ) : ℝ) : ℂ) * alC38 α k := by push_cast; ring
  rw [this, Complex.re_ofReal_mul, Complex.re_sum]
  simp only [Complex.re_ofReal_mul]

theorem isOpen_alDiskAn38 : IsOpen (alDisk38 L) := by
  have : alDisk38 L = ⋂ j : ZMod L, {α : ZMod L → ℂ | ‖α j‖ < 1} := by
    ext α; simp [alDisk38, IsALField38]
  rw [this]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const

/-- The `ℝ`-linear embedding of the real slice `α ↦ (α, conj α)`. -/
def alIota38 : (ZMod L → ℂ) →L[ℝ] (ZMod L → ℂ) × (ZMod L → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => (α, fun j => star (α j))
      map_add' := fun a b => by ext <;> simp
      map_smul' := fun r a => by ext <;> simp }

theorem alIota38_apply (α : ZMod L → ℂ) : alIota38 α = (α, fun j => star (α j)) := rfl

/-- `D:thm:ALfinite`, real analyticity of `E_{W,h}` at a point of `𝔻^L`. -/
theorem analyticAt_alEnergy38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h)
    {α₀ : ZMod L → ℂ} (hα₀ : IsALField38 α₀) : AnalyticAt ℝ (alEnergy38 c h) α₀ := by
  obtain ⟨U, ρ₁, hUo, hp0U, hUdom, hρ, hρ1, hDG, hlog, hexp, hreal⟩ := exists_alComplexLogNhd38 hα₀
  set p0 : (ZMod L → ℂ) × (ZMod L → ℂ) := (α₀, fun j => star (α₀ j)) with hp0
  obtain ⟨s, hs, hsU, ρ, S, hρpos, hS0, hCb⟩ := exists_alCc_bound38 hρ hUo hlog hp0U
  set q : ℝ := (ρ ^ 2)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  set R : ℝ := max 1 q with hR
  have hR0 : 0 ≤ R := le_trans zero_le_one (le_max_left _ _)
  set f : ℕ → (ZMod L → ℂ) × (ZMod L → ℂ) → ℂ := fun j p =>
    ((NlsGge.coefficient c j * (h⁻¹) ^ (2 * j + 1) : ℝ) : ℂ) * alKc38 j p with hf
  have hcoef : ∀ j, 0 ≤ NlsGge.coefficient c j := coefficient_nonneg_of_class38 hc
  set m : ℕ → ℝ := fun j => (NlsGge.coefficient c j * (h⁻¹) ^ (2 * j + 1)) *
    (2 * S * (8 * R) ^ j) with hm
  have hmsum : Summable m := by
    have hw := (NlsGge.Weights.weightTerm_summable lo up c hc.1 (fun i => (hc.2.2 i).1)
      (fun i => (hc.2.2 i).2) (Real.sqrt (8 * R) / h)).mul_left (2 * S * h⁻¹)
    refine hw.congr fun j => ?_
    simp only [hm, NlsGge.weightTerm]
    have : (Real.sqrt (8 * R) / h) ^ (2 * j) = (8 * R) ^ j * (h⁻¹) ^ (2 * j) := by
      rw [pow_mul, div_pow, Real.sq_sqrt (by positivity), pow_mul, div_eq_mul_inv, inv_pow, mul_pow]
    rw [this, pow_succ]; ring
  have hbd : ∀ j, ∀ p ∈ closedBall p0 s, ‖f j p‖ ≤ m j := by
    intro j p hp
    simp only [hf, hm]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (mul_nonneg (hcoef j) (pow_nonneg (inv_nonneg.2 hh.le) _))]
    exact mul_le_mul_of_nonneg_left (norm_alKc38_le hS0 hq0 (hCb p hp) j)
      (mul_nonneg (hcoef j) (pow_nonneg (inv_nonneg.2 hh.le) _))
  have hfan : ∀ j, AnalyticOnNhd ℂ (f j) (closedBall p0 s) := fun j p hp =>
    analyticAt_const.mul (analyticAt_alKc38 hρ hUo hlog j (hsU hp))
  have hEc : AnalyticAt ℂ (fun y => ∑' j, f j y) p0 :=
    NlsGge.AnalyticTsum38.analyticAt_tsum_of_bound38 hs hfan hmsum hbd
  have hι : AnalyticAt ℝ (alIota38 (L := L)) α₀ := alIota38.analyticAt α₀
  have hEcR : AnalyticAt ℝ (fun y => ∑' j, f j y) (alIota38 α₀) := hEc.restrictScalars
  have hcomp : AnalyticAt ℝ (fun α => (∑' j, f j (alIota38 α)).re) α₀ :=
    (Complex.reCLM.analyticAt _).comp (hEcR.comp hι)
  refine hcomp.congr ?_
  have hn1 : ∀ᶠ α in 𝓝 α₀, α ∈ alDisk38 L := isOpen_alDiskAn38.mem_nhds hα₀
  have hn2 : ∀ᶠ α in 𝓝 α₀, alIota38 α ∈ closedBall p0 s :=
    alIota38.continuous.continuousAt.eventually (closedBall_mem_nhds _ hs)
  filter_upwards [hn1, hn2] with α hα hαB
  have hαU : (α, fun j => star (α j)) ∈ U := hsU hαB
  have hrl := hreal α hα hαU
  have hsm : Summable (fun j => f j (alIota38 α)) :=
    Summable.of_norm_bounded hmsum (fun j => hbd j _ hαB)
  have hre := Complex.hasSum_re hsm.hasSum
  rw [← hre.tsum_eq]
  unfold alEnergy38
  refine tsum_congr fun j => ?_
  simp only [hf, alEnergyTerm38, alQ38, alIota38_apply]
  rw [Complex.re_ofReal_mul, alKc38_re hα hρ hrl]
  ring

theorem analyticOnNhd_alEnergy38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) :
    AnalyticOnNhd ℝ (alEnergy38 c h) (alDisk38 L) := fun _ hα => analyticAt_alEnergy38 hc hh hα

end NlsGge.AblowitzLadik
end
