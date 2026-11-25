import Mathlib
import QuantumNLS.RB01Resolvent

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-4: the projection columns and the compression at
high labels, for arbitrary real fields.

Source (collective_actions.tex:239-280): "Since `R_{0,n}χ_{n,α} = χ_{n,α}/w`, the resolvent identity gives
`R_n χ_{n,α} = χ_{n,α}/w + F_n A_n χ_{n,α}/w` ... `S_n = P_n^0 P_n P_n^0` ... At `q_0`, `S_n → 1`.  By increasing
`N` and shrinking the neighborhood, we may arrange `sup_{|n|>N} ‖S_n - 1‖ < 1/2`."

Proved here for the actual objects (real slice), with `A_n(z) χ = R_{0,n}(z)(V_u χ)` realized as
`T_n(z̄)^* χ` (`adjT_chi`) — the source's `A_n = R_0 V` on vectors whose image under `V` is square integrable:
* `graph_symm`: `𝓛_u` is symmetric on `D_{(-1)^n}` for every potential (from the proved LOCAL-001 at `p_n + iπ/L`).
* `resolvent_adjoint`: `R(z)^* = R(z̄)` for every real field (and `u = 0`).
* `Vchi`: the square-integrable vector `V_u χ_{m,j}`; `Vchi_trig` for finite Fourier sums.
* `column_decay`: for every `u₀` and `ε > 0` there are `N`, `ρ` with `‖R_{0,n}(z)(V_u χ_{n,j})‖ ≤ ε` for `|n| > N`,
  `‖u - u₀‖ < ρ`, `z` on the annulus (the pointwise form of the collective column bound).
* `proj_column`: `‖(P_n(u) - P_n^0) χ_{n,j}‖ ≤ W ε` under square-smallness.
* **`small_compression`**: for every `u₀` there are `N`, `ρ` such that for `|n| > N`, `‖u - u₀‖ < ρ` the actual
  compression satisfies `‖E^* P_n(u) E - 1‖ ≤ 1/2` (in particular LOCAL-003's `SmallCompression`).
The collective `ℓ²` (rather than pointwise) column bound and its analyticity are later stages. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.RB01Columns
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free QuantumNLS.Local002Rank
  QuantumNLS.Local002SA QuantumNLS.Local002Basis QuantumNLS.RB01FourierAction QuantumNLS.RB01SquareSmall
  QuantumNLS.RB01Resolvent

variable {L κ : ℝ}

/-! ### Symmetry and adjoints of resolvents -/

theorem graph_symm (hL : 0 < L) (n : ℤ) (u : ℝ → ℂ) :
    ∀ p ∈ LuGraph L κ u (parity n), ∀ q ∈ LuGraph L κ u (parity n), ⟪p.1, q.2⟫_ℂ = ⟪p.2, q.1⟫_ℂ := by
  set r0 : ℝ := Real.pi / L with hr0def
  have hr0 : 0 < r0 := by positivity
  have hr02 : r0 < 2 * Real.pi / L := by
    rw [hr0def]; exact div_lt_div_of_pos_right (by linarith [Real.pi_pos]) hL
  obtain ⟨z, hzdef⟩ : ∃ z : ℂ, z = (pm L n : ℂ) + (r0 : ℂ) * Complex.I := ⟨_, rfl⟩
  have hz : ‖z - (pm L n : ℂ)‖ = r0 := by
    rw [hzdef]; simp [abs_of_pos hr0]
  have hzc : ‖conj z - (pm L n : ℂ)‖ = r0 := by
    have : conj z - (pm L n : ℂ) = conj (z - (pm L n : ℂ)) := by simp [Complex.conj_ofReal]
    rw [this, RCLike.norm_conj, hz]
  have him : z.im ≠ 0 := by
    rw [hzdef]; simpa using hr0.ne'
  obtain ⟨R0, hR0, -⟩ := (QuantumNLS.Local002Discharge.free_resolvent_hyp L κ).res r0 n z hr0 hr02 hz
  obtain ⟨R0', hR0', -⟩ :=
    (QuantumNLS.Local002Discharge.free_resolvent_hyp L κ).res r0 n (conj z) hr0 hr02 hzc
  exact fun p hp q hq => Gu_symm hL him hR0 hR0' hp hq

theorem resolvent_adjoint {u : ℝ → ℂ} {σ : ℤˣ}
    (hsym : ∀ p ∈ LuGraph L κ u σ, ∀ q ∈ LuGraph L κ u σ, ⟪p.1, q.2⟫_ℂ = ⟪p.2, q.1⟫_ℂ)
    {z : ℂ} {R R' : H2 L →L[ℂ] H2 L} (hR : IsResolvent L κ u σ z R)
    (hR' : IsResolvent L κ u σ (conj z) R') : ContinuousLinearMap.adjoint R = R' := by
  ext1 φ
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  have h := hsym _ (hR.1 g) _ (hR'.1 φ)
  simp only at h
  rw [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left] at h
  linear_combination -h

/-! ### The vector `V_u χ_{m,j}` -/

theorem memLp_Vchi (κ : ℝ) (u : Lp ℂ 2 (μI L)) (m : ℤ) (j : Fin 2) :
    MemLp (fun x => Vpt κ ((u : ℝ → ℂ) x) (chiFun L m j x)) 2 (μI L) := by
  have hpair : AEStronglyMeasurable (fun x => ((u : ℝ → ℂ) x, chiFun L m j x)) (μI L) :=
    (Lp.aestronglyMeasurable u).prodMk (continuous_chiFun L m j).aestronglyMeasurable
  have hmeas := (QuantumNLS.Local002Domain.continuous_Vpt κ).comp_aestronglyMeasurable hpair
  refine (QuantumNLS.Local002Domain.memLp_dom u (2 * Real.sqrt κ * (Real.sqrt L)⁻¹)).mono hmeas ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h := QuantumNLS.Local002Domain.norm_Vpt_le κ ((u : ℝ → ℂ) x) (chiFun L m j x)
  rw [norm_chiFun] at h
  have h2 : 2 * Real.sqrt κ * ‖(u : ℝ → ℂ) x‖ * (Real.sqrt L)⁻¹ =
      2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ‖(u : ℝ → ℂ) x‖ := by ring
  rw [h2] at h
  exact h.trans (Real.le_norm_self _)

/-- `V_u χ_{m,j} ∈ L²(0,L;ℂ²)`. -/
def Vchi (κ : ℝ) (u : Lp ℂ 2 (μI L)) (m : ℤ) (j : Fin 2) : H2 L := (memLp_Vchi κ u m j).toLp _

theorem Vchi_add (u u' : Lp ℂ 2 (μI L)) (m : ℤ) (j : Fin 2) :
    Vchi κ (u + u') m j = Vchi κ u m j + Vchi κ u' m j := by
  apply Lp.ext
  filter_upwards [(memLp_Vchi κ (u + u') m j).coeFn_toLp, (memLp_Vchi κ u m j).coeFn_toLp,
    (memLp_Vchi κ u' m j).coeFn_toLp, Lp.coeFn_add (Vchi κ u m j) (Vchi κ u' m j),
    Lp.coeFn_add u u'] with x a1 a2 a3 a4 a5
  rw [a4, Pi.add_apply]
  change _ = (Vchi κ u m j : ℝ → E2) x + (Vchi κ u' m j : ℝ → E2) x
  unfold Vchi
  rw [a1, a2, a3, a5, Pi.add_apply, QuantumNLS.Local002.Vpt_add_pot]

theorem Vchi_mode (hL : 0 < L) (c : ℂ) (k m : ℤ) (j : Fin 2) :
    Vchi κ (c • emode L k) m j = coef κ L c j • chi L (2 * k - m) (flip j) := by
  apply Lp.ext
  filter_upwards [(memLp_Vchi κ (c • emode L k) m j).coeFn_toLp, Lp.coeFn_smul c (emode L k),
    coeFn_emode L k, Lp.coeFn_smul (coef κ L c j) (chi L (2 * k - m) (flip j)),
    (memLp_chiFun L (2 * k - m) (flip j)).coeFn_toLp] with x a1 a2 a3 a4 a5
  unfold Vchi
  rw [a1, a4, a2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, a3]
  have e5 : (chi L (2 * k - m) (flip j) : ℝ → E2) x = chiFun L (2 * k - m) (flip j) x := a5
  rw [e5, Vpt_mode_chi]

theorem Vchi_zero (m : ℤ) (j : Fin 2) : Vchi κ (0 : Lp ℂ 2 (μI L)) m j = 0 := by
  apply Lp.ext
  filter_upwards [(memLp_Vchi κ (0 : Lp ℂ 2 (μI L)) m j).coeFn_toLp, Lp.coeFn_zero ℂ 2 (μI L),
    Lp.coeFn_zero E2 2 (μI L)] with x a1 a2 a3
  unfold Vchi
  rw [a1, a2, a3]
  simp [QuantumNLS.Local002.Vpt_zero_pot]

theorem Vchi_trig (hL : 0 < L) (S : Finset ℤ) (c : ℤ → ℂ) (m : ℤ) (j : Fin 2) :
    Vchi κ (∑ k ∈ S, c k • emode L k) m j = ∑ k ∈ S, coef κ L (c k) j • chi L (2 * k - m) (flip j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Vchi_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Vchi_add, ih, Vchi_mode hL]

/-- `T(z̄)^* χ = R_0(z)(V_u χ)`: the source's `A_n χ = R_0 V χ`. -/
theorem adjT_chi {R0 R0' T' : H2 L →L[ℂ] H2 L} {u : Lp ℂ 2 (μI L)}
    (hT' : QuantumNLS.Local002.IsMulOp κ R0' (u : ℝ → ℂ) T')
    (hadj : ContinuousLinearMap.adjoint R0' = R0) (m : ℤ) (j : Fin 2) :
    ContinuousLinearMap.adjoint T' (chi L m j) = R0 (Vchi κ u m j) := by
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, ← hadj, ContinuousLinearMap.adjoint_inner_right,
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hT' g, (memLp_chiFun L m j).coeFn_toLp, (memLp_Vchi κ u m j).coeFn_toLp]
    with x a1 a2 a3
  have e2 : (chi L m j : ℝ → E2) x = chiFun L m j x := a2
  have e3 : (Vchi κ u m j : ℝ → E2) x = Vpt κ ((u : ℝ → ℂ) x) (chiFun L m j x) := a3
  rw [a1, e2, e3]
  exact (QuantumNLS.Local002SA.Vpt_herm κ _ _ _).symm

/-- The free resolvents at `z` and `z̄` are adjoint. -/
theorem free_adjoint (hL : 0 < L) {n : ℤ} {z : ℂ} {R0 R0' : H2 L →L[ℂ] H2 L}
    (hR0 : IsResolvent L κ (fun _ => 0) (parity n) z R0)
    (hR0' : IsResolvent L κ (fun _ => 0) (parity n) (conj z) R0') :
    ContinuousLinearMap.adjoint R0' = R0 := by
  refine resolvent_adjoint (graph_symm hL n (fun _ => 0)) hR0' ?_
  rwa [Complex.conj_conj]

theorem conj_annulus {n : ℤ} {z : ℂ} : ‖conj z - (pm L n : ℂ)‖ = ‖z - (pm L n : ℂ)‖ := by
  have : conj z - (pm L n : ℂ) = conj (z - (pm L n : ℂ)) := by simp [Complex.conj_ofReal]
  rw [this, RCLike.norm_conj]

/-! ### Decay of the columns at high labels -/

theorem column_decay [Fact (0 < L)] (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (u₀ : Lp ℂ 2 (μI L)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → ∀ u : Lp ℂ 2 (μI L), ‖u - u₀‖ < ρ →
      ∀ z : ℂ, r / 2 ≤ ‖z - (pm L n : ℂ)‖ → ‖z - (pm L n : ℂ)‖ ≤ r →
      ∀ R0 : H2 L →L[ℂ] H2 L, IsResolvent L κ (fun _ => 0) (parity n) z R0 →
      ∀ j : Fin 2, ‖R0 (Vchi κ u n j)‖ ≤ ε := by
  set M := Mr L κ r with hM
  have hM0 : 0 ≤ M := Mr_nonneg L κ r
  set ε₁ := ε / (4 * (M + 1)) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  obtain ⟨S, c, hac⟩ := exists_trig_approx u₀ hε₁pos
  set a : Lp ℂ 2 (μI L) := ∑ k ∈ S, c k • emode L k with ha
  set K : ℕ := S.sup (fun k => k.natAbs) with hKdef
  have hK : ∀ k ∈ S, |(k : ℝ)| ≤ K := by
    intro k hk
    have h1 : k.natAbs ≤ K := Finset.le_sup (f := fun k : ℤ => k.natAbs) hk
    have h2 : (k.natAbs : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← h2]; exact_mod_cast h1
  set A := ∑ k ∈ S, 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ‖c k‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => by positivity
  set N : ℕ := K + ⌈(2 * A / ε + r) * L / (4 * Real.pi)⌉₊ with hN
  refine ⟨N, ε₁, hε₁pos, ?_⟩
  intro n hn u hu z h1 h2 R0 hR0 j
  have hzc1 : r / 2 ≤ ‖conj z - (pm L n : ℂ)‖ := by rw [conj_annulus]; exact h1
  have hzc2 : ‖conj z - (pm L n : ℂ)‖ ≤ r := by rw [conj_annulus]; exact h2
  obtain ⟨R0', hR0', -⟩ := free_res_annulus (κ := κ) hL hr hr2 hzc1 hzc2
  have hadj := free_adjoint hL hR0 hR0'
  -- the remainder field `b = u - a`
  obtain ⟨Tb, hTb, hTbn⟩ := exists_T_annulus hL hr hr2 hzc1 hzc2 hR0' (u - a)
  have hb : ‖u - a‖ ≤ 2 * ε₁ := by
    have h' : ‖a - u₀‖ < ε₁ := hac
    have := norm_sub_le (u - u₀) (a - u₀)
    rw [show u - u₀ - (a - u₀) = u - a by abel] at this
    linarith
  have hbpart : ‖R0 (Vchi κ (u - a) n j)‖ ≤ ε / 2 := by
    rw [← adjT_chi hTb hadj n j]
    calc ‖ContinuousLinearMap.adjoint Tb (chi L n j)‖
        ≤ ‖ContinuousLinearMap.adjoint Tb‖ * ‖chi L n j‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Tb‖ := by rw [LinearIsometryEquiv.norm_map, norm_chi hL, mul_one]
      _ ≤ M * (2 * ε₁) := hTbn.trans (mul_le_mul_of_nonneg_left hb hM0)
      _ ≤ ε / 2 := by
          rw [hε₁]
          have : M * (2 * (ε / (4 * (M + 1)))) = ε / 2 * (M / (M + 1)) := by field_simp; ring
          rw [this]
          have : M / (M + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          nlinarith
  -- the trigonometric part
  have hdist : ∀ k ∈ S, 4 * Real.pi * (|(n : ℝ)| - K) / L - r ≤ ‖z - (pm L (2 * k - n) : ℂ)‖ := by
    intro k hkS
    have hge := norm_z_sub_pm_ge (l := 2 * k - n) hL h2
    have habs : 2 * (|(n : ℝ)| - K) ≤ |((2 * k - n : ℤ) : ℝ) - n| := by
      have e : ((2 * k - n : ℤ) : ℝ) - n = -(2 * ((n : ℝ) - k)) := by push_cast; ring
      rw [e, abs_neg, abs_mul, abs_two]
      have := abs_sub_abs_le_abs_sub (n : ℝ) (k : ℝ)
      linarith [hK k hkS]
    have : 4 * Real.pi * (|(n : ℝ)| - K) / L ≤ 2 * Real.pi * |((2 * k - n : ℤ) : ℝ) - n| / L := by
      apply div_le_div_of_nonneg_right _ hL.le
      nlinarith [Real.pi_pos]
    linarith
  have hδ : 2 * A / ε < 4 * Real.pi * (|(n : ℝ)| - K) / L - r := by
    have hceil : (2 * A / ε + r) * L / (4 * Real.pi) ≤ (N : ℝ) - K := by
      rw [hN]; push_cast
      linarith [Nat.le_ceil ((2 * A / ε + r) * L / (4 * Real.pi))]
    have h3 : (2 * A / ε + r) * L / (4 * Real.pi) < |(n : ℝ)| - K := by linarith
    rw [div_lt_iff₀ (by positivity)] at h3
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hL]
    linarith
  have hδpos : 0 < 4 * Real.pi * (|(n : ℝ)| - K) / L - r := lt_of_le_of_lt (by positivity) hδ
  have hzne : ∀ m : ℤ, z ≠ (pm L m : ℂ) := fun m h => by
    have := (inv_sq_le_gmaj (l := m) hL hr hr2 h1 h2).1
    rw [h, sub_self, norm_zero] at this
    exact lt_irrefl _ this
  have hapart : ‖R0 (Vchi κ a n j)‖ ≤ ε / 2 := by
    rw [ha, Vchi_trig hL, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ S, ‖R0 (coef κ L (c k) j • chi L (2 * k - n) (flip j))‖ ≤
        2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ‖c k‖ / (4 * Real.pi * (|(n : ℝ)| - K) / L - r) := by
      intro k hkS
      rw [map_smul, res_chi hL (flip j) hR0 (parity_reflect k n) (hzne _), smul_smul, norm_smul,
        norm_chi hL, mul_one, norm_mul, norm_coef, norm_inv, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by positivity) hδpos (hdist k hkS)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_div, ← hA, div_le_iff₀ hδpos]
    have := (div_lt_iff₀ hε).mp (show 2 * A / ε < _ from hδ)
    nlinarith
  have hsplit : Vchi κ u n j = Vchi κ a n j + Vchi κ (u - a) n j := by
    rw [← Vchi_add, add_sub_cancel]
  rw [hsplit, map_add]
  calc ‖R0 (Vchi κ a n j) + R0 (Vchi κ (u - a) n j)‖
      ≤ ‖R0 (Vchi κ a n j)‖ + ‖R0 (Vchi κ (u - a) n j)‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hapart hbpart
    _ = ε := by ring

/-! ### The projection columns and the compression -/

theorem resolvent_sub_chi (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u) {z : ℂ} (hz : ‖z - (pm L n : ℂ)‖ = r)
    {ε : ℝ} (j : Fin 2)
    (hcol : ∀ R0 : H2 L →L[ℂ] H2 L, IsResolvent L κ (fun _ => 0) (parity n) z R0 →
      ‖R0 (Vchi κ u n j)‖ ≤ ε) :
    ‖(resolvent L κ (u : ℝ → ℂ) (parity n) z - resolvent L κ (fun _ => 0) (parity n) z) (chi L n j)‖ ≤
      Wb L κ r u * ε / r := by
  have h1 : r / 2 ≤ ‖z - (pm L n : ℂ)‖ := by rw [hz]; linarith
  have h2 : ‖z - (pm L n : ℂ)‖ ≤ r := hz.le
  have hzc1 : r / 2 ≤ ‖conj z - (pm L n : ℂ)‖ := by rw [conj_annulus]; exact h1
  have hzc2 : ‖conj z - (pm L n : ℂ)‖ ≤ r := by rw [conj_annulus]; exact h2
  obtain ⟨R0, hR0, -⟩ := free_res_annulus (κ := κ) hL hr hr2 h1 h2
  obtain ⟨R0', hR0', -⟩ := free_res_annulus (κ := κ) hL hr hr2 hzc1 hzc2
  have hadj := free_adjoint hL hR0 hR0'
  obtain ⟨T', hT', hT'n⟩ := exists_T_annulus hL hr hr2 hzc1 hzc2 hR0' u
  obtain ⟨S', hS1, hS2, hSn⟩ := inverse_bound (hu (conj z) hzc1 hzc2 R0' T' hR0' hT')
  have hR' : IsResolvent L κ (u : ℝ → ℂ) (parity n) (conj z) (R0' * S') :=
    resolvent_of_inverse hR0' hT' hS1 hS2
  obtain ⟨R, hR, -⟩ := resolvent_exists hL hr hr2 hu h1 h2
  have hRadj : ContinuousLinearMap.adjoint (R0' * S') = R := by
    refine resolvent_adjoint (graph_symm hL n (u : ℝ → ℂ)) hR' ?_
    rwa [Complex.conj_conj]
  have hS' : S' - 1 = T' * S' := by
    have : S' - T' * S' = 1 := by rw [← hS1, sub_mul, one_mul]
    rw [← this]; abel
  have hdiff : R - R0 = ContinuousLinearMap.adjoint S' * ContinuousLinearMap.adjoint T' *
      ContinuousLinearMap.adjoint R0' := by
    rw [← hRadj, ← hadj, ← map_sub]
    have e : R0' * S' - R0' = R0' * (T' * S') := by rw [← hS', mul_sub, mul_one]
    rw [e]
    change ContinuousLinearMap.adjoint (R0' ∘L (T' ∘L S')) = _
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
    rfl
  have hne : z ≠ (pm L n : ℂ) := fun h => by
    rw [h, sub_self, norm_zero] at hz; exact hr.ne' hz.symm
  rw [resolvent_eq hR, resolvent_eq hR0, hdiff, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply, hadj, res_chi hL j hR0 rfl hne, map_smul, map_smul,
    adjT_chi hT' hadj n j, norm_smul, norm_inv, hz]
  have hb : ‖ContinuousLinearMap.adjoint S' (R0 (Vchi κ u n j))‖ ≤ Wb L κ r u * ε := by
    have hS'W : ‖S'‖ ≤ Wb L κ r u := by
      refine hSn.trans ?_
      unfold Wb
      gcongr
    calc ‖ContinuousLinearMap.adjoint S' (R0 (Vchi κ u n j))‖
        ≤ ‖ContinuousLinearMap.adjoint S'‖ * ‖R0 (Vchi κ u n j)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Wb L κ r u * ε := by
          rw [LinearIsometryEquiv.norm_map]
          exact mul_le_mul hS'W (hcol R0 hR0) (norm_nonneg _) ((norm_nonneg _).trans hS'W)
  calc r⁻¹ * ‖ContinuousLinearMap.adjoint S' (R0 (Vchi κ u n j))‖ ≤ r⁻¹ * (Wb L κ r u * ε) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = Wb L κ r u * ε / r := by ring

theorem proj_column (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u) {ε : ℝ} (j : Fin 2)
    (hcol : ∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r → ∀ R0 : H2 L →L[ℂ] H2 L,
      IsResolvent L κ (fun _ => 0) (parity n) z R0 → ‖R0 (Vchi κ u n j)‖ ≤ ε) :
    ‖(perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r) (chi L n j)‖ ≤ Wb L κ r u * ε := by
  have hsph : ∀ z ∈ sphere (QuantumNLS.LocalSpectral.center L n) r, ‖z - (pm L n : ℂ)‖ = r :=
    fun z hz => by simpa [QuantumNLS.LocalSpectral.center, mem_sphere_iff_norm] using hz
  have hcu : ContinuousOn (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z)
      (sphere (QuantumNLS.LocalSpectral.center L n) r) :=
    continuousOn_resolvent _ (Rb_nonneg L κ hr u) (fun z hz => by
      have h := hsph z hz
      exact resolvent_exists hL hr hr2 hu (by rw [h]; linarith) h.le)
  have hc0 : ContinuousOn (fun z => resolvent L κ (fun _ => 0) (parity n) z)
      (sphere (QuantumNLS.LocalSpectral.center L n) r) :=
    continuousOn_resolvent _ (M := 2 / r) (by positivity) (fun z hz => by
      have h := hsph z hz
      exact free_res_annulus (κ := κ) hL hr hr2 (by rw [h]; linarith) h.le)
  have hvu : ContinuousOn (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z (chi L n j))
      (sphere (QuantumNLS.LocalSpectral.center L n) r) := hcu.clm_apply continuousOn_const
  have hv0 : ContinuousOn (fun z => resolvent L κ (fun _ => 0) (parity n) z (chi L n j))
      (sphere (QuantumNLS.LocalSpectral.center L n) r) := hc0.clm_apply continuousOn_const
  have key := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (c := QuantumNLS.LocalSpectral.center L n) (R := r) (C := Wb L κ r u * ε / r)
    (f := fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z (chi L n j) -
      resolvent L κ (fun _ => 0) (parity n) z (chi L n j)) hr.le
    (fun z hz => by
      have := resolvent_sub_chi hL hr hr2 hu (hsph z hz) j (hcol z (hsph z hz))
      simpa using this)
  rw [circleIntegral.integral_sub (hvu.circleIntegrable hr.le) (hv0.circleIntegrable hr.le),
    smul_sub, ← circleIntegral_apply _ (hcu.circleIntegrable hr.le),
    ← circleIntegral_apply _ (hc0.circleIntegrable hr.le)] at key
  unfold perturbedProj freeProj rieszProj
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  refine key.trans (le_of_eq ?_)
  field_simp

theorem norm_embed_le (hL : 0 < L) (n : ℤ) : ‖embed L n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  have h : ‖embed L n v‖ = ‖v‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_embed hL]
  rw [h, one_mul]

/-- `(C_n(u) - 1) v = E^*((P_n(u) - P_n^0)(E v))`. -/
theorem compression_sub_apply (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : ℝ → ℂ) (v : E2) :
    (compressionMatrix L κ u n r - 1) v = ContinuousLinearMap.adjoint (embed L n)
      ((perturbedProj L κ u n r - freeProj L κ n r) (embed L n v)) := by
  have hres : ∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r → ∃ R : H2 L →L[ℂ] H2 L,
      IsResolvent L κ (fun _ => 0) (parity n) z R ∧ ‖R‖ ≤ 1 / r := fun z hz =>
    (QuantumNLS.Local002Discharge.free_resolvent_hyp L κ).res r n z hr hr2 hz
  have hid : ContinuousLinearMap.adjoint (embed L n) (embed L n v) = v := by
    have := congrArg (fun A : E2 →L[ℂ] E2 => A v) (adjoint_embed_comp_embed hL n)
    simpa using this
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, map_sub,
    freeProj_eq hL hr hr2 n hres]
  simp only [ContinuousLinearMap.comp_apply, compressionMatrix, hid, ContinuousLinearMap.one_apply]

/-- **The compression at high labels**: `‖C_n(u) - 1‖ ≤ 1/2` for `|n| > N` and `‖u - u₀‖ < ρ`. -/
theorem small_compression [Fact (0 < L)] (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (u₀ : Lp ℂ 2 (μI L)) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → ∀ u : Lp ℂ 2 (μI L), ‖u - u₀‖ < ρ →
      SqSmall L κ r n u ∧ ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ ≤ 1 / 2 ∧
      SmallCompression L κ (u : ℝ → ℂ) n r := by
  obtain ⟨N1, ρ1, hρ1, h1⟩ := arbitrary_field_riesz (κ := κ) hL hr hr2 u₀
  set W₀ : ℝ := (1 + Mr L κ r * (‖u₀‖ + 1)) * (4 / 3) with hW₀
  have hM0 := Mr_nonneg L κ r
  have hW₀pos : 0 < W₀ := by positivity
  obtain ⟨N2, ρ2, hρ2, h2⟩ := column_decay (κ := κ) hL hr hr2 u₀ (ε := 1 / (4 * W₀)) (by positivity)
  refine ⟨max N1 N2, min (min ρ1 ρ2) 1, lt_min (lt_min hρ1 hρ2) one_pos, ?_⟩
  intro n hn u hu
  have hn1 : (N1 : ℝ) < |(n : ℝ)| := lt_of_le_of_lt (by exact_mod_cast le_max_left N1 N2) hn
  have hn2 : (N2 : ℝ) < |(n : ℝ)| := lt_of_le_of_lt (by exact_mod_cast le_max_right N1 N2) hn
  have hu1 : ‖u - u₀‖ < ρ1 := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_left _ _))
  have hu2 : ‖u - u₀‖ < ρ2 := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_right _ _))
  have hu3 : ‖u - u₀‖ < 1 := lt_of_lt_of_le hu (min_le_right _ _)
  have hs : SqSmall L κ r n u := (h1 n hn1 u hu1).1
  have hW : Wb L κ r u ≤ W₀ := by
    have : ‖u‖ ≤ ‖u₀‖ + 1 := by have := norm_le_insert' u u₀; linarith
    unfold Wb; rw [hW₀]; gcongr
  have hcol : ∀ j : Fin 2, ‖(perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r) (chi L n j)‖ ≤
      1 / 4 := by
    intro j
    refine (proj_column hL hr hr2 hs j (fun z hz R0 hR0 =>
      h2 n hn2 u hu2 z (by rw [hz]; linarith) hz.le R0 hR0 j)).trans ?_
    calc Wb L κ r u * (1 / (4 * W₀)) ≤ W₀ * (1 / (4 * W₀)) :=
          mul_le_mul_of_nonneg_right hW (by positivity)
      _ = 1 / 4 := by field_simp
  have hbound : ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ ≤ 1 / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
    rw [compression_sub_apply hL hr hr2 n]
    set D := perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r
    have hE : ‖ContinuousLinearMap.adjoint (embed L n)‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact norm_embed_le hL n
    calc ‖ContinuousLinearMap.adjoint (embed L n) (D (embed L n v))‖
        ≤ ‖ContinuousLinearMap.adjoint (embed L n)‖ * ‖D (embed L n v)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖D (embed L n v)‖ := mul_le_mul_of_nonneg_right hE (norm_nonneg _)
      _ = ‖v 0 • D (chi L n 0) + v 1 • D (chi L n 1)‖ := by
          rw [one_mul, embed_apply, map_add, map_smul, map_smul]
      _ ≤ ‖v 0‖ * (1 / 4) + ‖v 1‖ * (1 / 4) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
          exact add_le_add (mul_le_mul_of_nonneg_left (hcol 0) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hcol 1) (norm_nonneg _))
      _ ≤ 1 / 2 * ‖v‖ := by
          have a0 := PiLp.norm_apply_le v 0
          have a1 := PiLp.norm_apply_le v 1
          linarith
  exact ⟨hs, hbound, lt_of_le_of_lt hbound (by norm_num)⟩

end QuantumNLS.RB01Columns
#print axioms QuantumNLS.RB01Columns.resolvent_adjoint
#print axioms QuantumNLS.RB01Columns.adjT_chi
#print axioms QuantumNLS.RB01Columns.column_decay
#print axioms QuantumNLS.RB01Columns.proj_column
#print axioms QuantumNLS.RB01Columns.small_compression
