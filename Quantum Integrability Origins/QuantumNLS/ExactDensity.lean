import Mathlib
import QuantumNLS.AuxiliaryDensity
import QuantumNLS.TraceClass

/-!
# R-BB03032A `prop:exact-density`: positivity, normalization, and entry orientation of `Γ_N[ψ]`

Source: `source/chapters/core/projective_reconstruction.tex`, Proposition `prop:exact-density` (line 27) and its proof
(lines 53-90).  Statement: for a unit `ψ ∈ 𝓗_N` there is a positive trace-class operator `Γ_N[ψ]` on `h = ℓ²(ℤ)` with trace one
whose row-`a`, column-`b` entry is `⟨e_a, Γ e_b⟩ = ⟨ψ, E^q_{N,ab}ψ⟩ = (1/N)⟨J_Nψ, b_b^*b_aJ_Nψ⟩
= (1/N) ∑_{ν∈𝓜_{N-1}} √((ν_a+1)(ν_b+1)) d_{ν+e_a} \overline{d_{ν+e_b}}` (all entry series absolutely convergent); for
`a ≠ b` it equals the shifted-entry sum over `m ∈ 𝓜_N`, `m_a ≥ 1`, of
`(√(m_a(m_b+1))/N) q_N(m) \overline{q_N(m-e_a+e_b)} g_m \overline{g_{m-e_a+e_b}}`.  (The closing remark, that the limiting rank-one
matrix has entries `w_a \overline{w_b}`, is the convention fixed in `AuxiliaryDensity.rankOneOperator_matrix`.)

## Realized objects used read-only (nothing unrealized is needed; no parameters beyond the statement's `b, g, ψ`)
DEF-029 `AuxiliaryDensity.gammaEntry b g ψ a c = ⟨ψ, E^q_{N,ac}ψ⟩` (and `gammaEntry_eq_coefficient`); DEF-026
`CartesianOccupationTransfer` (`physical = E^q`, `coordinates b g = J_N` as the coefficient vector `d`, `auxiliary` the
normalized collective one-body operator `N⁻¹ b_c^* b_a` on `Sym^N ℓ²(ℤ)`, `physical_fock`); `OccupationHilbert.E` (the
realized occupation transfer `E_{N,ac}` on `ℓ²(𝓜_N)`); the realized `TraceClass` (`IsTraceClass`, `posTrace`, `traceNorm`).
`N = 1+q` with `q ≥ 0` (every positive `N`); the printed proposition divides by `N`, so `N ≥ 1`.

## Proof (as printed, with the trace-class bookkeeping done through Hilbert-Schmidt)
`(v_ν)_a = √((ν_a+1)/N) d_{ν+e_a}` (`vEntry`, `vec`).  The Tonelli computation `eq:trace-sum` is
`tsum_tsum_vEntry`/`tsum_vec_sq`/`hasSum_vec_sq` (per-donor reindexing `ν ↦ ν+e_a`, `tsum_reindex`, and `∑_a m_a = N`),
proving `∑_ν ‖v_ν‖² = ‖d‖² = 1` and `v_ν ∈ h`.  `T : h → ℓ²(𝓜_{N-1})`, `x ↦ (⟨v_ν, x⟩)_ν` is a bounded (Hilbert-Schmidt) operator
(`Top`), and `Γ := T†T` (`Gamma`) is `∑_ν |v_ν⟩⟨v_ν|` (`eq:positive-series`; `inner_Gamma`).  Positivity is
`isPositive_adjoint_comp_self`; its trace (`posTrace_Gamma`) is the Hilbert-Schmidt sum `∑_a‖Te_a‖²`, which is `∑_ν‖v_ν‖² = 1` by
the same Tonelli identity, so it is trace class (`traceNorm_of_isPositive`) with trace one.  The entry `⟨d, E_{ac} d⟩` is computed
from the realized `E` (`inner_E`: `E = inject∘diag∘restrict`, `⟨d, E d⟩ = ∑_{m, m_a≥1} \overline{d_{m-e_a+e_c}} c_{ac}(m) d_m`), and
reindexed by `donorEquiv` (`ν ↦ ν+e_a`, `shiftArr_plusE`, `coef_plusE`) to the common-occupation series (`inner_E_eq_tsum`,
`entryTerm_eq`, `summable_norm_entryTerm`).  The phases: `d_m = q_N(m) g_m` (`coordinates_apply`) with the repository's gauge
convention `q_N(m) = \overline{g(m)}` (the gauged basis is `g(m)Ψ_m`; `BetheOccupationGauge` records that the coefficient
transform of vectors rephased by `g` uses the conjugate), `g_m = ⟨Ψ_{N,m}, ψ⟩` (`gCoef`, `qPhase`).

## Qualifications
* The Fock-sector form is stated with the realized `auxiliary` (the actual symmetric-tensor collective operator
  `N⁻¹ ∑_i |b⟩⟨a|_i`), which is `N⁻¹ b_b^*b_a` on `Sym^N h` (this is the definition of `OccupationConjugacy.collective`
  and DEF-026's description); no separate Fock-space `b_a` is introduced.
* Hypothesis: `‖ψ‖ = 1`; the basis `b`, the gauge `g` and `ψ` are arbitrary.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter Topology

noncomputable section

namespace QuantumNLS.ExactDensity

open QuantumNLS.Occupation QuantumNLS.OccupationHilbert
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)

section Arrays

variable {q : ℕ}

/-- `ν ↦ ν + e_a`, `𝓜_q → 𝓜_{1+q}`. -/
def plusE (ν : Arr q) (a : ℤ) : Arr (1 + q) :=
  ⟨ν.1 + e a, by
    have h := ν.2
    unfold IsArray total at h ⊢
    rw [map_add, Finsupp.degree_single, h]
    omega⟩

theorem plusE_val (ν : Arr q) (a : ℤ) : (plusE ν a).1 = ν.1 + e a := rfl

theorem plusE_apply_self (ν : Arr q) (a : ℤ) : (plusE ν a).1 a = ν.1 a + 1 := by
  simp [plusE_val, e]

theorem plusE_apply_ne (ν : Arr q) {a b : ℤ} (h : b ≠ a) : (plusE ν a).1 b = ν.1 b := by
  simp [plusE_val, e, Finsupp.single_apply, Ne.symm h]

theorem plusE_injective (a : ℤ) : Function.Injective (fun ν : Arr q => plusE ν a) := by
  intro ν ν' h
  apply Subtype.ext
  have := congrArg Subtype.val h
  simpa [plusE_val] using this

theorem donorOK_plusE (ν : Arr q) (a : ℤ) : DonorOK a (plusE ν a).1 := by
  unfold DonorOK
  rw [plusE_apply_self]; omega

/-- Every occupied-donor array is `ν + e_a`. -/
theorem exists_plusE {m : Arr (1 + q)} {a : ℤ} (h : DonorOK a m.1) : ∃ ν : Arr q, plusE ν a = m := by
  have hle : e a ≤ m.1 := single_le_of_donorOK h
  refine ⟨⟨m.1 - e a, ?_⟩, ?_⟩
  · have hm := m.2
    unfold IsArray total at hm ⊢
    have h2 := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
    rw [map_add, Finsupp.degree_single] at h2
    omega
  · apply Subtype.ext
    simp [plusE_val, tsub_add_cancel_of_le hle]

theorem plusE_injective_right (ν : Arr q) : Function.Injective (fun a : ℤ => plusE ν a) := by
  intro a a' h
  have := congrArg Subtype.val h
  simp only [plusE_val, add_right_inj] at this
  exact (Finsupp.single_left_inj (one_ne_zero)).1 this

theorem lp_sq_hasSum {ι : Type*} (f : lp (fun _ : ι => ℂ) 2) :
    HasSum (fun i => ‖f i‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) f
  simpa [Real.rpow_two] using h

end Arrays

section VEntry

variable {q : ℕ} (d : H (1 + q))

/-- `(v_ν)_a = √((ν_a+1)/N) d_{ν+e_a}`. -/
def vEntry (ν : Arr q) (a : ℤ) : ℂ :=
  ((Real.sqrt (((ν.1 a : ℝ) + 1) / ((1 + q : ℕ) : ℝ)) : ℝ) : ℂ) * d (plusE ν a)

theorem norm_vEntry_sq (ν : Arr q) (a : ℤ) :
    ‖vEntry d ν a‖ ^ 2 = (((ν.1 a : ℝ) + 1) / ((1 + q : ℕ) : ℝ)) * ‖d (plusE ν a)‖ ^ 2 := by
  unfold vEntry
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

theorem occ_succ_le (ν : Arr q) (a : ℤ) : (ν.1 a : ℝ) + 1 ≤ ((1 + q : ℕ) : ℝ) := by
  have h1 := occ_le_total a ν.1
  have h2 : total ν.1 = q := ν.2
  rw [h2] at h1
  have : ν.1 a + 1 ≤ 1 + q := by omega
  exact_mod_cast this

theorem vEntry_sq_le (ν : Arr q) (a : ℤ) : ‖vEntry d ν a‖ ^ 2 ≤ ‖d (plusE ν a)‖ ^ 2 := by
  rw [norm_vEntry_sq]
  have hN : (0 : ℝ) < ((1 + q : ℕ) : ℝ) := by positivity
  have : ((ν.1 a : ℝ) + 1) / ((1 + q : ℕ) : ℝ) ≤ 1 := (div_le_one hN).2 (occ_succ_le ν a)
  nlinarith [sq_nonneg ‖d (plusE ν a)‖]

theorem summable_d_sq : Summable (fun m : Arr (1 + q) => ‖d m‖ ^ 2) := (lp_sq_hasSum d).summable

theorem summable_vEntry_sq (ν : Arr q) : Summable (fun a : ℤ => ‖vEntry d ν a‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (vEntry_sq_le d ν)
    ((summable_d_sq d).comp_injective (plusE_injective_right ν))

theorem memℓp_vEntry (ν : Arr q) : Memℓp (vEntry d ν) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  simpa [Real.rpow_two] using summable_vEntry_sq d ν

/-- The vector `v_ν ∈ h = ℓ²(ℤ)`. -/
def vec (ν : Arr q) : OneParticle := ⟨vEntry d ν, memℓp_vEntry d ν⟩

theorem vec_apply (ν : Arr q) (a : ℤ) : vec d ν a = vEntry d ν a := rfl

theorem norm_vec_sq (ν : Arr q) : ‖vec d ν‖ ^ 2 = ∑' a : ℤ, ‖vEntry d ν a‖ ^ 2 :=
  ((lp_sq_hasSum (vec d ν)).tsum_eq).symm

/-- Per-donor reindexing: `∑_ν ((ν_a+1)/N)|d_{ν+e_a}|² = ∑_m (m_a/N)|d_m|²`. -/
theorem tsum_reindex (a : ℤ) :
    ∑' ν : Arr q, ENNReal.ofReal (‖vEntry d ν a‖ ^ 2) =
      ∑' m : Arr (1 + q), ENNReal.ofReal (((m.1 a : ℝ) / ((1 + q : ℕ) : ℝ)) * ‖d m‖ ^ 2) := by
  have h1 : ∀ ν : Arr q, ENNReal.ofReal (‖vEntry d ν a‖ ^ 2) =
      (fun m : Arr (1 + q) => ENNReal.ofReal (((m.1 a : ℝ) / ((1 + q : ℕ) : ℝ)) * ‖d m‖ ^ 2))
        (plusE ν a) := by
    intro ν
    simp only [norm_vEntry_sq, plusE_apply_self]
    push_cast
    rfl
  simp_rw [h1]
  have hsupp : Function.support
      (fun m : Arr (1 + q) => ENNReal.ofReal (((m.1 a : ℝ) / ((1 + q : ℕ) : ℝ)) * ‖d m‖ ^ 2)) ⊆
      Set.range (fun ν : Arr q => plusE ν a) := by
    intro m hm
    by_contra hr
    apply hm
    have hz : m.1 a = 0 := by
      by_contra hne
      obtain ⟨ν, hν⟩ := exists_plusE (q := q) (m := m) (a := a) (by unfold DonorOK; omega)
      exact hr ⟨ν, hν⟩
    simp [hz]
  exact Function.Injective.tsum_eq (plusE_injective a) hsupp

end VEntry

/-! ### The trace sum (`eq:trace-sum`) -/

section TraceSum

variable {q : ℕ} (d : H (1 + q))

theorem tsum_inner_finite (m : Arr (1 + q)) :
    ∑' a : ℤ, ENNReal.ofReal (((m.1 a : ℝ) / ((1 + q : ℕ) : ℝ)) * ‖d m‖ ^ 2) =
      ENNReal.ofReal (‖d m‖ ^ 2) := by
  have hN : (0 : ℝ) < ((1 + q : ℕ) : ℝ) := by positivity
  rw [tsum_eq_sum (s := m.1.support) (fun a ha => by
    simp [Finsupp.notMem_support_iff.1 ha])]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity)]
  congr 1
  rw [← Finset.sum_mul, ← Finset.sum_div]
  have hd : (∑ a ∈ m.1.support, (m.1 a : ℝ)) = ((1 + q : ℕ) : ℝ) := by
    have h1 : total m.1 = 1 + q := m.2
    unfold total at h1
    rw [Finsupp.degree_apply] at h1
    exact_mod_cast h1
  rw [hd, div_self hN.ne', one_mul]

theorem tsum_tsum_vEntry : ∑' a : ℤ, ∑' ν : Arr q, ENNReal.ofReal (‖vEntry d ν a‖ ^ 2) =
    ENNReal.ofReal (‖d‖ ^ 2) := by
  calc ∑' a : ℤ, ∑' ν : Arr q, ENNReal.ofReal (‖vEntry d ν a‖ ^ 2)
      = ∑' a : ℤ, ∑' m : Arr (1 + q),
          ENNReal.ofReal (((m.1 a : ℝ) / ((1 + q : ℕ) : ℝ)) * ‖d m‖ ^ 2) := by
        simp_rw [tsum_reindex]
    _ = ∑' m : Arr (1 + q), ∑' a : ℤ,
          ENNReal.ofReal (((m.1 a : ℝ) / ((1 + q : ℕ) : ℝ)) * ‖d m‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' m : Arr (1 + q), ENNReal.ofReal (‖d m‖ ^ 2) := by simp_rw [tsum_inner_finite]
    _ = ENNReal.ofReal (‖d‖ ^ 2) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (summable_d_sq d),
          (lp_sq_hasSum d).tsum_eq]

theorem tsum_vec_sq : ∑' ν : Arr q, ENNReal.ofReal (‖vec d ν‖ ^ 2) = ENNReal.ofReal (‖d‖ ^ 2) := by
  calc ∑' ν : Arr q, ENNReal.ofReal (‖vec d ν‖ ^ 2)
      = ∑' ν : Arr q, ∑' a : ℤ, ENNReal.ofReal (‖vEntry d ν a‖ ^ 2) := by
        congr 1; ext ν
        rw [norm_vec_sq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
          (summable_vEntry_sq d ν)]
    _ = ∑' a : ℤ, ∑' ν : Arr q, ENNReal.ofReal (‖vEntry d ν a‖ ^ 2) := ENNReal.tsum_comm
    _ = ENNReal.ofReal (‖d‖ ^ 2) := tsum_tsum_vEntry d

theorem hasSum_vec_sq : HasSum (fun ν : Arr q => ‖vec d ν‖ ^ 2) (‖d‖ ^ 2) := by
  have hne : ∑' ν : Arr q, ENNReal.ofReal (‖vec d ν‖ ^ 2) ≠ ⊤ := by
    rw [tsum_vec_sq]; exact ENNReal.ofReal_ne_top
  have hS : Summable (fun ν : Arr q => ‖vec d ν‖ ^ 2) := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have hv : ∑' ν : Arr q, ‖vec d ν‖ ^ 2 = ‖d‖ ^ 2 := by
    have h1 := ENNReal.tsum_toReal_eq (f := fun ν : Arr q => ENNReal.ofReal (‖vec d ν‖ ^ 2))
      (fun _ => ENNReal.ofReal_ne_top)
    rw [tsum_vec_sq, ENNReal.toReal_ofReal (sq_nonneg _)] at h1
    simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using h1.symm
  rw [← hv]
  exact hS.hasSum

end TraceSum

/-! ### The operator `T`, `Γ = T† T = ∑_ν |v_ν⟩⟨v_ν|` -/

section Operator

variable {q : ℕ} (d : H (1 + q))

theorem summable_inner_vec_sq (x : OneParticle) :
    Summable (fun ν : Arr q => ‖⟪vec d ν, x⟫_ℂ‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun ν => ?_)
    ((hasSum_vec_sq d).summable.mul_right (‖x‖ ^ 2))
  calc ‖⟪vec d ν, x⟫_ℂ‖ ^ 2 ≤ (‖vec d ν‖ * ‖x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
    _ = ‖vec d ν‖ ^ 2 * ‖x‖ ^ 2 := by ring

theorem summable_vEntry_sq_nu (a : ℤ) : Summable (fun ν : Arr q => ‖vEntry d ν a‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun ν => by
    have h := lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by norm_num) (vec d ν) a
    exact pow_le_pow_left₀ (norm_nonneg _) h 2) (hasSum_vec_sq d).summable

theorem memℓp_inner_vec (x : OneParticle) : Memℓp (fun ν : Arr q => ⟪vec d ν, x⟫_ℂ) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  simpa [Real.rpow_two] using summable_inner_vec_sq d x

/-- `(T x)_ν = ⟨v_ν, x⟩`. -/
def Tfun (x : OneParticle) : lp (fun _ : Arr q => ℂ) 2 :=
  ⟨fun ν => ⟪vec d ν, x⟫_ℂ, memℓp_inner_vec d x⟩

def Tlin : OneParticle →ₗ[ℂ] lp (fun _ : Arr q => ℂ) 2 where
  toFun := Tfun d
  map_add' x y := by
    apply Subtype.ext; funext ν
    exact inner_add_right _ _ _
  map_smul' c x := by
    apply Subtype.ext; funext ν
    exact inner_smul_right _ _ _

theorem norm_Tfun_le (x : OneParticle) : ‖Tfun d x‖ ≤ ‖d‖ * ‖x‖ := by
  have h1 : ‖Tfun d x‖ ^ 2 = ∑' ν : Arr q, ‖⟪vec d ν, x⟫_ℂ‖ ^ 2 :=
    ((lp_sq_hasSum (Tfun d x)).tsum_eq).symm
  have h2 : ∑' ν : Arr q, ‖⟪vec d ν, x⟫_ℂ‖ ^ 2 ≤ ∑' ν : Arr q, ‖vec d ν‖ ^ 2 * ‖x‖ ^ 2 := by
    refine Summable.tsum_le_tsum (fun ν => ?_) (summable_inner_vec_sq d x)
      ((hasSum_vec_sq d).summable.mul_right _)
    calc ‖⟪vec d ν, x⟫_ℂ‖ ^ 2 ≤ (‖vec d ν‖ * ‖x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
      _ = ‖vec d ν‖ ^ 2 * ‖x‖ ^ 2 := by ring
  have h3 : ∑' ν : Arr q, ‖vec d ν‖ ^ 2 * ‖x‖ ^ 2 = ‖d‖ ^ 2 * ‖x‖ ^ 2 :=
    ((hasSum_vec_sq d).mul_right _).tsum_eq
  have h4 : ‖Tfun d x‖ ^ 2 ≤ (‖d‖ * ‖x‖) ^ 2 := by
    rw [mul_pow, ← h3]; exact h1 ▸ h2
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h4

/-- The (Hilbert-Schmidt) operator `T : h → ℓ²(𝓜_{N-1})`, `x ↦ (⟨v_ν, x⟩)_ν`. -/
def Top : OneParticle →L[ℂ] lp (fun _ : Arr q => ℂ) 2 :=
  (Tlin d).mkContinuous ‖d‖ (norm_Tfun_le d)

theorem Top_apply (x : OneParticle) (ν : Arr q) : Top d x ν = ⟪vec d ν, x⟫_ℂ := rfl

theorem Top_oneBasis (a : ℤ) (ν : Arr q) : Top d (oneBasis a) ν = conj (vEntry d ν a) := by
  rw [Top_apply, QuantumNLS.OccupationUnitary.oneBasis_apply, lp.inner_single_right]
  simp [vec_apply]

/-- **`Γ = T† T = ∑_ν |v_ν⟩⟨v_ν|`**, the operator of `eq:positive-series`. -/
def Gamma : OneParticle →L[ℂ] OneParticle :=
  ContinuousLinearMap.adjoint (Top d) ∘L Top d

theorem gamma_isPositive : (Gamma d).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self (Top d)

theorem inner_Gamma (a c : ℤ) :
    ⟪oneBasis a, Gamma d (oneBasis c)⟫_ℂ = ∑' ν : Arr q, vEntry d ν a * conj (vEntry d ν c) := by
  unfold Gamma
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum]
  refine tsum_congr fun ν => ?_
  rw [Top_oneBasis, Top_oneBasis]
  simp [mul_comm]

end Operator

/-! ### The trace -/

section Trace

variable {q : ℕ} (d : H (1 + q))

theorem posTrace_Gamma : QuantumNLS.TraceClass.posTrace (Gamma d) = ENNReal.ofReal (‖d‖ ^ 2) := by
  rw [QuantumNLS.TraceClass.posTrace_eq oneBasis (gamma_isPositive d)]
  unfold Gamma
  rw [QuantumNLS.TraceClass.traceIn_adjoint_comp_self]
  unfold QuantumNLS.TraceClass.hsSq
  rw [← tsum_tsum_vEntry d]
  refine tsum_congr fun a => ?_
  have h1 : ‖Top d (oneBasis a)‖ ^ 2 = ∑' ν : Arr q, ‖vEntry d ν a‖ ^ 2 := by
    rw [← (lp_sq_hasSum (Top d (oneBasis a))).tsum_eq]
    refine tsum_congr fun ν => ?_
    rw [Top_oneBasis, Complex.norm_conj]
  rw [h1, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (summable_vEntry_sq_nu d a)]

end Trace

/-! ### The entries: the occupation transfer `E_{ab}` on the coefficient vector -/

section EntrySide

variable {q : ℕ} (d : H (1 + q))

/-- `𝓜_q ≃ {m ∈ 𝓜_{1+q} : m_a ≥ 1}`, `ν ↦ ν + e_a`. -/
def donorEquiv (a : ℤ) : Arr q ≃ Donor (1 + q) a :=
  Equiv.ofBijective (fun ν => ⟨plusE ν a, donorOK_plusE ν a⟩)
    ⟨fun ν ν' h => plusE_injective a (congrArg Subtype.val h), fun m => by
      obtain ⟨ν, hν⟩ := exists_plusE (q := q) (m := m.1) (a := a) m.2
      exact ⟨ν, Subtype.ext hν⟩⟩

theorem shiftArr_plusE (ν : Arr q) (a c : ℤ) :
    shiftArr a c (plusE ν a) (donorOK_plusE ν a) = plusE ν c := by
  apply Subtype.ext
  simp [shiftArr, shift, plusE_val]

theorem coef_plusE (ν : Arr q) (a c : ℤ) :
    coef (1 + q) a c (plusE ν a).1 =
      Real.sqrt (((ν.1 a : ℝ) + 1) * ((ν.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) := by
  unfold coef
  split_ifs with hac
  · subst hac
    rw [plusE_apply_self, Real.sqrt_mul_self (by positivity)]
    push_cast; rfl
  · rw [plusE_apply_self, plusE_apply_ne ν (Ne.symm hac)]
    push_cast; rfl

/-- `⟨d, E_{ac} d⟩ = ∑_{m, m_a ≥ 1} conj(d_{m-e_a+e_c}) c_{ac}(m) d_m`. -/
theorem inner_E (a c : ℤ) :
    ⟪d, E (1 + q) a c d⟫_ℂ =
      ∑' m : Donor (1 + q) a,
        conj (d (destination (1 + q) a c m)) * ((coef (1 + q) a c m.1.1 : ℝ) : ℂ) * d m.1 := by
  have h : ⟪d, E (1 + q) a c d⟫_ℂ =
      ⟪restrictL2 (destination (1 + q) a c) (destination_injective (1 + q) a c) d,
        diagonal (fun m : Donor (1 + q) a => ((coef (1 + q) a c m.1.1 : ℝ) : ℂ)) 1 zero_le_one
          (fun m => coefficient_bound (1 + q) a c m.1)
          (restrictL2 (Subtype.val : Donor (1 + q) a → Arr (1 + q)) Subtype.val_injective d)⟫_ℂ := by
    unfold E transferOp restrictL2
    simp only [ContinuousLinearMap.comp_apply]
    exact (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
  rw [h, lp.inner_eq_tsum]
  refine tsum_congr fun m => ?_
  simp [restrictL2_apply]
  ring

end EntrySide

/-! ### Assembly: `prop:exact-density` -/

section Assembly

variable {q : ℕ} (d : H (1 + q))

theorem entryTerm_eq (ν : Arr q) (a c : ℤ) :
    vEntry d ν a * conj (vEntry d ν c) =
      ((Real.sqrt (((ν.1 a : ℝ) + 1) * ((ν.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) : ℝ) : ℂ) *
        d (plusE ν a) * conj (d (plusE ν c)) := by
  have hN : (0 : ℝ) < ((1 + q : ℕ) : ℝ) := by positivity
  have hx : (0 : ℝ) ≤ (ν.1 a : ℝ) + 1 := by positivity
  have hy : (0 : ℝ) ≤ (ν.1 c : ℝ) + 1 := by positivity
  have hs : Real.sqrt (((ν.1 a : ℝ) + 1) / ((1 + q : ℕ) : ℝ)) *
        Real.sqrt (((ν.1 c : ℝ) + 1) / ((1 + q : ℕ) : ℝ)) =
      Real.sqrt (((ν.1 a : ℝ) + 1) * ((ν.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) := by
    rw [Real.sqrt_div hx, Real.sqrt_div hy, Real.sqrt_mul hx]
    have hN2 : Real.sqrt ((1 + q : ℕ) : ℝ) * Real.sqrt ((1 + q : ℕ) : ℝ) = ((1 + q : ℕ) : ℝ) :=
      Real.mul_self_sqrt hN.le
    have hNs : Real.sqrt ((1 + q : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
    field_simp
    nlinarith [hN2]
  unfold vEntry
  rw [map_mul, Complex.conj_ofReal]
  have hc : ((Real.sqrt (((ν.1 a : ℝ) + 1) / ((1 + q : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((Real.sqrt (((ν.1 c : ℝ) + 1) / ((1 + q : ℕ) : ℝ)) : ℝ) : ℂ) =
      ((Real.sqrt (((ν.1 a : ℝ) + 1) * ((ν.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hs]
  calc _ = (((Real.sqrt (((ν.1 a : ℝ) + 1) / ((1 + q : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((Real.sqrt (((ν.1 c : ℝ) + 1) / ((1 + q : ℕ) : ℝ)) : ℝ) : ℂ)) *
        d (plusE ν a) * conj (d (plusE ν c)) := by ring
    _ = _ := by rw [hc]

theorem summable_norm_entryTerm (a c : ℤ) :
    Summable (fun ν : Arr q => ‖vEntry d ν a * conj (vEntry d ν c)‖) := by
  have h1 := summable_vEntry_sq_nu d a
  have h2 := summable_vEntry_sq_nu d c
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ν => ?_)
    ((h1.add h2).div_const 2)
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖vEntry d ν a‖ - ‖vEntry d ν c‖)]

theorem donor_term (a c : ℤ) (ν : Arr q) :
    conj (d (destination (1 + q) a c (donorEquiv (q := q) a ν))) *
        ((coef (1 + q) a c (donorEquiv (q := q) a ν).1.1 : ℝ) : ℂ) * d (donorEquiv (q := q) a ν).1 =
      vEntry d ν a * conj (vEntry d ν c) := by
  have hd : destination (1 + q) a c (donorEquiv (q := q) a ν) = plusE ν c := shiftArr_plusE ν a c
  have hm : (donorEquiv (q := q) a ν).1 = plusE ν a := rfl
  rw [hd, hm, entryTerm_eq, coef_plusE]
  push_cast
  ring

theorem inner_E_eq_tsum (a c : ℤ) :
    ⟪d, E (1 + q) a c d⟫_ℂ = ∑' ν : Arr q, vEntry d ν a * conj (vEntry d ν c) := by
  rw [inner_E, ← (donorEquiv (q := q) a).tsum_eq]
  exact tsum_congr fun ν => donor_term d a c ν

theorem hasSum_entry (a c : ℤ) :
    HasSum (fun ν : Arr q => vEntry d ν a * conj (vEntry d ν c)) ⟪d, E (1 + q) a c d⟫_ℂ := by
  rw [inner_E_eq_tsum]
  exact (summable_norm_entryTerm d a c).of_norm.hasSum

end Assembly

section Gauge

open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
  QuantumNLS.CartesianOccupationTransfer

variable {L : ℝ} [Fact (0 < L)] {q : ℕ}

/-- `g_m = ⟨Ψ_{N,m}, ψ⟩`, indexed by the occupation arrays `Arr N`. -/
def gCoef (b : BetheBasis L (1 + q)) (ψ : HN L (1 + q)) (m : Arr (1 + q)) : ℂ :=
  ⟪b ((marrArr (1 + q)).symm m), ψ⟫_ℂ

/-- The report's phase `q_N(m)`: in the repository's convention (the gauged basis is `g(m) Ψ_m`) it is `\overline{g(m)}`. -/
def qPhase (g : Gauge) (m : Arr (1 + q)) : ℂ := conj (g (1 + q) ((marrArr (1 + q)).symm m)).1

/-- **`d_m = q_N(m) g_m`**. -/
theorem coordinates_apply (b : BetheBasis L (1 + q)) (g : Gauge) (ψ : HN L (1 + q)) (m : Arr (1 + q)) :
    coordinates b g ψ m = qPhase g m * gCoef b ψ m := by
  have h := occupationCoefficient_apply (gaugedBasis b g) ψ ((marrArr (1 + q)).symm m)
  rw [Equiv.apply_symm_apply, gaugedBasis_apply, inner_smul_left] at h
  exact h

end Gauge

/-! ### The proposition -/

section Main

open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
  QuantumNLS.CartesianOccupationTransfer QuantumNLS.AuxiliaryDensity

variable {L : ℝ} [Fact (0 < L)] {q : ℕ}

theorem hasSum_donor (d : H (1 + q)) (a c : ℤ) :
    HasSum (fun m : Donor (1 + q) a =>
      conj (d (destination (1 + q) a c m)) * ((coef (1 + q) a c m.1.1 : ℝ) : ℂ) * d m.1)
      ⟪d, E (1 + q) a c d⟫_ℂ := by
  have hs : Summable (fun m : Donor (1 + q) a =>
      conj (d (destination (1 + q) a c m)) * ((coef (1 + q) a c m.1.1 : ℝ) : ℂ) * d m.1) := by
    rw [← (donorEquiv (q := q) a).summable_iff]
    have : (fun m : Donor (1 + q) a =>
        conj (d (destination (1 + q) a c m)) * ((coef (1 + q) a c m.1.1 : ℝ) : ℂ) * d m.1) ∘
        (donorEquiv (q := q) a) = fun ν : Arr q => vEntry d ν a * conj (vEntry d ν c) :=
      funext fun ν => donor_term d a c ν
    rw [this]
    exact (summable_norm_entryTerm d a c).of_norm
  rw [inner_E]
  exact hs.hasSum

/-- **`prop:exact-density` (R-BB03032A), Positivity, normalization, and entry orientation.**
For a unit vector `ψ ∈ 𝓗_N` (`N = 1+q ≥ 1`), a basis `Ψ_{N,m}` and the universal gauge `g`, with
`d = J_N ψ` the gauged coefficient vector (`d_m = q_N(m) g_m`):
there is a positive trace-class operator `Γ` on `h = ℓ²(ℤ)` with trace one whose row-`a`, column-`c` entry
`⟨e_a, Γ e_c⟩` equals `⟨ψ, E^q_{N,ac} ψ⟩` (DEF-029's `gammaEntry`), `= ⟨d, E_{ac} d⟩ = (1/N)⟨J_Nψ, b_c^* b_a J_Nψ⟩`
(`E` the occupation transfer; the last in the Fock sector as `auxiliary`, the normalized collective one-body
operator), `= (1/N) ∑_{ν∈𝓜_{N-1}} √((ν_a+1)(ν_c+1)) d_{ν+e_a} \overline{d_{ν+e_c}}` with absolute convergence;
and, for `a ≠ c`, `= ∑_{m, m_a ≥ 1} (√(m_a(m_c+1))/N) q_N(m) \overline{q_N(m-e_a+e_c)} g_m \overline{g_{m-e_a+e_c}}`. -/
theorem exact_density (b : BetheBasis L (1 + q)) (g : Gauge) (ψ : HN L (1 + q)) (hψ : ‖ψ‖ = 1) :
    ∃ Γ : OneParticle →L[ℂ] OneParticle,
      Γ.IsPositive ∧ QuantumNLS.TraceClass.IsTraceClass Γ ∧ QuantumNLS.TraceClass.posTrace Γ = 1 ∧
      (∀ a c : ℤ, ⟪oneBasis a, Γ (oneBasis c)⟫_ℂ = gammaEntry b g ψ a c) ∧
      (∀ a c : ℤ, gammaEntry b g ψ a c =
        ⟪coordinates b g ψ, E (1 + q) a c (coordinates b g ψ)⟫_ℂ) ∧
      (∀ a c : ℤ, gammaEntry b g ψ a c =
        ⟪fockTransform (gaugedBasis b g) ψ, auxiliary q a c (fockTransform (gaugedBasis b g) ψ)⟫_ℂ) ∧
      (∀ a c : ℤ, HasSum (fun ν : Arr q =>
        ((Real.sqrt (((ν.1 a : ℝ) + 1) * ((ν.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) : ℝ) : ℂ) *
          coordinates b g ψ (plusE ν a) * conj (coordinates b g ψ (plusE ν c)))
        (gammaEntry b g ψ a c)) ∧
      (∀ a c : ℤ, Summable (fun ν : Arr q => ‖
        ((Real.sqrt (((ν.1 a : ℝ) + 1) * ((ν.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) : ℝ) : ℂ) *
          coordinates b g ψ (plusE ν a) * conj (coordinates b g ψ (plusE ν c))‖)) ∧
      (∀ a c : ℤ, a ≠ c → HasSum (fun m : Donor (1 + q) a =>
        ((Real.sqrt ((m.1.1 a : ℝ) * ((m.1.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) : ℝ) : ℂ) *
          (qPhase g m.1 * conj (qPhase g (destination (1 + q) a c m))) *
          (gCoef b ψ m.1 * conj (gCoef b ψ (destination (1 + q) a c m))))
        (gammaEntry b g ψ a c)) := by
  set d := coordinates b g ψ with hdef
  have hd : ‖d‖ = 1 := by rw [hdef, LinearIsometryEquiv.norm_map, hψ]
  have hent : ∀ a c, gammaEntry b g ψ a c = ⟪d, E (1 + q) a c d⟫_ℂ := fun a c =>
    gammaEntry_eq_coefficient b g ψ a c
  refine ⟨Gamma d, gamma_isPositive d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [QuantumNLS.TraceClass.IsTraceClass, QuantumNLS.TraceClass.traceNorm_of_isPositive
      (gamma_isPositive d), posTrace_Gamma, hd]
    simp
  · rw [posTrace_Gamma, hd]; simp
  · intro a c
    rw [inner_Gamma, hent, inner_E_eq_tsum]
  · exact hent
  · intro a c
    have h := (fockTransform (gaugedBasis b g) : HN L (1 + q) ≃ₗᵢ[ℂ] _).inner_map_map ψ
      (physical b g a c ψ)
    unfold gammaEntry
    rw [← h, physical_fock]
  · intro a c
    rw [hent]
    have := hasSum_entry d a c
    convert this using 1
    funext ν
    rw [entryTerm_eq]
  · intro a c
    have := summable_norm_entryTerm d a c
    convert this using 1
    funext ν
    rw [entryTerm_eq]
  · intro a c hne
    rw [hent]
    have h := hasSum_donor d a c
    convert h using 1
    funext m
    have hcoef : coef (1 + q) a c m.1.1 =
        Real.sqrt ((m.1.1 a : ℝ) * ((m.1.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) := by
      unfold coef; rw [if_neg hne]
    rw [hcoef, hdef, coordinates_apply, coordinates_apply, map_mul]
    ring

end Main

end QuantumNLS.ExactDensity

#print axioms QuantumNLS.ExactDensity.tsum_vec_sq
#print axioms QuantumNLS.ExactDensity.hasSum_vec_sq
#print axioms QuantumNLS.ExactDensity.posTrace_Gamma
#print axioms QuantumNLS.ExactDensity.inner_Gamma
#print axioms QuantumNLS.ExactDensity.inner_E
#print axioms QuantumNLS.ExactDensity.inner_E_eq_tsum
#print axioms QuantumNLS.ExactDensity.coordinates_apply
#print axioms QuantumNLS.ExactDensity.hasSum_donor
#print axioms QuantumNLS.ExactDensity.exact_density
