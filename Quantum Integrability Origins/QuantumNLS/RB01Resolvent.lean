import Mathlib
import QuantumNLS.RB01SquareSmall
import QuantumNLS.TerraMultiRound35SquareInverse
import QuantumNLS.TerraMultiRound34RankPath
import QuantumNLS.Local002Domain

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-3: the arbitrary-field resolvent, self-adjointness,
the Riesz projection, and its rank along the path `t u` (FIN-EXT025-GP-17 corrected, route (ii), PROVED for the
actual family).

Source (collective_actions.tex:183-235): "`F_n(w,q) = (1 - A_n)^{-1} = (1 + A_n)(1 - A_n^2)^{-1}` is uniformly
bounded ... The same bound holds for `tq`, `0 ≤ t ≤ 1`, since `A_n(w,tq)^2 = t^2 A_n(w,q)^2` ... `R_n = F_n R_{0,n}`
... This proves self-adjointness on `H^1` for arbitrary real `L^2` fields ... The contour `|z - p_n| = r` is now in the
resolvent set for all `tq`.  Its Riesz projection `P_n(q)` is a finite-rank idempotent, continuous along `tq`.  Its
rank is two at zero and is constant along that path, since sufficiently close finite-rank idempotents have equal rank."

Everything is stated for the actual DEF-049 objects `LuGraph`, `IsResolvent`, `perturbedProj` (real slice) with the
LOCAL-002 operator `T = V_u R_{0,n}(z)` (`IsMulOp`); `SqSmall L κ r n u` is the conclusion of
`RB01SquareSmall.square_small` on the annulus `r/2 ≤ |z - p_n| ≤ r`.
* `resolvent_of_inverse`: a two-sided inverse of `1 - T` gives the resolvent `R_0 S` (no smallness of `T` itself).
* `sqSmall_smul`: square-smallness is inherited by `t u`, `|t| ≤ 1` (real homogeneity of `T`).
* `resolvent_exists`: resolvents on the whole annulus with a uniform bound.
* `selfAdjoint_of_sqSmall`: `𝓛_u` is self-adjoint on `D_{(-1)^n}`.
* `idem_of_sqSmall`: `P_n(u)² = P_n(u)`.
* `path_lipschitz`: `t ↦ P_n(t u)` is Lipschitz on `[0,1]`.
* `rank_two_of_sqSmall`: `rank P_n(u) = 2`, by `TerraMultiRound34RankPath.rank_two_from_actual_free` (base: the actual
  free projection) — the repaired GP-17 route (ii) with its application duty discharged.
* **`arbitrary_field_riesz`**: for every `u₀` there are `N`, `ρ > 0` such that for all `|n| > N` and `‖u - u₀‖ < ρ`
  all of the above hold. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.RB01Resolvent
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free QuantumNLS.Local002Rank
  QuantumNLS.Local002SA QuantumNLS.Local002Idem QuantumNLS.RB01FourierAction QuantumNLS.RB01SquareSmall

variable {L κ : ℝ}

/-- The square-smallness conclusion of `square_small`, on the annulus `r/2 ≤ |z - p_n| ≤ r`. -/
def SqSmall (L κ r : ℝ) (n : ℤ) (u : Lp ℂ 2 (μI L)) : Prop :=
  ∀ z : ℂ, r / 2 ≤ ‖z - (pm L n : ℂ)‖ → ‖z - (pm L n : ℂ)‖ ≤ r →
    ∀ R0 T : H2 L →L[ℂ] H2 L, IsResolvent L κ (fun _ => 0) (parity n) z R0 →
      QuantumNLS.Local002.IsMulOp κ R0 (u : ℝ → ℂ) T → ‖T * T‖ ≤ 1 / 4

/-- The uniform constant `M = 2√κ C_{L,r/2}` of `‖T‖ ≤ M ‖u‖` on the annulus. -/
def Mr (L κ r : ℝ) : ℝ := 2 * Real.sqrt κ * Cmax L (r / 2)

theorem Mr_nonneg (L κ r : ℝ) : 0 ≤ Mr L κ r := by
  unfold Mr; have : 0 ≤ Cmax L (r / 2) := Real.sqrt_nonneg _; positivity

/-! ### The resolvent from a two-sided inverse of `1 - T` -/

theorem resolvent_of_inverse {u : ℝ → ℂ} {σ : ℤˣ} {z : ℂ} {R0 T S : H2 L →L[ℂ] H2 L}
    (h0 : IsResolvent L κ (fun _ => 0) σ z R0)
    (hT : ∀ φ : H2 L, (T φ : ℝ → E2) =ᵐ[μI L] fun x => Vpt κ (u x) ((R0 φ : ℝ → E2) x))
    (hS1 : (1 - T) * S = 1) (hS2 : S * (1 - T) = 1) :
    IsResolvent L κ u σ z (R0 * S) := by
  have hS1' : ∀ φ : H2 L, S φ - T (S φ) = φ := fun φ => by
    have h := congrArg (fun A : H2 L →L[ℂ] H2 L => A φ) hS1
    simpa [sub_mul] using h
  have hS2' : ∀ φ : H2 L, S (φ - T φ) = φ := fun φ => by
    have h := congrArg (fun A : H2 L →L[ℂ] H2 L => A φ) hS2
    simpa [mul_sub] using h
  refine ⟨?_, ?_⟩
  · intro φ
    obtain ⟨g, h, hrep, hbd, hae⟩ := h0.1 (S φ)
    refine ⟨g, h, hrep, hbd, ?_⟩
    have hφ : (φ : ℝ → E2) =ᵐ[μI L] fun x => (S φ : ℝ → E2) x - (T (S φ) : ℝ → E2) x := by
      have := Lp.coeFn_sub (S φ) (T (S φ))
      rwa [hS1' φ] at this
    filter_upwards [coe_zsub z (R0 (S φ)) φ, coe_zsub z (R0 (S φ)) (S φ), hφ, hae, hT (S φ),
      hrep.1] with x e1 e2 e3 e4 e5 e6
    change ((z • R0 (S φ) - φ : H2 L) : ℝ → E2) x = lopPt κ (u x) (h x) (g x)
    simp only [lopPt_zero_pot] at e4
    have e7 : z • (R0 (S φ) : ℝ → E2) x - (φ : ℝ → E2) x =
        (z • (R0 (S φ) : ℝ → E2) x - (S φ : ℝ → E2) x) + (T (S φ) : ℝ → E2) x := by
      rw [e3]; abel
    rw [e1, e7, ← e2, e4, e5, e6, lopPt_split]
  · rintro ⟨f, φ⟩ ⟨g, h, hrep, hbd, hae⟩
    have hmem : MemLp (fun x => (2 * Complex.I) • Jm (h x)) 2 (μI L) := by
      have := (Jcl.comp_memLp' hrep.2.1).const_smul (2 * Complex.I)
      convert this using 1
      funext x
      simp [Jcl_apply]
    set ψ₁ : H2 L := hmem.toLp _ with hψ₁
    have hpsi1 : (f, ψ₁) ∈ LuGraph L κ (fun _ => 0) σ := by
      refine ⟨g, h, hrep, hbd, ?_⟩
      filter_upwards [hmem.coeFn_toLp] with x hx
      simp only [lopPt_zero_pot]
      exact hx
    have hψ' : R0 (z • f - ψ₁) = f := h0.2 (f, ψ₁) hpsi1
    have hTψ := hT (z • f - ψ₁)
    rw [hψ'] at hTψ
    have key : (z • f - ψ₁) - T (z • f - ψ₁) = z • f - φ := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (z • f - ψ₁) (T (z • f - ψ₁)), coe_zsub z f ψ₁, hTψ,
        coe_zsub z f φ, hae, hrep.1, hmem.coeFn_toLp] with x a1 a2 a3 a4 a5 a6 a7
      rw [a1, Pi.sub_apply, a2, a3, a4, a5, lopPt_split, ← a6, ← a7]
      simp only [hψ₁]
      abel
    show R0 (S (z • f - φ)) = f
    rw [← key, hS2', hψ']

/-! ### Square-smallness along `t u` -/

theorem annulus_facts (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ} {z : ℂ}
    (h1 : r / 2 ≤ ‖z - (pm L n : ℂ)‖) (h2 : ‖z - (pm L n : ℂ)‖ ≤ r) :
    0 < ‖z - (pm L n : ℂ)‖ ∧ ‖z - (pm L n : ℂ)‖ < 2 * Real.pi / L ∧
      Cconst L ‖z - (pm L n : ℂ)‖ ≤ Cmax L (r / 2) := by
  have hs0 : 0 < ‖z - (pm L n : ℂ)‖ := lt_of_lt_of_le (by positivity) h1
  have hs2 : ‖z - (pm L n : ℂ)‖ < 2 * Real.pi / L := lt_of_le_of_lt h2 hr2
  exact ⟨hs0, hs2, Cconst_le hL (by positivity) h1 hs2⟩

/-- `T` exists on the annulus with `‖T‖ ≤ M ‖u‖`. -/
theorem exists_T_annulus (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ} {z : ℂ}
    (h1 : r / 2 ≤ ‖z - (pm L n : ℂ)‖) (h2 : ‖z - (pm L n : ℂ)‖ ≤ r) {R0 : H2 L →L[ℂ] H2 L}
    (hR0 : IsResolvent L κ (fun _ => 0) (parity n) z R0) (u : Lp ℂ 2 (μI L)) :
    ∃ T : H2 L →L[ℂ] H2 L, QuantumNLS.Local002.IsMulOp κ R0 (u : ℝ → ℂ) T ∧ ‖T‖ ≤ Mr L κ r * ‖u‖ := by
  obtain ⟨hs0, hs2, hC⟩ := annulus_facts hL hr hr2 h1 h2
  obtain ⟨T, hT, hTn⟩ := exists_mulOp hs0 hs2 rfl hR0 u
  refine ⟨T, hT, hTn.trans ?_⟩
  unfold Mr
  have : 0 ≤ 2 * Real.sqrt κ := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC this) (norm_nonneg _)

theorem free_res_annulus (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ} {z : ℂ}
    (h1 : r / 2 ≤ ‖z - (pm L n : ℂ)‖) (h2 : ‖z - (pm L n : ℂ)‖ ≤ r) :
    ∃ R0 : H2 L →L[ℂ] H2 L, IsResolvent L κ (fun _ => 0) (parity n) z R0 ∧ ‖R0‖ ≤ 2 / r := by
  obtain ⟨hs0, hs2, -⟩ := annulus_facts hL hr hr2 h1 h2
  obtain ⟨R0, hR0, hn⟩ := (QuantumNLS.Local002Discharge.free_resolvent_hyp L κ).res _ n z hs0 hs2 rfl
  refine ⟨R0, hR0, hn.trans ?_⟩
  rw [div_le_div_iff₀ hs0 hr]; linarith

theorem sqSmall_smul (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u) {t : ℝ} (ht : |t| ≤ 1) : SqSmall L κ r n (t • u) := by
  intro z h1 h2 R0 T' hR0 hT'
  obtain ⟨T, hT, -⟩ := exists_T_annulus hL hr hr2 h1 h2 hR0 u
  have heq : T' = (t : ℂ) • T := hT'.unique (hT.real_smul t)
  have hTT := hu z h1 h2 R0 T hR0 hT
  rw [heq, smul_mul_smul_comm, norm_smul]
  have ht2 : ‖(t : ℂ) * (t : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg t]
  calc ‖(t : ℂ) * (t : ℂ)‖ * ‖T * T‖ ≤ 1 * (1 / 4) :=
        mul_le_mul ht2 hTT (norm_nonneg _) zero_le_one
    _ = 1 / 4 := one_mul _

/-! ### Resolvents on the annulus -/

/-- The inverse of `1 - T` for `‖T²‖ ≤ 1/4`, with the uniform bound. -/
theorem inverse_bound {T : H2 L →L[ℂ] H2 L} (hTT : ‖T * T‖ ≤ 1 / 4) :
    ∃ S : H2 L →L[ℂ] H2 L, (1 - T) * S = 1 ∧ S * (1 - T) = 1 ∧ ‖S‖ ≤ (1 + ‖T‖) * (4 / 3) := by
  obtain ⟨S, h1, h2, hn⟩ := QuantumNLS.TerraMultiRound35SquareInverse.square_small_inverse
    ContinuousLinearMap.norm_id_le T (by linarith)
  refine ⟨S, h1, h2, hn.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- The uniform resolvent bound `(2/r)(1 + M‖u‖)(4/3)`. -/
def Rb (L κ r : ℝ) (u : Lp ℂ 2 (μI L)) : ℝ := 2 / r * ((1 + Mr L κ r * ‖u‖) * (4 / 3))

theorem resolvent_exists (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u) {z : ℂ}
    (h1 : r / 2 ≤ ‖z - (pm L n : ℂ)‖) (h2 : ‖z - (pm L n : ℂ)‖ ≤ r) :
    ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (u : ℝ → ℂ) (parity n) z R ∧ ‖R‖ ≤ Rb L κ r u := by
  obtain ⟨R0, hR0, hR0n⟩ := free_res_annulus (κ := κ) hL hr hr2 h1 h2
  obtain ⟨T, hT, hTn⟩ := exists_T_annulus hL hr hr2 h1 h2 hR0 u
  obtain ⟨S, hS1, hS2, hSn⟩ := inverse_bound (hu z h1 h2 R0 T hR0 hT)
  refine ⟨R0 * S, resolvent_of_inverse hR0 hT hS1 hS2, ?_⟩
  calc ‖R0 * S‖ ≤ ‖R0‖ * ‖S‖ := norm_mul_le _ _
    _ ≤ 2 / r * ((1 + Mr L κ r * ‖u‖) * (4 / 3)) := by
        apply mul_le_mul hR0n (hSn.trans _) (norm_nonneg _) (by positivity)
        gcongr
    _ = Rb L κ r u := rfl

theorem Rb_nonneg (L κ : ℝ) {r : ℝ} (hr : 0 < r) (u : Lp ℂ 2 (μI L)) : 0 ≤ Rb L κ r u := by
  unfold Rb; have := Mr_nonneg L κ r; positivity

/-! ### Self-adjointness and idempotence -/

theorem selfAdjoint_of_sqSmall (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u) :
    IsSelfAdjointGraph (LuGraph L κ (u : ℝ → ℂ) (parity n)) := by
  obtain ⟨z, hzdef⟩ : ∃ z : ℂ, z = (pm L n : ℂ) + (r : ℂ) * Complex.I := ⟨_, rfl⟩
  have hz : ‖z - (pm L n : ℂ)‖ = r := by
    rw [hzdef]; simp [abs_of_pos hr]
  have hzc : ‖conj z - (pm L n : ℂ)‖ = r := by
    have : conj z - (pm L n : ℂ) = conj (z - (pm L n : ℂ)) := by simp [Complex.conj_ofReal]
    rw [this, RCLike.norm_conj, hz]
  have him : z.im ≠ 0 := by
    rw [hzdef]; simpa using hr.ne'
  have hr1 : r / 2 ≤ r := by linarith
  obtain ⟨R0, hR0, -⟩ := free_res_annulus (κ := κ) hL hr hr2 (n := n) (z := z) (by rw [hz]; exact hr1)
    hz.le
  obtain ⟨R0', hR0', -⟩ := free_res_annulus (κ := κ) hL hr hr2 (n := n) (z := conj z)
    (by rw [hzc]; exact hr1) hzc.le
  obtain ⟨R, hR, -⟩ := resolvent_exists hL hr hr2 hu (z := z) (by rw [hz]; exact hr1) hz.le
  obtain ⟨R', hR', -⟩ := resolvent_exists hL hr hr2 hu (z := conj z) (by rw [hzc]; exact hr1) hzc.le
  have hsym : ∀ p ∈ LuGraph L κ (u : ℝ → ℂ) (parity n), ∀ q ∈ LuGraph L κ (u : ℝ → ℂ) (parity n),
      ⟪p.1, q.2⟫_ℂ = ⟪p.2, q.1⟫_ℂ := fun p hp q hq => Gu_symm hL him hR0 hR0' hp hq
  refine ⟨?_, ?_⟩
  · have hd := (local_selfadjoint (κ := κ) (QuantumNLS.Local002Discharge.free_resolvent_hyp L κ) hL hr hr2 n
      (0 : Lp ℂ 2 (μI L)) (by simp [qpar])).dense
    rw [QuantumNLS.Local002Domain.domOf_LuGraph hL.le] at hd ⊢
    exact hd
  · apply Set.Subset.antisymm
    · intro p hp q hq
      exact hsym p hp q hq
    · exact adj_subset hsym R R' hR.1 hR'.1

theorem idem_of_sqSmall (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u) :
    perturbedProj L κ (u : ℝ → ℂ) n r * perturbedProj L κ (u : ℝ → ℂ) n r =
      perturbedProj L κ (u : ℝ → ℂ) n r := by
  have hM : ∀ z : ℂ, r / 2 ≤ ‖z - center L n‖ → ‖z - center L n‖ ≤ r →
      ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (u : ℝ → ℂ) (parity n) z R ∧ ‖R‖ ≤ Rb L κ r u :=
    fun z h1 h2 => resolvent_exists hL hr hr2 hu h1 h2
  exact (annulus_idem (u := (u : ℝ → ℂ)) (σ := parity n) (n := n) (r1 := r / 2) (r2 := r)
    (by positivity) (by linarith) hM).2

/-! ### Continuity along the path `t u` and rank two -/

/-- The uniform bound `W = (1 + M‖u‖)(4/3)` of the inverses along the path. -/
def Wb (L κ r : ℝ) (u : Lp ℂ 2 (μI L)) : ℝ := (1 + Mr L κ r * ‖u‖) * (4 / 3)

theorem res_diff (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u) {z : ℂ} (hz : ‖z - (pm L n : ℂ)‖ = r)
    {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    ‖resolvent L κ (((t • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) (parity n) z -
        resolvent L κ (((s • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) (parity n) z‖ ≤
      2 / r * Wb L κ r u ^ 2 * (Mr L κ r * ‖u‖) * |t - s| := by
  have h1 : r / 2 ≤ ‖z - (pm L n : ℂ)‖ := by rw [hz]; linarith
  have h2 : ‖z - (pm L n : ℂ)‖ ≤ r := hz.le
  obtain ⟨R0, hR0, hR0n⟩ := free_res_annulus (κ := κ) hL hr hr2 h1 h2
  obtain ⟨T, hT, hTn⟩ := exists_T_annulus hL hr hr2 h1 h2 hR0 u
  have hM0 : 0 ≤ Mr L κ r * ‖u‖ := mul_nonneg (Mr_nonneg L κ r) (norm_nonneg _)
  have hpath : ∀ a : ℝ, |a| ≤ 1 → ∃ S : H2 L →L[ℂ] H2 L, (1 - (a : ℂ) • T) * S = 1 ∧
      S * (1 - (a : ℂ) • T) = 1 ∧ ‖S‖ ≤ Wb L κ r u ∧
      resolvent L κ (((a • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) (parity n) z = R0 * S := by
    intro a ha
    have hTa := hT.real_smul a
    obtain ⟨S, hS1, hS2, hSn⟩ := inverse_bound ((sqSmall_smul hL hr hr2 hu ha) z h1 h2 R0 _ hR0 hTa)
    refine ⟨S, hS1, hS2, hSn.trans ?_, resolvent_eq (resolvent_of_inverse hR0 hTa hS1 hS2)⟩
    unfold Wb
    gcongr
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |a| * ‖T‖ ≤ 1 * (Mr L κ r * ‖u‖) := mul_le_mul ha hTn (norm_nonneg _) zero_le_one
      _ = Mr L κ r * ‖u‖ := one_mul _
  obtain ⟨St, hSt1, hSt2, hStn, hRt⟩ := hpath t ht
  obtain ⟨Ss, hSs1, hSs2, hSsn, hRs⟩ := hpath s hs
  rw [hRt, hRs]
  have key : St - Ss = St * ((t : ℂ) • T - (s : ℂ) • T) * Ss := by
    calc St - Ss = St * ((1 - (s : ℂ) • T) * Ss) - (St * (1 - (t : ℂ) • T)) * Ss := by
          rw [hSs1, hSt2, mul_one, one_mul]
      _ = St * ((t : ℂ) • T - (s : ℂ) • T) * Ss := by
          have hring : ∀ X Y : H2 L →L[ℂ] H2 L,
              St * ((1 - Y) * Ss) - (St * (1 - X)) * Ss = St * (X - Y) * Ss := by
            intro X Y; simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc]; abel
          exact hring _ _
  have hdiff : ‖(t : ℂ) • T - (s : ℂ) • T‖ ≤ |t - s| * (Mr L κ r * ‖u‖) := by
    have e : (t : ℂ) • T - (s : ℂ) • T = (((t - s : ℝ)) : ℂ) • T := by
      rw [Complex.ofReal_sub]; exact (sub_smul _ _ _).symm
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hTn (abs_nonneg _)
  have hW0 : 0 ≤ Wb L κ r u := (norm_nonneg _).trans hStn
  calc ‖R0 * St - R0 * Ss‖ = ‖R0 * (St * ((t : ℂ) • T - (s : ℂ) • T) * Ss)‖ := by
        rw [← key, mul_sub]
    _ ≤ ‖R0‖ * (‖St‖ * ‖(t : ℂ) • T - (s : ℂ) • T‖ * ‖Ss‖) := by
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 2 / r * (Wb L κ r u * (|t - s| * (Mr L κ r * ‖u‖)) * Wb L κ r u) := by
        apply mul_le_mul hR0n _ (by positivity) (by positivity)
        apply mul_le_mul (mul_le_mul hStn hdiff (norm_nonneg _) hW0) hSsn (norm_nonneg _)
          (by positivity)
    _ = 2 / r * Wb L κ r u ^ 2 * (Mr L κ r * ‖u‖) * |t - s| := by ring

theorem path_lipschitz (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u) {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    ‖perturbedProj L κ (((t • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) n r -
        perturbedProj L κ (((s • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) n r‖ ≤
      r * (2 / r * Wb L κ r u ^ 2 * (Mr L κ r * ‖u‖) * |t - s|) := by
  have hsph : ∀ z ∈ sphere (QuantumNLS.LocalSpectral.center L n) r, ‖z - (pm L n : ℂ)‖ = r :=
    fun z hz => by simpa [QuantumNLS.LocalSpectral.center, mem_sphere_iff_norm] using hz
  have hcont : ∀ a : ℝ, |a| ≤ 1 → ContinuousOn
      (fun z => resolvent L κ (((a • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) (parity n) z)
      (sphere (QuantumNLS.LocalSpectral.center L n) r) := fun a ha =>
    continuousOn_resolvent _ (Rb_nonneg L κ hr (a • u)) (fun z hz => by
      have h := hsph z hz
      exact resolvent_exists hL hr hr2 (sqSmall_smul hL hr hr2 hu ha) (by rw [h]; linarith) h.le)
  unfold perturbedProj rieszProj
  have key := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (c := QuantumNLS.LocalSpectral.center L n) (R := r)
    (C := 2 / r * Wb L κ r u ^ 2 * (Mr L κ r * ‖u‖) * |t - s|)
    (f := fun z => resolvent L κ (((t • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) (parity n) z -
      resolvent L κ (((s • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) (parity n) z) hr.le
    (fun z hz => res_diff hL hr hr2 hu (hsph z hz) ht hs)
  rw [circleIntegral.integral_sub ((hcont t ht).circleIntegrable hr.le)
    ((hcont s hs).circleIntegrable hr.le), smul_sub] at key
  exact key

/-- **Rank two along the path** (FIN-EXT025-GP-17 corrected, route (ii), application duty discharged):
`t ↦ P_n(t u)` is a continuous family of idempotents on `[0,1]` with `P_n(0)` the actual free projection. -/
theorem rank_two_of_sqSmall (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u) :
    Module.finrank ℂ (rng (perturbedProj L κ (u : ℝ → ℂ) n r)) = 2 := by
  have : PreconnectedSpace unitInterval :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let P : unitInterval → H2 L →L[ℂ] H2 L :=
    fun t => perturbedProj L κ ((((t : ℝ) • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) n r
  have habs : ∀ t : unitInterval, |(t : ℝ)| ≤ 1 := fun t => by
    rw [abs_of_nonneg t.2.1]; exact t.2.2
  set C : ℝ := r * (2 / r * Wb L κ r u ^ 2 * (Mr L κ r * ‖u‖)) with hC
  have hW0 : 0 ≤ Wb L κ r u := by
    unfold Wb; have := Mr_nonneg L κ r; positivity
  have hC0 : 0 ≤ C := by
    have := Mr_nonneg L κ r; rw [hC]; positivity
  have hc : Continuous P := by
    apply LipschitzWith.continuous (K := C.toNNReal)
    apply LipschitzWith.of_dist_le_mul
    intro t s
    rw [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC0]
    have h := path_lipschitz hL hr hr2 hu (habs t) (habs s)
    calc ‖P t - P s‖ ≤ r * (2 / r * Wb L κ r u ^ 2 * (Mr L κ r * ‖u‖) * |(t : ℝ) - s|) := h
      _ = C * |(t : ℝ) - s| := by rw [hC]; ring
  have hi : ∀ t, P t ∘L P t = P t := fun t =>
    idem_of_sqSmall hL hr hr2 (sqSmall_smul hL hr hr2 hu (habs t))
  have hbase : P 0 = freeProj L κ n r := by
    have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
    show perturbedProj L κ (((((0 : unitInterval) : ℝ) • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) n r =
      perturbedProj L κ (fun _ => 0) n r
    rw [h0, zero_smul]
    exact QuantumNLS.Local002Bridge.perturbedProj_congr (Lp.coeFn_zero ℂ 2 (μI L)) n r
  have hr2' := QuantumNLS.TerraMultiRound34RankPath.rank_two_from_actual_free (κ := κ) hL hr hr2 n
    P hc hi 0 hbase 1
  have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  have hP1 : P 1 = perturbedProj L κ (u : ℝ → ℂ) n r := by
    show perturbedProj L κ (((((1 : unitInterval) : ℝ) • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) n r = _
    rw [h1, one_smul]
  rw [← hP1]
  exact hr2'

/-! ### The arbitrary-field package -/

/-- **Arbitrary-field resolvent and Riesz projection.**  For every interval field `u₀` there are a
field-dependent cutoff `N` and a radius `ρ > 0` such that for every `|n| > N` and `‖u - u₀‖ < ρ`:
`T_n(z,u)^2` is small on the annulus, `𝓛_u` is self-adjoint on `D_{(-1)^n}`, resolvents exist on the
annulus with one bound, `P_n(u)` is idempotent of rank two, and `t ↦ P_n(t u)` is Lipschitz on `[-1,1]`. -/
theorem arbitrary_field_riesz [Fact (0 < L)] (hL : 0 < L) {r : ℝ} (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (u₀ : Lp ℂ 2 (μI L)) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → ∀ u : Lp ℂ 2 (μI L), ‖u - u₀‖ < ρ →
      SqSmall L κ r n u ∧
      IsSelfAdjointGraph (LuGraph L κ (u : ℝ → ℂ) (parity n)) ∧
      (∀ z : ℂ, r / 2 ≤ ‖z - (pm L n : ℂ)‖ → ‖z - (pm L n : ℂ)‖ ≤ r →
        ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (u : ℝ → ℂ) (parity n) z R ∧ ‖R‖ ≤ Rb L κ r u) ∧
      perturbedProj L κ (u : ℝ → ℂ) n r * perturbedProj L κ (u : ℝ → ℂ) n r =
        perturbedProj L κ (u : ℝ → ℂ) n r ∧
      Module.finrank ℂ (rng (perturbedProj L κ (u : ℝ → ℂ) n r)) = 2 ∧
      (∀ t s : ℝ, |t| ≤ 1 → |s| ≤ 1 →
        ‖perturbedProj L κ (((t • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) n r -
          perturbedProj L κ (((s • u : Lp ℂ 2 (μI L))) : ℝ → ℂ) n r‖ ≤
        r * (2 / r * Wb L κ r u ^ 2 * (Mr L κ r * ‖u‖) * |t - s|)) := by
  obtain ⟨N, ρ, hρ, h⟩ := square_small (κ := κ) hL hr hr2 u₀
  refine ⟨N, ρ, hρ, fun n hn u hu => ?_⟩
  have hs : SqSmall L κ r n u := fun z h1 h2 R0 T hR0 hT => h n hn u hu z h1 h2 R0 T hR0 hT
  exact ⟨hs, selfAdjoint_of_sqSmall hL hr hr2 hs, fun z h1 h2 => resolvent_exists hL hr hr2 hs h1 h2,
    idem_of_sqSmall hL hr hr2 hs, rank_two_of_sqSmall hL hr hr2 hs,
    fun t s ht hs' => path_lipschitz hL hr hr2 hs ht hs'⟩

end QuantumNLS.RB01Resolvent
#print axioms QuantumNLS.RB01Resolvent.resolvent_of_inverse
#print axioms QuantumNLS.RB01Resolvent.selfAdjoint_of_sqSmall
#print axioms QuantumNLS.RB01Resolvent.idem_of_sqSmall
#print axioms QuantumNLS.RB01Resolvent.rank_two_of_sqSmall
#print axioms QuantumNLS.RB01Resolvent.arbitrary_field_riesz
