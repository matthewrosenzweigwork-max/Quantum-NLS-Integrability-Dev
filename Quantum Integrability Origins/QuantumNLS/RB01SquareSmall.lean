import Mathlib
import QuantumNLS.RB01FourierAction
import QuantumNLS.TerraMultiRound35SquareStability

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-2: the field-dependent high-frequency
square estimate.

Source (collective_actions.tex:152-187): "approximate `q_0` ... by a trigonometric polynomial `a` supported on
`|k| ≤ K` ... `A_n(w,a)^2` is a finite sum of weighted shifts.  The two resolvent denominators ... `η = w+p_n-p_m`,
`ξ = w+p_n-p_{2k-m}` ... Their sum is `2(w+p_n-p_k)` ... the identity `1/(ηξ) = (1/η+1/ξ)/(η+ξ)` gives
`sup ‖A_n(w,a)^2‖ ≤ C_a/(|n|-K)`.  For `q = a + b` ... `‖A_n(q)^2 - A_n(a)^2‖ ≤ C(2‖a‖‖b‖ + ‖b‖^2)`.  Choose the
polynomial approximation first, then the cutoff and a ... neighborhood `U` of `q_0`."

Proved here for the actual operator `T_n(z,u) = V_u R_{0,n}(z)` (LOCAL-002's `IsMulOp`, real slice):
* `hs_bound`: Hilbert–Schmidt-type operator bound from a square-summable bound on a Hilbert basis.
* `chiBasis`: the free functions of one parity form a Hilbert basis of `L²(0,L;ℂ²)`.
* `inv_sq_le_gmaj`, `summable_gmaj`: on the annulus `r/2 ≤ |z - p_n| ≤ r`, `Σ_l |z - p_l|^{-2}` is bounded
  uniformly in `n` and `z`.
* `trig_square_bound`: for a finite Fourier sum `a`, `‖T_n(z,a)^2‖ ≤ √Q_a / δ_n` with
  `δ_n = 2π(|n| - K)/L - r`.
* **`square_small`**: for every field `u₀ ∈ L²(0,L)` there are `N` and `ρ > 0` with
  `‖T_n(z,u)^2‖ ≤ 1/4` for all `|n| > N`, `‖u - u₀‖ < ρ`, and `r/2 ≤ |z - p_n| ≤ r`.
The annulus (rather than only the circle `|z - p_n| = r`) is what the Riesz idempotence argument needs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.RB01SquareSmall
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Basis QuantumNLS.Local002Free
  QuantumNLS.Local002Rank QuantumNLS.RB01FourierAction

variable {L κ : ℝ}

/-! ### A Hilbert–Schmidt bound -/

theorem hs_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (X : H →L[ℂ] H) (h : ι → ℝ)
    (hh : ∀ i, ‖X (b i)‖ ≤ h i) (hs : Summable fun i => h i ^ 2) :
    ‖X‖ ≤ Real.sqrt (∑' i, h i ^ 2) := by
  refine X.opNorm_le_bound (Real.sqrt_nonneg _) fun φ => ?_
  set c := b.repr φ with hc
  have h0 : ∀ i, 0 ≤ h i := fun i => (norm_nonneg _).trans (hh i)
  have hsum : HasSum (fun i => c i • X (b i)) (X φ) := by
    have := (b.hasSum_repr φ).mapL X
    simpa only [map_smul] using this
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hc2 : Summable fun i => ‖c i‖ ^ (2 : ℝ) := by
    have := (lp.memℓp c).summable hp
    simpa using this
  have hh2 : Summable fun i => h i ^ (2 : ℝ) := by
    simpa [Real.rpow_two] using hs
  have hmul := Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun i => norm_nonneg (c i)) h0 hc2 hh2
  have hCS := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun i => norm_nonneg (c i)) h0 hc2 hh2
  have hparse : ∑' i, ‖c i‖ ^ (2 : ℝ) = ‖φ‖ ^ (2 : ℝ) := by
    have := lp.norm_rpow_eq_tsum hp c
    simp only [ENNReal.toReal_ofNat] at this
    rw [← this, hc, LinearIsometryEquiv.norm_map]
  have hbd : Summable fun i => ‖c i • X (b i)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _)
      (fun i => by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hh i) (norm_nonneg _)) hmul
  calc ‖X φ‖ = ‖∑' i, c i • X (b i)‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' i, ‖c i • X (b i)‖ := norm_tsum_le_tsum_norm hbd
    _ ≤ ∑' i, ‖c i‖ * h i := by
        refine hbd.tsum_le_tsum (fun i => ?_) hmul
        rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hh i) (norm_nonneg _)
    _ ≤ (∑' i, ‖c i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑' i, h i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hCS
    _ = Real.sqrt (∑' i, h i ^ 2) * ‖φ‖ := by
        rw [hparse, ← Real.rpow_mul (norm_nonneg _)]
        simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
        norm_num
        ring

/-! ### The free Hilbert basis of one parity -/

/-- The index set `{(m, j) : parity m = parity n}`. -/
abbrev Idx (n : ℤ) := {p : ℤ × Fin 2 // parity p.1 = parity n}

theorem chi_orth_bot (hL : 0 < L) (n : ℤ) :
    (Submodule.span ℂ (Set.range (fun p : Idx n => chi L p.1.1 p.1.2)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  apply chi_complete hL n f
  intro m j hm
  have := (Submodule.mem_orthogonal _ _).1 hf (chi L m j)
    (Submodule.subset_span ⟨⟨(m, j), hm⟩, rfl⟩)
  exact this

/-- The Hilbert basis `(χ_{m,j})_{parity m = parity n}` of `L²(0,L;ℂ²)`. -/
def chiBasis (hL : 0 < L) (n : ℤ) : HilbertBasis (Idx n) ℂ (H2 L) :=
  HilbertBasis.mkOfOrthogonalEqBot (chi_orthonormal hL (parity n)) (chi_orth_bot hL n)

theorem chiBasis_apply (hL : 0 < L) (n : ℤ) (p : Idx n) : chiBasis hL n p = chi L p.1.1 p.1.2 := by
  unfold chiBasis
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- Sums over the parity index set are dominated by twice the sum over labels. -/
theorem idx_sum (n : ℤ) (F : ℤ → ℝ) (hF0 : ∀ l, 0 ≤ F l) (hF : Summable F) :
    Summable (fun p : Idx n => F p.1.1) ∧ ∑' p : Idx n, F p.1.1 ≤ 2 * ∑' l, F l := by
  let G : ℤ × Fin 2 → ℝ := fun q => F q.1
  have hfin : ∀ x : ℤ, Summable fun y : Fin 2 => G (x, y) := fun x => (hasSum_fintype _).summable
  have hG : Summable G := by
    refine (summable_prod_of_nonneg (fun q => hF0 q.1)).2 ⟨hfin, ?_⟩
    have : (fun x : ℤ => ∑' y : Fin 2, G (x, y)) = fun x => 2 * F x := by
      funext x; simp [G, tsum_fintype]
    rw [this]; exact hF.mul_left 2
  have hGt : ∑' q, G q = 2 * ∑' l, F l := by
    rw [hG.tsum_prod' hfin]
    simp only [G, tsum_fintype, Fin.sum_univ_two]
    rw [← tsum_mul_left]
    congr 1; funext x; ring
  have hsub : Summable (fun p : Idx n => F p.1.1) :=
    hG.comp_injective (i := fun p : Idx n => p.1) Subtype.val_injective
  refine ⟨hsub, ?_⟩
  rw [← hGt]
  exact hsub.tsum_le_tsum_of_inj (fun p : Idx n => p.1) Subtype.val_injective
    (fun q _ => hF0 q.1) (fun p => le_rfl) hG

/-! ### Uniform free sums on the annulus -/

/-- A summable majorant of `|z - p_l|^{-2}` in the variable `l - n`. -/
def gmaj (r ε : ℝ) (m : ℤ) : ℝ := (if m = 0 then (2 / r) ^ 2 else 0) + ε⁻¹ ^ 2 * (1 / (m : ℝ) ^ 2)

theorem summable_gmaj (r ε : ℝ) : Summable (gmaj r ε) := by
  have h1 : Summable fun m : ℤ => (if m = 0 then (2 / r) ^ 2 else 0 : ℝ) :=
    (hasSum_ite_eq (0 : ℤ) ((2 / r) ^ 2)).summable
  have h2 : Summable fun m : ℤ => 1 / (m : ℝ) ^ 2 :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  exact h1.add (h2.mul_left _)

theorem gmaj_nonneg (r ε : ℝ) (m : ℤ) : 0 ≤ gmaj r ε m := by
  unfold gmaj; split_ifs <;> positivity

theorem norm_pm_sub (hL : 0 < L) (a b : ℤ) :
    ‖(pm L a : ℂ) - (pm L b : ℂ)‖ = 2 * Real.pi * |(a : ℝ) - b| / L := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  unfold pm
  rw [show 2 * Real.pi * (a : ℝ) / L - 2 * Real.pi * b / L = (2 * Real.pi / L) * ((a : ℝ) - b) by ring,
    abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / L)]
  ring

/-- On the annulus, `|z - p_l| ≥ (2π/L - r)|l - n|` and `|z - p_n| ≥ r/2`. -/
theorem norm_z_sub_pm_ge (hL : 0 < L) {r : ℝ} {n l : ℤ} {z : ℂ}
    (h2 : ‖z - (pm L n : ℂ)‖ ≤ r) :
    2 * Real.pi * |(l : ℝ) - n| / L - r ≤ ‖z - (pm L l : ℂ)‖ := by
  have h := norm_sub_norm_le ((pm L n : ℂ) - pm L l) ((pm L n : ℂ) - z)
  rw [norm_pm_sub hL, show (pm L n : ℂ) - pm L l - ((pm L n : ℂ) - z) = z - pm L l by ring,
    norm_sub_rev (pm L n : ℂ) z, abs_sub_comm] at h
  linarith

theorem inv_sq_le_gmaj (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n l : ℤ}
    {z : ℂ} (h1 : r / 2 ≤ ‖z - (pm L n : ℂ)‖) (h2 : ‖z - (pm L n : ℂ)‖ ≤ r) :
    0 < ‖z - (pm L l : ℂ)‖ ∧ ‖z - (pm L l : ℂ)‖⁻¹ ^ 2 ≤ gmaj r (2 * Real.pi / L - r) (l - n) := by
  by_cases hln : l = n
  · subst hln
    have hpos : 0 < ‖z - (pm L l : ℂ)‖ := lt_of_lt_of_le (by positivity) h1
    refine ⟨hpos, ?_⟩
    simp only [gmaj, sub_self, if_true, Int.cast_zero]
    have : ‖z - (pm L l : ℂ)‖⁻¹ ≤ 2 / r := by
      rw [inv_le_comm₀ hpos (by positivity), inv_div]; linarith
    have h0 : (1 : ℝ) / (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0, mul_zero, add_zero]
    exact pow_le_pow_left₀ (inv_nonneg.2 hpos.le) this 2
  · have hε : 0 < 2 * Real.pi / L - r := by linarith
    have hm : (1 : ℝ) ≤ |(l : ℝ) - n| := by
      have := Int.one_le_abs (sub_ne_zero.2 hln)
      exact_mod_cast this
    have hge := norm_z_sub_pm_ge (l := l) hL h2
    have hlow : (2 * Real.pi / L - r) * |(l : ℝ) - n| ≤ ‖z - (pm L l : ℂ)‖ := by
      have : (2 * Real.pi / L - r) * |(l : ℝ) - n| = 2 * Real.pi * |(l : ℝ) - n| / L - r * |(l : ℝ) - n| := by
        ring
      nlinarith
    have hpos' : 0 < (2 * Real.pi / L - r) * |(l : ℝ) - n| := by positivity
    have hpos : 0 < ‖z - (pm L l : ℂ)‖ := lt_of_lt_of_le hpos' hlow
    refine ⟨hpos, ?_⟩
    simp only [gmaj, if_neg (sub_ne_zero.2 hln), zero_add]
    have hinv : ‖z - (pm L l : ℂ)‖⁻¹ ≤ ((2 * Real.pi / L - r) * |(l : ℝ) - n|)⁻¹ :=
      inv_anti₀ hpos' hlow
    have hsq := pow_le_pow_left₀ (inv_nonneg.2 hpos.le) hinv 2
    refine hsq.trans (le_of_eq ?_)
    push_cast
    rw [mul_inv, mul_pow, inv_pow (|(l : ℝ) - n|), sq_abs]
    ring

/-- `Σ_l |z - p_l|^{-2} ≤ G` on the annulus, uniformly in `n` and `z`. -/
theorem free_sum (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {z : ℂ} (h1 : r / 2 ≤ ‖z - (pm L n : ℂ)‖) (h2 : ‖z - (pm L n : ℂ)‖ ≤ r) :
    Summable (fun l : ℤ => ‖z - (pm L l : ℂ)‖⁻¹ ^ 2) ∧
      ∑' l : ℤ, ‖z - (pm L l : ℂ)‖⁻¹ ^ 2 ≤ ∑' m, gmaj r (2 * Real.pi / L - r) m := by
  set g := gmaj r (2 * Real.pi / L - r) with hg
  have hgs : Summable (fun l : ℤ => g (l - n)) :=
    (Equiv.subRight n).summable_iff.mpr (summable_gmaj _ _)
  have hle : ∀ l : ℤ, ‖z - (pm L l : ℂ)‖⁻¹ ^ 2 ≤ g (l - n) := fun l =>
    (inv_sq_le_gmaj (l := l) hL hr hr2 h1 h2).2
  have hs : Summable (fun l : ℤ => ‖z - (pm L l : ℂ)‖⁻¹ ^ 2) :=
    Summable.of_nonneg_of_le (fun l => by positivity) hle hgs
  refine ⟨hs, (hs.tsum_le_tsum hle hgs).trans (le_of_eq ?_)⟩
  exact (Equiv.subRight n).tsum_eq g

/-- The reflected free sum `Σ_l |z - p_{2k-l}|^{-2}` is the same sum. -/
theorem free_sum_reflect (k : ℤ) (z : ℂ) :
    ∑' l : ℤ, ‖z - (pm L (2 * k - l) : ℂ)‖⁻¹ ^ 2 = ∑' l : ℤ, ‖z - (pm L l : ℂ)‖⁻¹ ^ 2 :=
  (Equiv.subLeft (2 * k)).tsum_eq (fun l : ℤ => ‖z - (pm L l : ℂ)‖⁻¹ ^ 2)

theorem summable_reflect (k : ℤ) (z : ℂ) (hs : Summable (fun l : ℤ => ‖z - (pm L l : ℂ)‖⁻¹ ^ 2)) :
    Summable (fun l : ℤ => ‖z - (pm L (2 * k - l) : ℂ)‖⁻¹ ^ 2) :=
  (Equiv.subLeft (2 * k)).summable_iff.mpr hs

/-! ### The square estimate for a finite Fourier sum -/

theorem pm_reflect_sum (L : ℝ) (k l : ℤ) :
    (pm L l : ℂ) + (pm L (2 * k - l) : ℂ) = 2 * (pm L k : ℂ) := by
  unfold pm; push_cast; ring

/-- `|z - p_l| + |z - p_{2k-l}| ≥ 2 |z - p_k|`: the sum of the two denominators. -/
theorem denom_sum (k l : ℤ) (z : ℂ) :
    2 * ‖z - (pm L k : ℂ)‖ ≤ ‖z - (pm L l : ℂ)‖ + ‖z - (pm L (2 * k - l) : ℂ)‖ := by
  have h : (z - (pm L l : ℂ)) + (z - (pm L (2 * k - l) : ℂ)) = 2 * (z - (pm L k : ℂ)) := by
    linear_combination (-1 : ℂ) * pm_reflect_sum L k l
  have := norm_add_le (z - (pm L l : ℂ)) (z - (pm L (2 * k - l) : ℂ))
  rw [h, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
  exact this

/-- `1/(DB) ≤ (1/D + 1/B)/(2δ)` when `D + B ≥ 2δ`. -/
theorem inv_mul_le {D B δ : ℝ} (hD : 0 < D) (hB : 0 < B) (hδ : 0 < δ) (h : 2 * δ ≤ D + B) :
    1 / (D * B) ≤ (D⁻¹ + B⁻¹) / (2 * δ) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : (D⁻¹ + B⁻¹) * (D * B) = D + B := by field_simp; ring
  nlinarith

theorem trig_square_bound (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {z : ℂ} (h1 : r / 2 ≤ ‖z - (pm L n : ℂ)‖) (h2 : ‖z - (pm L n : ℂ)‖ ≤ r)
    {R0 T : H2 L →L[ℂ] H2 L} (hR0 : IsResolvent L κ (fun _ => 0) (parity n) z R0)
    (S : Finset ℤ) (c : ℤ → ℂ) (K : ℕ) (hK : ∀ k ∈ S, |(k : ℝ)| ≤ K)
    (hδ : 0 < 2 * Real.pi * (|(n : ℝ)| - K) / L - r)
    (hT : QuantumNLS.Local002.IsMulOp κ R0 ((∑ k ∈ S, c k • emode L k : Lp ℂ 2 (μI L)) : ℝ → ℂ) T) :
    ‖T * T‖ ≤ Real.sqrt (8 * S.card * (∑' m, gmaj r (2 * Real.pi / L - r) m) *
      ∑ k ∈ S, ((2 * Real.sqrt κ * (Real.sqrt L)⁻¹) ^ 2 * ‖c k‖ * ∑ k' ∈ S, ‖c k'‖) ^ 2) /
      (2 * (2 * Real.pi * (|(n : ℝ)| - K) / L - r)) := by
  set δ := 2 * Real.pi * (|(n : ℝ)| - K) / L - r with hδdef
  set G := ∑' m, gmaj r (2 * Real.pi / L - r) m with hG
  set A := ∑ k' ∈ S, ‖c k'‖ with hA
  set a := 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ with ha
  set x : ℤ → ℝ := fun k => a ^ 2 * ‖c k‖ * A with hx
  set w : ℤ → ℝ := fun k => x k / (2 * δ) with hw
  set D : ℤ → ℝ := fun l => ‖z - (pm L l : ℂ)‖ with hDdef
  have hs0 : 0 < ‖z - (pm L n : ℂ)‖ := lt_of_lt_of_le (by positivity) h1
  have hs2 : ‖z - (pm L n : ℂ)‖ < 2 * Real.pi / L := lt_of_le_of_lt h2 hr2
  have hex : ∀ u : Lp ℂ 2 (μI L), ∃ T', QuantumNLS.Local002.IsMulOp κ R0 (u : ℝ → ℂ) T' :=
    fun u => (exists_mulOp hs0 hs2 rfl hR0 u).imp fun _ h => h.1
  have hDpos : ∀ l, 0 < D l := fun l => (inv_sq_le_gmaj (l := l) hL hr hr2 h1 h2).1
  have hz : ∀ m : ℤ, parity m = parity n → z ≠ (pm L m : ℂ) := fun m _ h => by
    have := hDpos m
    simp only [hDdef, h, sub_self, norm_zero, lt_self_iff_false] at this
  have hfs := free_sum hL hr hr2 h1 h2
  have hx0 : ∀ k, 0 ≤ x k := fun k => by simp only [hx]; positivity
  have hw0 : ∀ k, 0 ≤ w k := fun k => by simp only [hw]; exact div_nonneg (hx0 k) (by positivity)
  -- the denominators
  have hk : ∀ k ∈ S, δ ≤ ‖z - (pm L k : ℂ)‖ := by
    intro k hkS
    have hge := norm_z_sub_pm_ge (l := k) hL h2
    have habs : |(n : ℝ)| - K ≤ |(k : ℝ) - n| := by
      have := abs_sub_abs_le_abs_sub (n : ℝ) (k : ℝ)
      rw [abs_sub_comm] at this
      linarith [hK k hkS]
    have : 2 * Real.pi * (|(n : ℝ)| - K) / L ≤ 2 * Real.pi * |(k : ℝ) - n| / L := by
      apply div_le_div_of_nonneg_right _ hL.le
      exact mul_le_mul_of_nonneg_left habs (by positivity)
    simp only [hδdef]; linarith
  -- the pointwise bound h'
  set h' : ℤ → ℝ := fun l => ∑ k ∈ S, w k * ((D l)⁻¹ + (D (2 * k - l))⁻¹) with hh'
  have hpt : ∀ p : Idx n, ‖(T * T) (chiBasis hL n p)‖ ≤ h' p.1.1 := by
    intro p
    rw [chiBasis_apply, ContinuousLinearMap.mul_apply]
    refine (norm_mulOp_trig_sq_chi hL p.1.2 hR0 p.2 hz S c hT hex).trans
      (Finset.sum_le_sum fun k hkS => ?_)
    have hB := hDpos (2 * k - p.1.1)
    have hD := hDpos p.1.1
    have hsum := denom_sum (L := L) k p.1.1 z
    have hle := inv_mul_le hD hB hδ (by linarith [hk k hkS])
    change x k / (D p.1.1 * D (2 * k - p.1.1)) ≤ w k * ((D p.1.1)⁻¹ + (D (2 * k - p.1.1))⁻¹)
    rw [div_eq_mul_one_div, hw]
    calc x k * (1 / (D p.1.1 * D (2 * k - p.1.1)))
        ≤ x k * (((D p.1.1)⁻¹ + (D (2 * k - p.1.1))⁻¹) / (2 * δ)) :=
          mul_le_mul_of_nonneg_left hle (hx0 k)
      _ = x k / (2 * δ) * ((D p.1.1)⁻¹ + (D (2 * k - p.1.1))⁻¹) := by ring
  -- the square-summable majorant
  set F : ℤ → ℝ := fun l => S.card * ∑ k ∈ S, w k ^ 2 * (2 * (D l)⁻¹ ^ 2 + 2 * (D (2 * k - l))⁻¹ ^ 2)
    with hF
  have hsq : ∀ l, h' l ^ 2 ≤ F l := by
    intro l
    refine (sq_sum_le_card_mul_sum_sq (s := S) (f := fun k => w k * ((D l)⁻¹ + (D (2 * k - l))⁻¹))).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum fun k _ => ?_
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith [sq_nonneg ((D l)⁻¹ - (D (2 * k - l))⁻¹)]
  have hF0 : ∀ l, 0 ≤ F l := fun l => by simp only [hF]; positivity
  have hDs : Summable fun l : ℤ => (D l)⁻¹ ^ 2 := hfs.1
  have hFhas : HasSum F (S.card * ∑ k ∈ S, w k ^ 2 * (2 * (∑' l, (D l)⁻¹ ^ 2) +
      2 * (∑' l, (D l)⁻¹ ^ 2))) := by
    apply HasSum.mul_left
    apply hasSum_sum
    intro k _
    apply HasSum.mul_left
    refine (hDs.hasSum.mul_left 2).add ?_
    have hr' := (summable_reflect (L := L) k z hDs).hasSum
    rw [free_sum_reflect] at hr'
    exact hr'.mul_left 2
  have hFle : ∑' l, F l ≤ S.card * ∑ k ∈ S, w k ^ 2 * (4 * G) := by
    rw [hFhas.tsum_eq]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum fun k _ => ?_
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    linarith [hfs.2]
  have hh2s : Summable fun l => h' l ^ 2 :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hsq hFhas.summable
  obtain ⟨hIs, hIle⟩ := idx_sum n (fun l => h' l ^ 2) (fun l => sq_nonneg _) hh2s
  have hHS := hs_bound (chiBasis hL n) (T * T) (fun p : Idx n => h' p.1.1) hpt hIs
  refine hHS.trans ?_
  have hmain : ∑' p : Idx n, h' p.1.1 ^ 2 ≤
      8 * S.card * G * ∑ k ∈ S, x k ^ 2 / (2 * δ) ^ 2 := by
    calc ∑' p : Idx n, h' p.1.1 ^ 2 ≤ 2 * ∑' l, h' l ^ 2 := hIle
      _ ≤ 2 * ∑' l, F l :=
          mul_le_mul_of_nonneg_left (hh2s.tsum_le_tsum hsq hFhas.summable) (by norm_num)
      _ ≤ 2 * (S.card * ∑ k ∈ S, w k ^ 2 * (4 * G)) := by gcongr
      _ = 8 * S.card * G * ∑ k ∈ S, x k ^ 2 / (2 * δ) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hw, div_pow]
          ring
  have hval : 8 * S.card * G * ∑ k ∈ S, x k ^ 2 / (2 * δ) ^ 2 =
      (8 * S.card * G * ∑ k ∈ S, x k ^ 2) / (2 * δ) ^ 2 := by
    rw [← Finset.sum_div, mul_div_assoc]
  rw [hval] at hmain
  have hG0 : 0 ≤ G := tsum_nonneg (gmaj_nonneg _ _)
  calc Real.sqrt (∑' p : Idx n, h' p.1.1 ^ 2)
      ≤ Real.sqrt ((8 * S.card * G * ∑ k ∈ S, x k ^ 2) / (2 * δ) ^ 2) := Real.sqrt_le_sqrt hmain
    _ = Real.sqrt (8 * S.card * G * ∑ k ∈ S, x k ^ 2) / (2 * δ) := by
        rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-! ### Field-dependent square-smallness -/

theorem square_small [Fact (0 < L)] (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (u₀ : Lp ℂ 2 (μI L)) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → ∀ u : Lp ℂ 2 (μI L), ‖u - u₀‖ < ρ →
      ∀ z : ℂ, r / 2 ≤ ‖z - (pm L n : ℂ)‖ → ‖z - (pm L n : ℂ)‖ ≤ r →
      ∀ R0 T : H2 L →L[ℂ] H2 L, IsResolvent L κ (fun _ => 0) (parity n) z R0 →
        QuantumNLS.Local002.IsMulOp κ R0 (u : ℝ → ℂ) T → ‖T * T‖ ≤ 1 / 4 := by
  set M := 2 * Real.sqrt κ * Cmax L (r / 2) with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ Cmax L (r / 2) := Real.sqrt_nonneg _
    positivity
  set B := M * (‖u₀‖ + 1) with hB
  have hB0 : 0 ≤ B := by positivity
  set ε₀ := min 1 (1 / (32 * (B * M + M ^ 2 + 1))) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min one_pos (by positivity)
  have hε₀1 : ε₀ ≤ 1 := min_le_left _ _
  have hε₀2 : ε₀ ≤ 1 / (32 * (B * M + M ^ 2 + 1)) := min_le_right _ _
  obtain ⟨S, c, hac⟩ := exists_trig_approx u₀ hε₀pos
  set a : Lp ℂ 2 (μI L) := ∑ k ∈ S, c k • emode L k with ha
  set K : ℕ := S.sup (fun k => k.natAbs) with hKdef
  have hK : ∀ k ∈ S, |(k : ℝ)| ≤ K := by
    intro k hk
    have h1 : k.natAbs ≤ K := Finset.le_sup (f := fun k : ℤ => k.natAbs) hk
    have h2 : (k.natAbs : ℝ) = |(k : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← h2]; exact_mod_cast h1
  set G := ∑' m, gmaj r (2 * Real.pi / L - r) m with hG
  set Q := 8 * S.card * G * ∑ k ∈ S, ((2 * Real.sqrt κ * (Real.sqrt L)⁻¹) ^ 2 * ‖c k‖ *
      ∑ k' ∈ S, ‖c k'‖) ^ 2 with hQ
  set N : ℕ := K + ⌈(4 * Real.sqrt Q + r) * L / (2 * Real.pi)⌉₊ with hN
  refine ⟨N, ε₀, hε₀pos, ?_⟩
  intro n hn u hu z h1 h2 R0 T hR0 hT
  have hs0 : 0 < ‖z - (pm L n : ℂ)‖ := lt_of_lt_of_le (by positivity) h1
  have hs2 : ‖z - (pm L n : ℂ)‖ < 2 * Real.pi / L := lt_of_le_of_lt h2 hr2
  have hCs : Cconst L ‖z - (pm L n : ℂ)‖ ≤ Cmax L (r / 2) :=
    Cconst_le hL (by positivity) h1 hs2
  have hbnd : ∀ v : Lp ℂ 2 (μI L), ∃ Tv : H2 L →L[ℂ] H2 L,
      QuantumNLS.Local002.IsMulOp κ R0 (v : ℝ → ℂ) Tv ∧ ‖Tv‖ ≤ M * ‖v‖ := by
    intro v
    obtain ⟨Tv, hTv, hTn⟩ := exists_mulOp hs0 hs2 rfl hR0 v
    refine ⟨Tv, hTv, hTn.trans ?_⟩
    rw [hM]
    have : 0 ≤ 2 * Real.sqrt κ := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCs this) (norm_nonneg _)
  obtain ⟨Ta, hTa, hTan⟩ := hbnd a
  obtain ⟨Tb, hTb, hTbn⟩ := hbnd (u - a)
  have hsum : T = Ta + Tb := by
    have h := hTa.add hTb
    rw [add_sub_cancel] at h
    exact hT.unique h
  -- the trigonometric part
  have hδ : 4 * Real.sqrt Q < 2 * Real.pi * (|(n : ℝ)| - K) / L - r := by
    have hceil : (4 * Real.sqrt Q + r) * L / (2 * Real.pi) ≤ (N : ℝ) - K := by
      rw [hN]; push_cast
      linarith [Nat.le_ceil ((4 * Real.sqrt Q + r) * L / (2 * Real.pi))]
    have h3 : (4 * Real.sqrt Q + r) * L / (2 * Real.pi) < |(n : ℝ)| - K := by linarith
    rw [div_lt_iff₀ (by positivity)] at h3
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hL]
    linarith
  have hQ0 : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  have hδpos : 0 < 2 * Real.pi * (|(n : ℝ)| - K) / L - r := by linarith
  have htrig := trig_square_bound hL hr hr2 h1 h2 hR0 S c K hK hδpos hTa
  have htrig' : ‖Ta * Ta‖ ≤ 1 / 8 := by
    refine htrig.trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith
  -- the remainder
  have ha1 : ‖a‖ ≤ ‖u₀‖ + 1 := by
    have := norm_le_insert' a u₀
    have h' : ‖a - u₀‖ < ε₀ := hac
    linarith
  have hTa' : ‖Ta‖ ≤ B := hTan.trans (by rw [hB]; exact mul_le_mul_of_nonneg_left ha1 hM0)
  have hub : ‖u - a‖ ≤ 2 * ε₀ := by
    have h' : ‖a - u₀‖ < ε₀ := hac
    have := norm_sub_le (u - u₀) (a - u₀)
    rw [show u - u₀ - (a - u₀) = u - a by abel] at this
    linarith
  have hTb' : ‖Tb‖ ≤ M * (2 * ε₀) := hTbn.trans (mul_le_mul_of_nonneg_left hub hM0)
  have hstab := QuantumNLS.TerraMultiRound35SquareStability.square_add_bound Ta Tb
  have hrem : 2 * ‖Ta‖ * ‖Tb‖ + ‖Tb‖ ^ 2 ≤ 1 / 8 := by
    have e1 : 2 * ‖Ta‖ * ‖Tb‖ ≤ 2 * B * (M * (2 * ε₀)) := by
      have := mul_le_mul hTa' hTb' (norm_nonneg _) hB0
      nlinarith [norm_nonneg Ta, norm_nonneg Tb]
    have e2 : ‖Tb‖ ^ 2 ≤ (M * (2 * ε₀)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hTb' 2
    have e3 : (M * (2 * ε₀)) ^ 2 ≤ 4 * M ^ 2 * ε₀ := by
      have : ε₀ ^ 2 ≤ ε₀ := by nlinarith
      nlinarith [sq_nonneg M]
    have hD : 0 < 32 * (B * M + M ^ 2 + 1) := by positivity
    have e4 : ε₀ * (32 * (B * M + M ^ 2 + 1)) ≤ 1 := by
      rw [le_div_iff₀ hD] at hε₀2
      linarith
    nlinarith [mul_nonneg hB0 hM0, sq_nonneg M]
  rw [hsum]
  calc ‖(Ta + Tb) * (Ta + Tb)‖ ≤ ‖Ta * Ta‖ + ‖(Ta + Tb) * (Ta + Tb) - Ta * Ta‖ := by
        have := norm_add_le (Ta * Ta) ((Ta + Tb) * (Ta + Tb) - Ta * Ta)
        rwa [add_sub_cancel] at this
    _ ≤ 1 / 8 + 1 / 8 := add_le_add htrig' (hstab.trans hrem)
    _ = 1 / 4 := by norm_num

end QuantumNLS.RB01SquareSmall
#print axioms QuantumNLS.RB01SquareSmall.hs_bound
#print axioms QuantumNLS.RB01SquareSmall.chiBasis_apply
#print axioms QuantumNLS.RB01SquareSmall.free_sum
#print axioms QuantumNLS.RB01SquareSmall.trig_square_bound
#print axioms QuantumNLS.RB01SquareSmall.square_small
