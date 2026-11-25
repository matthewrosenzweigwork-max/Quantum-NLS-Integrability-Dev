import Mathlib
import QuantumNLS.BetheConvexity

/-!
# R-CD2257D0 (`basis:lem:zero`): zero-coupling limit of the Bethe roots

Source: `source/chapters/foundations/periodic_basis.tex` lines 164–180 (statement) with its proof;
`q(n,c)` is the root of `basis:eq:logbethe` (lines 27–31), labels `n ∈ 𝔑_N` (line 24, decreasing).
Accepted inputs, imported read-only: `BetheConvexity.source_roots_spec` (R-4C8D7C9E: the root curve
`BetheSmooth.sourceRoots L n c` solves the printed equation, is strictly decreasing, is bounded, and
is the unique solution). No root is supplied: `q(n,c) := BetheSmooth.sourceRoots L n c`.

Claims (for each fixed admissible label `n`, `L > 0`):

* `zero_limit_root`: `q(n,c) → q(n,0) = (2π/L) n` as `c ↓ 0`, and
  `(q_i(n,c) − q_j(n,c))/c → +∞` for `i < j` (also when `n_i = n_j`).
* `root_identification`: for `c > 0`, `sourceRoots L n c` is the unique real solution of the printed
  equation (the accepted uniqueness clause).

Argument (a deviation from the printed proof, same conclusion). The printed proof passes to the limit in
the Yang–Yang functional `Y_c → Y_0` locally uniformly and identifies minimizers. This module uses the
exact root equation instead, with no compactness and no minimization. Write `d = q(n,c) − q(n,0)`,
`T_ij = π/2·sgn(j−i) − arctan((q_i−q_j)/c)` (`zTm`), and `ρ_i = (N−1)/2 − i` (`zrho`). The root equation is
`L d_i = 2 ∑_j T_ij`, and `T` is antisymmetric. Symmetrizing gives

  `L ∑_i d_i² = ∑_{i,j} (d_i − d_j) T_ij`,

and for `i < j`, `(d_i − d_j) T_ij ≤ c` (using `arctan(x) ≤ x` on `x = c/(q_i−q_j)` and
`q_0` nondecreasing in index). Hence `∑ d_i² ≤ N²c/L`, which gives (1) with rate `√c`. For (2), the
`ρ`-weighted identity `L ∑_k ρ_k d_k = ∑_{k,j} (ρ_k − ρ_j) T_kj` has nonnegative terms, and the term
`(i,j)` dominates `T_ij`. Therefore `T_ij ≤ C√c → 0`, so `arctan((q_i−q_j)/c) → π/2`, so
`(q_i−q_j)/c → +∞`.
-/

namespace QuantumNLS.BetheZeroLimit

open Real Finset Filter Topology

/-- Zero-based decreasing-rank correction `ρ_i = (N−1)/2 − i` (so `I_i = n_i + ρ_i`). -/
noncomputable def zrho (N : ℕ) (i : Fin N) : ℝ := ((N : ℝ) - 1) / 2 - (i.val : ℝ)

/-- Index-order sign: `+1` if `i < j`, `−1` if `j < i`, else `0`. -/
noncomputable def zsg {N : ℕ} (i j : Fin N) : ℝ := if i < j then 1 else if j < i then -1 else 0

lemma zsg_neg {N : ℕ} (i j : Fin N) : zsg j i = - zsg i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [zsg, h, lt_asymm h]
  · simp [zsg]
  · simp [zsg, h, lt_asymm h]

lemma zsg_self {N : ℕ} (i : Fin N) : zsg i i = 0 := by simp [zsg]

lemma sum_zsg {N : ℕ} (i : Fin N) : ∑ j, zsg i j = 2 * zrho N i := by
  have h1 : ∀ j : Fin N,
      zsg i j = (if i < j then (1:ℝ) else 0) - (if j < i then (1:ℝ) else 0) := by
    intro j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [zsg, h, lt_asymm h]
    · simp [zsg]
    · simp [zsg, h, lt_asymm h]
  have hI : (Finset.univ.filter (fun j : Fin N => i < j)) = Finset.Ioi i := by
    ext j; simp
  have hL : (Finset.univ.filter (fun j : Fin N => j < i)) = Finset.Iio i := by
    ext j; simp
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_boole]
  rw [hI, hL, Fin.card_Ioi, Fin.card_Iio]
  have hi : i.val < N := i.isLt
  unfold zrho
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- Antisymmetric pair form `T_ij = (π/2)·sgn(j−i) − arctan((x_i−x_j)/c)`. -/
noncomputable def zTm {N : ℕ} (c : ℝ) (x : Fin N → ℝ) (i j : Fin N) : ℝ :=
  π / 2 * zsg i j - arctan ((x i - x j) / c)

lemma zTm_neg {N : ℕ} (c : ℝ) (x : Fin N → ℝ) (i j : Fin N) :
    zTm c x j i = - zTm c x i j := by
  unfold zTm
  rw [zsg_neg, show (x j - x i) / c = -((x i - x j) / c) by ring, arctan_neg]
  ring

lemma zTm_self {N : ℕ} (c : ℝ) (x : Fin N → ℝ) (i : Fin N) : zTm c x i i = 0 := by
  unfold zTm
  rw [zsg_self]
  simp

lemma zTm_lt {N : ℕ} (c : ℝ) (x : Fin N → ℝ) {i j : Fin N} (h : i < j) :
    zTm c x i j = π / 2 - arctan ((x i - x j) / c) := by
  unfold zTm
  rw [show zsg i j = 1 by simp [zsg, h]]
  ring

lemma zTm_nonneg_of_lt {N : ℕ} (c : ℝ) (x : Fin N → ℝ) {i j : Fin N} (h : i < j) :
    0 ≤ zTm c x i j := by
  rw [zTm_lt c x h]
  linarith [arctan_lt_pi_div_two ((x i - x j) / c)]

/-- Symmetrization: `∑_{i,j} (f_i − f_j) T_ij = 2 ∑_{i,j} f_i T_ij`. -/
lemma sym_sum {N : ℕ} (c : ℝ) (x : Fin N → ℝ) (f : Fin N → ℝ) :
    ∑ i, ∑ j, (f i - f j) * zTm c x i j = 2 * ∑ i, ∑ j, f i * zTm c x i j := by
  have h2 : ∑ i, ∑ j, f j * zTm c x i j = - ∑ i, ∑ j, f i * zTm c x i j := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [zTm_neg]
    ring
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [h2]
  ring

/-- Weighted root identity: `L ∑_k f_k d_k = 2 ∑_{k,j} f_k T_kj`, where `d = x − yv`, `L·yv_i = 2π n_i`
and `x` satisfies the printed equation `L x_i + 2∑_j arctan((x_i−x_j)/c) = 2π(n_i + ρ_i)`. -/
lemma L_weighted {N : ℕ} {L c : ℝ} {x yv n : Fin N → ℝ}
    (hE : ∀ i, L * x i + 2 * ∑ j, arctan ((x i - x j) / c) = 2 * π * (n i + zrho N i))
    (hyv : ∀ i, L * yv i = 2 * π * n i) (f : Fin N → ℝ) :
    L * ∑ k, f k * (x k - yv k) = 2 * ∑ k, ∑ j, f k * zTm c x k j := by
  have hLd : ∀ i, L * (x i - yv i) = 2 * ∑ j, zTm c x i j := by
    intro i
    have hs : ∑ j, zTm c x i j = π / 2 * (2 * zrho N i) - ∑ j, arctan ((x i - x j) / c) := by
      unfold zTm
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_zsg]
    rw [hs, mul_sub]
    linear_combination hE i - hyv i
  calc L * ∑ k, f k * (x k - yv k)
      = ∑ k, f k * (L * (x k - yv k)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ = ∑ k, f k * (2 * ∑ j, zTm c x k j) := Finset.sum_congr rfl (fun k _ => by rw [hLd k])
    _ = 2 * ∑ k, ∑ j, f k * zTm c x k j := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Scalar pair estimate: `(X − Y)·(π/2 − arctan(X/c)) ≤ c` when `Y ≥ 0`. -/
lemma pair_bound {c : ℝ} (hc : 0 < c) {X Y : ℝ} (hY : 0 ≤ Y) (D : ℝ)
    (hD : D = π / 2 - arctan (X / c)) : (X - Y) * D ≤ c := by
  have hD0 : 0 ≤ D := by
    rw [hD]; linarith [arctan_lt_pi_div_two (X / c)]
  have hXD : X * D ≤ c := by
    rcases le_or_gt X 0 with hX | hX
    · nlinarith
    · have hu : 0 < X / c := div_pos hX hc
      have hinv : arctan (X / c)⁻¹ = π / 2 - arctan (X / c) := arctan_inv_of_pos hu
      have hle : arctan (X / c)⁻¹ ≤ (X / c)⁻¹ := arctan_le_self (inv_nonneg.mpr hu.le)
      have hD' : D ≤ (X / c)⁻¹ := by rw [hD, ← hinv]; exact hle
      calc X * D ≤ X * (X / c)⁻¹ := mul_le_mul_of_nonneg_left hD' hX.le
        _ = c := by field_simp
  nlinarith [mul_nonneg hY hD0]

lemma pair_lt {N : ℕ} {c : ℝ} (hc : 0 < c) (x yv : Fin N → ℝ)
    (hY : ∀ i j, i < j → 0 ≤ yv i - yv j) {i j : Fin N} (h : i < j) :
    (x i - yv i - (x j - yv j)) * zTm c x i j ≤ c := by
  rw [zTm_lt c x h]
  have e : x i - yv i - (x j - yv j) = (x i - x j) - (yv i - yv j) := by ring
  rw [e]
  exact pair_bound hc (hY i j h) _ rfl

lemma pair_all {N : ℕ} {c : ℝ} (hc : 0 < c) (x yv : Fin N → ℝ)
    (hY : ∀ i j, i < j → 0 ≤ yv i - yv j) (i j : Fin N) :
    (x i - yv i - (x j - yv j)) * zTm c x i j ≤ c := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact pair_lt hc x yv hY h
  · rw [zTm_self]; simp [hc.le]
  · rw [show (x i - yv i - (x j - yv j)) * zTm c x i j
        = (x j - yv j - (x i - yv i)) * zTm c x j i by rw [zTm_neg]; ring]
    exact pair_lt hc x yv hY h

/-- `L ∑ d_k² ≤ N² c`, from the symmetrized identity and the pair bound. -/
lemma quad_bound {N : ℕ} {L c : ℝ} (hc : 0 < c) {x yv n : Fin N → ℝ}
    (hE : ∀ i, L * x i + 2 * ∑ j, arctan ((x i - x j) / c) = 2 * π * (n i + zrho N i))
    (hyv : ∀ i, L * yv i = 2 * π * n i)
    (hY : ∀ i j, i < j → 0 ≤ yv i - yv j) :
    L * ∑ k, (x k - yv k) * (x k - yv k) ≤ (N : ℝ) * ((N : ℝ) * c) := by
  have h1 := L_weighted hE hyv (fun k => x k - yv k)
  have h2 := sym_sum c x (fun k => x k - yv k)
  beta_reduce at h1 h2
  rw [h1, ← h2]
  calc ∑ i, ∑ j, (x i - yv i - (x j - yv j)) * zTm c x i j
      ≤ ∑ i : Fin N, ∑ j : Fin N, c :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => pair_all hc x yv hY i j))
    _ = (N : ℝ) * ((N : ℝ) * c) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Coordinatewise bound `|q_i − y_i| ≤ √(N²c/L)`. -/
lemma sq_bound {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {x yv n : Fin N → ℝ}
    (hE : ∀ i, L * x i + 2 * ∑ j, arctan ((x i - x j) / c) = 2 * π * (n i + zrho N i))
    (hyv : ∀ i, L * yv i = 2 * π * n i)
    (hY : ∀ i j, i < j → 0 ≤ yv i - yv j) (i : Fin N) :
    |x i - yv i| ≤ Real.sqrt ((N : ℝ) * ((N : ℝ) * c) / L) := by
  have hq := quad_bound hc hE hyv hY
  have hs : (x i - yv i) * (x i - yv i) ≤ ∑ k, (x k - yv k) * (x k - yv k) :=
    Finset.single_le_sum (f := fun k => (x k - yv k) * (x k - yv k))
      (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
  have hsq : (x i - yv i) ^ 2 ≤ (N : ℝ) * ((N : ℝ) * c) / L := by
    rw [le_div_iff₀ hL]
    nlinarith [mul_le_mul_of_nonneg_right hs hL.le]
  exact Real.abs_le_sqrt hsq

/-- Nonnegativity of the `ρ`-weighted antisymmetric terms. -/
lemma rho_term_nonneg {N : ℕ} (c : ℝ) (x : Fin N → ℝ) (k j : Fin N) :
    0 ≤ (zrho N k - zrho N j) * zTm c x k j := by
  rcases lt_trichotomy k j with h | rfl | h
  · have hkj : (k.val : ℝ) ≤ j.val := by exact_mod_cast (Fin.lt_def.mp h).le
    have hr : 0 ≤ zrho N k - zrho N j := by unfold zrho; linarith
    exact mul_nonneg hr (zTm_nonneg_of_lt c x h)
  · simp [zTm_self]
  · have hkj : (j.val : ℝ) ≤ k.val := by exact_mod_cast (Fin.lt_def.mp h).le
    have hr : zrho N k - zrho N j ≤ 0 := by unfold zrho; linarith
    have hT : zTm c x k j ≤ 0 := by
      rw [zTm_neg]; linarith [zTm_nonneg_of_lt c x h]
    nlinarith

/-- `L ∑_k ρ_k d_k = ∑_{k,j} (ρ_k − ρ_j) T_kj`. -/
lemma rho_identity {N : ℕ} {L c : ℝ} {x yv n : Fin N → ℝ}
    (hE : ∀ i, L * x i + 2 * ∑ j, arctan ((x i - x j) / c) = 2 * π * (n i + zrho N i))
    (hyv : ∀ i, L * yv i = 2 * π * n i) :
    L * ∑ k, zrho N k * (x k - yv k)
      = ∑ k, ∑ j, (zrho N k - zrho N j) * zTm c x k j := by
  have h1 := L_weighted hE hyv (fun k => zrho N k)
  have h2 := sym_sum c x (fun k => zrho N k)
  beta_reduce at h1 h2
  rw [h1, h2]

/-- **Part (2) estimate.** For `i < j`: `T_ij ≤ L·(∑_k |ρ_k|)·√(N²c/L)`. -/
lemma Tm_le_bound {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {x yv n : Fin N → ℝ}
    (hE : ∀ i, L * x i + 2 * ∑ j, arctan ((x i - x j) / c) = 2 * π * (n i + zrho N i))
    (hyv : ∀ i, L * yv i = 2 * π * n i)
    (hY : ∀ i j, i < j → 0 ≤ yv i - yv j) {i j : Fin N} (hij : i < j) :
    zTm c x i j ≤ L * ((∑ k, |zrho N k|) * Real.sqrt ((N : ℝ) * ((N : ℝ) * c) / L)) := by
  have hρ : 1 ≤ zrho N i - zrho N j := by
    unfold zrho
    have h' : i.val + 1 ≤ j.val := Fin.lt_def.mp hij
    have : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h'
    linarith
  have hT := zTm_nonneg_of_lt c x hij
  have h1 : zTm c x i j ≤ (zrho N i - zrho N j) * zTm c x i j := by nlinarith
  have h2 : (zrho N i - zrho N j) * zTm c x i j
      ≤ ∑ k, ∑ j', (zrho N k - zrho N j') * zTm c x k j' :=
    le_trans
      (Finset.single_le_sum (f := fun j' => (zrho N i - zrho N j') * zTm c x i j')
        (fun j' _ => rho_term_nonneg c x i j') (Finset.mem_univ j))
      (Finset.single_le_sum (f := fun k => ∑ j', (zrho N k - zrho N j') * zTm c x k j')
        (fun k _ => Finset.sum_nonneg (fun j' _ => rho_term_nonneg c x k j'))
        (Finset.mem_univ i))
  have hsum : ∑ k, zrho N k * (x k - yv k)
      ≤ (∑ k, |zrho N k|) * Real.sqrt ((N : ℝ) * ((N : ℝ) * c) / L) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    have hd := sq_bound hL hc hE hyv hY k
    calc zrho N k * (x k - yv k) ≤ |zrho N k * (x k - yv k)| := le_abs_self _
      _ = |zrho N k| * |x k - yv k| := abs_mul _ _
      _ ≤ |zrho N k| * Real.sqrt ((N : ℝ) * ((N : ℝ) * c) / L) :=
          mul_le_mul_of_nonneg_left hd (abs_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left hsum hL.le
  rw [rho_identity hE hyv] at hmain
  linarith

/-- **Abstract zero-coupling limit.** Any family `x c` of solutions of the printed equation for all `c > 0`
satisfies (1) and (2). Real labels `n` with `n_j ≤ n_i` for `i < j`. -/
theorem zero_limit_abstract {N : ℕ} {L : ℝ} (hL : 0 < L) {n : Fin N → ℝ}
    (hn : ∀ i j : Fin N, i < j → n j ≤ n i) (x : ℝ → Fin N → ℝ)
    (hE : ∀ c, 0 < c → ∀ i, L * x c i + 2 * ∑ j, arctan ((x c i - x c j) / c)
      = 2 * π * (n i + zrho N i)) :
    Tendsto x (𝓝[>] 0) (𝓝 (fun i => 2 * π / L * n i)) ∧
    ∀ i j : Fin N, i < j →
      Tendsto (fun c => (x c i - x c j) / c) (𝓝[>] 0) atTop := by
  set yv : Fin N → ℝ := fun i => 2 * π / L * n i with hyv_def
  have hyv : ∀ i, L * yv i = 2 * π * n i := by
    intro i
    simp only [hyv_def]
    field_simp
  have hY : ∀ i j, i < j → 0 ≤ yv i - yv j := by
    intro i j h
    have hcoef : 0 ≤ 2 * π / L := by positivity
    have hnij : 0 ≤ n i - n j := sub_nonneg.mpr (hn i j h)
    simp only [hyv_def]
    rw [← mul_sub]
    exact mul_nonneg hcoef hnij
  refine ⟨?_, ?_⟩
  · -- (1) `q(n,c) → (2π/L) n`
    rw [tendsto_pi_nhds]
    intro i
    have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), |x c i - yv i| ≤
        Real.sqrt ((N : ℝ) * ((N : ℝ) * c) / L) := by
      filter_upwards [self_mem_nhdsWithin] with c hc
      exact sq_bound hL (Set.mem_Ioi.mp hc) (hE c (Set.mem_Ioi.mp hc)) hyv hY i
    have hsq : Tendsto (fun c : ℝ => Real.sqrt ((N : ℝ) * ((N : ℝ) * c) / L)) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous (fun c : ℝ => Real.sqrt ((N : ℝ) * ((N : ℝ) * c) / L)) := by
        fun_prop
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    have hd : Tendsto (fun c => x c i - yv i) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hsq
      filter_upwards [hev] with c hc
      rw [Real.norm_eq_abs]
      exact hc
    exact tendsto_sub_nhds_zero_iff.mp hd
  · -- (2) `(q_i − q_j)/c → +∞` for `i < j`, including `n_i = n_j`
    intro i j hij
    have hB : Tendsto (fun c : ℝ => L * ((∑ k, |zrho N k|) *
        Real.sqrt ((N : ℝ) * ((N : ℝ) * c) / L))) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous (fun c : ℝ => L * ((∑ k, |zrho N k|) *
          Real.sqrt ((N : ℝ) * ((N : ℝ) * c) / L))) := by
        fun_prop
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    have hlow : Tendsto (fun c => arctan ((x c i - x c j) / c)) (𝓝[>] 0) (𝓝 (π / 2)) := by
      have hg : Tendsto (fun c : ℝ => π / 2 - L * ((∑ k, |zrho N k|) *
          Real.sqrt ((N : ℝ) * ((N : ℝ) * c) / L))) (𝓝[>] 0) (𝓝 (π / 2 - 0)) :=
        tendsto_const_nhds.sub hB
      rw [sub_zero] at hg
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with c hc
        have hcpos : 0 < c := Set.mem_Ioi.mp hc
        have hb := Tm_le_bound hL hcpos (hE c hcpos) hyv hY hij
        rw [zTm_lt c (x c) hij] at hb
        linarith
      · filter_upwards with c
        exact (arctan_lt_pi_div_two _).le
    have hlow' : Tendsto (fun c => arctan ((x c i - x c j) / c)) (𝓝[>] 0)
        (𝓝[<] (π / 2)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlow, Eventually.of_forall
        (fun c => Set.mem_Iio.mpr (arctan_lt_pi_div_two _))⟩
    exact (Real.tendsto_tan_pi_div_two.comp hlow').congr (fun c => Real.tan_arctan _)

/-- **R-CD2257D0 for the accepted root curve.** For `L > 0` and an antitone label `n`, with
`q(n,c) := BetheSmooth.sourceRoots L n c` (the accepted R-4C8D7C9E root vector):
(1) `q(n,c) → q(n,0) = (2π/L) n` as `c ↓ 0`;
(2) `(q_i(n,c) − q_j(n,c))/c → +∞` for `i < j`, including `n_i = n_j`. -/
theorem zero_limit_root {N : ℕ} {L : ℝ} (hL : 0 < L) {n : Fin N → ℤ} (hn : Antitone n) :
    Tendsto (fun c => QuantumNLS.BetheSmooth.sourceRoots L n c) (𝓝[>] 0)
      (𝓝 (fun i => 2 * π / L * (n i : ℝ))) ∧
    ∀ i j : Fin N, i < j →
      Tendsto (fun c => (QuantumNLS.BetheSmooth.sourceRoots L n c i
        - QuantumNLS.BetheSmooth.sourceRoots L n c j) / c) (𝓝[>] 0) atTop := by
  have hE : ∀ c, 0 < c → ∀ i,
      L * QuantumNLS.BetheSmooth.sourceRoots L n c i
        + 2 * ∑ j, arctan ((QuantumNLS.BetheSmooth.sourceRoots L n c i
          - QuantumNLS.BetheSmooth.sourceRoots L n c j) / c)
        = 2 * π * ((n i : ℝ) + zrho N i) := by
    intro c hc i
    have h := congrFun ((QuantumNLS.BetheConvexity.source_roots_spec hL hn).2 c hc).1 i
    have hs : QuantumNLS.BetheSmooth.sourceNumbers n i = (n i : ℝ) + zrho N i := by
      unfold QuantumNLS.BetheSmooth.sourceNumbers zrho
      ring
    unfold QuantumNLS.BetheAdmission.logMap at h
    rw [hs] at h
    exact h
  have hn' : ∀ i j : Fin N, i < j → (n j : ℝ) ≤ n i := fun i j h =>
    Int.cast_le.mpr (hn h.le)
  exact zero_limit_abstract hL hn' (fun c => QuantumNLS.BetheSmooth.sourceRoots L n c) hE

/-- **Identification.** For `c > 0`, `q(n,c) = BetheSmooth.sourceRoots L n c` is the unique real solution
of the printed equation `L q_i + 2∑_{j≠i} arctan((q_i−q_j)/c) = 2π I_i` (accepted uniqueness clause). -/
theorem root_identification {N : ℕ} {L : ℝ} (hL : 0 < L) {n : Fin N → ℤ} (hn : Antitone n)
    {c : ℝ} (hc : 0 < c) :
    ∀ q : Fin N → ℝ,
      QuantumNLS.BetheAdmission.logMap L c q
          = (fun i => 2 * π * QuantumNLS.BetheSmooth.sourceNumbers n i) →
        q = QuantumNLS.BetheSmooth.sourceRoots L n c :=
  fun q hq => ((QuantumNLS.BetheConvexity.source_roots_spec hL hn).2 c hc).2.2.2 q hq

end QuantumNLS.BetheZeroLimit

#print axioms QuantumNLS.BetheZeroLimit.zero_limit_abstract
#print axioms QuantumNLS.BetheZeroLimit.zero_limit_root
#print axioms QuantumNLS.BetheZeroLimit.root_identification
