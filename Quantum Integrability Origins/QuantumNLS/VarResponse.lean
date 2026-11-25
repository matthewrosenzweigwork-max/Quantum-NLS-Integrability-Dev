import Mathlib
import QuantumNLS.FiniteResponse

/-!
# CC:F04:variable-coupling (R-C88B5D59), step 5: the parameter-response bound (CC:F04:parameter-response-bound)

Source: `F04.tex` line 412, proof of Proposition `CC:F04:variable-coupling`: for a fixed ordered array `q`, `B_{N,ξ}` the response matrix with contact `ξ/N`, edge weights `w^{(ξ)}_{ij} = (2ξ/N)/((ξ/N)² + (q_i−q_j)²)`; `r_N = κ_N/κ`, `ε_N = max(r_N, r_N^{-1}) − 1`:

  `min(r_N, r_N^{-1}) ≤ w^{(κ_N)}_{ij}/w^{(κ)}_{ij} ≤ max(r_N, r_N^{-1})`,
  `B̃ ≥ (1 − ε_N) B` as quadratic forms, `|vᵀ(B̃ − B)w| ≤ ε_N (vᵀBv)^{1/2} (wᵀBw)^{1/2}` (Cauchy–Schwarz over unordered edges);
  for `f = B^{-1}q`, `f̃ = B̃^{-1}q`, `d = f̃ − f`: `B̃ d = (B − B̃) f`, `(1−ε_N) dᵀBd ≤ dᵀB̃d ≤ ε_N (dᵀBd)^{1/2}(fᵀBf)^{1/2}`, `B ≥ L Id`, `fᵀBf = qᵀB^{-1}q ≤ ‖q‖²/L`, hence
  `‖f̃ − f‖/√N ≤ ε_N/(L(1−ε_N)) ‖q‖/√N`  (CC:F04:parameter-response-bound).

Here `c = ξ/N` and `c' = κ_N/N` are arbitrary positive contacts, `m = max(c'/c, c/c')` (`= 1 + ε`), and the response vectors are given by their defining equations `Bop L c q f = q`, `Bop L c' q f' = q` (so no inverse is needed):
* `wt_upper`, `wt_lower`: `(2 − m) w ≤ w' ≤ m w`;
* `Pf_sq_diff`: `(P'(u,v) − P(u,v))² ≤ (m−1)² P(u,u) P(v,v)` (Cauchy–Schwarz over pairs);
* `param_response`: `(2 − m)² L² Σ (f'_i − f_i)² ≤ (m−1)² Σ q_i²` for `m < 2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open Finset
open scoped BigOperators

namespace QuantumNLS.VarResponse

open QuantumNLS.FiniteResponse (Bop wt dot dotB_bil wt_nonneg Bop_add)

variable {N : ℕ}

/-- The edge form `P_c(u,v) = ½ Σ_{i,j} w_ij (u_i−u_j)(v_i−v_j)`. -/
def Pf (c : ℝ) (q u v : Fin N → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, wt c (q i) (q j) * ((u i - u j) * (v i - v j))

theorem dot_Bop (L c : ℝ) (q u v : Fin N → ℝ) :
    dot u (Bop L c q v) = L * ∑ i, u i * v i + Pf c q u v := dotB_bil L c q u v

theorem Pf_nonneg {c : ℝ} (hc : 0 ≤ c) (q v : Fin N → ℝ) : 0 ≤ Pf c q v v := by
  unfold Pf
  refine mul_nonneg (by norm_num) (sum_nonneg fun i _ => sum_nonneg fun j _ => ?_)
  have := wt_nonneg hc (q i) (q j)
  nlinarith [sq_nonneg (v i - v j)]

theorem wt_le {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (a b : ℝ) :
    wt c' a b ≤ max (c' / c) (c / c') * wt c a b := by
  unfold wt
  set d := (a - b) ^ 2 with hd
  have hd0 : 0 ≤ d := sq_nonneg _
  have h1 : 0 < c ^ 2 + d := by positivity
  have h2 : 0 < c' ^ 2 + d := by positivity
  rcases le_total c c' with h | h
  · have hm : max (c' / c) (c / c') = c' / c := max_eq_left (by
      rw [div_le_div_iff₀ hc' hc]; nlinarith)
    rw [hm]
    have e : c' / c * (2 * c / (c ^ 2 + d)) = 2 * c' / (c ^ 2 + d) := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) h1 (by nlinarith)
  · have hm : max (c' / c) (c / c') = c / c' := max_eq_right (by
      rw [div_le_div_iff₀ hc hc']; nlinarith)
    rw [hm]
    have e : c / c' * (2 * c / (c ^ 2 + d)) = 2 * c ^ 2 / (c' * (c ^ 2 + d)) := by field_simp
    rw [e, div_le_div_iff₀ h2 (by positivity)]
    nlinarith [mul_nonneg hd0 (by nlinarith : 0 ≤ c ^ 2 - c' ^ 2), hc, hc']

theorem one_le_m {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') : 1 ≤ max (c' / c) (c / c') := by
  rcases le_total c c' with h | h
  · exact le_max_of_le_left ((one_le_div hc).2 h)
  · exact le_max_of_le_right ((one_le_div hc').2 h)

theorem wt_upper {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (a b : ℝ) :
    wt c' a b ≤ max (c' / c) (c / c') * wt c a b := wt_le hc hc' a b

theorem wt_lower {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (a b : ℝ) :
    (2 - max (c' / c) (c / c')) * wt c a b ≤ wt c' a b := by
  set m := max (c' / c) (c / c') with hm
  have h2 : wt c a b ≤ m * wt c' a b := by
    have := wt_le hc' hc a b
    rwa [max_comm] at this
  have hm1 : 1 ≤ m := one_le_m hc hc'
  have hw : 0 ≤ wt c a b := wt_nonneg hc.le a b
  have hw' : 0 ≤ wt c' a b := wt_nonneg hc'.le a b
  by_contra hcon
  push Not at hcon
  -- `m w' ≥ w` and `w' < (2 - m) w`
  have : m * wt c' a b < m * ((2 - m) * wt c a b) :=
    mul_lt_mul_of_pos_left hcon (by linarith)
  nlinarith [sq_nonneg (m - 1), mul_nonneg hw (sq_nonneg (m - 1))]

/-- Cauchy–Schwarz over pairs. -/
theorem cs_pairs {c : ℝ} (hc : 0 ≤ c) (q u v : Fin N → ℝ) :
    (∑ i, ∑ j, wt c (q i) (q j) * (|u i - u j| * |v i - v j|)) ^ 2 ≤
      (∑ i, ∑ j, wt c (q i) (q j) * (u i - u j) ^ 2) *
        (∑ i, ∑ j, wt c (q i) (q j) * (v i - v j) ^ 2) := by
  have hw : ∀ i j, 0 ≤ wt c (q i) (q j) := fun i j => wt_nonneg hc _ _
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ ×ˢ Finset.univ : Finset (Fin N × Fin N))
    (fun p => Real.sqrt (wt c (q p.1) (q p.2)) * |u p.1 - u p.2|)
    (fun p => Real.sqrt (wt c (q p.1) (q p.2)) * |v p.1 - v p.2|)
  simp only [Finset.sum_product] at h
  have e1 : ∀ i j, Real.sqrt (wt c (q i) (q j)) * |u i - u j| *
      (Real.sqrt (wt c (q i) (q j)) * |v i - v j|) =
        wt c (q i) (q j) * (|u i - u j| * |v i - v j|) := by
    intro i j
    have := Real.mul_self_sqrt (hw i j)
    calc Real.sqrt (wt c (q i) (q j)) * |u i - u j| *
          (Real.sqrt (wt c (q i) (q j)) * |v i - v j|) =
        (Real.sqrt (wt c (q i) (q j)) * Real.sqrt (wt c (q i) (q j))) *
          (|u i - u j| * |v i - v j|) := by ring
      _ = _ := by rw [this]
  have e2 : ∀ i j, (Real.sqrt (wt c (q i) (q j)) * |u i - u j|) ^ 2 =
      wt c (q i) (q j) * (u i - u j) ^ 2 := by
    intro i j
    rw [mul_pow, Real.sq_sqrt (hw i j), sq_abs]
  have e3 : ∀ i j, (Real.sqrt (wt c (q i) (q j)) * |v i - v j|) ^ 2 =
      wt c (q i) (q j) * (v i - v j) ^ 2 := by
    intro i j
    rw [mul_pow, Real.sq_sqrt (hw i j), sq_abs]
  simpa only [e1, e2, e3] using h

theorem Pf_sq_diff {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (q u v : Fin N → ℝ) :
    (Pf c' q u v - Pf c q u v) ^ 2 ≤
      (max (c' / c) (c / c') - 1) ^ 2 * (Pf c q u u * Pf c q v v) := by
  set m := max (c' / c) (c / c') with hm
  have hm1 : 1 ≤ m := one_le_m hc hc'
  -- termwise bound
  have hterm : ∀ i j, |(wt c' (q i) (q j) - wt c (q i) (q j)) * ((u i - u j) * (v i - v j))| ≤
      (m - 1) * (wt c (q i) (q j) * (|u i - u j| * |v i - v j|)) := by
    intro i j
    have h1 := wt_upper hc hc' (q i) (q j)
    have h2 := wt_lower hc hc' (q i) (q j)
    have hw := wt_nonneg hc.le (q i) (q j)
    have hab : |wt c' (q i) (q j) - wt c (q i) (q j)| ≤ (m - 1) * wt c (q i) (q j) := by
      rw [abs_le]; constructor <;> nlinarith
    rw [abs_mul, abs_mul]
    calc |wt c' (q i) (q j) - wt c (q i) (q j)| * (|u i - u j| * |v i - v j|)
        ≤ ((m - 1) * wt c (q i) (q j)) * (|u i - u j| * |v i - v j|) :=
          mul_le_mul_of_nonneg_right hab (by positivity)
      _ = _ := by ring
  have hdiff : Pf c' q u v - Pf c q u v = (1 / 2) * ∑ i, ∑ j,
      (wt c' (q i) (q j) - wt c (q i) (q j)) * ((u i - u j) * (v i - v j)) := by
    unfold Pf
    rw [← mul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  have habs : |Pf c' q u v - Pf c q u v| ≤
      (1 / 2) * ((m - 1) * ∑ i, ∑ j, wt c (q i) (q j) * (|u i - u j| * |v i - v j|)) := by
    rw [hdiff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine sum_le_sum fun i _ => ?_
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    exact sum_le_sum fun j _ => hterm i j
  have hcs := cs_pairs hc.le q u v
  have hPu : Pf c q u u = (1 / 2) * ∑ i, ∑ j, wt c (q i) (q j) * (u i - u j) ^ 2 := by
    unfold Pf; simp_rw [← sq]
  have hPv : Pf c q v v = (1 / 2) * ∑ i, ∑ j, wt c (q i) (q j) * (v i - v j) ^ 2 := by
    unfold Pf; simp_rw [← sq]
  set S := ∑ i, ∑ j, wt c (q i) (q j) * (|u i - u j| * |v i - v j|) with hS
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => sum_nonneg fun j _ =>
    mul_nonneg (wt_nonneg hc.le _ _) (by positivity)
  have hP0 := Pf_nonneg hc.le q u
  have hQ0 := Pf_nonneg hc.le q v
  have hsq : ((1 / 2) * ((m - 1) * S)) ^ 2 ≤ (m - 1) ^ 2 * (Pf c q u u * Pf c q v v) := by
    rw [hPu, hPv]
    have : ((1 / 2) * ((m - 1) * S)) ^ 2 = (m - 1) ^ 2 * ((1 / 4) * S ^ 2) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith [hcs]
  have h0 : 0 ≤ (1 / 2) * ((m - 1) * S) := by
    have : 0 ≤ m - 1 := by linarith
    positivity
  calc (Pf c' q u v - Pf c q u v) ^ 2 = |Pf c' q u v - Pf c q u v| ^ 2 := (sq_abs _).symm
    _ ≤ ((1 / 2) * ((m - 1) * S)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ _ := hsq

theorem Pf_lower {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (q v : Fin N → ℝ) :
    (2 - max (c' / c) (c / c')) * Pf c q v v ≤ Pf c' q v v := by
  unfold Pf
  have h : (2 - max (c' / c) (c / c')) * ∑ i, ∑ j, wt c (q i) (q j) * ((v i - v j) * (v i - v j)) ≤
      ∑ i, ∑ j, wt c' (q i) (q j) * ((v i - v j) * (v i - v j)) := by
    rw [Finset.mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_le_sum fun j _ => ?_
    have := wt_lower hc hc' (q i) (q j)
    nlinarith [sq_nonneg (v i - v j)]
  linarith

theorem Bop_sub_aux (L c : ℝ) (q f f' : Fin N → ℝ) :
    Bop L c q (f' - f) = Bop L c q f' - Bop L c q f := by
  have := Bop_add L c q (f' - f) f
  rw [sub_add_cancel] at this
  rw [this]; abel

/-- **`CC:F04:parameter-response-bound`**: `(2 − m)² L² Σ (f'_i − f_i)² ≤ (m − 1)² Σ q_i²`. -/
theorem param_response {L c c' : ℝ} (hL : 0 < L) (hc : 0 < c) (hc' : 0 < c') (q f f' : Fin N → ℝ)
    (hf : Bop L c q f = q) (hf' : Bop L c' q f' = q)
    (hm2 : max (c' / c) (c / c') < 2) :
    (2 - max (c' / c) (c / c')) ^ 2 * L ^ 2 * ∑ i, (f' i - f i) ^ 2 ≤
      (max (c' / c) (c / c') - 1) ^ 2 * ∑ i, q i ^ 2 := by
  set m := max (c' / c) (c / c') with hm
  have hm1 : 1 ≤ m := one_le_m hc hc'
  set d : Fin N → ℝ := f' - f with hd
  set e : ℝ := 2 - m with he
  have he0 : 0 < e := by rw [he]; linarith
  have he1 : e ≤ 1 := by rw [he]; linarith
  set Dd : ℝ := ∑ i, d i ^ 2 with hDd
  have hDd0 : 0 ≤ Dd := sum_nonneg fun i _ => sq_nonneg _
  set Q : ℝ := ∑ i, q i ^ 2 with hQ
  have hQ0 : 0 ≤ Q := sum_nonneg fun i _ => sq_nonneg _
  have sqsum : ∀ v : Fin N → ℝ, ∑ i, v i * v i = ∑ i, v i ^ 2 := fun v =>
    sum_congr rfl fun i _ => (sq (v i)).symm
  -- the identity `dᵀ B' d = P(d,f) - P'(d,f)`
  have hBd : Bop L c' q d = q - Bop L c' q f := by
    rw [hd, Bop_sub_aux, hf']
  have hkey : dot d (Bop L c' q d) = Pf c q d f - Pf c' q d f := by
    rw [hBd]
    have h1 : dot d (q - Bop L c' q f) = dot d q - dot d (Bop L c' q f) := by
      unfold dot
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
    have h2 : dot d q = dot d (Bop L c q f) := by rw [hf]
    rw [h1, h2, dot_Bop, dot_Bop]
    ring
  have hlow : dot d (Bop L c' q d) = L * Dd + Pf c' q d d := by
    rw [dot_Bop, sqsum]
  have hP1 := Pf_lower hc hc' q d
  have hPnn := Pf_nonneg hc.le q d
  -- `X = dᵀBd`
  set X : ℝ := L * Dd + Pf c q d d with hX
  have hX0 : 0 ≤ X := by rw [hX]; have := mul_nonneg hL.le hDd0; linarith
  have hLD : L * Dd ≤ X := by rw [hX]; linarith
  have hPX : Pf c q d d ≤ X := by rw [hX]; have := mul_nonneg hL.le hDd0; linarith
  have hY : dot f (Bop L c q f) = L * ∑ i, f i ^ 2 + Pf c q f f := by rw [dot_Bop, sqsum]
  set Y : ℝ := dot f (Bop L c q f) with hYdef
  have hPff := Pf_nonneg hc.le q f
  have hYf : Pf c q f f ≤ Y := by
    rw [hY]; have := mul_nonneg hL.le (Finset.sum_nonneg (fun i _ => sq_nonneg (f i)) : 0 ≤ ∑ i, f i ^ 2); linarith
  have hY0 : 0 ≤ Y := le_trans hPff hYf
  -- `e X ≤ |P(d,f) - P'(d,f)|`
  have heX : e * X ≤ Pf c q d f - Pf c' q d f := by
    rw [← hkey, hlow]
    have : e * (L * Dd) ≤ L * Dd := by
      have := mul_nonneg hL.le hDd0
      nlinarith
    rw [hX]
    nlinarith [hP1, this]
  have hsq := Pf_sq_diff hc hc' q d f
  have hR : (Pf c' q d f - Pf c q d f) ^ 2 ≤ (m - 1) ^ 2 * (X * Y) := by
    refine hsq.trans ?_
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact mul_le_mul hPX hYf hPff hX0
  have heX0 : 0 ≤ e * X := mul_nonneg he0.le hX0
  have hRX : (e * X) ^ 2 ≤ (m - 1) ^ 2 * (X * Y) := by
    have h1 : (e * X) ^ 2 ≤ (Pf c q d f - Pf c' q d f) ^ 2 := pow_le_pow_left₀ heX0 heX 2
    calc (e * X) ^ 2 ≤ (Pf c q d f - Pf c' q d f) ^ 2 := h1
      _ = (Pf c' q d f - Pf c q d f) ^ 2 := by ring
      _ ≤ (m - 1) ^ 2 * (X * Y) := hR
  -- `Y ≤ Q / L`
  have hYQ : L * Y ≤ Q := by
    have hLf : L * ∑ i, f i ^ 2 ≤ Y := by
      rw [hY]; linarith
    have hYq : Y = ∑ i, f i * q i := by
      have := dot_Bop L c q f f
      simp only [hYdef, dot, hf]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N)) f q
    rw [← hYq] at hcs
    -- `Y² ≤ (Σ f²) Q`, `L Σ f² ≤ Y`
    have h1 : L * Y ^ 2 ≤ Y * Q := by
      calc L * Y ^ 2 ≤ L * ((∑ i, f i ^ 2) * Q) := mul_le_mul_of_nonneg_left hcs hL.le
        _ = (L * ∑ i, f i ^ 2) * Q := by ring
        _ ≤ Y * Q := mul_le_mul_of_nonneg_right hLf hQ0
    rcases hY0.eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using hQ0
    · nlinarith
  -- conclude
  have hfinal : e ^ 2 * (L * Dd) ≤ (m - 1) ^ 2 * Y := by
    rcases hX0.eq_or_lt with h0 | hpos
    · have : L * Dd ≤ 0 := by rw [← h0] at hLD; exact hLD
      have h2 : 0 ≤ (m - 1) ^ 2 * Y := mul_nonneg (sq_nonneg _) hY0
      nlinarith [mul_nonneg hL.le hDd0, sq_nonneg e]
    · have h1 : e ^ 2 * X ≤ (m - 1) ^ 2 * Y := by
        have : X * (e ^ 2 * X) ≤ X * ((m - 1) ^ 2 * Y) := by nlinarith [hRX]
        exact le_of_mul_le_mul_left this hpos
      calc e ^ 2 * (L * Dd) ≤ e ^ 2 * X := mul_le_mul_of_nonneg_left hLD (sq_nonneg _)
        _ ≤ _ := h1
  -- multiply by `L`
  have : L * (e ^ 2 * (L * Dd)) ≤ L * ((m - 1) ^ 2 * Y) := mul_le_mul_of_nonneg_left hfinal hL.le
  have h3 : e ^ 2 * L ^ 2 * Dd ≤ (m - 1) ^ 2 * Q := by
    calc e ^ 2 * L ^ 2 * Dd = L * (e ^ 2 * (L * Dd)) := by ring
      _ ≤ L * ((m - 1) ^ 2 * Y) := this
      _ = (m - 1) ^ 2 * (L * Y) := by ring
      _ ≤ (m - 1) ^ 2 * Q := mul_le_mul_of_nonneg_left hYQ (sq_nonneg _)
  exact h3

end QuantumNLS.VarResponse

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.VarResponse.wt_lower
#print axioms QuantumNLS.VarResponse.Pf_sq_diff
#print axioms QuantumNLS.VarResponse.param_response
