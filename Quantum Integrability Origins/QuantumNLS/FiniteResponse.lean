import Mathlib

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (F): the finite problem

Source: the first part of the proof of `CC:F03:deterministic` (`F03.tex`): with `c_N = κ/N`,
`(B_N v)_i = L v_i + Σ_{j≠i} 2c_N/(c_N² + (q_i - q_j)²) (v_i - v_j)`,
`ℰ_N(v) = (1/N²) Σ_{i≠j} (v_i-v_j)²/(c_N² + (q_i-q_j)²)` (the double integral over `(0,1)²` of the step function `v` with the step quantile `Q_N`, whose same-cell numerator vanishes),
`𝒥_N(v) = (L/2)‖v‖² + (κ/2) ℰ_N(v) - ⟨Q_N, v⟩` with `‖v‖² = (1/N) Σ v_i²`, `⟨Q_N,v⟩ = (1/N) Σ q_i v_i`.

All statements are for vectors `v : Fin N → ℝ` (the values of the step function on the `N` cells); the identification of these sums with the integrals over `(0,1)` of the step functions is
in the later stages.  Here:
* `dotB_eq`: `Σ v_i (B v)_i = L Σ v_i² + ½ Σ_{i,j} w_ij (v_i-v_j)²` (symmetrization of the kernel `w_ij = 2c/(c²+(q_i-q_j)²)`);
* `Qf_eq`: `L ‖v‖² + κ ℰ_N(v) = (1/N) ⟨v, B_N v⟩`  (the printed `𝒥_N(v) = (1/2N) vᵀ B_N v - (1/N) qᵀ v`, `JN_eq`);
* `exists_unique_response`: `B_N v = q` has a unique solution `F_N = B_N⁻¹ q` (`B_N` is symmetric positive definite);
* `response_bounds`: `L² ‖F_N‖² ≤ ‖Q_N‖²` and `L‖F_N‖² + κ ℰ_N(F_N) = ⟨Q_N, F_N⟩` (`CC:F03:finite-bound`);
* `JN_sub_JN`: the quadratic completion `𝒥_N(v) - 𝒥_N(F_N) = (L/2)‖v - F_N‖² + (κ/2) ℰ_N(v - F_N)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Finset
open scoped BigOperators

noncomputable section

namespace QuantumNLS.FiniteResponse

variable {N : ℕ}

/-- The kernel `w(a,b) = 2c/(c² + (a-b)²)`. -/
def wt (c a b : ℝ) : ℝ := 2 * c / (c ^ 2 + (a - b) ^ 2)

theorem wt_symm (c a b : ℝ) : wt c a b = wt c b a := by
  unfold wt; rw [show (b - a) ^ 2 = (a - b) ^ 2 by ring]

theorem wt_nonneg {c : ℝ} (hc : 0 ≤ c) (a b : ℝ) : 0 ≤ wt c a b := by unfold wt; positivity

/-- `(B_N v)_i = L v_i + Σ_j w_ij (v_i - v_j)` (the term `j = i` vanishes: this is the printed `Σ_{j≠i}`). -/
def Bop (L c : ℝ) (q : Fin N → ℝ) (v : Fin N → ℝ) (i : Fin N) : ℝ :=
  L * v i + ∑ j, wt c (q i) (q j) * (v i - v j)

theorem Bop_eq_erase (L c : ℝ) (q v : Fin N → ℝ) (i : Fin N) :
    Bop L c q v i = L * v i + ∑ j ∈ univ.erase i, wt c (q i) (q j) * (v i - v j) := by
  unfold Bop
  rw [← Finset.add_sum_erase _ _ (mem_univ i)]
  simp

/-- `Σ_i x_i y_i`. -/
def dot (x y : Fin N → ℝ) : ℝ := ∑ i, x i * y i

theorem dot_comm (x y : Fin N → ℝ) : dot x y = dot y x := by
  unfold dot; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem Bop_add (L c : ℝ) (q u v : Fin N → ℝ) : Bop L c q (u + v) = Bop L c q u + Bop L c q v := by
  funext i
  simp only [Bop, Pi.add_apply]
  have : ∀ j, wt c (q i) (q j) * (u i + v i - (u j + v j)) =
      wt c (q i) (q j) * (u i - u j) + wt c (q i) (q j) * (v i - v j) := fun j => by ring
  simp_rw [this, sum_add_distrib]; ring

theorem Bop_smul (L c : ℝ) (q v : Fin N → ℝ) (a : ℝ) : Bop L c q (a • v) = a • Bop L c q v := by
  funext i
  simp only [Bop, Pi.smul_apply, smul_eq_mul]
  have : ∀ j, wt c (q i) (q j) * (a * v i - a * v j) = a * (wt c (q i) (q j) * (v i - v j)) :=
    fun j => by ring
  simp_rw [this, ← Finset.mul_sum]; ring

/-- Bilinear symmetrization: `Σ_i u_i Σ_j w_ij (v_i - v_j) = ½ Σ_{i,j} w_ij (u_i-u_j)(v_i-v_j)`. -/
theorem sum_sym2 (c : ℝ) (q u v : Fin N → ℝ) :
    ∑ i, u i * ∑ j, wt c (q i) (q j) * (v i - v j) =
      (1 / 2) * ∑ i, ∑ j, wt c (q i) (q j) * ((u i - u j) * (v i - v j)) := by
  have h1 : ∑ i, u i * ∑ j, wt c (q i) (q j) * (v i - v j) =
      ∑ i, ∑ j, wt c (q i) (q j) * (v i - v j) * u i := by
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, ∑ j, wt c (q i) (q j) * (v i - v j) * u i =
      ∑ i, ∑ j, wt c (q i) (q j) * (v j - v i) * u j := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [wt_symm c (q j) (q i)]
  have h3 : ∑ i, ∑ j, wt c (q i) (q j) * ((u i - u j) * (v i - v j)) =
      ∑ i, ∑ j, wt c (q i) (q j) * (v i - v j) * u i +
        ∑ i, ∑ j, wt c (q i) (q j) * (v j - v i) * u j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [h1, h3, ← h2]; ring

/-- `⟨u, B_N v⟩ = L Σ u_i v_i + ½ Σ w_ij (u_i-u_j)(v_i-v_j)`: symmetric in `u, v`. -/
theorem dotB_bil (L c : ℝ) (q u v : Fin N → ℝ) :
    dot u (Bop L c q v) =
      L * ∑ i, u i * v i + (1 / 2) * ∑ i, ∑ j, wt c (q i) (q j) * ((u i - u j) * (v i - v j)) := by
  unfold dot Bop
  have : ∀ i, u i * (L * v i + ∑ j, wt c (q i) (q j) * (v i - v j)) =
      L * (u i * v i) + u i * ∑ j, wt c (q i) (q j) * (v i - v j) := fun i => by ring
  simp_rw [this]
  rw [sum_add_distrib, ← Finset.mul_sum, sum_sym2]

theorem dotB_symm (L c : ℝ) (q u v : Fin N → ℝ) : dot u (Bop L c q v) = dot v (Bop L c q u) := by
  rw [dotB_bil, dotB_bil]
  congr 1
  · congr 1; exact sum_congr rfl fun i _ => mul_comm _ _
  · congr 1
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [mul_comm (u i - u j)]

theorem dotB_eq (L c : ℝ) (q v : Fin N → ℝ) :
    dot v (Bop L c q v) = L * ∑ i, v i ^ 2 + (1 / 2) * ∑ i, ∑ j, wt c (q i) (q j) * (v i - v j) ^ 2 := by
  rw [dotB_bil]
  simp_rw [← sq]

theorem dotB_ge (L c : ℝ) (hc : 0 ≤ c) (q v : Fin N → ℝ) :
    L * ∑ i, v i ^ 2 ≤ dot v (Bop L c q v) := by
  rw [dotB_eq]
  have : 0 ≤ ∑ i, ∑ j, wt c (q i) (q j) * (v i - v j) ^ 2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (wt_nonneg hc _ _) (sq_nonneg _)
  linarith

/-! ### Finite norms and energies -/

/-- `‖v‖² = (1/N) Σ v_i²` (the `L²(0,1)` norm of the step function). -/
def L2N (N : ℕ) (v : Fin N → ℝ) : ℝ := (1 / (N : ℝ)) * ∑ i, v i ^ 2

/-- `ℰ_N(v) = (1/N²) Σ_{i,j} (v_i-v_j)²/(c² + (q_i-q_j)²)` (`c = κ/N`; the diagonal terms vanish). -/
def EN (N : ℕ) (c : ℝ) (q v : Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, (v i - v j) ^ 2 / (c ^ 2 + (q i - q j) ^ 2)

/-- `⟨Q_N, v⟩ = (1/N) Σ q_i v_i`. -/
def ipN (N : ℕ) (q v : Fin N → ℝ) : ℝ := (1 / (N : ℝ)) * dot q v

theorem Qf_eq (L κ : ℝ) (hN : 0 < N) (q v : Fin N → ℝ) :
    L * L2N N v + κ * EN N (κ / N) q v = (1 / (N : ℝ)) * dot v (Bop L (κ / N) q v) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [dotB_eq]
  unfold L2N EN
  have h1 : ∑ i, ∑ j, wt (κ / N) (q i) (q j) * (v i - v j) ^ 2 =
      2 * (κ / N) * ∑ i, ∑ j, (v i - v j) ^ 2 / ((κ / N) ^ 2 + (q i - q j) ^ 2) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    unfold wt; ring
  rw [h1]
  field_simp

/-- The printed energy `𝒥_N(v) = (L/2)‖v‖² + (κ/2)ℰ_N(v) - ⟨Q_N,v⟩`. -/
def JN (L κ : ℝ) (N : ℕ) (q v : Fin N → ℝ) : ℝ :=
  (L / 2) * L2N N v + (κ / 2) * EN N (κ / N) q v - ipN N q v

/-- `𝒥_N(v) = (1/2N) vᵀ B_N v - (1/N) qᵀ v`. -/
theorem JN_eq (L κ : ℝ) (hN : 0 < N) (q v : Fin N → ℝ) :
    JN L κ N q v = (1 / (2 * (N : ℝ))) * dot v (Bop L (κ / N) q v) - (1 / (N : ℝ)) * dot q v := by
  have h := Qf_eq L κ hN q v
  unfold JN ipN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : (L / 2) * L2N N v + (κ / 2) * EN N (κ / N) q v =
      (1 / 2) * (L * L2N N v + κ * EN N (κ / N) q v) := by ring
  rw [this, h]; field_simp

/-! ### The response `F_N = B_N⁻¹ q` -/

/-- `B_N` as a linear map. -/
def BL (L c : ℝ) (q : Fin N → ℝ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun := Bop L c q
  map_add' := Bop_add L c q
  map_smul' := fun a v => by simpa using Bop_smul L c q v a

theorem BL_injective {L c : ℝ} (hL : 0 < L) (hc : 0 ≤ c) (q : Fin N → ℝ) : Function.Injective (BL L c q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h0 : Bop L c q v = 0 := hv
  have := dotB_ge L c hc q v
  rw [h0] at this
  have hz : dot v (0 : Fin N → ℝ) = 0 := by simp [dot]
  rw [hz] at this
  have hs : ∑ i, v i ^ 2 = 0 := by
    have hnn : 0 ≤ ∑ i, v i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).1 hs i (mem_univ i)
  simpa using this

/-- **The finite response exists and is unique**: `B_N v = q` has exactly one solution. -/
theorem exists_unique_response {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hN : 0 < N) (q : Fin N → ℝ) :
    ∃! v : Fin N → ℝ, Bop L (κ / N) q v = q := by
  have hc : 0 ≤ κ / (N : ℝ) := by positivity
  have hsurj : Function.Surjective (BL L (κ / N) q) :=
    LinearMap.injective_iff_surjective.1 (BL_injective hL hc q)
  obtain ⟨v, hv⟩ := hsurj q
  exact ⟨v, hv, fun w hw => BL_injective hL hc q (hw.trans hv.symm)⟩

/-- `CC:F03:finite-bound`: `L²‖F_N‖² ≤ ‖Q_N‖²` and `L‖F_N‖² + κℰ_N(F_N) = ⟨Q_N, F_N⟩`. -/
theorem response_bounds {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hN : 0 < N) {q F : Fin N → ℝ}
    (hF : Bop L (κ / N) q F = q) :
    L ^ 2 * L2N N F ≤ L2N N q ∧ L * L2N N F + κ * EN N (κ / N) q F = ipN N q F := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 ≤ κ / (N : ℝ) := by positivity
  have hid : L * L2N N F + κ * EN N (κ / N) q F = (1 / (N : ℝ)) * dot F q := by
    rw [Qf_eq L κ hN, hF]
  refine ⟨?_, ?_⟩
  · have h1 : L * ∑ i, F i ^ 2 ≤ dot F q := by
      have := dotB_ge L (κ / N) hc q F
      rwa [hF] at this
    have hcs : (dot F q) ^ 2 ≤ (∑ i, F i ^ 2) * ∑ i, q i ^ 2 := by
      unfold dot
      simpa [sq] using Finset.sum_mul_sq_le_sq_mul_sq univ F q
    have hS : 0 ≤ ∑ i, F i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    have hT : 0 ≤ ∑ i, q i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    have h2 : L ^ 2 * ∑ i, F i ^ 2 ≤ ∑ i, q i ^ 2 := by
      rcases hS.eq_or_lt with h0 | hpos
      · rw [← h0]; simpa using hT
      · have : (L * ∑ i, F i ^ 2) ^ 2 ≤ (∑ i, F i ^ 2) * ∑ i, q i ^ 2 := by
          have h0 : 0 ≤ L * ∑ i, F i ^ 2 := by positivity
          exact le_trans (pow_le_pow_left₀ h0 h1 2) hcs
        have h3 : (∑ i, F i ^ 2) * (L ^ 2 * ∑ i, F i ^ 2) ≤ (∑ i, F i ^ 2) * ∑ i, q i ^ 2 := by
          nlinarith [this]
        exact le_of_mul_le_mul_left h3 hpos
    unfold L2N
    rw [← mul_assoc, mul_comm (L ^ 2), mul_assoc]
    calc (1 / (N : ℝ)) * (L ^ 2 * ∑ i, F i ^ 2) ≤ (1 / (N : ℝ)) * ∑ i, q i ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  · rw [hid]; unfold ipN; rw [dot_comm]

theorem dot_sub_left (a b c : Fin N → ℝ) : dot (a - b) c = dot a c - dot b c := by
  unfold dot; simp [sub_mul, sum_sub_distrib]

theorem dot_sub_right (a b c : Fin N → ℝ) : dot a (b - c) = dot a b - dot a c := by
  unfold dot; simp [mul_sub, sum_sub_distrib]

/-- The quadratic completion `𝒥_N(v) - 𝒥_N(F_N) = (L/2)‖v-F_N‖² + (κ/2)ℰ_N(v-F_N)`. -/
theorem JN_sub_JN {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hN : 0 < N) {q F : Fin N → ℝ}
    (hF : Bop L (κ / N) q F = q) (v : Fin N → ℝ) :
    JN L κ N q v - JN L κ N q F =
      (L / 2) * L2N N (v - F) + (κ / 2) * EN N (κ / N) q (v - F) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := Qf_eq L κ hN q (v - F)
  have hlin : Bop L (κ / N) q (v - F) = Bop L (κ / N) q v - Bop L (κ / N) q F := by
    have := Bop_add L (κ / (N : ℝ)) q v (-F)
    have h2 : Bop L (κ / (N : ℝ)) q (-F) = - Bop L (κ / (N : ℝ)) q F := by
      have := Bop_smul L (κ / (N : ℝ)) q F (-1)
      simpa using this
    rw [sub_eq_add_neg, this, h2]; ring
  have hs := dotB_symm L (κ / N) q F v
  have e1 : dot (v - F) (Bop L (κ / N) q (v - F)) =
      dot v (Bop L (κ / N) q v) - 2 * dot q v + dot q F := by
    rw [hlin, dot_sub_right, dot_sub_left, dot_sub_left, hF, dot_comm F q]
    have : dot F (Bop L (κ / N) q v) = dot v q := by rw [hs, hF]
    rw [this, dot_comm v q]; ring
  have hFF : dot F (Bop L (κ / N) q F) = dot q F := by rw [hF, dot_comm]
  have hRHS : (L / 2) * L2N N (v - F) + (κ / 2) * EN N (κ / N) q (v - F) =
      (1 / (2 * (N : ℝ))) * dot (v - F) (Bop L (κ / N) q (v - F)) := by
    have : (L / 2) * L2N N (v - F) + (κ / 2) * EN N (κ / N) q (v - F) =
        (1 / 2) * (L * L2N N (v - F) + κ * EN N (κ / N) q (v - F)) := by ring
    rw [this, h1]; field_simp
  rw [hRHS, e1, JN_eq L κ hN q v, JN_eq L κ hN q F, hFF]
  field_simp
  ring

end QuantumNLS.FiniteResponse

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.FiniteResponse.exists_unique_response
#print axioms QuantumNLS.FiniteResponse.response_bounds
#print axioms QuantumNLS.FiniteResponse.JN_sub_JN
