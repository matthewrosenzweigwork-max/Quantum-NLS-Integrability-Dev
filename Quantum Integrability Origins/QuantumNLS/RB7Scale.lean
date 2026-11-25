import Mathlib
import QuantumNLS.RB7Seq
import QuantumNLS.LossSobolev

/-!
# R-7B122087 `thm:hierarchy`: the DEF-002 Sobolev scale and the `lem:loss` interface

* `Hinf L z`: `z ∈ ⋂_b h^b` (rapidly decreasing coordinates).  `hzP_of_Hinf`: for such `z` and any finite family of orders `S_r ≥ 0` the
  `P`-moments `Σ_j V_j P_j^{2k}|z_j|²`, `V = h^a`, `P_j = Σ_r (1+|p_j|)^{2 S_r}`, are finite (printed "every time derivative is controlled by a fixed
  polynomial weight times the rapidly decreasing initial sequence").
* `scaleData`: `SeqData` on the DEF-002 scale `h^a` from `C²` rotation-invariant functionals on `h^{S_r}`, `S_r ≤ a`.
* `isCompact_smoothTorus`: the full modulus torus is compact in the smooth (Fréchet) topology of `⋂_k h^k`, realized as the product topology of
  `∏_{k∈ℕ} h^k` (the seminorm topology), as the continuous image of the compact space `ℤ → Circle`.
* `FContDiff` / `inv_of_chart` (the `lem:loss` interface): given the accepted `lem:loss` (`LossSobolev.loss_h_to_H`, `k = 2`, printed `s = 3q+1 > 3q`)
  and a real functional `I` which is `C²` on `H^q`, `F = I ∘ emb ∘ g` is `C²` on `h^S`; and rotation invariance on finitely supported sequences
  (the printed "for rapidly decreasing coordinates, the scalar moment and uniqueness identities show invariance") extends to all of `h^S` by density.
  The hypotheses `hg` (continuity of the restriction `g : h^S → H^S` of the analytic inverse chart: the REG-015 Sobolev homeomorphism input),
  `hI` (`C²` of the charge on `H^q`) and `hfin` (the moment/uniqueness identity on finite support) are EXPLICIT hypotheses, not proved here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology NNReal ContDiff
open Filter Set Metric

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev
open QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Fourier (sobolevWeight MemHs sobolevWeight_pos)

/-- Rapidly decreasing coordinates: `z ∈ h^b` for every real `b`. -/
def Hinf (L : ℝ) (z : ℤ → ℂ) : Prop := ∀ b : ℝ, MemHs L b z

theorem sobolevWeight_eq (L s : ℝ) (j : ℤ) :
    sobolevWeight L s j = (1 + |2 * Real.pi * (j : ℝ) / L|) ^ (2 * s) := rfl

theorem one_le_x (L : ℝ) (j : ℤ) : 1 ≤ 1 + |2 * Real.pi * (j : ℝ) / L| := by
  linarith [abs_nonneg (2 * Real.pi * (j : ℝ) / L)]

theorem sobolevWeight_add (L s t : ℝ) (j : ℤ) :
    sobolevWeight L s j * sobolevWeight L t j = sobolevWeight L (s + t) j := by
  have hx : 0 < 1 + |2 * Real.pi * (j : ℝ) / L| := lt_of_lt_of_le one_pos (one_le_x L j)
  rw [sobolevWeight_eq, sobolevWeight_eq, sobolevWeight_eq, ← Real.rpow_add hx]
  congr 1; ring

theorem sobolevWeight_pow (L s : ℝ) (j : ℤ) (m : ℕ) :
    sobolevWeight L s j ^ m = sobolevWeight L (m * s) j := by
  have hx : 0 ≤ 1 + |2 * Real.pi * (j : ℝ) / L| := (zero_le_one.trans (one_le_x L j))
  rw [sobolevWeight_eq, sobolevWeight_eq, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1; ring

theorem sobolevWeight_le (L : ℝ) {s t : ℝ} (hst : s ≤ t) (j : ℤ) :
    sobolevWeight L s j ≤ sobolevWeight L t j := sobolevWeight_mono L hst j

section Moments

variable {ι : Type} [Fintype ι]

/-- **The `P`-moments of a rapidly decreasing sequence are finite.** -/
theorem hzP_of_Hinf (L : ℝ) (S : ι → ℝ) (hS : ∀ r, 0 ≤ S r) (a : ℝ) (z : ℤ → ℂ) (hz : Hinf L z) (k : ℕ) :
    Summable fun j : ℤ => sobolevWeight L a j * (∑ r, sobolevWeight L (S r) j) ^ (2 * k) * ‖z j‖ ^ 2 := by
  set b0 : ℝ := ∑ r, S r with hb0
  set c : ℝ := (Fintype.card ι : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hSb : ∀ r, S r ≤ b0 := fun r =>
    Finset.single_le_sum (f := S) (fun r _ => hS r) (Finset.mem_univ r)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    ((hz (a + (2 * k) * b0)).mul_left (c ^ (2 * k)))
  · have := sobolevWeight_pos L a j
    have h2 : 0 ≤ ∑ r, sobolevWeight L (S r) j := Finset.sum_nonneg fun r _ => (sobolevWeight_pos L _ j).le
    positivity
  · have hP : ∑ r, sobolevWeight L (S r) j ≤ c * sobolevWeight L b0 j := by
      calc ∑ r, sobolevWeight L (S r) j ≤ ∑ _r : ι, sobolevWeight L b0 j :=
            Finset.sum_le_sum fun r _ => sobolevWeight_le L (hSb r) j
        _ = c * sobolevWeight L b0 j := by simp [hc]
    have hP0 : 0 ≤ ∑ r, sobolevWeight L (S r) j := Finset.sum_nonneg fun r _ => (sobolevWeight_pos L _ j).le
    have h1 : (∑ r, sobolevWeight L (S r) j) ^ (2 * k) ≤ (c * sobolevWeight L b0 j) ^ (2 * k) :=
      pow_le_pow_left₀ hP0 hP _
    have h2 : (c * sobolevWeight L b0 j) ^ (2 * k) = c ^ (2 * k) * sobolevWeight L ((2 * k : ℕ) * b0) j := by
      rw [mul_pow, sobolevWeight_pow]
    have hwa := sobolevWeight_pos L a j
    calc sobolevWeight L a j * (∑ r, sobolevWeight L (S r) j) ^ (2 * k) * ‖z j‖ ^ 2
        ≤ sobolevWeight L a j * (c ^ (2 * k) * sobolevWeight L ((2 * k : ℕ) * b0) j) * ‖z j‖ ^ 2 := by
          rw [← h2]; gcongr
      _ = c ^ (2 * k) * (sobolevWeight L (a + (2 * k) * b0) j * ‖z j‖ ^ 2) := by
          rw [← sobolevWeight_add]; push_cast; ring

end Moments

/-! ## `SeqData` on the DEF-002 scale -/

/-- Rotation-invariant `C²` functionals on `h^{S_r}` give `SeqData` on `h^a`, `S_r ≤ a`. -/
def scaleData (L : ℝ) {ι : Type} (S : ι → ℝ) (a : ℝ) (ha : ∀ r, S r ≤ a)
    (F : ∀ r, h02 L (S r) → ℝ) (hF : ∀ r, ContDiff ℝ 2 (F r))
    (hinv : ∀ r (u : ℤ → Circle) (z : h02 L (S r)), F r (rot u z) = F r z) : SeqData (def002 L a) ι where
  W r := def002 L (S r)
  F := F
  C _ := 1
  hC _ := zero_le_one
  hle r n := def002_le_of_le L (ha r) n
  smooth := hF
  inv := hinv

/-- The full modulus torus is compact in the smooth topology `∏_k h^k`. -/
theorem isCompact_smoothTorus (L : ℝ) (z : ∀ k : ℕ, h02 L (k : ℝ)) :
    IsCompact (Set.range fun u : ℤ → Circle => fun k : ℕ => rot u (z k)) :=
  isCompact_range (continuous_pi fun k => continuous_rot_u (z k))

/-! ## The `lem:loss` interface -/

section Loss

open QuantumNLS.LossSobolev QuantumNLS.Loss

variable (L : ℝ) [Fact (0 < L)]

/-- **`F = I ∘ g` is `C²` on `h^S`** by the accepted `lem:loss` (`k = 2`, `S > 3q`): hypotheses are the analyticity of the inverse chart on `ℓ² → L²`,
the continuity of its restriction `h^S → H^S` (REG-015 input) and `C²` of the charge functional on `H^q`. -/
theorem F_contDiff {q S : ℝ≥0} (hq : 0 < q) (hS : (2 + 1) * (q : ℝ) < S) (hqS : q ≤ S)
    (f : (seqScale L).Y 0 → (fieldScale L).Y 0) (hf : AnalyticOnNhd ℝ f univ)
    (g : (seqScale L).Y S → (fieldScale L).Y S) (hg : Continuous g)
    (hres : ∀ x, (fieldScale L).emb S 0 (nn_zero_le S) (g x) = f ((seqScale L).emb S 0 (nn_zero_le S) x))
    (I : (fieldScale L).Y q → ℝ) (hI : ContDiff ℝ 2 I) :
    ContDiff ℝ 2 (fun x => I ((fieldScale L).emb S q hqS (g x))) := by
  have h := (loss_h_to_H L (k := 2) (by norm_num) hq (by exact_mod_cast hS) hqS f hf g hg hres).1
  exact hI.comp h

/-- **Rotation invariance on all of `h^S` from invariance on finite support** (printed "density and continuity extend invariance to `h^s`"). -/
theorem inv_of_chart {q S : ℝ≥0} (hqS : q ≤ S) (g : h02 L (S : ℝ) → H02 L (S : ℝ))
    (hg : Continuous g) (I : (fieldScale L).Y q → ℝ) (hI : Continuous I)
    (hfin : ∀ (u : ℤ → Circle) (T : Finset ℤ) (z : h02 L (S : ℝ)),
      I ((fieldScale L).emb S q hqS (g (rot u (trunc T z)))) = I ((fieldScale L).emb S q hqS (g (trunc T z))))
    (u : ℤ → Circle) (z : h02 L (S : ℝ)) :
    I ((fieldScale L).emb S q hqS (g (rot u z))) = I ((fieldScale L).emb S q hqS (g z)) := by
  refine inv_of_finite (fun x : h02 L (S : ℝ) => I ((fieldScale L).emb S q hqS (g x))) ?_ hfin u z
  exact hI.comp (((fieldScale L).emb S q hqS).continuous.comp hg)

end Loss

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.hzP_of_Hinf
#print axioms QuantumNLS.RB7.scaleData
#print axioms QuantumNLS.RB7.isCompact_smoothTorus
#print axioms QuantumNLS.RB7.F_contDiff
#print axioms QuantumNLS.RB7.inv_of_chart
