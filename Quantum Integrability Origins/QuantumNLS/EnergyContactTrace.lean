import QuantumNLS.CollisionIdentification
import QuantumNLS.PhysicalEnergyTrace

/-!
# ENERGY-002 `lem:A1-trace` (source `chapters/energy_prepared/cubic_charge.tex:74`): contact traces at
the energy level

Source (pinned PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`): for `m ≥ 2` and `i ≠ j`,
`T_ij : H¹(𝕋_L^m) → H^{1/2}(𝕋_L^{m-1})` is bounded; `T_ij A_m^{-1/2} : L² → L²(𝕋_L^{m-1})` is
compact; consequently `B_ij = T_ij^* D_ij T_ij` is bounded `H¹ → H^{-1}` and
`A_m^{-1/2} T_ij^* T_ij A_m^{-1/2}` is compact; then the finite-rank smooth-kernel commutator clause.
Proof route followed exactly: the elementary discrete estimate `eq:A1-discrete`, weighted
Cauchy–Schwarz in the fibre `a ↦ (a, s−a, ℓ)`, rank-one blocks with a uniform tail, truncation.

Frozen imports (read-only): `CollisionIdentification` (`ffd608f4…`: the physical trace
`productTrace` into `L²(dy_ij)`, `collisionProductUnitary`), `PhysicalEnergyTrace` (`67f87c5d…`),
and through them `CollisionTrace` (`traceCLM`, `fib`, `TIdx`), `PhysicalEnergy` (`PhysH1`,
`PhysH1.unitary = A^{1/2}`), `EnergyMultiplier` (`Mult`, `mulCLM`).

What is proved (no supplied trace, nothing assumed):
* Part 1 `lattice_finite`, `lattice_weight`: `Σ_a 1/(c + κ(a−t)²) ≤ C₀(κ)/√c` (`c ≥ 1`), by comparison
  with `∫ 1/(r²+v²) = π/r` on disjoint unit intervals (`inv_sq_comparable`).
* Part 2 `kinWeight_fib_square` (completing the square in `a − s/2`) and `fibre_kernel`:
  `Σ_a 1/a_m(a,s−a,ℓ) ≤ C_L/√(1+λ_s²+|λ_ℓ|²)` — `eq:A1-discrete` with `C_L = √2 C₀(2(2π/L)²)`.
* Part 3 `row_bound`, `trace_half_bound`, Part 4 `traceHalf`: **(a)** `T_ij : PhysH1 → H^{1/2}`
  bounded, `H^{1/2}` the form domain `Hhalf` of the multiplier `(1+λ_s²+|λ_ℓ|²)^{1/4}` in the
  collision-torus Fourier coordinates, `‖T_ijψ‖²_{H^{1/2}} ≤ (C_L/L)‖ψ‖²_{H¹}` (`norm_traceHalf_le`);
  `productTrace_half` ties it to the frozen physical trace into `L²(dy_ij)`.
* Part 5 `traceInv_isCompact`, `Sop_isCompact`: **(b)** `T_ij A_m^{-1/2}` compact `L² → ℓ²(TIdx)` and
  `L² → L²(dy_ij)` (norm limit of the finite-rank box truncations, rate `B_N`, `traceInv_tail`).
* Part 6 `Bsand`, `bform`, `bform_bound`, `bform_conj`, `Bsand_isSelfAdjoint`: **(c)**
  `b_ij(f,g) = ⟨T_ijf, D_ij T_ijg⟩` (Fourier duality `H^{1/2}×H^{-1/2}`) satisfies
  `|b_ij(f,g)| ≤ (C_L/L)‖f‖_{H¹}‖g‖_{H¹}`, is Hermitian, with the sandwich operator
  `A^{-1/2}B_ijA^{-1/2} = Q^* D_norm Q` bounded self-adjoint on `L²`; `sandwich_isCompact`:
  `A_m^{-1/2} T_ij^* T_ij A_m^{-1/2} = S^*S` compact, `sandwich_inner` its contact pairing (frozen
  `productTrace_inner`); `Sop_adjoint_isCompact`; `commutator_sandwich_isCompact` (the assembly
  `S^*V − V'^*S` compact for bounded `V, V'`).

NOT proved here (explicit remaining clause): the smoothing-trace bounds
`D_ij T_ij (J⊗Id) A^{-1/2}` bounded (`eq:A1-smoothing-trace`) for a finite-rank smooth-kernel `J` —
the tensor structure `J ⊗ Id` on the Fourier carrier, the fibre re-indexing for external/internal
contacts and the Young estimate — and hence the identification of the commutator sandwich with
`S^*V − V'^*S`; the bosonic restriction; the statement for the Hilbert-tensor-product `J⊗Id` operator.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate InnerProductSpace ENNReal
open MeasureTheory

namespace QuantumNLS.EnergyContactTrace

/-! ## Part 1: the elementary discrete estimate `eq:A1-discrete` -/

section Lattice

theorem integral_inv_sq (r : ℝ) (hr : 0 < r) : ∫ v : ℝ, 1/(r^2+v^2) = Real.pi / r := by
  have h : (fun v : ℝ => 1/(r^2+v^2)) = fun v => (r⁻¹ ^ 2) * (1 + (v / r)^2)⁻¹ := by
    funext v; field_simp
  rw [h, integral_const_mul, Measure.integral_comp_div (fun x : ℝ => (1 + x^2)⁻¹) r,
    integral_univ_inv_one_add_sq]
  rw [abs_of_pos hr, smul_eq_mul]; field_simp

theorem integrable_inv_sq (r : ℝ) (hr : 0 < r) : Integrable (fun v : ℝ => 1/(r^2+v^2)) := by
  have h := (integrable_inv_one_add_sq.comp_div hr.ne').const_mul (r⁻¹ ^ 2)
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  field_simp

theorem inv_sq_comparable {r u v : ℝ} (hr : 0 < r) (h : |v - u| ≤ 1/2) :
    1 / (r^2 + u^2) ≤ (2 + 1/(2*r^2)) * (1 / (r^2 + v^2)) := by
  have hv : v^2 ≤ 2*u^2 + 1/2 := by
    have h1 : |v| ≤ |u| + 1/2 := by have := abs_sub_abs_le_abs_sub v u; linarith
    have h2 : v^2 ≤ (|u| + 1/2)^2 := by
      rw [← sq_abs v]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_abs u, sq_nonneg (|u| - 1/2)]
  have hpos1 : 0 < r^2 + u^2 := by positivity
  have hpos2 : 0 < r^2 + v^2 := by positivity
  rw [mul_one_div, div_le_div_iff₀ hpos1 hpos2]
  have h3 : (1:ℝ)/2 ≤ (r^2+u^2)/(2*r^2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg u]
  have h4 : (2 + 1/(2*r^2)) * (r^2+u^2) = 2*(r^2+u^2) + (r^2+u^2)/(2*r^2) := by field_simp
  nlinarith [h4, h3]

/-- Shifted lattice sum of the Cauchy kernel, compared with its integral on disjoint unit intervals. -/
theorem lattice_finite (r : ℝ) (hr : 0 < r) (t : ℝ) (S : Finset ℤ) :
    ∑ a ∈ S, 1 / (r^2 + ((a:ℝ) - t)^2) ≤ (2 + 1/(2*r^2)) * (Real.pi / r) := by
  set K : ℝ := 2 + 1/(2*r^2) with hK
  have hK0 : 0 < K := by positivity
  set f : ℝ → ℝ := fun v => 1/(r^2+v^2) with hf
  have hint := integrable_inv_sq r hr
  set I : ℤ → Set ℝ := fun a => Set.Ioc ((a:ℝ) - t - 1/2) ((a:ℝ) - t + 1/2) with hI
  have hmeas : ∀ a, MeasurableSet (I a) := fun a => measurableSet_Ioc
  have hdisj : Set.Pairwise (↑S : Set ℤ) (Function.onFun Disjoint I) := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    simp only [hI, Set.mem_Ioc] at hxa hxb
    rcases lt_or_gt_of_ne hab with h | h
    · have : (a:ℝ) + 1 ≤ b := by exact_mod_cast h
      linarith [hxa.2, hxb.1]
    · have : (b:ℝ) + 1 ≤ a := by exact_mod_cast h
      linarith [hxb.2, hxa.1]
  have hpt : ∀ a : ℤ, 1 / (r^2 + ((a:ℝ) - t)^2) ≤ K * ∫ v in I a, f v := by
    intro a
    have hlow : ∀ v ∈ I a, f ((a:ℝ) - t) / K ≤ f v := by
      intro v hv
      simp only [hI, Set.mem_Ioc] at hv
      have hc := inv_sq_comparable (r := r) (u := (a:ℝ) - t) (v := v) hr
        (by rw [abs_le]; constructor <;> linarith [hv.1, hv.2])
      rw [div_le_iff₀ hK0]; simp only [hf]; linarith
    have := setIntegral_ge_of_const_le (μ := volume) (hmeas a) (by simp [hI]) hlow
      (hint.integrableOn)
    have hvol : (volume : Measure ℝ).real (I a) = 1 := by
      simp only [hI, Real.volume_real_Ioc]; ring_nf; simp
    rw [hvol, smul_eq_mul, one_mul] at this
    have h2 : f ((a:ℝ) - t) ≤ K * ∫ v in I a, f v := by
      rw [div_le_iff₀ hK0] at this; linarith
    exact h2
  calc ∑ a ∈ S, 1 / (r^2 + ((a:ℝ) - t)^2) ≤ ∑ a ∈ S, K * ∫ v in I a, f v :=
        Finset.sum_le_sum fun a _ => hpt a
    _ = K * ∫ v in ⋃ a ∈ S, I a, f v := by
        rw [← Finset.mul_sum, integral_biUnion_finset S (fun a _ => hmeas a) hdisj
          (fun a _ => hint.integrableOn)]
    _ ≤ K * ∫ v, f v := by
        refine mul_le_mul_of_nonneg_left ?_ hK0.le
        exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun v => by
          simp only [hf, Pi.zero_apply]; positivity)
    _ = K * (Real.pi / r) := by rw [integral_inv_sq r hr]

/-- The constant `C₀(κ) = (2 + κ/2) π / √κ`. -/
def C0 (κ : ℝ) : ℝ := (2 + κ / 2) * Real.pi / Real.sqrt κ

/-- `Σ_a 1/(c + κ(a−t)²) ≤ C₀(κ)/√c` for `c ≥ 1`. -/
theorem lattice_weight {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 1 ≤ c) (t : ℝ) (S : Finset ℤ) :
    ∑ a ∈ S, 1 / (c + κ * ((a:ℝ) - t)^2) ≤ C0 κ / Real.sqrt c := by
  have hc0 : 0 < c := by linarith
  set r : ℝ := Real.sqrt (c / κ) with hr
  have hrpos : 0 < r := Real.sqrt_pos.2 (div_pos hc0 hκ)
  have hr2 : r ^ 2 = c / κ := Real.sq_sqrt (div_pos hc0 hκ).le
  have h1 := lattice_finite r hrpos t S
  have e : ∀ a : ℤ, 1 / (c + κ * ((a:ℝ) - t)^2) = κ⁻¹ * (1 / (r^2 + ((a:ℝ) - t)^2)) := by
    intro a
    rw [hr2]; field_simp
  simp_rw [e]
  rw [← Finset.mul_sum]
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hrr : r = Real.sqrt c / Real.sqrt κ := by rw [hr, Real.sqrt_div hc0.le]
  have h2 : (2 + 1/(2*r^2)) ≤ 2 + κ / 2 := by
    have : 1/(2*r^2) ≤ κ/2 := by
      rw [hr2]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : κ * c ≥ κ * 1 := by nlinarith
      field_simp
      nlinarith
    linarith
  have h3 : (2 + 1/(2*r^2)) * (Real.pi / r) ≤ (2 + κ/2) * (Real.pi / r) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have h4 : κ⁻¹ * ((2 + κ/2) * (Real.pi / r)) = C0 κ / Real.sqrt c := by
    unfold C0
    rw [hrr, div_div_eq_mul_div]
    field_simp
    exact Real.sq_sqrt hκ.le
  calc κ⁻¹ * ∑ a ∈ S, 1 / (r^2 + ((a:ℝ) - t)^2) ≤ κ⁻¹ * ((2 + 1/(2*r^2)) * (Real.pi / r)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hκ.le)
    _ ≤ κ⁻¹ * ((2 + κ/2) * (Real.pi / r)) := mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hκ.le)
    _ = C0 κ / Real.sqrt c := h4

end Lattice

/-! ## Part 2: the collision torus weight and the fibre kernel bound -/

section Fibre

open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.CollisionTrace QuantumNLS.Fourier
  QuantumNLS.CollisionIdentification

variable (L : ℝ) {m : ℕ} (i j : Fin m)

/-- The additive Fourier weight `1 + Σ_{d} λ_d²` on the collision torus `𝕋_L^{m-1}`, in its
momentum coordinates `(s, ℓ)` (`s` the common coordinate, `ℓ` the other `m−2`). -/
def colWeight (t : TIdx m i j) : ℝ := 1 + freq L t.1 ^ 2 + ∑ r : Rest m i j, freq L (t.2 r) ^ 2

theorem one_le_colWeight (t : TIdx m i j) : 1 ≤ colWeight L i j t := by
  unfold colWeight
  have : 0 ≤ ∑ r : Rest m i j, freq L (t.2 r) ^ 2 := Finset.sum_nonneg fun r _ => sq_nonneg _
  nlinarith [sq_nonneg (freq L t.1)]

variable {L i j}

theorem fib_rest (hij : i ≠ j) (t : TIdx m i j) (a : ℤ) (r : Rest m i j) :
    fib i j hij t a r.1 = t.2 r := by
  obtain ⟨l, h1, h2⟩ := r
  simp [fib, splitEquiv, h1, h2]

theorem sum_fib (hij : i ≠ j) (g : ℤ → ℝ) (t : TIdx m i j) (a : ℤ) :
    ∑ l, g (fib i j hij t a l) = g a + g (t.1 - a) + ∑ r : Rest m i j, g (t.2 r) := by
  have hji : j ≠ i := hij.symm
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase (Finset.univ.erase i) _ (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩),
    fib_i, fib_j, ← add_assoc]
  congr 1
  rw [Finset.sum_subtype ((Finset.univ.erase i).erase j) (p := fun l => l ≠ i ∧ l ≠ j)
    (fun l => by simp [and_comm])]
  exact Finset.sum_congr rfl fun r _ => by rw [fib_rest hij]

theorem kinWeight_fib (hij : i ≠ j) (t : TIdx m i j) (a : ℤ) :
    kinWeight L m (fib i j hij t a) =
      1 + freq L a ^ 2 + freq L (t.1 - a) ^ 2 + ∑ r : Rest m i j, freq L (t.2 r) ^ 2 := by
  unfold kinWeight
  rw [sum_fib hij (fun n => freq L n ^ 2)]
  ring

/-- Completing the square in `a − s/2`: `a_m(a, s−a, ℓ) = c + κ (a − s/2)²`. -/
theorem kinWeight_fib_square (hij : i ≠ j) (t : TIdx m i j) (a : ℤ) :
    kinWeight L m (fib i j hij t a) =
      (1 + freq L t.1 ^ 2 / 2 + ∑ r : Rest m i j, freq L (t.2 r) ^ 2) +
        2 * (2 * Real.pi / L) ^ 2 * ((a : ℝ) - (t.1 : ℝ) / 2) ^ 2 := by
  rw [kinWeight_fib hij]
  unfold freq
  push_cast
  ring

/-- The constant of `eq:A1-discrete`: `C_L = √2 · C₀(2(2π/L)²)`. -/
def CL (L : ℝ) : ℝ := Real.sqrt 2 * C0 (2 * (2 * Real.pi / L) ^ 2)

theorem fibre_kernel_finite [Fact (0 < L)] (hij : i ≠ j) (t : TIdx m i j) (S : Finset ℤ) :
    ∑ a ∈ S, 1 / kinWeight L m (fib i j hij t a) ≤ CL L / Real.sqrt (colWeight L i j t) := by
  have hL : 0 < L := Fact.out
  have hκ : 0 < 2 * (2 * Real.pi / L) ^ 2 := by positivity
  set ν : ℝ := ∑ r : Rest m i j, freq L (t.2 r) ^ 2 with hν
  have hν0 : 0 ≤ ν := Finset.sum_nonneg fun r _ => sq_nonneg _
  set c : ℝ := 1 + freq L t.1 ^ 2 / 2 + ν with hc
  have hc1 : 1 ≤ c := by nlinarith [sq_nonneg (freq L t.1)]
  have h1 := lattice_weight hκ hc1 ((t.1 : ℝ) / 2) S
  have e : ∀ a : ℤ, 1 / kinWeight L m (fib i j hij t a) =
      1 / (c + 2 * (2 * Real.pi / L) ^ 2 * ((a : ℝ) - (t.1 : ℝ) / 2) ^ 2) := fun a => by
    rw [kinWeight_fib_square hij]
  simp_rw [e]
  refine h1.trans ?_
  have hcol : colWeight L i j t ≤ 2 * c := by
    unfold colWeight; rw [← hν]; simp only [hc]; nlinarith [sq_nonneg (freq L t.1)]
  have hcw : 0 < colWeight L i j t := by linarith [one_le_colWeight L i j t]
  have hsq : Real.sqrt (colWeight L i j t) ≤ Real.sqrt 2 * Real.sqrt c := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hcol
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 (by linarith)
  have hsw : 0 < Real.sqrt (colWeight L i j t) := Real.sqrt_pos.2 hcw
  have hC0 : 0 ≤ C0 (2 * (2 * Real.pi / L) ^ 2) := by unfold C0; positivity
  unfold CL
  rw [div_le_div_iff₀ hsc hsw]
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  calc C0 (2 * (2 * Real.pi / L) ^ 2) * Real.sqrt (colWeight L i j t)
      ≤ C0 (2 * (2 * Real.pi / L) ^ 2) * (Real.sqrt 2 * Real.sqrt c) :=
        mul_le_mul_of_nonneg_left hsq hC0
    _ = Real.sqrt 2 * C0 (2 * (2 * Real.pi / L) ^ 2) * Real.sqrt c := by ring

/-- The fibre kernel is summable, with `Σ_a 1/a_m(a, s−a, ℓ) ≤ C_L/√(1+λ_s²+|λ_ℓ|²)`. -/
theorem fibre_kernel [Fact (0 < L)] (hij : i ≠ j) (t : TIdx m i j) :
    Summable (fun a : ℤ => 1 / kinWeight L m (fib i j hij t a)) ∧
      ∑' a, 1 / kinWeight L m (fib i j hij t a) ≤ CL L / Real.sqrt (colWeight L i j t) := by
  have hnn : ∀ a : ℤ, 0 ≤ 1 / kinWeight L m (fib i j hij t a) := fun a => by
    have := one_le_kinWeight L m (fib i j hij t a)
    positivity
  have hsum : Summable (fun a : ℤ => 1 / kinWeight L m (fib i j hij t a)) :=
    summable_of_sum_le hnn (fun S => fibre_kernel_finite hij t S)
  exact ⟨hsum, hsum.tsum_le_of_sum_le (fun S => fibre_kernel_finite hij t S)⟩

end Fibre

/-! ## Part 3: the trace is bounded `H¹ → H^{1/2}` (weighted Cauchy–Schwarz in the fibre) -/

section Bounded

open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.CollisionTrace QuantumNLS.Fourier
  QuantumNLS.CollisionIdentification

variable {L : ℝ} [Fact (0 < L)] {m : ℕ} {i j : Fin m}

/-- **Row estimate** (`eq:A1-discrete` + weighted Cauchy–Schwarz in the fibre `a ↦ (a, s−a, ℓ)`):
for a coefficient array with finite `H¹` weight,
`|(T c)(s,ℓ)|² ≤ (C_L/L) (1+λ_s²+|λ_ℓ|²)^{-1/2} Σ_a a_m(a,s−a,ℓ) |c_{a,s−a,ℓ}|²`. -/
theorem row_bound (hij : i ≠ j) (c : Mom m → ℂ)
    (hc : Summable fun w => kinWeight L m w * ‖c w‖ ^ 2) (t : TIdx m i j) :
    Summable (fun a : ℤ => kinWeight L m (fib i j hij t a) * ‖c (fib i j hij t a)‖ ^ 2) ∧
    ‖traceCoeff L i j hij c t‖ ^ 2 ≤ (CL L / L) * (Real.sqrt (colWeight L i j t))⁻¹ *
      ∑' a : ℤ, kinWeight L m (fib i j hij t a) * ‖c (fib i j hij t a)‖ ^ 2 := by
  have hL : 0 < L := Fact.out
  have hsumH := hc.comp_injective (fib_injective i j hij t)
  set g : ℤ → ℝ := fun a => kinWeight L m (fib i j hij t a) with hg
  have hg1 : ∀ a, 1 ≤ g a := fun a => one_le_kinWeight L m _
  have hgpos : ∀ a, 0 < g a := fun a => by linarith [hg1 a]
  obtain ⟨hker, hkerle⟩ := fibre_kernel (L := L) hij t
  set f : ℤ → ℝ := fun a => (Real.sqrt (g a))⁻¹ with hf
  set h : ℤ → ℝ := fun a => Real.sqrt (g a) * ‖c (fib i j hij t a)‖ with hh
  have hf0 : ∀ a, 0 ≤ f a := fun a => by simp only [hf]; positivity
  have hh0 : ∀ a, 0 ≤ h a := fun a => by simp only [hh]; positivity
  have hf2 : ∀ a, f a ^ 2 = 1 / g a := fun a => by
    simp only [hf]; rw [inv_pow, Real.sq_sqrt (hgpos a).le, one_div]
  have hh2 : ∀ a, h a ^ 2 = g a * ‖c (fib i j hij t a)‖ ^ 2 := fun a => by
    simp only [hh]; rw [mul_pow, Real.sq_sqrt (hgpos a).le]
  have hfs : Summable fun a => f a ^ 2 := by simp_rw [hf2]; exact hker
  have hhs : Summable fun a => h a ^ 2 := by simp_rw [hh2]; exact hsumH
  obtain ⟨hfh, cs⟩ := tsum_mul_sq_le hf0 hh0 hfs hhs
  have hfh_eq : ∀ a, f a * h a = ‖c (fib i j hij t a)‖ := fun a => by
    simp only [hf, hh]
    have : 0 < Real.sqrt (g a) := Real.sqrt_pos.2 (hgpos a)
    field_simp
  simp_rw [hfh_eq] at hfh cs
  simp_rw [hf2, hh2] at cs
  refine ⟨hsumH, ?_⟩
  have hnorm : ‖traceCoeff L i j hij c t‖ ^ 2 = L⁻¹ * ‖∑' a, c (fib i j hij t a)‖ ^ 2 := by
    unfold traceCoeff
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt hL.le]
  rw [hnorm]
  have h1 : ‖∑' a, c (fib i j hij t a)‖ ≤ ∑' a, ‖c (fib i j hij t a)‖ :=
    norm_tsum_le_tsum_norm hfh
  have h2 : ‖∑' a, c (fib i j hij t a)‖ ^ 2 ≤ (∑' a, ‖c (fib i j hij t a)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hT0 : 0 ≤ ∑' a, g a * ‖c (fib i j hij t a)‖ ^ 2 :=
    tsum_nonneg fun a => mul_nonneg (hgpos a).le (sq_nonneg _)
  have hK0 : 0 ≤ ∑' a, 1 / g a := tsum_nonneg fun a => by have := hgpos a; positivity
  have h3 : (∑' a, 1 / g a) * ∑' a, g a * ‖c (fib i j hij t a)‖ ^ 2 ≤
      (CL L / Real.sqrt (colWeight L i j t)) * ∑' a, g a * ‖c (fib i j hij t a)‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hkerle hT0
  have hLi : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
  calc L⁻¹ * ‖∑' a, c (fib i j hij t a)‖ ^ 2
      ≤ L⁻¹ * ((∑' a, 1 / g a) * ∑' a, g a * ‖c (fib i j hij t a)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h2.trans cs) hLi
    _ ≤ L⁻¹ * ((CL L / Real.sqrt (colWeight L i j t)) * ∑' a, g a * ‖c (fib i j hij t a)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hLi
    _ = (CL L / L) * (Real.sqrt (colWeight L i j t))⁻¹ *
          ∑' a, kinWeight L m (fib i j hij t a) * ‖c (fib i j hij t a)‖ ^ 2 := by
        simp only [hg]; field_simp

/-- Re-summation over the fibres `ℤ^m ≃ TIdx × ℤ`. -/
theorem fibre_total (hij : i ≠ j) (G : Mom m → ℝ) (hG : Summable G) :
    Summable (fun t : TIdx m i j => ∑' a : ℤ, G (fib i j hij t a)) ∧
      ∑' t : TIdx m i j, ∑' a : ℤ, G (fib i j hij t a) = ∑' w, G w := by
  let e : TIdx m i j × ℤ ≃ Mom m := (fibEquiv i j hij).symm
  have hs : Summable (G ∘ e) := e.summable_iff.2 hG
  have hee : ∀ p : TIdx m i j × ℤ, (G ∘ e) p = G (fib i j hij p.1 p.2) := fun p => rfl
  refine ⟨?_, ?_⟩
  · exact hs.prod
  · rw [← e.tsum_eq G]
    exact hs.tsum_prod.symm

theorem summable_coeffFun_form (x : PhysH1 L m) :
    Summable fun w => kinWeight L m w * ‖coeffFun x w‖ ^ 2 := by
  have h := summable_kin_form (show H1Dom L m from x)
  have e : coeffFun x = ((show H1Dom L m from x).val : Mom m → ℂ) := by
    funext w
    unfold coeffFun
    rw [PhysH1.momUnitary_val]
  rw [e]; exact h

theorem tsum_coeffFun_form (x : PhysH1 L m) :
    ∑' w, kinWeight L m w * ‖coeffFun x w‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [PhysH1.norm_sq_eq]; rfl

/-- **(a)** The trace is bounded `H¹ → H^{1/2}` on the Fourier side:
`Σ_{(s,ℓ)} (1+λ_s²+|λ_ℓ|²)^{1/2} |(T_ij ψ)^(s,ℓ)|² ≤ (C_L/L) ‖ψ‖²_{H¹}`. -/
theorem trace_half_bound (hij : i ≠ j) (x : PhysH1 L m) :
    Summable (fun t : TIdx m i j => Real.sqrt (colWeight L i j t) *
        ‖traceCoeff L i j hij (coeffFun x) t‖ ^ 2) ∧
      ∑' t : TIdx m i j, Real.sqrt (colWeight L i j t) *
        ‖traceCoeff L i j hij (coeffFun x) t‖ ^ 2 ≤ (CL L / L) * ‖x‖ ^ 2 := by
  have hG := summable_coeffFun_form x
  obtain ⟨hfs, hft⟩ := fibre_total hij _ hG
  have hpt : ∀ t : TIdx m i j, Real.sqrt (colWeight L i j t) *
      ‖traceCoeff L i j hij (coeffFun x) t‖ ^ 2 ≤
      (CL L / L) * ∑' a : ℤ, kinWeight L m (fib i j hij t a) *
        ‖coeffFun x (fib i j hij t a)‖ ^ 2 := fun t => by
    have hcw : 0 < Real.sqrt (colWeight L i j t) :=
      Real.sqrt_pos.2 (by linarith [one_le_colWeight L i j t])
    have h := (row_bound hij (coeffFun x) hG t).2
    calc Real.sqrt (colWeight L i j t) * ‖traceCoeff L i j hij (coeffFun x) t‖ ^ 2
        ≤ Real.sqrt (colWeight L i j t) * ((CL L / L) * (Real.sqrt (colWeight L i j t))⁻¹ *
          ∑' a : ℤ, kinWeight L m (fib i j hij t a) * ‖coeffFun x (fib i j hij t a)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h hcw.le
      _ = _ := by field_simp
  have hnn : ∀ t : TIdx m i j, 0 ≤ Real.sqrt (colWeight L i j t) *
      ‖traceCoeff L i j hij (coeffFun x) t‖ ^ 2 := fun t => by positivity
  have hsum : Summable (fun t : TIdx m i j => Real.sqrt (colWeight L i j t) *
        ‖traceCoeff L i j hij (coeffFun x) t‖ ^ 2) :=
    Summable.of_nonneg_of_le hnn hpt (hfs.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' t : TIdx m i j, Real.sqrt (colWeight L i j t) *
        ‖traceCoeff L i j hij (coeffFun x) t‖ ^ 2
      ≤ ∑' t : TIdx m i j, (CL L / L) * ∑' a : ℤ, kinWeight L m (fib i j hij t a) *
        ‖coeffFun x (fib i j hij t a)‖ ^ 2 := hsum.tsum_le_tsum hpt (hfs.mul_left _)
    _ = (CL L / L) * ‖x‖ ^ 2 := by
        rw [tsum_mul_left, hft, tsum_coeffFun_form]

end Bounded

/-! ## Part 4: `H^{1/2}` of the collision torus and the bounded operator `T_ij : H¹ → H^{1/2}` -/

section Half

set_option linter.unusedSectionVars false

open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.CollisionTrace QuantumNLS.Fourier
  QuantumNLS.CollisionIdentification

variable {L : ℝ} [Fact (0 < L)] {m : ℕ} (i j : Fin m)

/-- The multiplier `(1 + λ_s² + |λ_ℓ|²)^{1/4}` on the collision-torus Fourier index set: the Hilbert
space `H^{1/2}(𝕋_L^{m-1})` is its form domain, with `‖y‖² = Σ (1+λ_s²+|λ_ℓ|²)^{1/2} |ŷ(s,ℓ)|²`. -/
def halfMult (L : ℝ) : Mult (TIdx m i j) :=
  ⟨fun t => Real.sqrt (Real.sqrt (colWeight L i j t)), fun t =>
    Real.one_le_sqrt.2 (Real.one_le_sqrt.2 (one_le_colWeight L i j t))⟩

theorem halfMult_sq (t : TIdx m i j) :
    (halfMult i j L).m t ^ 2 = Real.sqrt (colWeight L i j t) := by
  show Real.sqrt (Real.sqrt (colWeight L i j t)) ^ 2 = _
  exact Real.sq_sqrt (Real.sqrt_nonneg _)

/-- `H^{1/2}(𝕋_L^{m-1})` on the collision torus, in the physical Fourier coordinates
`(s, ℓ)` of `dy_ij`. -/
abbrev Hhalf (L : ℝ) : Type := (halfMult (m := m) i j L).DomSpace

variable {i j}

theorem CL_nonneg : 0 ≤ CL L := by
  have hL : 0 < L := Fact.out
  unfold CL C0
  positivity

theorem trace_mem_half (hij : i ≠ j) (x : PhysH1 L m) :
    (traceCLM i j hij x : L2 (TIdx m i j)) ∈ mulDomain (halfMult i j L).m := by
  rw [mem_mulDomain_iff]
  refine (trace_half_bound hij x).1.congr fun t => ?_
  rw [halfMult_sq]
  rfl

/-- The trace as a linear map `H¹ → H^{1/2}`. -/
def traceHalfLin (hij : i ≠ j) : PhysH1 L m →ₗ[ℂ] Hhalf i j L where
  toFun x := Mult.DomSpace.mk (traceCLM i j hij x) (trace_mem_half hij x)
  map_add' x y := by
    apply Mult.DomSpace.ext
    simp only [Mult.DomSpace.val_mk, map_add, Mult.DomSpace.val_add]
  map_smul' c x := by
    apply Mult.DomSpace.ext
    simp only [Mult.DomSpace.val_mk, map_smul, Mult.DomSpace.val_smul, RingHom.id_apply]

theorem traceHalfLin_val (hij : i ≠ j) (x : PhysH1 L m) :
    (traceHalfLin hij x).val = traceCLM i j hij x := rfl

theorem traceHalfLin_norm_sq (hij : i ≠ j) (x : PhysH1 L m) :
    ‖traceHalfLin hij x‖ ^ 2 ≤ (CL L / L) * ‖x‖ ^ 2 := by
  rw [Mult.DomSpace.norm_sq_eq_tsum]
  refine le_trans (le_of_eq ?_) (trace_half_bound hij x).2
  refine tsum_congr fun t => ?_
  rw [halfMult_sq, traceHalfLin_val]
  rfl

/-- **(a) `T_ij : H¹(𝕋_L^m) → H^{1/2}(𝕋_L^{m-1})` is a bounded operator**, with the actual Fourier
`H^{1/2}` norm on the collision torus: `‖T_ij ψ‖²_{H^{1/2}} ≤ (C_L/L) ‖ψ‖²_{H¹}`. -/
def traceHalf (hij : i ≠ j) : PhysH1 L m →L[ℂ] Hhalf i j L :=
  (traceHalfLin hij).mkContinuous (Real.sqrt (CL L / L)) (fun x => by
    have hL : 0 < L := Fact.out
    have h := traceHalfLin_norm_sq hij x
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [mul_pow, Real.sq_sqrt (div_nonneg CL_nonneg hL.le)]
    exact h)

theorem norm_traceHalf_le (hij : i ≠ j) : ‖traceHalf (L := L) hij‖ ≤ Real.sqrt (CL L / L) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

theorem traceHalf_val (hij : i ≠ j) (x : PhysH1 L m) :
    (traceHalf hij x).val = traceCLM i j hij x := rfl

/-- In the physical `L²(dy_ij)` picture: the Fourier coefficients (in the product modes of the
collision torus, Sol's `collisionProductUnitary`) of the actual restriction `productTrace` of an
`H¹` function are those of `traceHalf`, hence lie in `H^{1/2}`. -/
theorem productTrace_half (hij : i ≠ j) (x : PhysH1 L m) :
    (traceHalf hij x).val = (collisionProductUnitary i j).symm (productTrace i j hij x) := by
  rw [traceHalf_val]
  unfold productTrace
  simp

end Half

/-! ## Part 5: `T_ij A_m^{-1/2} : L² → L²(𝕋_L^{m-1})` is compact -/

section Compactness

set_option linter.unusedSectionVars false

open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.CollisionTrace QuantumNLS.Fourier
  QuantumNLS.CollisionIdentification QuantumNLS.EnergyRealization QuantumNLS.PhysicalTensor

variable {L : ℝ} [Fact (0 < L)] {m : ℕ} {i j : Fin m}

/-- `T_ij A_m^{-1/2}` in Fourier coefficients: `A_m^{-1/2} = (PhysH1.unitary)⁻¹ : L²(𝕋_L^m) → H¹`
followed by the constructed collision trace. -/
def traceInv (hij : i ≠ j) : L2TN L m →L[ℂ] L2 (TIdx m i j) :=
  (traceCLM i j hij).comp
    ((PhysH1.unitary (L := L) (k := m)).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem traceInv_apply (hij : i ≠ j) (y : L2TN L m) :
    traceInv hij y = traceCLM i j hij ((PhysH1.unitary (L := L) (k := m)).symm y) := rfl

theorem coeff_unitary_symm (y : L2TN L m) (w : Mom m) :
    ‖(momUnitary L m y : Mom m → ℂ) w‖ ^ 2 =
      kinWeight L m w * ‖coeffFun ((PhysH1.unitary (L := L) (k := m)).symm y) w‖ ^ 2 := by
  have h := PhysH1.unitary_coeff ((PhysH1.unitary (L := L) (k := m)).symm y) w
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  have h' : (momUnitary L m y : Mom m → ℂ) w =
      (kinSqrt L m w : ℂ) * coeffFun ((PhysH1.unitary (L := L) (k := m)).symm y) w := h
  rw [h', norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, kinSqrt_sq]

theorem traceInv_row (hij : i ≠ j) (y : L2TN L m) (t : TIdx m i j) :
    ‖(traceInv hij y : TIdx m i j → ℂ) t‖ ^ 2 ≤ (CL L / L) * (Real.sqrt (colWeight L i j t))⁻¹ *
      ∑' a : ℤ, ‖(momUnitary L m y : Mom m → ℂ) (fib i j hij t a)‖ ^ 2 := by
  set x := (PhysH1.unitary (L := L) (k := m)).symm y with hx
  have h := (row_bound hij (coeffFun x) (summable_coeffFun_form x) t).2
  have e : ∀ a : ℤ, kinWeight L m (fib i j hij t a) * ‖coeffFun x (fib i j hij t a)‖ ^ 2 =
      ‖(momUnitary L m y : Mom m → ℂ) (fib i j hij t a)‖ ^ 2 := fun a =>
    (coeff_unitary_symm y _).symm
  simp_rw [e] at h
  exact h

open scoped Classical in
/-- Truncation of output frequencies: `y ↦ (1_U y)`. -/
def truncOp {ι : Type*} (U : Finset ι) : L2 ι →L[ℂ] L2 ι :=
  mulCLM (fun t => if t ∈ U then (1 : ℝ) else 0) 1 zero_le_one (fun t => by
    by_cases h : t ∈ U <;> simp [h])

open scoped Classical in
theorem truncOp_apply {ι : Type*} (U : Finset ι) (z : L2 ι) (t : ι) :
    (truncOp U z : ι → ℂ) t = if t ∈ U then (z : ι → ℂ) t else 0 := by
  unfold truncOp
  rw [mulCLM_apply]
  by_cases h : t ∈ U <;> simp [h]

open scoped Classical in
/-- A finite output truncation is a compact operator (finite rank). -/
theorem isCompactOperator_truncOp {ι : Type*} (U : Finset ι) : IsCompactOperator (truncOp U) := by
  classical
  let Emb : (U → ℂ) →L[ℂ] L2 ι := LinearMap.toContinuousLinearMap
    { toFun := fun c => ∑ t : U, c t • ev t.1
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  let Coord : L2 ι →L[ℂ] (U → ℂ) := ContinuousLinearMap.pi (fun t : U => innerSL ℂ (ev t.1))
  have hEC : (truncOp U) = Emb.comp Coord := by
    ext z s
    show ((truncOp U z : L2 ι) : ι → ℂ) s = ((Emb (Coord z) : L2 ι) : ι → ℂ) s
    rw [← inner_ev_left s (Emb (Coord z))]
    have horth : ∀ t : ι, ⟪ev s, ev t⟫_ℂ = if s = t then 1 else 0 := fun t => by
      have := (orthonormal_iff_ite.1 (stdBasis (ι := ι)).orthonormal) s t
      exact this
    have hEmb : Emb (Coord z) = ∑ t : U, ⟪ev t.1, z⟫_ℂ • ev t.1 := rfl
    rw [hEmb, inner_sum]
    simp_rw [inner_smul_right, horth]
    rw [truncOp_apply]
    by_cases hs : s ∈ U
    · simp only [hs, ↓reduceIte]
      rw [Finset.sum_eq_single ⟨s, hs⟩]
      · simp [inner_ev_left]
      · intro b _ hb
        have : s ≠ b.1 := fun h => hb (Subtype.ext h.symm)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [hs, ↓reduceIte]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      have : s ≠ b.1 := fun h => hs (h ▸ b.2)
      simp [this]
  rw [hEC]
  exact (isCompactOperator_of_locallyCompactSpace_rng Emb).comp_clm Coord

/-- **Tail estimate** for `T_ij A_m^{-1/2}`: the part of the output with frequencies outside `U`
has `‖(1−1_U) T A^{-1/2} y‖² ≤ (C_L/L) δ ‖y‖²` when `(1+λ_s²+|λ_ℓ|²)^{-1/2} ≤ δ` off `U`. -/
theorem traceInv_tail (hij : i ≠ j) (U : Finset (TIdx m i j)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ t ∉ U, (Real.sqrt (colWeight L i j t))⁻¹ ≤ δ) (y : L2TN L m) :
    ‖traceInv hij y - truncOp U (traceInv hij y)‖ ^ 2 ≤ (CL L / L) * δ * ‖y‖ ^ 2 := by
  classical
  have hL : 0 < L := Fact.out
  set v := traceInv hij y - truncOp U (traceInv hij y) with hv
  have hG : Summable (fun w : Mom m => ‖(momUnitary L m y : Mom m → ℂ) w‖ ^ 2) :=
    summable_sq (momUnitary L m y)
  obtain ⟨hfs, hft⟩ := fibre_total hij _ hG
  have hnorm : ∑' w : Mom m, ‖(momUnitary L m y : Mom m → ℂ) w‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← (momUnitary L m).norm_map y, norm_sq_eq_tsum]
  have hC : 0 ≤ CL L / L := div_nonneg CL_nonneg hL.le
  have hpt : ∀ t : TIdx m i j, ‖(v : TIdx m i j → ℂ) t‖ ^ 2 ≤
      (CL L / L) * δ * ∑' a : ℤ, ‖(momUnitary L m y : Mom m → ℂ) (fib i j hij t a)‖ ^ 2 := by
    intro t
    have hT0 : 0 ≤ ∑' a : ℤ, ‖(momUnitary L m y : Mom m → ℂ) (fib i j hij t a)‖ ^ 2 :=
      tsum_nonneg fun a => sq_nonneg _
    by_cases ht : t ∈ U
    · have : (v : TIdx m i j → ℂ) t = 0 := by
        rw [hv, lp.coeFn_sub, Pi.sub_apply, truncOp_apply]
        simp only [ht, ↓reduceIte, sub_self]
      rw [this, norm_zero]
      have : 0 ≤ (CL L / L) * δ * ∑' a : ℤ, ‖(momUnitary L m y : Mom m → ℂ) (fib i j hij t a)‖ ^ 2 :=
        mul_nonneg (mul_nonneg hC hδ0) hT0
      simpa using this
    · have : (v : TIdx m i j → ℂ) t = (traceInv hij y : TIdx m i j → ℂ) t := by
        rw [hv, lp.coeFn_sub, Pi.sub_apply, truncOp_apply]
        simp only [ht, ↓reduceIte, sub_zero]
      rw [this]
      refine (traceInv_row hij y t).trans ?_
      have h1 : (CL L / L) * (Real.sqrt (colWeight L i j t))⁻¹ ≤ (CL L / L) * δ :=
        mul_le_mul_of_nonneg_left (hδ t ht) hC
      exact mul_le_mul_of_nonneg_right h1 hT0
  have hsum : Summable (fun t : TIdx m i j => ‖(v : TIdx m i j → ℂ) t‖ ^ 2) := summable_sq v
  calc ‖v‖ ^ 2 = ∑' t : TIdx m i j, ‖(v : TIdx m i j → ℂ) t‖ ^ 2 := norm_sq_eq_tsum v
    _ ≤ ∑' t : TIdx m i j, (CL L / L) * δ * ∑' a : ℤ,
          ‖(momUnitary L m y : Mom m → ℂ) (fib i j hij t a)‖ ^ 2 :=
        hsum.tsum_le_tsum hpt (hfs.mul_left _)
    _ = (CL L / L) * δ * ‖y‖ ^ 2 := by rw [tsum_mul_left, hft, hnorm]

/-- The box of output frequencies `|s|, |ℓ_r| ≤ N`. -/
def box (i j : Fin m) (N : ℕ) : Finset (TIdx m i j) :=
  (Finset.Icc (-(N : ℤ)) N) ×ˢ (Fintype.piFinset fun _ : Rest m i j => Finset.Icc (-(N : ℤ)) N)

theorem freq_sq_ge (n : ℤ) (N : ℕ) (h : (N : ℤ) < |n|) :
    (2 * Real.pi * ((N : ℝ) + 1) / L) ^ 2 ≤ freq L n ^ 2 := by
  have hL : 0 < L := Fact.out
  have h1 : (N : ℤ) + 1 ≤ |n| := h
  have h2 : (N : ℝ) + 1 ≤ |(n : ℝ)| := by
    have : (((N : ℤ) + 1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h1
    simpa using this
  unfold freq
  rw [← sq_abs (2 * Real.pi * (n : ℝ) / L), abs_div, abs_mul, abs_of_pos (by positivity :
    (0 : ℝ) < 2 * Real.pi), abs_of_pos (Fact.out : 0 < L)]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) (Fact.out : 0 < L).le

theorem box_tail (N : ℕ) (t : TIdx m i j) (ht : t ∉ box i j N) :
    (Real.sqrt (colWeight L i j t))⁻¹ ≤ L / (2 * Real.pi * ((N : ℝ) + 1)) := by
  have hL : 0 < L := Fact.out
  have hν : 0 ≤ ∑ r : Rest m i j, freq L (t.2 r) ^ 2 := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hbig : (2 * Real.pi * ((N : ℝ) + 1) / L) ^ 2 ≤ colWeight L i j t := by
    unfold box at ht
    simp only [Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc, not_and, not_forall,
      not_le] at ht
    by_cases h1 : -(N : ℤ) ≤ t.1 ∧ t.1 ≤ N
    · obtain ⟨r, hr⟩ := ht h1
      have hr' : (N : ℤ) < |t.2 r| := by
        rcases le_or_gt (-(N : ℤ)) (t.2 r) with h | h
        · have := hr h; exact lt_of_lt_of_le this (le_abs_self _)
        · rw [abs_of_neg (by omega)]; omega
      have := freq_sq_ge (L := L) (t.2 r) N hr'
      have hs := Finset.single_le_sum (f := fun r : Rest m i j => freq L (t.2 r) ^ 2)
        (fun r _ => sq_nonneg _) (Finset.mem_univ r)
      unfold colWeight
      nlinarith [sq_nonneg (freq L t.1)]
    · have hlt : (N : ℤ) < |t.1| := by
        rw [not_and_or] at h1
        rcases h1 with h | h
        · rw [abs_of_neg (by omega)]; omega
        · exact lt_of_lt_of_le (by omega) (le_abs_self _)
      have := freq_sq_ge (L := L) t.1 N hlt
      unfold colWeight
      nlinarith
  have hpos : 0 < 2 * Real.pi * ((N : ℝ) + 1) / L := by positivity
  have hsq : 2 * Real.pi * ((N : ℝ) + 1) / L ≤ Real.sqrt (colWeight L i j t) := by
    calc 2 * Real.pi * ((N : ℝ) + 1) / L
        = Real.sqrt ((2 * Real.pi * ((N : ℝ) + 1) / L) ^ 2) := (Real.sqrt_sq hpos.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt hbig
  calc (Real.sqrt (colWeight L i j t))⁻¹ ≤ (2 * Real.pi * ((N : ℝ) + 1) / L)⁻¹ :=
        inv_anti₀ hpos hsq
    _ = L / (2 * Real.pi * ((N : ℝ) + 1)) := inv_div _ _

/-- The approximation rate `B_N = √((C_L/L) · L/(2π(N+1)))`. -/
def Brate (L : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt ((CL L / L) * (L / (2 * Real.pi * ((N : ℝ) + 1))))

theorem Brate_tendsto : Filter.Tendsto (Brate L) Filter.atTop (nhds 0) := by
  have hL : 0 < L := Fact.out
  have h1 : Filter.Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Filter.Tendsto (fun N : ℕ => (CL L / L) * (L / (2 * Real.pi)) * (1 / ((N : ℝ) + 1)))
      Filter.atTop (nhds 0) := by simpa using h1.const_mul ((CL L / L) * (L / (2 * Real.pi)))
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h3
  refine h3.congr (fun N => ?_)
  simp only [Function.comp, Brate]
  congr 1
  field_simp

/-- Finite output truncation approximates `T_ij A_m^{-1/2}` in operator norm at rate `B_N`. -/
theorem traceInv_trunc_bound (hij : i ≠ j) (N : ℕ) :
    ‖(truncOp (box i j N)).comp (traceInv (L := L) hij) - traceInv hij‖ ≤ Brate L N := by
  classical
  have hL : 0 < L := Fact.out
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun y => ?_)
  have hδ0 : 0 ≤ L / (2 * Real.pi * ((N : ℝ) + 1)) := by positivity
  have h := traceInv_tail hij (box i j N) hδ0 (fun t ht => box_tail N t ht) y
  rw [sub_apply, norm_sub_rev]
  have hFy : ((truncOp (box i j N)).comp (traceInv (L := L) hij)) y =
      truncOp (box i j N) (traceInv hij y) := rfl
  rw [hFy]
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 ?_
  have hB2 : Brate L N ^ 2 = (CL L / L) * (L / (2 * Real.pi * ((N : ℝ) + 1))) :=
    Real.sq_sqrt (by have := CL_nonneg (L := L); positivity)
  unfold Brate at hB2
  rw [mul_pow, hB2]
  exact h

/-- **(b) `T_ij A_m^{-1/2} : L²(𝕋_L^m) → L²(𝕋_L^{m-1})` is compact** (norm limit of the finite-rank
output truncations, with the fibre estimate `eq:A1-discrete` giving the uniform tail bound). -/
theorem traceInv_isCompact (hij : i ≠ j) : IsCompactOperator (traceInv (L := L) hij) := by
  have hT : Filter.Tendsto (fun N : ℕ => (truncOp (box i j N)).comp (traceInv (L := L) hij))
      Filter.atTop (nhds (traceInv hij)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun N => norm_nonneg _) (traceInv_trunc_bound hij) Brate_tendsto
  exact isCompactOperator_of_tendsto hT (Filter.Eventually.of_forall fun N =>
    (isCompactOperator_truncOp (box i j N)).comp_clm (traceInv hij))

end Compactness

/-! ## Part 6: `B_ij` bounded `H¹ → H^{-1}` and `A^{-1/2} T* T A^{-1/2}` compact -/

section Contact

set_option linter.unusedSectionVars false

open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.CollisionTrace QuantumNLS.Fourier
  QuantumNLS.CollisionIdentification QuantumNLS.EnergyRealization QuantumNLS.PhysicalTensor

variable {L : ℝ} [Fact (0 < L)] {m : ℕ} {i j : Fin m}

theorem norm_unitary_symm (y : L2TN L m) : ‖(PhysH1.unitary (L := L) (k := m)).symm y‖ = ‖y‖ :=
  (PhysH1.unitary (L := L) (k := m)).symm.norm_map y

theorem traceInv_half_summable (hij : i ≠ j) (y : L2TN L m) :
    Summable fun t : TIdx m i j => Real.sqrt (colWeight L i j t) *
      ‖(traceInv hij y : TIdx m i j → ℂ) t‖ ^ 2 :=
  (trace_half_bound hij ((PhysH1.unitary (L := L) (k := m)).symm y)).1

theorem traceInv_half_tsum (hij : i ≠ j) (y : L2TN L m) :
    ∑' t : TIdx m i j, Real.sqrt (colWeight L i j t) *
      ‖(traceInv hij y : TIdx m i j → ℂ) t‖ ^ 2 ≤ (CL L / L) * ‖y‖ ^ 2 := by
  have h := (trace_half_bound hij ((PhysH1.unitary (L := L) (k := m)).symm y)).2
  rwa [norm_unitary_symm] at h

theorem memL2_half (hij : i ≠ j) (y : L2TN L m) :
    Memℓp (fun t : TIdx m i j => (((halfMult i j L).m t : ℝ) : ℂ) *
      (traceInv hij y : TIdx m i j → ℂ) t) 2 := by
  rw [memL2_iff]
  refine (traceInv_half_summable hij y).congr fun t => ?_
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, halfMult_sq]

/-- `Q = (1+λ_s²+|λ_ℓ|²)^{1/4} T_ij A_m^{-1/2} : L² → ℓ²`, bounded by `√(C_L/L)` (this is the
operator form of (a)). -/
def Qop (hij : i ≠ j) : L2TN L m →L[ℂ] L2 (TIdx m i j) :=
  LinearMap.mkContinuous
    { toFun := fun y => ⟨fun t => (((halfMult i j L).m t : ℝ) : ℂ) *
        (traceInv hij y : TIdx m i j → ℂ) t, memL2_half hij y⟩
      map_add' := fun x y => by
        apply Subtype.ext; funext t
        simp only [map_add, lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c x => by
        apply Subtype.ext; funext t
        simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    (Real.sqrt (CL L / L)) (fun y => by
      have hL : 0 < L := Fact.out
      refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
      rw [mul_pow, Real.sq_sqrt (div_nonneg CL_nonneg hL.le), norm_sq_eq_tsum]
      refine le_trans (le_of_eq ?_) (traceInv_half_tsum hij y)
      refine tsum_congr fun t => ?_
      show ‖(((halfMult i j L).m t : ℝ) : ℂ) * (traceInv hij y : TIdx m i j → ℂ) t‖ ^ 2 = _
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, halfMult_sq])

theorem Qop_apply (hij : i ≠ j) (y : L2TN L m) (t : TIdx m i j) :
    (Qop hij y : TIdx m i j → ℂ) t =
      (((halfMult i j L).m t : ℝ) : ℂ) * (traceInv hij y : TIdx m i j → ℂ) t := rfl

theorem norm_Qop_le (hij : i ≠ j) : ‖Qop (L := L) hij‖ ≤ Real.sqrt (CL L / L) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

omit [Fact (0 < L)] in
theorem abs_freq_le_sqrt_colWeight (t : TIdx m i j) :
    |freq L t.1| ≤ Real.sqrt (colWeight L i j t) := by
  have h : freq L t.1 ^ 2 ≤ colWeight L i j t := by
    unfold colWeight
    have : 0 ≤ ∑ r : Rest m i j, freq L (t.2 r) ^ 2 := Finset.sum_nonneg fun r _ => sq_nonneg _
    linarith
  exact Real.abs_le_sqrt h

/-- The common-coordinate derivative `D_ij` on the collision torus, normalized by the `H^{1/2}`
weight: the bounded multiplier `λ_s / (1+λ_s²+|λ_ℓ|²)^{1/2}` (`|·| ≤ 1`). -/
def Dnorm (i j : Fin m) (L : ℝ) : L2 (TIdx m i j) →L[ℂ] L2 (TIdx m i j) :=
  mulCLM (fun t => freq L t.1 / Real.sqrt (colWeight L i j t)) 1 zero_le_one (fun t => by
    have hs : 0 < Real.sqrt (colWeight L i j t) :=
      Real.sqrt_pos.2 (by linarith [one_le_colWeight L i j t])
    rw [abs_div, abs_of_pos hs, div_le_one hs]
    exact abs_freq_le_sqrt_colWeight t)

/-- **The sandwiched contact form** `A_m^{-1/2} B_ij A_m^{-1/2} = Q* D_norm Q`, a bounded operator
on `L²(𝕋_L^m)` — the operator form of "`B_ij : H¹ → H^{-1}` bounded". -/
def Bsand (hij : i ≠ j) : L2TN L m →L[ℂ] L2TN L m :=
  (ContinuousLinearMap.adjoint (Qop hij)) ∘L (Dnorm i j L) ∘L (Qop hij)

theorem norm_Bsand_le (hij : i ≠ j) : ‖Bsand (L := L) hij‖ ≤ CL L / L := by
  have hL : 0 < L := Fact.out
  have h1 : ‖Dnorm i j L‖ ≤ 1 := by
    unfold Dnorm mulCLM
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hQ := norm_Qop_le (L := L) (i := i) (j := j) hij
  have hQ0 := norm_nonneg (Qop (L := L) hij)
  calc ‖Bsand hij‖ ≤ ‖ContinuousLinearMap.adjoint (Qop hij)‖ * ‖Dnorm i j L‖ * ‖Qop hij‖ := by
        unfold Bsand
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Qop (L := L) hij‖ * 1 * ‖Qop hij‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        gcongr
    _ ≤ Real.sqrt (CL L / L) * 1 * Real.sqrt (CL L / L) := by gcongr
    _ = CL L / L := by
        rw [mul_one, Real.mul_self_sqrt (div_nonneg CL_nonneg hL.le)]

/-- `⟨Bsand x, y⟩ = Σ_{(s,ℓ)} conj((T A^{-1/2}x)(s,ℓ)) · λ_s · (T A^{-1/2}y)(s,ℓ)`: the form
`b_ij(f,g) = ⟨T_ij f, D_ij T_ij g⟩` with `D_ij` the common-coordinate derivative. -/
theorem Bsand_inner (hij : i ≠ j) (x y : L2TN L m) :
    ⟪Bsand hij x, y⟫_ℂ = ∑' t : TIdx m i j, conj ((traceInv hij x : TIdx m i j → ℂ) t) *
      (((freq L t.1 : ℝ) : ℂ) * (traceInv hij y : TIdx m i j → ℂ) t) := by
  show ⟪(ContinuousLinearMap.adjoint (Qop hij)) (Dnorm i j L (Qop hij x)), y⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_left, inner_eq_tsum']
  refine tsum_congr fun t => ?_
  have hs : 0 < Real.sqrt (colWeight L i j t) :=
    Real.sqrt_pos.2 (by linarith [one_le_colWeight L i j t])
  have hm : ((halfMult i j L).m t) ^ 2 = Real.sqrt (colWeight L i j t) := halfMult_sq i j t
  show conj ((((freq L t.1 / Real.sqrt (colWeight L i j t) : ℝ)) : ℂ) *
      ((((halfMult i j L).m t : ℝ) : ℂ) * (traceInv hij x : TIdx m i j → ℂ) t)) *
      ((((halfMult i j L).m t : ℝ) : ℂ) * (traceInv hij y : TIdx m i j → ℂ) t) = _
  simp only [map_mul, Complex.conj_ofReal]
  have hc : ((((halfMult i j L).m t : ℝ) : ℂ)) ^ 2 = ((Real.sqrt (colWeight L i j t) : ℝ) : ℂ) := by
    exact_mod_cast hm
  have hs' : ((Real.sqrt (colWeight L i j t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp
  linear_combination (conj ((traceInv hij x : TIdx m i j → ℂ) t) * ((freq L t.1 : ℝ) : ℂ) *
    (traceInv hij y : TIdx m i j → ℂ) t) * hc

theorem Bsand_symm (hij : i ≠ j) (x y : L2TN L m) : ⟪Bsand hij x, y⟫_ℂ = ⟪x, Bsand hij y⟫_ℂ := by
  show ⟪(ContinuousLinearMap.adjoint (Qop hij)) (Dnorm i j L (Qop hij x)), y⟫_ℂ =
    ⟪x, (ContinuousLinearMap.adjoint (Qop hij)) (Dnorm i j L (Qop hij y))⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  exact inner_mulCLM _ _ _ _ _ _

theorem Bsand_isSelfAdjoint (hij : i ≠ j) : IsSelfAdjoint (Bsand (L := L) hij) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 (fun x y => Bsand_symm hij x y)

/-- The contact form `b_ij(f,g) = ⟨T_ij f, D_ij T_ij g⟩` on `H¹`, through the Fourier coefficients
of the constructed trace (the duality `H^{1/2} × H^{-1/2}`). -/
def bform (hij : i ≠ j) (f g : PhysH1 L m) : ℂ :=
  ∑' t : TIdx m i j, conj ((traceCLM i j hij f : TIdx m i j → ℂ) t) *
    (((freq L t.1 : ℝ) : ℂ) * (traceCLM i j hij g : TIdx m i j → ℂ) t)

theorem bform_eq (hij : i ≠ j) (f g : PhysH1 L m) :
    bform hij f g = ⟪Bsand hij (PhysH1.unitary f), PhysH1.unitary g⟫_ℂ := by
  rw [Bsand_inner]
  unfold bform
  simp only [traceInv_apply, LinearIsometryEquiv.symm_apply_apply]

/-- **(c) `B_ij` is bounded `H¹ → H^{-1}`**: `|b_ij(f,g)| ≤ (C_L/L) ‖f‖_{H¹} ‖g‖_{H¹}`. -/
theorem bform_bound (hij : i ≠ j) (f g : PhysH1 L m) :
    ‖bform hij f g‖ ≤ (CL L / L) * ‖f‖ * ‖g‖ := by
  rw [bform_eq]
  calc ‖⟪Bsand hij (PhysH1.unitary f), PhysH1.unitary g⟫_ℂ‖
      ≤ ‖Bsand hij (PhysH1.unitary f)‖ * ‖PhysH1.unitary g‖ := norm_inner_le_norm _ _
    _ ≤ (‖Bsand hij‖ * ‖PhysH1.unitary f‖) * ‖PhysH1.unitary g‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ((CL L / L) * ‖PhysH1.unitary f‖) * ‖PhysH1.unitary g‖ := by
        gcongr
        exact norm_Bsand_le hij
    _ = (CL L / L) * ‖f‖ * ‖g‖ := by
        rw [(PhysH1.unitary (L := L) (k := m)).norm_map f, (PhysH1.unitary (L := L) (k := m)).norm_map g]

/-- The form is Hermitian. -/
theorem bform_conj (hij : i ≠ j) (f g : PhysH1 L m) :
    conj (bform hij f g) = bform hij g f := by
  rw [bform_eq, bform_eq, inner_conj_symm, ← Bsand_symm]

/-- The sandwiched trace `S = T_ij A_m^{-1/2} : L²(𝕋_L^m) → L²(dy_ij)`, with the frozen physical
trace `productTrace` and the actual coordinate measure `dy_ij`. -/
def Sop (hij : i ≠ j) : L2TN L m →L[ℂ] CollisionProductL2 (L := L) i j :=
  (productTrace i j hij).comp
    ((PhysH1.unitary (L := L) (k := m)).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- **(b), physical form:** `T_ij A_m^{-1/2} : L²(𝕋_L^m) → L²(dy_ij)` is compact. -/
theorem Sop_isCompact (hij : i ≠ j) : IsCompactOperator (Sop (L := L) hij) := by
  have h := (traceInv_isCompact (L := L) hij).clm_comp
    ((collisionProductUnitary (L := L) i j).toContinuousLinearEquiv.toContinuousLinearMap)
  exact h

/-- **(c) `A_m^{-1/2} T_ij^* T_ij A_m^{-1/2} = S^* S` is compact.** -/
theorem sandwich_isCompact (hij : i ≠ j) :
    IsCompactOperator (ContinuousLinearMap.adjoint (Sop (L := L) hij) ∘L Sop hij) :=
  (Sop_isCompact hij).clm_comp (ContinuousLinearMap.adjoint (Sop (L := L) hij))

/-- `⟨x, S^*S y⟩ = ⟨T_ij A^{-1/2}x, T_ij A^{-1/2}y⟩_{L²(dy_ij)}`, the contact pairing of the frozen
form `ContactForm.q` (`productTrace_inner`). -/
theorem sandwich_inner (hij : i ≠ j) (x y : L2TN L m) :
    ⟪x, (ContinuousLinearMap.adjoint (Sop (L := L) hij) ∘L Sop hij) y⟫_ℂ =
      ⟪traceCLM i j hij ((PhysH1.unitary (L := L) (k := m)).symm x),
        traceCLM i j hij ((PhysH1.unitary (L := L) (k := m)).symm y)⟫_ℂ := by
  show ⟪x, (ContinuousLinearMap.adjoint (Sop hij)) (Sop hij y)⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact productTrace_inner i j hij _ _

open scoped Classical in
theorem adjoint_truncOp {ι : Type*} (U : Finset ι) :
    ContinuousLinearMap.adjoint (truncOp U) = truncOp U := by
  unfold truncOp
  exact (mulCLM_isSelfAdjoint _ _ _ _).adjoint_eq

/-- The adjoint `S^* = (T_ij A_m^{-1/2})^*` is compact as well (norm limit of the adjoints of the
finite-rank truncations; used instead of Schauder's theorem, which is not in the pinned mathlib). -/
theorem Sop_adjoint_isCompact (hij : i ≠ j) :
    IsCompactOperator (ContinuousLinearMap.adjoint (Sop (L := L) hij)) := by
  classical
  set U : L2 (TIdx m i j) →L[ℂ] CollisionProductL2 (L := L) i j :=
    (collisionProductUnitary (L := L) i j).toContinuousLinearEquiv.toContinuousLinearMap with hU
  set G : ℕ → (L2TN L m →L[ℂ] CollisionProductL2 (L := L) i j) :=
    fun N => U.comp ((truncOp (box i j N)).comp (traceInv hij)) with hG
  have hS : Sop (L := L) hij = U.comp (traceInv hij) := rfl
  have hbound : ∀ N, ‖G N - Sop hij‖ ≤ Brate L N := by
    intro N
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun y => ?_)
    have h := (traceInv_trunc_bound (L := L) hij N)
    set D : L2TN L m →L[ℂ] L2 (TIdx m i j) :=
      (truncOp (box i j N)).comp (traceInv (L := L) hij) - traceInv hij with hD
    have e : (G N - Sop hij : L2TN L m →L[ℂ] CollisionProductL2 (L := L) i j) y = U (D y) := by
      rw [hS, sub_apply, hD, sub_apply]
      simp only [hG, ContinuousLinearMap.comp_apply, map_sub]
    rw [e]
    have : ‖U (D y)‖ = ‖D y‖ := (collisionProductUnitary (L := L) i j).norm_map _
    rw [this]
    exact (ContinuousLinearMap.le_opNorm D y).trans (mul_le_mul_of_nonneg_right h (norm_nonneg y))
  have hT : Filter.Tendsto (fun N : ℕ => ContinuousLinearMap.adjoint (G N)) Filter.atTop
      (nhds (ContinuousLinearMap.adjoint (Sop hij))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (Brate_tendsto (L := L))
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
    exact hbound N
  refine isCompactOperator_of_tendsto hT (Filter.Eventually.of_forall fun N => ?_)
  have e : ContinuousLinearMap.adjoint (G N) =
      (ContinuousLinearMap.adjoint (traceInv (L := L) hij)).comp
        ((truncOp (box i j N)).comp (ContinuousLinearMap.adjoint U)) := by
    simp only [hG, ContinuousLinearMap.adjoint_comp, adjoint_truncOp]
    rfl
  rw [e]
  exact ((isCompactOperator_truncOp (box i j N)).comp_clm (ContinuousLinearMap.adjoint U)).clm_comp
    (ContinuousLinearMap.adjoint (traceInv (L := L) hij))

/-- **The assembly step of the commutator clause** (`eq:A1-compact-comm`): once the smoothing-trace
bounds make `V = D_ij T_ij (J⊗Id) A^{-1/2}` and `V' = D_ij T_ij (J^*⊗Id) A^{-1/2}` bounded
`L² → L²(dy_ij)`, the sandwiched commutator `S^* V − V'^* S` (`S = T_ij A^{-1/2}` compact) is
compact, being (compact)∘(bounded) minus (bounded)∘(compact).  The boundedness of `V, V'` is NOT
proved here (see the module docstring). -/
theorem commutator_sandwich_isCompact (hij : i ≠ j)
    (V V' : L2TN L m →L[ℂ] CollisionProductL2 (L := L) i j) :
    IsCompactOperator (ContinuousLinearMap.adjoint (Sop (L := L) hij) ∘L V -
      ContinuousLinearMap.adjoint V' ∘L Sop hij) := by
  have h1 : IsCompactOperator (ContinuousLinearMap.adjoint (Sop (L := L) hij) ∘L V) :=
    (Sop_adjoint_isCompact hij).comp_clm V
  have h2 : IsCompactOperator (ContinuousLinearMap.adjoint V' ∘L Sop (L := L) hij) :=
    (Sop_isCompact hij).clm_comp (ContinuousLinearMap.adjoint V')
  exact h1.sub h2

end Contact


/-! Kernel axiom audit. -/
#print axioms integral_inv_sq
#print axioms lattice_finite
#print axioms lattice_weight
#print axioms kinWeight_fib_square
#print axioms fibre_kernel
#print axioms row_bound
#print axioms fibre_total
#print axioms trace_half_bound
#print axioms traceHalf
#print axioms norm_traceHalf_le
#print axioms productTrace_half
#print axioms traceInv_row
#print axioms isCompactOperator_truncOp
#print axioms traceInv_tail
#print axioms box_tail
#print axioms traceInv_trunc_bound
#print axioms traceInv_isCompact
#print axioms norm_Bsand_le
#print axioms Bsand_inner
#print axioms Bsand_isSelfAdjoint
#print axioms bform_eq
#print axioms bform_bound
#print axioms bform_conj
#print axioms Sop_isCompact
#print axioms sandwich_isCompact
#print axioms sandwich_inner
#print axioms Sop_adjoint_isCompact
#print axioms commutator_sandwich_isCompact

end QuantumNLS.EnergyContactTrace
