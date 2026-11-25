import QuantumNLS.LocalWellPosednessFull

/-! integrator-authored trusted spec for R-501CA032 `F04:lem-local` (foundations/F04.tex:130-145, with the
F04 setup lines 14-30: L > 0, κ ≥ 0, i∂_t u = −∂_x²u + 2κ|u|²u, p_n = 2πn/L, H^s on the Fourier side with
‖f‖² = Σ (1+p_n²)^s |f̂(n)|², S(t) = e^{it∂²} i.e. (S(t)a)_n = e^{−itp_n²} a_n, F(u) = |u|²u, mild =
F04:eq-duhamel u(t) = S(t)u₀ − 2iκ ∫₀ᵗ S(t−r)F(u(r)) dr).
The spec pins S, F, −∂_x² and H^s ↪ H^{s−2} by their Fourier coefficients (F via the accepted R-00E786F0
`nlRep` = |u|²u of the series representative), writes the mild-solution condition literally, and states:
(1) for s ≥ 1 and u₀ ∈ H^s a local mild solution exists (on [−τ,τ], τ > 0) and mild solutions are unique;
(2) a mild solution is C¹ into H^{s−2} at interior times with derivative G, i·G = −∂²u + 2κ|u|²u in H^{s−2};
(3) there is a unique maximal open interval containing 0 carrying a mild solution, and at a finite endpoint
    the H^s norm is unbounded;
(4) every C_tH¹ distributional solution (tested against φ(t)·conj(e_n), φ ∈ C_c^∞(I) real — the Fourier-mode
    reading, Terra r90) is mild from each of its times, satisfies F04:eq-stability and is unique. -/

open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull
open scoped ContDiff

namespace QuantumNLS.R501Spec

variable {L : ℝ} [Fact (0 < L)]

def Spec (L : ℝ) [Fact (0 < L)] : Prop :=
  -- pinning of the objects by Fourier coefficients
  (∀ (s t : ℝ) (a : h04 L s) (n : ℤ),
      (Sgrp (L := L) s t a).val n = Complex.exp (-(Complex.I * ((t * (2 * Real.pi * n / L) ^ 2 : ℝ) : ℂ))) * a.val n) ∧
  (∀ (s : ℝ) (hs : 1 ≤ s) (a : h04 L s), (Fh hs a).val = coeff L (nlRep L a.val)) ∧
  (∀ (s : ℝ) (a : h04 L s) (n : ℤ), (lapOp (L := L) s a).val n = (((2 * Real.pi * n / L) ^ 2 : ℝ) : ℂ) * a.val n) ∧
  (∀ (s : ℝ) (a : h04 L s) (n : ℤ), (ι2 (L := L) s a).val n = a.val n) ∧
  -- the mild-solution condition is literally F04:eq-duhamel on an interval containing 0
  (∀ (s : ℝ) (hs : 1 ≤ s) (κ : ℝ) (I : Set ℝ) (u0 : h04 L s) (u : ℝ → h04 L s),
    IsMild hs κ I u0 u ↔ ((0 : ℝ) ∈ I ∧ I.OrdConnected ∧ ContinuousOn u I ∧
      ∀ t ∈ I, u t = Sgrp s t u0 - (2 * Complex.I * κ) • ∫ r in (0 : ℝ)..t, Sgrp s (t - r) (Fh hs (u r)))) ∧
  -- (1) local existence and uniqueness
  (∀ (s : ℝ) (hs : 1 ≤ s) (κ : ℝ), 0 ≤ κ → ∀ u0 : h04 L s,
    (∃ τ : ℝ, 0 < τ ∧ ∃ u, IsMild hs κ (Set.Icc (-τ) τ) u0 u) ∧
    ∀ (I : Set ℝ) (u v : ℝ → h04 L s), IsMild hs κ I u0 u → IsMild hs κ I u0 v → ∀ t ∈ I, u t = v t) ∧
  -- (2) C¹ into H^{s−2} at interior times, and the equation there
  (∀ (s : ℝ) (hs : 1 ≤ s) (κ : ℝ) (I : Set ℝ) (u0 : h04 L s) (u : ℝ → h04 L s), IsMild hs κ I u0 u →
    ContinuousOn (fun t => Gder hs κ (u t)) I ∧
    ∀ t ∈ interior I, HasDerivAt (fun t => ι2 s (u t)) (Gder hs κ (u t)) t ∧
      Complex.I • Gder hs κ (u t) = lapOp s (u t) + ((2 * κ : ℝ) : ℂ) • ι2 s (Fh hs (u t))) ∧
  -- (3) maximal interval and blow-up alternative
  (∀ (s : ℝ) (hs : 1 ≤ s) (κ : ℝ), 0 ≤ κ → ∀ u0 : h04 L s,
    (∃! I : Set ℝ, IsOpen I ∧ I.OrdConnected ∧ (0 : ℝ) ∈ I ∧ (∃ u, IsMild hs κ I u0 u) ∧
      ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → (∃ v, IsMild hs κ J u0 v) → J ⊆ I) ∧
    (BddAbove (Imax hs κ u0) → ∀ M δ : ℝ, 0 < δ → ∃ t ∈ Imax hs κ u0,
      sSup (Imax hs κ u0) - δ < t ∧ M < ‖umax hs κ u0 t‖) ∧
    (BddBelow (Imax hs κ u0) → ∀ M δ : ℝ, 0 < δ → ∃ t ∈ Imax hs κ u0,
      t < sInf (Imax hs κ u0) + δ ∧ M < ‖umax hs κ u0 t‖) ∧
    IsMild hs κ (Imax hs κ u0) u0 (umax hs κ u0)) ∧
  -- (4) C_tH¹ distributional solutions
  (∀ (κ : ℝ) (I : Set ℝ) (u : ℝ → h04 L 1),
    (IsDistSol κ I u ↔ (IsOpen I ∧ I.OrdConnected ∧ ContinuousOn u I ∧
      ∀ n : ℤ, ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ I) →
        -Complex.I * ∫ t, deriv φ t • (u t).val n =
          ∫ t, φ t • ((((2 * Real.pi * n / L) ^ 2 : ℝ) : ℂ) * (u t).val n +
            ((2 * κ : ℝ) : ℂ) * (Fh (le_refl (1 : ℝ)) (u t)).val n)))) ∧
  (∀ (κ : ℝ), 0 ≤ κ → ∀ (I : Set ℝ) (u v : ℝ → h04 L 1), IsDistSol κ I u → IsDistSol κ I v →
    ((0 : ℝ) ∈ I → IsMild (le_refl (1 : ℝ)) κ I (u 0) u) ∧
    (∀ K : ℝ, (∀ r ∈ I, ‖u r‖ ≤ K ∧ ‖v r‖ ≤ K) → ∀ t0 ∈ I, ∀ t ∈ I,
      ‖u t - v t‖ ≤ Real.exp (4 * κ * Cs L 1 * K ^ 2 * |t - t0|) * ‖u t0 - v t0‖) ∧
    (∀ t0 ∈ I, u t0 = v t0 → ∀ t ∈ I, u t = v t))

theorem spec : Spec L := by
  refine ⟨fun s t a n => rfl, fun s hs a => rfl, fun s a n => rfl, fun s a n => ?_,
    fun s hs κ I u0 u => ⟨fun h => ⟨h.zero_mem, h.ordConnected, h.cont, h.duhamel_eq⟩,
      fun ⟨h0, hc, hu, hd⟩ => ⟨h0, hc, hu, hd⟩⟩,
    fun s hs κ hκ u0 => ⟨?_, fun I u v hu hv => mild_unique hs hκ hu hv⟩,
    fun s hs κ I u0 u hu => ?_,
    fun s hs κ hκ u0 => ⟨maximal_interval (hs := hs) hκ u0, blowup_right (hs := hs) hκ u0,
      blowup_left (hs := hs) hκ u0, umax_mild hκ u0⟩,
    fun κ I u => ⟨fun h => ⟨h.isOpen, h.ordConnected, h.cont, h.weak⟩,
      fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩,
    fun κ hκ I u v hu hv => ⟨fun h0 => dist_isMild hu h0,
      fun K hK t0 ht0 t ht => dist_stability hκ hu hv hK ht0 ht,
      fun t0 ht0 h => dist_unique hκ hu hv ht0 h⟩⟩
  · simp [ι2, h04_mono, incl_val]
  · obtain ⟨hτ, u, hu, -⟩ := local_existence hs hκ u0
    exact ⟨_, hτ, u, hu⟩
  · obtain ⟨h1, -, -, h4, h5⟩ := mild_C1 hu
    exact ⟨h1, fun t ht => ⟨h4 t ht, h5 t (interior_subset ht)⟩⟩

end QuantumNLS.R501Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R501Spec.spec
  IO.println s!"R501Spec.spec axioms: {ax}"
