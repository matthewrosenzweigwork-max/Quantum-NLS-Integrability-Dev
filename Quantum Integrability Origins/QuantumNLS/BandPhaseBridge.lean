import QuantumNLS.MonotoneIndexedMasses

/-!
The real-analysis/algebra step in ROOT_indexed_masses.tex:46-82.
The half-integer level is a zero of the real discriminant by the boundary
cosine identity. Continuity places a neighborhood in an open band, and a
positive derivative gives local strict increase. No separator uniqueness or
global strict increase is an input. Source phase facts are explicit here;
this module does not construct the quantum measure or the boundary phase.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.BandPhaseBridge
open QuantumNLS.MonotoneIndexedMasses

/-- A half-integer phase level has zero real cosine. -/
theorem cos_level (n : ℤ) : Real.cos (level n) = 0 := by
  have he : level n = Real.pi / 2 + (n : ℝ) * Real.pi := by
    dsimp [level, QuantumNLS.IndexedMasses.level]; ring
  rw [he, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero]

/-- Only the real part of the boundary cosine identity is needed here. -/
theorem real_cosine (z : ℂ) :
    (2 * Complex.cos z).re = 2 * Real.cos z.re * Real.cosh z.im := by
  rw [Complex.cos_eq]
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, Complex.sinh_ofReal_re,
    Complex.sinh_ofReal_im, mul_assoc]

/-- Every half-level of the boundary phase is a zero of the discriminant. -/
theorem half_level_zero {γ : ℝ → ℂ} {Δ : ℝ → ℝ}
    (hcos : ∀ x, (2 * Complex.cos (γ x)).re = Δ x)
    {n : ℤ} {x : ℝ} (hx : (γ x).re = level n) : Δ x = 0 := by
  rw [← hcos x, real_cosine, hx, cos_level]
  ring

/-- Open bands provide the strict neighborhoods required by the faithful interface. -/
theorem locallyStrictAtLevels {γ : ℝ → ℂ} {Δ : ℝ → ℝ}
    (hc : Continuous fun x => (γ x).re) (hd : Continuous Δ)
    (hcos : ∀ x, (2 * Complex.cos (γ x)).re = Δ x)
    (hpos : ∀ x, |Δ x| < 2 → 0 < deriv (fun y => (γ y).re) x) :
    LocallyStrictAtLevels (fun x => (γ x).re) := by
  intro n x hx
  have hz := half_level_zero hcos hx
  have hopen : IsOpen {y | |Δ y| < 2} := isOpen_lt hd.abs continuous_const
  have hxband : x ∈ {y | |Δ y| < 2} := by simp [hz]
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hxband)
  refine ⟨a, b, hax, hxb, strictMonoOn_of_deriv_pos (convex_Ioo a b) hc.continuousOn ?_⟩
  intro y hy
  exact hpos y (hab (interior_subset hy))

/-- Faithful phase from the source's nondecreasing, onto and band derivative facts. -/
def phase (γ : ℝ → ℂ) (Δ : ℝ → ℝ)
    (hm : Monotone fun x => (γ x).re) (hc : Continuous fun x => (γ x).re)
    (ho : Function.Surjective fun x => (γ x).re) (hd : Continuous Δ)
    (hcos : ∀ x, (2 * Complex.cos (γ x)).re = Δ x)
    (hpos : ∀ x, |Δ x| < 2 → 0 < deriv (fun y => (γ y).re) x) : BoundaryPhase :=
  ofLocal (fun x => (γ x).re) hm hc ho (locallyStrictAtLevels hc hd hcos hpos)

/-- A nonempty flat open gap contradicts the old global StrictMono requirement. -/
theorem not_strictMono_of_gap {φ : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hflat : ∀ x ∈ Ioo a b, φ x = c) : ¬StrictMono φ := by
  intro hs
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  obtain ⟨y, hxy, hyb⟩ := exists_between hxb
  have h := hs hxy
  rw [hflat x ⟨hax, hxb⟩, hflat y ⟨hax.trans hxy, hyb⟩] at h
  exact lt_irrefl c h

/-- A gap containing a separator would force an integer to equal a half-integer. -/
theorem level_ne_integer_pi (n k : ℤ) : level n ≠ (k : ℝ) * Real.pi := by
  intro h
  have he : (n : ℝ) + 1 / 2 = (k : ℝ) := by
    apply (mul_right_cancel₀ Real.pi_ne_zero)
    exact h
  have he' : (2 * n + 1 : ℤ) = 2 * k := by
    exact_mod_cast (show 2 * (n : ℝ) + 1 = 2 * (k : ℝ) by linarith)
  omega

/-- The source's integer-valued gap constancy excludes all separator levels there. -/
theorem no_half_level_on_gap {φ : ℝ → ℝ} {a b : ℝ} {k : ℤ}
    (hgap : ∀ x ∈ Ioo a b, φ x = (k : ℝ) * Real.pi) (n : ℤ)
    {x : ℝ} (hx : x ∈ Ioo a b) : φ x ≠ level n := by
  rw [hgap x hx]
  exact (level_ne_integer_pi n k).symm

end QuantumNLS.BandPhaseBridge

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.BandPhaseBridge.cos_level
#print axioms QuantumNLS.BandPhaseBridge.real_cosine
#print axioms QuantumNLS.BandPhaseBridge.half_level_zero
#print axioms QuantumNLS.BandPhaseBridge.locallyStrictAtLevels
#print axioms QuantumNLS.BandPhaseBridge.phase
#print axioms QuantumNLS.BandPhaseBridge.not_strictMono_of_gap
#print axioms QuantumNLS.BandPhaseBridge.level_ne_integer_pi
#print axioms QuantumNLS.BandPhaseBridge.no_half_level_on_gap

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.BandPhaseBridge." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
