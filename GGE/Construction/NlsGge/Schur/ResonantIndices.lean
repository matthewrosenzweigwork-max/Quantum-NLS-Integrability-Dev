import Mathlib.Data.Int.Basic
import Mathlib.Logic.Equiv.Defs
import Lean.Elab.Tactic.Omega

/-!
# Indices for one periodic or antiperiodic spectral sector

The sector contains all integer modes of the parity of `n`, including negative
modes and the zero mode when `n` is even. Reflection is the source index `2*n-m`.
This file concerns index arithmetic; it does not construct spectral operators.
-/

set_option autoImplicit false

namespace NlsGge.Schur

/-- The integer modes satisfying the boundary condition of spectral index `n`. -/
abbrev Sector (n : ℤ) := {m : ℤ // m % 2 = n % 2}

/-- The resonant integer in its own parity sector. -/
def resonantIndex (n : ℤ) : Sector n := ⟨n, rfl⟩

/-- Both positive and negative translates by an even integer remain in the sector. -/
def sectorIndex (n k : ℤ) : Sector n := ⟨n + 2 * k, by omega⟩

/-- Every mode in the parity sector has the unique form `n + 2*k`. -/
theorem sectorIndex_covers (n : ℤ) (m : Sector n) :
    ∃ k : ℤ, sectorIndex n k = m := by
  refine ⟨(m.val - n) / 2, ?_⟩
  apply Subtype.ext
  have hm := m.property
  dsimp [sectorIndex]
  omega

theorem sectorIndex_injective (n : ℤ) : Function.Injective (sectorIndex n) := by
  intro k l h
  have hv := congrArg Subtype.val h
  dsimp [sectorIndex] at hv
  omega

/-- Index reflection from the upper-potential own-mode multiplication. -/
def reflectIndex (n : ℤ) (m : Sector n) : Sector n :=
  ⟨2 * n - m.val, by have hm := m.property; omega⟩

@[simp] theorem reflectIndex_val (n : ℤ) (m : Sector n) :
    (reflectIndex n m).val = 2 * n - m.val := rfl

@[simp] theorem reflectIndex_resonant (n : ℤ) :
    reflectIndex n (resonantIndex n) = resonantIndex n := by
  apply Subtype.ext
  dsimp [reflectIndex, resonantIndex]
  omega

@[simp] theorem reflectIndex_involutive (n : ℤ) (m : Sector n) :
    reflectIndex n (reflectIndex n m) = m := by
  apply Subtype.ext
  dsimp [reflectIndex]
  omega

@[simp] theorem reflectIndex_eq_resonant (n : ℤ) (m : Sector n) :
    reflectIndex n m = resonantIndex n ↔ m = resonantIndex n := by
  constructor
  · intro h
    have hh := congrArg (reflectIndex n) h
    simpa using hh
  · rintro rfl
    exact reflectIndex_resonant n

/-- Reflected translates are `n - 2*k`, without an absolute-value convention. -/
theorem reflectIndex_sectorIndex (n k : ℤ) :
    reflectIndex n (sectorIndex n k) = sectorIndex n (-k) := by
  apply Subtype.ext
  dsimp [reflectIndex, sectorIndex]
  omega

/-- Reflection preserves the complementary indices. -/
theorem reflectIndex_ne_resonant (n : ℤ) (m : Sector n)
    (hm : m ≠ resonantIndex n) : reflectIndex n m ≠ resonantIndex n := by
  simpa using hm

/-- The zero mode belongs exactly to the even sectors. -/
theorem zero_in_sector_iff (n : ℤ) : (0 : ℤ) % 2 = n % 2 ↔ n % 2 = 0 := by
  omega

/-- A permutation of the actual parity-sector indices, for Hilbert-space reindexing. -/
def reflectEquiv (n : ℤ) : Sector n ≃ Sector n where
  toFun := reflectIndex n
  invFun := reflectIndex n
  left_inv := reflectIndex_involutive n
  right_inv := reflectIndex_involutive n

end NlsGge.Schur
