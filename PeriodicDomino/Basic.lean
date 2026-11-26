module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.Reduce

@[expose] public section

namespace PeriodicDomino.Wang

/-- A Wang tile with four edge colors. -/
structure Tile where
  W : ℕ
  N : ℕ
  S : ℕ
  E : ℕ
  deriving DecidableEq

/-- The source tile's four edge colors, in W/N/S/E order. -/
def Tile.codeEquiv : Tile ≃ ℕ × ℕ × ℕ × ℕ where
  toFun t := (t.W, t.N, t.S, t.E)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Denumerable Tile := Denumerable.ofEquiv _ Tile.codeEquiv

/-- Edge-matching on the integer plane with at least one nonzero translation period. -/
def HasPeriodicTiling (s : Finset Tile) : Prop :=
  ∃ f : ℤ → ℤ → Tile,
    (∀ row col, (f row col).S = (f (row + 1) col).N) ∧
    (∀ row col, (f row col).E = (f row (col + 1)).W) ∧
    (∀ row col, f row col ∈ s) ∧
    ∃ row_period col_period : ℤ, (row_period ≠ 0 ∨ col_period ≠ 0) ∧ ∀ row col, f (row + row_period) (col + col_period) = f row col

end PeriodicDomino.Wang
