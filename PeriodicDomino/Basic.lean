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

/-- An allowed unordered pair of west and north colors. -/
def Compatible (s : Finset Tile) (a b : ℕ) : Prop :=
  ∃ t ∈ s, (t.W = a ∧ t.N = b) ∨ (t.W = b ∧ t.N = a)

def NWDeterministic (s : Finset Tile) : Prop :=
  ∀ t ∈ s, ∀ u ∈ s, t.N = u.N → t.W = u.W → t = u

def NWCommutative (s : Finset Tile) : Prop :=
  ∀ t ∈ s, Tile.mk t.N t.W t.S t.E ∈ s

def SEIdentical (s : Finset Tile) : Prop := ∀ t ∈ s, t.S = t.E

/-- With E=S as output, replacing either input by that output disables the pair. -/
def SelfDisabling (s : Finset Tile) : Prop :=
  ∀ t ∈ s, ¬ Compatible s t.W t.E ∧ ¬ Compatible s t.N t.E

/-- After two linked tiles, neither original input may pair with the final output. -/
def GrandparentExclusion (s : Finset Tile) : Prop :=
  ∀ t ∈ s, ∀ u ∈ s, (t.E = u.W ∨ t.E = u.N) → ¬ Compatible s t.W u.E ∧ ¬ Compatible s t.N u.E

end PeriodicDomino.Wang
