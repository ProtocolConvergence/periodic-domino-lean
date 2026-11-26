module

public import PeriodicDomino.Basic

public section

namespace PeriodicDomino.Wang

theorem undecidable : ¬ ComputablePred HasPeriodicTiling := by
  sorry

/-- No total computable test agrees with periodic tilability on all promised inputs. -/
abbrev UndecidableOn (promise : Finset Tile → Prop) : Prop :=
  ¬ ∃ P : Finset Tile → Prop, ComputablePred P ∧
    ∀ s, promise s → (P s ↔ HasPeriodicTiling s)

theorem restricted_undecidable :
    UndecidableOn (fun s =>
      NWDeterministic s ∧ NWCommutative s ∧ SEIdentical s ∧
      SelfDisabling s ∧ GrandparentExclusion s) := by
  sorry

theorem nw_deterministic_undecidable : UndecidableOn NWDeterministic := by
  sorry

theorem nw_commutative_undecidable : UndecidableOn NWCommutative := by
  sorry

theorem se_identical_undecidable : UndecidableOn SEIdentical := by
  sorry

theorem self_disabling_undecidable : UndecidableOn SelfDisabling := by
  sorry

theorem grandparent_exclusion_undecidable : UndecidableOn GrandparentExclusion := by
  sorry

end PeriodicDomino.Wang
