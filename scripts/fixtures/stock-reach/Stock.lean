/-! Shared declarations of the stock-reach fixtures: a vote binding, its `stock` value, a setup
carrying it, the root `fixture_root` and the listed (stock-only) declaration `stock_helper`. -/

namespace Fx

structure VoteBinding where
  k : Nat

def stock : VoteBinding := ⟨0⟩

structure Setup where
  n : Nat
  vote : VoteBinding

/-- The root of the static cases. -/
theorem fixture_root : True := trivial

/-- Listed: stated at the stock binding. -/
theorem stock_helper (S : Setup) : ({ S with vote := stock } : Setup).vote = stock := rfl

end Fx
