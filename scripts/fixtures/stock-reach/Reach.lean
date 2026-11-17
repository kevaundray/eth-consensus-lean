namespace Fx

/-- Two unrelated types with a method of the same name. -/
structure A where
  x : Nat

structure B where
  x : Nat

/-- Generic. -/
theorem A.foo (_a : A) (S : Setup) : S.n = S.n := rfl

/-- Stock, with a `Setup` binder: flagged when reached. -/
theorem B.foo (_b : B) (S : Setup) : ({ S with vote := stock } : Setup).n = S.n := rfl

/-- Calls `A.foo` by dot notation; `+dots` also follows `B.foo`, the elaborated closure does not. -/
theorem dots_root (a : A) (S : Setup) : S.n = S.n := a.foo S

/-- Controls: a `Setup` binder using `stock` (flagged) and one that does not. -/
theorem ctrl_stock (S : Setup) : ({ S with vote := stock } : Setup).n = S.n := rfl

theorem ctrl_generic (S : Setup) : S.n = S.n := rfl

end Fx
