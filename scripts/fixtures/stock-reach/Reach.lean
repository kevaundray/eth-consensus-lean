namespace Fx

/-- Two unrelated types with a method of the same name. -/
structure A where
  x : Nat

structure B where
  x : Nat

/-- Generic. -/
theorem A.foo (_a : A) (S : Setup) : S.n = S.n := rfl

/-- Stock, with a `Setup` binder. -/
theorem B.foo (_b : B) (S : Setup) : ({ S with vote := stock } : Setup).n = S.n := rfl

/-- Calls `A.foo` by dot notation; `+dots` also follows `B.foo`. -/
theorem dots_root (a : A) (S : Setup) : S.n = S.n := a.foo S

end Fx
