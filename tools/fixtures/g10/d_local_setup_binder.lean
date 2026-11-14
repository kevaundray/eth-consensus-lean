namespace Fx

section Generic

variable (S : BoundSetup)

/-- Stock: the explicit `(S : Setup)` binder shadows the section's `BoundSetup` variable. -/
theorem d_local (S : Setup) (h : S.ok) : True := stock_helper S

end Generic

end Fx
