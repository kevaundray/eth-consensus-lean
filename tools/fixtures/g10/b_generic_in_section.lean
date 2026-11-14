namespace Fx

variable (S : Setup)

section Generic

variable (S : BoundSetup)

/-- Generic: `S` is the section's `BoundSetup` variable, and it calls a §S declaration. -/
theorem b_generic (h : S.ok) : True := stock_helper S

end Generic

end Fx
