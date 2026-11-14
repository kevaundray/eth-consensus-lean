namespace Fx

variable (S : Setup)

/-- Stock: `S` is the file-level `Setup` variable; the `BoundSetup` section starts below. -/
theorem a_stock (h : S.ok) : True := stock_helper S

section Generic

variable (S : BoundSetup)

theorem a_generic (h : S.ok) : True := trivial

end Generic

end Fx
