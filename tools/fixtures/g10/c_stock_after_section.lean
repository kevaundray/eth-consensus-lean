namespace Fx

variable (S : Setup)

section Generic

variable (S : BoundSetup)

theorem c_generic (h : S.ok) : True := trivial

end Generic

/-- Stock: the `BoundSetup` variable was dropped at `end Generic`. -/
theorem c_stock (h : S.ok) : True := stock_helper S

end Fx
