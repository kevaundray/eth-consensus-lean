namespace Fx

variable (S : Setup) (hS : S.vote = stock)

/-- Generic: its own `hS` shadows the stock variable. -/
theorem local_shadow (S : Setup) (hS : S.n = 0) : True := by have := @stock_helper; trivial

/-- Stock: its own `S` binder, with the marker in its own header. -/
theorem local_stock (S : Setup) (h : ({ S with vote := stock } : Setup).n = 0) : True := by
  have := @stock_helper; trivial

end Fx
