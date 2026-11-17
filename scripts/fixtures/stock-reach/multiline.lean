namespace Fx

variable (S : Setup)
  (hS :
    S.vote = stock)

/-- Stock: `hS`'s binder spans lines. -/
theorem uses_hS (h : hS = hS) : True := by have := @stock_helper; trivial

/-- Generic: `S` only. -/
theorem only_S (h : S.n = 0) : True := by have := @stock_helper; trivial

end Fx
