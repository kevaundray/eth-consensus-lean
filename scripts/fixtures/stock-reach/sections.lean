namespace Fx

variable (S : Setup) (hS : S.n = 0)

/-- Generic: before the section, the file's `hS`. -/
theorem before_section (h : hS = hS) : True := by have := @stock_helper; trivial

section Stock

variable (hS : S.vote = stock)

/-- Stock: its header names the section's `hS`, which shadows the file's and carries the marker. -/
theorem inside_stock (h : hS = hS) : True := by have := @stock_helper; trivial

section Inner

variable (h2 : S.n = 1)

/-- Stock: nested, through the enclosing section's `hS`. -/
theorem nested_stock (h : hS = hS) (h' : h2 = h2) : True := by have := @stock_helper; trivial

/-- Generic: nested, names `h2` (and through its type `S`) but not `hS`. -/
theorem nested_generic (h' : h2 = h2) : True := by have := @stock_helper; trivial

end Inner

/-- Generic: inside the section, does not name `hS`. -/
theorem inside_generic (h : S.n = 0) : True := by have := @stock_helper; trivial

end Stock

/-- Generic: after the section's `end`, `hS` is the file's again. -/
theorem after_section (h : hS = hS) : True := by have := @stock_helper; trivial

end Fx
