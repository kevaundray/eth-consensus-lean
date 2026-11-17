namespace Fx

variable (S : Setup)

/-- Generic: the proof uses `{ S with vote := stock }`, the header does not. -/
theorem body_only (S : Setup) : True := by
  have : ({ S with vote := stock } : Setup).vote = stock := rfl
  have := @stock_helper
  trivial

/-- Stock: a definition is classified by its whole text. -/
def def_body (S : Setup) : Setup := { S with vote := stock }

/-- Stock: an `hstock` hypothesis, no `Setup` binder. -/
theorem hstock_hyp (n : Nat) (hstock : n = 0) : True := by have := @stock_helper; trivial

/-- Neither: the `variable (S : Setup)` is not named by the header. -/
theorem unused_variable (n : Nat) : True := by have := @stock_helper; trivial

/-- Stock: its header names the stock definition `def_body`. -/
theorem via_def (h : (def_body S).n = 0) : True := by have := @stock_helper; trivial

end Fx
