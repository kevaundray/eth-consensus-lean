namespace Fx

/-- Reaches the listed `stock_helper`. -/
theorem listed_root (S : Setup) : True := by
  have := stock_helper S
  trivial

/-- Reaches `B.foo`. -/
theorem stock_root (S : Setup) : True := by
  have := B.foo ⟨0⟩ S
  trivial

private theorem hidden_stock (S : Setup) : ({ S with vote := stock } : Setup).n = S.n := rfl

/-- Reaches the stock private helper `hidden_stock`. -/
theorem private_root (S : Setup) : S.n = S.n := by
  have := hidden_stock S
  rfl

end Fx
