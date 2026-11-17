namespace Fx.Other

/-- Generic twin of the listed `stock_helper`: a local `Setup` binder. -/
theorem stock_helper (S : Setup) (h : S.n = 0) : True := trivial

end Fx.Other

namespace Fx.Scoped

section
variable (S : Setup) (hS : S.n = 0)

/-- Generic twin through the section's `variable`s (the later stock `hS` is not in scope). -/
theorem stock_helper (h : hS = hS) : True := trivial

end

variable (S : Setup) (hS : S.vote = stock)

/-- Stock, so not a twin. -/
theorem stock_helper' (h : hS = hS) : True := trivial

end Fx.Scoped

namespace Fx.Third

variable (S : Setup) (hS : S.vote = stock)

/-- Stock, so not a twin. -/
theorem stock_helper (h : hS = hS) : True := trivial

end Fx.Third
