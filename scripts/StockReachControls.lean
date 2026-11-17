import ConsensusLean
import Solution
/-!
# Controls of the stock-dependence reach check

Prepended by `scripts/stock-reach.py --elab` to `StockReach.lean`, which checks each control's
verdict under its flag rule (a `Setup` binder and a use of `stock` or a listed declaration):
`stock_use` applies a generic lemma at the stock binding `{ S with vote := stock }` and must be
flagged; `generic_use` applies it at `S` and `setup_field` reads a `Setup` field: neither may be.
-/

namespace StockReachCtrl
open Consensus Consensus.Shape Consensus.Goldilocks Consensus.Goldilocks.AsChainShape
open Consensus.Goldilocks.Simulation

theorem stock_use {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks { S with vote := stock })) E)
    (y : Fin (Fintype.card V)) :
    y ∈ honestKeys { S with vote := stock } rho ↔ rho.key y ∉ rho.faultyAt 0 :=
  mem_honestKeys_iff _ rho y

theorem generic_use {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (y : Fin (Fintype.card V)) :
    y ∈ honestKeys S rho ↔ rho.key y ∉ rho.faultyAt 0 :=
  mem_honestKeys_iff S rho y

theorem setup_field (S : Setup) : S.k ≤ S.k + 1 := Nat.le_succ _

end StockReachCtrl
