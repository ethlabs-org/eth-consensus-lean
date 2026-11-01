module
public import AvailableChainFGSA.Model.Restart

public section

namespace AvailableChain.FGSA.Run.Tests.ReplayClocks
abbrev k3 : Params :=
  ⟨⟨1, 4, 3, 64, by decide, by decide, by decide, by decide⟩,
    2, 4, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩
abbrev k4 : Params :=
  ⟨⟨1, 4, 4, 64, by decide, by decide, by decide, by decide⟩,
    2, 4, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩
abbrev n7 : Params :=
  ⟨⟨1, 7, 2, 4096, by decide, by decide, by decide, by decide⟩,
    2, 4, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩
abbrev split : Params :=
  ⟨⟨2, 7, 2, 4096, by decide, by decide, by decide, by decide⟩,
    5, 10, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩
abbrev env1 : Generic.Env (Fin 4) := ⟨1, by decide, 21, by decide, fun _ _ => true⟩
abbrev env7 : Generic.Env (Fin 7) := ⟨1, by decide, 1001, by decide, fun _ _ => true⟩
abbrev envSplit : Generic.Env (Fin 7) :=
  ⟨2, by decide, 2002, by decide, fun _ _ => true⟩

end AvailableChain.FGSA.Run.Tests.ReplayClocks

namespace AvailableChain.FGSA.Run.Tests.StaleLeaseReplay
open AvailableChain.SimplexFG

abbrev params (k : Nat) (hk : 2 ≤ k) : Params :=
  { ReplayClocks.k3 with k := k, kLarge := hk, digest := fun d => ⟨d.app + 1⟩ }
abbrev p3 := params 3 (by decide)
abbrev p4 := params 4 (by decide)
abbrev bodyB (p : Params) : NamedProposal p.n := namedProposal p .genesis 1 1 [] [] []
abbrev bodyD (p : Params) : NamedProposal p.n := namedProposal p .genesis 2 2 [] [] []
abbrev deliver (p : Params) (st : State p.n) (N : NamedProposal p.n) : State p.n :=
  process p st ⟨.proposer N.slot, .proposal N⟩
abbrev initial (p : Params) : State p.n :=
  deliver p (deliver p (initialAt p.n 8) (bodyB p)) (bodyD p)
abbrev votes (p : Params) (st : State p.n) (s : Slot) (b : BlockId)
    (seats : List (Fin p.n)) : State p.n :=
  seats.foldl (fun st j => process p st ⟨.seat (.head s) j, .head b⟩) st
abbrev clocks (p : Params) (st : State p.n) (ts : List Time) : State p.n :=
  ts.foldl (clock p) st

abbrev oldWrite (p : Params) (seats : List (Fin p.n)) : State p.n :=
  clocks p (votes p (clock p (initial p) 13) 3 (bodyD p).root seats) [14, 15, 18]
abbrev reader (p : Params) (seats : List (Fin p.n)) : State p.n :=
  clocks p (votes p (clock p (acRestart p (oldWrite p seats) 21) 21)
    5 (bodyB p).root seats) [22, 23, 25]
abbrev source (p : Params) (seats : List (Fin p.n)) : State p.n :=
  clocks p (votes p (clock p (initial p) 21) 5 (bodyB p).root seats) [22, 23, 26]
abbrev seats : List (Fin 4) := [0, 3]

abbrev oneVote6 : State 4 :=
  votes p4 (reader p4 seats) 6 (bodyB p4).root [0]
abbrev proposalRead : State 4 := clocks p4 oneVote6 [26, 27, 28]
abbrev headRead : State 4 := clock p4 proposalRead 29
abbrev outputRead : State 4 := clock p4 headRead 30

end AvailableChain.FGSA.Run.Tests.StaleLeaseReplay

namespace AvailableChain.FGSA.Run.Tests.SlowLeaseReplay
open AvailableChain.SimplexFG StaleLeaseReplay

abbrev params : Params :=
  { ReplayClocks.n7 with digest := fun d => ⟨d.app + 1⟩ }
abbrev quorum (h : Nat) (b : BlockId) (timeout : Bool) : List (RowWire 7) :=
  ([0, 1, 2, 3, 4] : List (Fin 7)).map
    (fun j => ⟨.seat .fg j, .vote ⟨.vote h b timeout, none⟩⟩)
abbrev B : NamedProposal 7 := namedProposal params .genesis 1 1 [] [] []
abbrev J : NamedProposal 7 := namedProposal params .genesis 2 2 [] [] (quorum 1 ⟨0⟩ false)
abbrev A : NamedProposal 7 := namedProposal params J 3 3 [] [] (quorum 2 J.root false)
abbrev prepared : State 7 :=
  [B, J, A].foldl (deliver params) (initialAt 7 100)
abbrev start : State 7 := acRestart params prepared 1000
abbrev votes250 : State 7 := votes params (clock params start 1001) 250 B.root [5, 6]
abbrev votes251 : State 7 :=
  votes params (votes params (clocks params votes250 [1002, 1003, 1005])
    251 B.root [5, 6]) 251 A.root [0]
abbrev saved : State 7 := clock params votes251 1006
abbrev beforeWrite : State 7 := clocks params saved [1007, 1009]
abbrev afterWrite : State 7 := clock params beforeWrite 1010

end AvailableChain.FGSA.Run.Tests.SlowLeaseReplay

namespace AvailableChain.FGSA.Run.Tests.SplitBatchReplay
open AvailableChain.SimplexFG StaleLeaseReplay

abbrev params : Params :=
  { ReplayClocks.split with digest := fun d => ⟨d.app + 1⟩ }
abbrev B : NamedProposal 7 := namedProposal params .genesis 1 1 [] [] []
abbrev JA : NamedProposal 7 :=
  namedProposal params .genesis 2 2 [] [] (SlowLeaseReplay.quorum 1 ⟨0⟩ false)
abbrev JB : NamedProposal 7 :=
  namedProposal params B 3 3 [] [] (SlowLeaseReplay.quorum 1 ⟨0⟩ false)
abbrev JC : NamedProposal 7 :=
  namedProposal params .genesis 4 4 [] [] (SlowLeaseReplay.quorum 1 ⟨0⟩ false)
abbrev A : NamedProposal 7 :=
  namedProposal params JA 5 5 [] [] (SlowLeaseReplay.quorum 2 JA.root false)
abbrev C : NamedProposal 7 :=
  namedProposal params JC 20 6 [] [] (SlowLeaseReplay.quorum 2 JC.root true)
abbrev WB : NamedProposal 7 :=
  namedProposal params JB 21 7 [] [] (SlowLeaseReplay.quorum 2 JB.root true)
abbrev prepared : State 7 :=
  [B, JA, JB, JC, A, C].foldl (deliver params) (initialAt 7 200)
abbrev batchPrefix (wake : Time) : State 7 :=
  let st := votes params (clock params (acRestart params prepared wake) 2002) 250 B.root [5, 6]
  let st := clocks params st [2004, 2006, 2008, 2010]
  clocks params (votes params (votes params st 251 B.root [5, 6]) 251 A.root [0]) [2012]
abbrev early : State 7 :=
  clock params (deliver params (clock params (batchPrefix 2000) 2013) WB) 2014
abbrev late : State 7 := deliver params (clock params (batchPrefix 2002) 2014) WB

abbrev earlyHead : State 7 := clock params early 2018
abbrev lateHead : State 7 := clock params late 2018
abbrev slowWrite : State 7 := clock params earlyHead 2020
abbrev fullBatch : State 7 :=
  let st := clock params slowWrite 2021
  let st := votes params st 252 (headVote params earlyHead 252).root [0, 1]
  let st := votes params st 252 (headVote params lateHead 252).root [2, 3, 4]
  clocks params st [2022, 2024, 2026]
abbrev otherBatch : State 7 :=
  let st := clock params (clock params lateHead 2020) 2021
  let st := votes params st 252 (headVote params earlyHead 252).root [0, 1]
  let st := votes params st 252 (headVote params lateHead 252).root [2, 3, 4]
  clocks params st [2022, 2024, 2026]
abbrev repairRead : State 7 :=
  let st := clock params fullBatch 2027
  let st := votes params st 253 (headVote params fullBatch 253).root [0]
  let st := votes params st 253 (headVote params otherBatch 253).root [1, 2, 3, 4]
  clocks params st [2028, 2030, 2032]

abbrev expiryRead : State 7 := clock params repairRead 2034

end AvailableChain.FGSA.Run.Tests.SplitBatchReplay

end
