module
public import AvailableChainPCSARun.Model.Protocol

@[expose] public section

/-! PC-SA M1 run smoke test: the ack duty at `e_s` and its payload
(pcsa34-v2-delta (5) check (i)). The fixtures repeat the store smoke test
(`AvailableChainPCSA/Tests/Smoke.lean`): a test imports only its own library
(check-layers TEST-SCOPE, TEST-USE). -/

namespace AvailableChain.PCSA.Run.Tests

open AvailableChain.SimplexFG

/-- The finite digest table over the PC-SA digest input. -/
def digestTable : List (DigestInput 4 × BlockId) :=
  [ (⟨genesisRoot, 1, 0, [], [], [], none⟩, ⟨1⟩) ]

/-- Positive IDs; 4095 is outside the finite table. -/
def fixtureDigest (d : FGSA.DigestInput 4) : BlockId :=
  ((digestTable.find? (fun e => e.1.toFGSA == d)).map Prod.snd).getD ⟨4095⟩

/-- The test parameters: Δ = 1, n = 4, k = 3, R = 2, δ_t = 1. -/
abbrev pT : Params :=
  { Δ := 1, n := 4, k := 3, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fixtureDigest }

def B1 : FGBlock (Fin 4) := .node .genesis 1 ⟨1⟩ (packInner 0 ([] : List (RowWire 4))) []
def b1 : Block := eraseFG B1
def N1 : NamedProposal 4 := .node .genesis 1 ⟨1⟩ b1.body [] [] [] none
def w1 : Wire 4 := ⟨.proposer 1, .proposal N1⟩
def atTime (st : State pT.n) (t : Time) : State pT.n :=
  { st with base := { st.base with now := t } }
def hv (i : Fin 4) : Wire 4 := ⟨.seat (.head 1) i, .head b1.root⟩
def ak (i : Fin 4) : AckWire 4 := ⟨.seat (.ack 1) i, b1.root⟩
def akWire (i : Fin 4) : Wire 4 := ⟨.seat (.ack 1) i, .ack b1.root⟩
/-- `B1` at `t_1 = 4`; three exact HEADs at `v_1 = 5`; the tick at `e_1 = 6`;
two acks. -/
def st5 : State pT.n :=
  [hv 0, hv 1, hv 2].foldl (process pT) (atTime (process pT (atTime {} 4) w1) 5)
def st6 : State pT.n := clock pT st5 6
/-- Three HEADs stamped at `e_1 = 6` (not timely); the tick at 6. -/
def st6late : State pT.n :=
  clock pT ([hv 0, hv 1, hv 2].foldl (process pT) (atTime (process pT (atTime {} 4) w1) 6)) 6
def stA : State pT.n := [akWire 0, akWire 1].foldl (process pT) st6
/-- At `a_1 = 14`, the first PC is frozen at `z_2` and supplies the FG source. -/
def st14 : State pT.n := clock pT (clock pT stA 11) 14

/-- (i) At `e_1 = 6 = a_0` the duties are the FG action of round 0 and the ack
of slot 1 (`R = 2`: the action of round `r` is at `e_{rR+1}`); at `e_2 = 10`
the ack alone; at `e_3 = 14 = a_1` the FG action of round 1 and the ack of
slot 3. The HEAD action is never due at `e_s`. -/
theorem duties_early : duties pT (SA.earlyTime pT.toParams 1) = [.fgAction 0, .ackAction 1] ∧
    duties pT (SA.earlyTime pT.toParams 2) = [.ackAction 2] ∧
    duties pT (SA.earlyTime pT.toParams 3) = [.fgAction 1, .ackAction 3] ∧
    RunDuty.headAction 1 ∉ duties pT 6 := by
  decide +kernel

/-- The ack of slot `s` is due at `e_s` for every `p` and `s`, and at no other
time (A6: one ack action per slot; `pcsa_duties_nodup` gives one per tick). -/
theorem ack_due (p : Params) (s : Slot) :
    RunDuty.ackAction s ∈ duties p (SA.earlyTime p.toParams s) :=
  (pcsa_duties_spec p _ _).mpr rfl
theorem ack_once (p : Params) (s : Slot) (t : Time) :
    RunDuty.ackAction s ∈ duties p t ↔ SA.earlyTime p.toParams s = t :=
  pcsa_duties_spec p _ t

/-- At `e_1` the ack duty sends the exact ack on the root of `b1`; with late
HEADs it sends nothing. -/
theorem ack_sent :
    act pT unitCodec ⟨st6, RecordOnce.initial⟩ (.ackAction 1) () = some (.ack b1.root) ∧
    act pT unitCodec ⟨st6late, RecordOnce.initial⟩ (.ackAction 1) () = none := by
  decide +kernel

/-- The sent ack decodes to the ack input and is pooled on delivery. -/
theorem ack_roundtrip :
    (toWire pT (ofAck pT (ak 0))).decode = some (.ack 1 0 b1.root) ∧
    processedS pT stA (ofAck pT (ak 0)) = true ∧
    processedS pT st6 (ofAck pT (ak 0)) = false := by
  decide +kernel

set_option maxRecDepth 2048 in
/-- At `e_3 = a_1`, AC-only mode sends no FG row. The enabled mode keeps
the `attest` payload and sends a row on the same state. -/
theorem pcsa_fg_mode :
    (pcsaAC pT unitCodec).act ⟨st14, RecordOnce.initial⟩ (.fgAction 1) () = none ∧
    (pcsa pT unitCodec).act ⟨st14, RecordOnce.initial⟩ (.fgAction 1) () =
      (attest pT st14 RecordOnce.initial ⟨0, pT.nPos⟩).1.map Msg.row ∧
    ((pcsa pT unitCodec).act ⟨st14, RecordOnce.initial⟩ (.fgAction 1) ()).isSome = true := by
  refine ⟨rfl, ?_, ?_⟩
  · exact actWith_def .on pT unitCodec ⟨st14, RecordOnce.initial⟩ (.fgAction 1) ()
  · decide +kernel

/-- The row-free tree contains genesis and `B1`. Its heights keep their
initial values: `h = h_max = 1` and `h_j = h_F = 0`. The FG filter keeps
the full tree when `F = Z = genesis` and `lo = 0`. -/
theorem pcsa_ac_fullTree :
    st6.fg.TF = {.genesis, B1} ∧ st6.fg.F = .genesis ∧ st6.fg.J = .genesis ∧
    st6.fg.h_max = 1 ∧ st6.fg.h_j = 0 ∧
    (∀ B ∈ st6.fg.TF, (FGSA.heightView pT B).h = 1 ∧
      (FGSA.heightView pT B).h_j = 0 ∧ (FGSA.Window.derive pT pT.K_W B).h_F = 0) ∧
    (controls pT st6).lo = 0 ∧ (controls pT st6).Z = .genesis ∧
    fullTree pT st6 = st6.fg.TF := by
  decide +kernel

#print axioms ack_sent

end AvailableChain.PCSA.Run.Tests
end
