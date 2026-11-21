module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Instance

@[expose] public section

/-! # Alternative time-shifted Goldilocks available chain

The AC payload type is shared with the stock instance, but the only valid value is the empty
pair. Block receipt never admits votes. As in the stock instance, wire authentication is a run
premise; stable validator identities and the two-vote admission cap are unchanged. -/

namespace Consensus.Goldilocks.SA.TimeShifted

variable {FGP : Type} (sp : SAParams)

/-- A mandatory old child: strict frozen majority and strict dominance against live opposition. -/
def mandatory (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) (C : Blk sp.n FGP) : Prop :=
  let j := (s : Int) - 1
  let F := voteView A Φ j (ETime.of (freeze sp s))
  let V := voteView A Φ j ⊤
  let L := goldfishScore sp Φ F j C
  let N := (voters V.votes).ncard
  C.slot < s ∧ N < 2 * L ∧ N - (supporters Φ V j C).ncard < L

/-- A current proposal may override an unforced local preference, but not the post-unlock anchor,
the FG viable heads, or a mandatory child at any fork from that anchor through its parent. -/
def accepts (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (P : Blk sp.n FGP) : Prop :=
  let s := sp.slot t
  let start := getAnchor sp A Φ t
  let tree := Φ.viableTree (voteDomain sp A Φ s)
  P.slot = s ∧ P ∈ tree ∧ P ∈ Φ.viableHeads ∧ Φ.Anc start P ∧
    ∀ X, Φ.Anc start X → Φ.Anc X P → X ≠ P → ∀ C ∈ tree, C.parent = some X.root →
      mandatory sp A Φ s C → Φ.Anc C P

open Classical in
/-- Wait on a failed early check without writing the speculative unlock. At timeout, prefer a
passing proposal; otherwise use the ordinary live-pool walk. Multiple passing proposals use
the existing deterministic deepest/root order. Slot zero uses the timeout fallback. -/
noncomputable def tryVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  let deadline := sp.ts s + sp.Δ
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ deadline < t then (A, []) else
  let j := (s : Int) - 1
  let V := voteView A Φ j ⊤
  let R := if 0 < s then { A with locks := unlock sp A.locks Φ t j V } else A
  let dom := voteDomain sp R Φ s
  let choice := if s = 0 then none else deepest Φ {P | accepts sp R Φ t P}
  if choice.isNone && t < deadline then (A, []) else
  let H := choice.getD (getHead sp R Φ t (Φ.viableTree dom) V j)
  let W := { R with votedSlot := s }
  let v : Vote sp.n := ⟨self, s, H.root⟩
  if A.mayVote s then
    (optimisticConfirmation sp (admitVote sp W t v) Φ t,
      [{ msg := v, readPoint := W, head := some ⟨H, getAnchor sp R Φ t, dom⟩ }])
  else (W, [])

open Classical in
/-- The restart preserves durable lock and confirmation state and stamps surviving non-genesis
blocks at wake. It neither replays votes nor synthesizes evidence from surviving blocks. -/
noncomputable def reset (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n :=
  { SAState.initial sp.genesisRoot with
    locks := A.locks, latestConfirmed := A.latestConfirmed, restartTime := (t : WithBot Time)
    mayVote := A.mayVote
    blockStamp := fun r => if r = sp.genesisRoot then ⊥ else if InTree Φ r then ETime.of t else ⊤ }

open Classical in
/-- A separate AC instance. The proposer uses its live unlock and ordinary walk but proposes
an empty payload; all confirmation, FG reporting and committee tests keep their stock meanings. -/
@[reducible] noncomputable def instanceAC (FGP : Type) : ACInterface sp.toParams FGP where
  State := SAState sp.n
  Msg := Vote sp.n
  Payload := Payload sp.n
  validPayload := fun B => B.acPayload = ([], [])
  validMsg := fun _ => True
  holdsMsg := fun A v => v ∈ A.pool v.slot
  genesisPayload := ([], [])
  initial := SAState.initial sp.genesisRoot
  onMessage := fun self A Φ t v =>
    tryVote sp self (optimisticConfirmation sp (admitVote sp A t v) Φ t) Φ t
  onBlock := fun self A Φ t B => tryVote sp self (optimisticConfirmation sp
    { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } Φ t) Φ t
  onTick := fun self A Φ t => Id.run do
    let s := sp.slot t
    if ¬ joined sp A t then return (A, [])
    let r := if t = sp.ts s + sp.Δ then tryVote sp self A Φ t else (A, [])
    let W := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmation sp r.1 Φ t (s - 1) else r.1
    return (W, r.2)
  proposal := fun A Φ t => let r := acProposal sp A Φ t; (r.1, r.2.map fun p => (p.1, ([], [])))
  toFG := acToFG sp
  confirmed := acConfirmed sp
  head := acHead sp
  restart := fun _ A Φ t => (reset sp A Φ t, [])

end Consensus.Goldilocks.SA.TimeShifted

end
