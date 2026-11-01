module
public import AvailableChainSimplexFG.ChainState

@[expose] public section

namespace AvailableChain.SimplexFG

/-! # The FG signing client

The record `Λ`, the two pair rules, `record_row` and `createRow` (ALFS
`fgsa-protocol-bd942ca0.tex`, Fig. `alg:client`, lines 1334–1401). The client
takes two AP inputs as parameters (`get_fg_vote`, lines 1303–1326): the
source block and the head fields. It never reads the store. -/

-- port: DC/DecoupledConsensusModel/Protocol/ValidatorClient.lean:89-98
/-- The record `Λ` of one signer: for each height, the first target, whether
the signer emitted a timeout, and the target of its first finality pair.
Targets are roots. The spec's `Λ.timeouts` set is not here: no FG-module
branch reads it. -/
structure Record where
  /-- `Λ.target[h]`: the first target at height `h`. -/
  target : Height → Option BlockId
  /-- `Λ.timeout[h]`: a timeout was emitted at height `h`. -/
  timeout : Height → Bool
  /-- `Λ.lock[h]`: the target of the first finality pair at height `h`. -/
  lock : Height → Option BlockId

namespace Record

-- port: DC/DecoupledConsensusModel/Protocol/ValidatorClient.lean:104-107
/-- The initial record: `(⊥, false, ⊥)` at every height. -/
def initial : Record where
  target := fun _ => none
  timeout := fun _ => false
  lock := fun _ => none

-- port: DC/DecoupledConsensusModel/Protocol/ValidatorClient.lean:110-111
/-- `Λ.target[h] ← T`. -/
def with_target (Λ : Record) (h : Height) (T : BlockId) : Record :=
  { Λ with target := fun k => if k = h then some T else Λ.target k }

-- port: DC/DecoupledConsensusModel/Protocol/ValidatorClient.lean:114-115
/-- `Λ.timeout[h] ← true`. -/
def with_timeout (Λ : Record) (h : Height) : Record :=
  { Λ with timeout := fun k => if k = h then true else Λ.timeout k }

-- port: DC/DecoupledConsensusModel/Protocol/ValidatorClient.lean:118-119
/-- `Λ.lock[h] ← J`. -/
def with_lock (Λ : Record) (h : Height) (J : BlockId) : Record :=
  { Λ with lock := fun k => if k = h then some J else Λ.lock k }

end Record

/-- The finality fields `(h_j, J, h_F)` that the finality pair reads. The
spec reads them from the chain state of the head that `get_head` returns
("finality stays head-derived", line 1312). They are not the lex pair of the
frame controls.

CALLER OBLIGATION (Astra G06): the AP must pass `HeadFields.ofBlock E cfg Hd`
for its head block `Hd`. This type admits any values, and a row signed from
arbitrary fields has no justification carrier. -/
structure HeadFields where
  h_j : Height
  J : BlockId
  h_F : Height
  deriving DecidableEq, Repr

/-- The head fields of the head block `Hd`: `(σ.h_j, σ.J.root, σ.h_F)` with
`σ = derive E cfg Hd`. -/
def HeadFields.ofBlock {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (Hd : FGBlock V) : HeadFields :=
  ⟨(derive E cfg Hd).h_j, (derive E cfg Hd).J.root, (derive E cfg Hd).h_F⟩

-- port: DC/DecoupledConsensusModel/Protocol/ValidatorClient.lean:160-170
/-- `finality_pair(Λ, h_j, J, h_F)` (spec lines 1334–1345). It emits
`(h_j, J)` when the justification is not finalized (`h_F < h_j`) and all
three record guards hold: `target[h_j] ∈ {⊥, J}`, no timeout at `h_j`, and
`lock[h_j] ∈ {⊥, J}`. Without the guards, a client that recorded a timeout at
`m` can later sign a finality pair at `m` and make E1 evidence against itself
(Astra G01). This rule does not write the lock; `record_row` does. -/
def finality_pair (Λ : Record) (hd : HeadFields) : Option FinalityPair :=
  if hd.h_F < hd.h_j ∧ (Λ.target hd.h_j = none ∨ Λ.target hd.h_j = some hd.J) ∧
      Λ.timeout hd.h_j = false ∧ (Λ.lock hd.h_j = none ∨ Λ.lock hd.h_j = some hd.J)
    then some ⟨hd.h_j, hd.J⟩ else none

-- port: DC/DecoupledConsensusModel/Protocol/ValidatorClient.lean:180-184
/-- The lock that `height_pair` reads at `h_c`: `Λ.lock[h_c]`, replaced by
the target of this row's own finality pair when the heights agree (spec line
1350, `if h_c = h_f then lock ← T_f`). -/
def own_lock (Λ : Record) (h_c : Height) (fp : Option FinalityPair) : Option BlockId :=
  match fp with
  | some p => if p.height = h_c then some p.target else Λ.lock h_c
  | none => Λ.lock h_c

-- port: DC/DecoupledConsensusModel/Protocol/ValidatorClient.lean:216-229
/-- `height_pair(Λ, h_c, T_c, ν, h_f, T_f)` (spec lines 1347–1377), with
`ν = false`: this module has no NJ heights. The fields are `(h_c, T_c)`, the
height and entry root of the source state; `none` is "no fresh source".
Branches in the spec's order:
- a recorded timeout repeats, and names the current entry;
- a lock (with this row's own lock) equal to `T_c` gives the target; a lock
  for another root gives the empty pair (wait out the height);
- a recorded target equal to `T_c` repeats;
- no recorded target: adopt the source's entry (the `not ν` branch);
- otherwise time out at `h_c`. -/
def height_pair (Λ : Record) (fields : Option (Height × BlockId))
    (fp : Option FinalityPair) : NamedHeightPair :=
  match fields with
  | none => .empty
  | some (h_c, T_c) =>
    if Λ.timeout h_c then
      .vote h_c T_c true
    else
      match own_lock Λ h_c fp with
      | some locked => if locked = T_c then .vote h_c T_c false else .empty
      | none =>
        match Λ.target h_c with
        | some recorded => if recorded = T_c then .vote h_c T_c false else .vote h_c T_c true
        | none => .vote h_c T_c false

-- port: DC/DecoupledConsensusModel/Protocol/ValidatorClient.lean:236-244
/-- `record_attestation(Λ, a)` (spec lines 1389–1401), the only writer of
`Λ`: `lock[h_f] ← T_f` for a finality pair; `target[h] ← T` for a target
when `target[h]` is empty; `timeout[h] ← true` for a timeout. The spec also
adds `(h, T)` to `Λ.timeouts`; that set is omitted (no FG-module branch reads
it). -/
def record_row {V : Type} (Λ : Record) (a : Row V) : Record :=
  let afterLock :=
    match a.finality_pair with
    | some p => Λ.with_lock p.height p.target
    | none => Λ
  match a.height_pair with
  | .empty => afterLock
  | .vote h _ true => afterLock.with_timeout h
  | .vote h T false =>
      if afterLock.target h = none then afterLock.with_target h T else afterLock

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- port: DC/DecoupledConsensusModel/Protocol/ValidatorClient.lean:253-260
/-- [helper] `create_attestation` (alfs4 lines 1379–1387): the finality pair, then the
height pair, then the record, then release. Two inputs are AP data
(`get_fg_vote`, lines 1303–1326): the selected `source` block `C` (or none),
whose state `σ = derive E cfg C` gives the height fields `(σ.h, σ.T_h.root)`;
and the head fields `hd`. With no source, the height pair is empty. Returns
the row and the updated record. -/
def createRow (E : Electorate V) (cfg : FGConfig) (Λ : Record) (signer : V)
    (source : Option (FGBlock V)) (hd : HeadFields) : Row V × Record :=
  let fp := finality_pair Λ hd
  let hp := height_pair Λ
    (source.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root)) fp
  let a : Row V := ⟨signer, hp, fp⟩
  (a, record_row Λ a)

/-- One honest signer with one record: fold `createRow` over the inputs, and
return the emitted rows in order. -/
def clientRun (E : Electorate V) (cfg : FGConfig) (signer : V) :
    Record → List (Option (FGBlock V) × HeadFields) → List (Row V)
  | _, [] => []
  | Λ, (src, hd) :: rest =>
      (createRow E cfg Λ signer src hd).1 ::
        clientRun E cfg signer (createRow E cfg Λ signer src hd).2 rest

/-! ## Examples -/

/-- A head at height 0 that finalizes nothing new: `h_j ≤ h_F`. -/
def clientHdNone : HeadFields := ⟨0, genesisRoot, 0⟩
/-- The head fields of `B1`, written out. -/
def clientHdB1 : HeadFields := ⟨1, genesisRoot, 0⟩

/-- The source `genesis` (`h = 1`, entry genesis) gives a target at height 1. -/
example :
    (createRow E4 cfg1 Record.initial 0 (some .genesis) clientHdNone).1.height_pair =
      .vote 1 genesisRoot false := by decide

/-- `clientB1alt` has the parent, the slot and the rows of `B1` but body `1`:
height 2, a different entry root. With the same content, it is `B1b` of
Frame.lean (it was the same term before I9 too). -/
def clientB1alt : FGBlock (Fin 4) := .node .genesis 1 ⟨14⟩ 1 [rowT 0, rowT 1, rowT 2]

/-- The two entries are different: distinct content gives distinct roots. -/
example : B1.root ≠ clientB1alt.root := by decide

/-- A second call at height 2 with a different entry repeats no target: it
times out (DC's target-repeat rule). -/
example :
    clientRun E4 cfg1 0 Record.initial
        [(some B1, clientHdNone), (some clientB1alt, clientHdNone)] =
      [⟨0, .vote 2 B1.root false, none⟩, ⟨0, .vote 2 clientB1alt.root true, none⟩] := by
  decide

/-- Rejection in a run (Astra G01): after the timeout at height 2, a head with
`(h_j, J) = (2, B1.root)` gives no finality pair. Without the timeout guard the
third row would carry `(2, B1.root)`, which is E1 with the second row. -/
example :
    clientRun E4 cfg1 0 Record.initial
        [(some B1, clientHdNone), (some clientB1alt, clientHdNone), (none, ⟨2, B1.root, 0⟩)] =
      [⟨0, .vote 2 B1.root false, none⟩, ⟨0, .vote 2 clientB1alt.root true, none⟩,
        ⟨0, .empty, none⟩] := by
  decide

/-- The same rule on the fields directly, at height 1. -/
example :
    height_pair (Record.initial.with_target 1 genesisRoot) (some (1, ⟨7⟩)) none =
      .vote 1 ⟨7⟩ true := by decide

/-- No source gives the empty height pair. -/
example : (createRow E4 cfg1 Record.initial 0 none clientHdNone).1.height_pair = .empty := by
  decide

/-- No finality pair when `h_j ≤ h_F`. -/
example : finality_pair Record.initial ⟨1, genesisRoot, 1⟩ = none := by decide
example : finality_pair Record.initial clientHdNone = none := by decide

/-- The head fields of `B1`: genesis is justified at height 1, and nothing is
finalized. -/
example : HeadFields.ofBlock E4 cfg1 B1 = ⟨1, genesisRoot, 0⟩ := by decide
example : finality_pair Record.initial (HeadFields.ofBlock E4 cfg1 B1) =
    some ⟨1, genesisRoot⟩ := by decide

/-- Rejection (Astra G01): a recorded timeout at `h_j` blocks the pair. -/
example : finality_pair (Record.initial.with_timeout 1) clientHdB1 = none := by decide
/-- Rejection (Astra G01): a recorded target for another root blocks the pair. -/
example : finality_pair (Record.initial.with_target 1 ⟨7⟩) clientHdB1 = none := by decide
/-- Rejection (Astra G01): a lock for another root blocks the pair. -/
example : finality_pair (Record.initial.with_lock 1 ⟨7⟩) clientHdB1 = none := by decide

/-- The guards still admit the pair: a recorded target equal to `J` does not
block it. -/
example : finality_pair (Record.initial.with_target 1 genesisRoot) clientHdB1 =
    some ⟨1, genesisRoot⟩ := by decide
/-- The guards still admit the pair: a lock on `J` does not block it. -/
example : finality_pair (Record.initial.with_lock 1 genesisRoot) clientHdB1 =
    some ⟨1, genesisRoot⟩ := by decide

/-- The same-row lock (Astra H05): the row's own finality pair locks height 1
on genesis, so a source entry `⟨7⟩` at height 1 gives the empty pair. -/
example : height_pair Record.initial (some (1, ⟨7⟩)) (some ⟨1, genesisRoot⟩) = .empty := by
  decide
/-- The same-row lock on the matching entry gives the target. -/
example :
    height_pair Record.initial (some (1, genesisRoot)) (some ⟨1, genesisRoot⟩) =
      .vote 1 genesisRoot false := by decide
/-- The free root `⟨5⟩` of the next two examples is not the entry `B1.root`. -/
example : B1.root ≠ ⟨5⟩ := by decide
/-- Through `createRow`: the source `B1` (`h = 2`, entry `B1.root`) and the
free head fields `(2, ⟨5⟩, 0)` give the finality pair `(2, ⟨5⟩)` and an empty
height pair. -/
example :
    (createRow E4 cfg1 Record.initial 0 (some B1) ⟨2, ⟨5⟩, 0⟩).1 =
      ⟨0, .empty, some ⟨2, ⟨5⟩⟩⟩ := by decide

/-- A lock kept across calls: the first row locks height 2 on `⟨5⟩`; with the
returned record, the source `B1` (height 2, entry `B1.root`) gives the empty
pair through the stored lock. -/
example :
    (createRow E4 cfg1 Record.initial 0 none ⟨2, ⟨5⟩, 0⟩).1.finality_pair = some ⟨2, ⟨5⟩⟩ ∧
      (createRow E4 cfg1 (createRow E4 cfg1 Record.initial 0 none ⟨2, ⟨5⟩, 0⟩).2 0
        (some B1) clientHdNone).1 = ⟨0, .empty, none⟩ := by decide

end AvailableChain.SimplexFG
end
