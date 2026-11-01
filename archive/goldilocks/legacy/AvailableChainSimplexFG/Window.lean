module
public import AvailableChainSimplexFG.ChainState

@[expose] public section

namespace AvailableChain.SimplexFG.Window

open AvailableChain.SimplexFG

/-- [spec 599–607] A retained justification and its finality identities. -/
structure Entry (V : Type) where
  j : Height
  X : FGBlock V
  Q : Finset V
  deriving DecidableEq

/-- [spec 594–607] The finality window state. The latest justification is
separate from the window. The NJ latch is absent because it is always false. -/
structure State (V : Type) where
  L : FGBlock V
  s : Slot
  h : Height
  T_h : FGBlock V
  target_participation : Finset V
  progress : Finset V
  W : List (Entry V)
  J : FGBlock V
  h_j : Height
  F : FGBlock V
  h_F : Height
  deriving DecidableEq

variable {V : Type}

/-- [spec 722–728] Genesis state, with an empty window. -/
def initial : State V :=
  { L := .genesis, s := 0, h := 1, T_h := .genesis
    target_participation := ∅, progress := ∅, W := []
    J := .genesis, h_j := 0, F := .genesis, h_F := 0 }

theorem initial_def :
    initial (V := V) =
  ({ L := .genesis, s := 0, h := 1, T_h := .genesis,
     target_participation := ∅, progress := ∅, W := [],
     J := .genesis, h_j := 0, F := .genesis, h_F := 0 }) := rfl

/-- [spec 1201–1216] Independent finality and height effects. Every matching
entry gets the bit; uniqueness of matching entries is a separate invariant. -/
def process_row [DecidableEq V] [RowCodec V] (σ : State V) (a : Row V) : State V :=
  let afterFinality := { σ with W := σ.W.map (fun e =>
    if a.finality_pair = some ⟨e.j, e.X.root⟩ then
      { e with Q := insert a.signer e.Q } else e) }
  if a.height_pair.matchesEntry σ.h σ.T_h.root then
    match a.height_pair with
    | .vote _ _ timeout =>
        if timeout then
          { afterFinality with progress := insert a.signer afterFinality.progress }
        else
          { afterFinality with
            target_participation := insert a.signer afterFinality.target_participation
            progress := insert a.signer afterFinality.progress }
    | .empty => afterFinality
  else afterFinality

theorem process_row_def [DecidableEq V] [RowCodec V] (σ : State V) (a : Row V) :
    process_row σ a =
  (let afterFinality := { σ with W := σ.W.map (fun e =>
    if a.finality_pair = some ⟨e.j, e.X.root⟩ then
      { e with Q := insert a.signer e.Q } else e) }
  if a.height_pair.matchesEntry σ.h σ.T_h.root then
    match a.height_pair with
    | .vote _ _ timeout =>
        if timeout then
          { afterFinality with progress := insert a.signer afterFinality.progress }
        else
          { afterFinality with
            target_participation := insert a.signer afterFinality.target_participation
            progress := insert a.signer afterFinality.progress }
    | .empty => afterFinality
  else afterFinality) := rfl

/-- [spec 1244–1250] Advance and clear only the height bit sets. -/
def advance_height (σ : State V) : State V :=
  { σ with
    h := σ.h + 1
    T_h := σ.L
    target_participation := ∅
    progress := ∅ }

theorem advance_height_def (σ : State V) :
    advance_height σ =
  ({ σ with
    h := σ.h + 1
    T_h := σ.L
    target_participation := ∅
    progress := ∅ }) := rfl

/-- [spec 1222–1225] Select the greatest ready height. Equal heights keep
the first entry; reachable windows have strictly increasing heights. -/
def greatestReady [Fintype V] (E : Electorate V) (σ : State V) : Option (Entry V) :=
  σ.W.foldl (fun best e =>
    if σ.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      match best with
      | none => some e
      | some old => if old.j < e.j then some e else best
    else best) none

theorem greatestReady_def [Fintype V] (E : Electorate V) (σ : State V) :
    greatestReady E σ =
  (σ.W.foldl (fun best e =>
    if σ.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      match best with
      | none => some e
      | some old => if old.j < e.j then some e else best
    else best) none) := rfl

/-- [spec 1222–1227] Finalize, then delete every entry at or below h_F. -/
def finalizeWindow [Fintype V] (E : Electorate V) (σ : State V) : State V :=
  let σ' := match greatestReady E σ with
    | none => σ
    | some e => { σ with F := e.X, h_F := e.j }
  { σ' with W := σ'.W.filter (fun e => decide (σ'.h_F < e.j)) }

theorem finalizeWindow_def [Fintype V] (E : Electorate V) (σ : State V) :
    finalizeWindow E σ =
  (let σ' := match greatestReady E σ with
    | none => σ
    | some e => { σ with F := e.X, h_F := e.j }
  { σ' with W := σ'.W.filter (fun e => decide (σ'.h_F < e.j)) }) := rfl

/-- [spec 1226] Weighted quorum on target identities, via the electorate. -/
def targetQuorum [Fintype V] (E : Electorate V) (σ : State V) : Bool :=
  decide (E.q ≤ E.weightOf σ.target_participation)

theorem targetQuorum_def [Fintype V] (E : Electorate V) (σ : State V) :
    targetQuorum E σ =
  (decide (E.q ≤ E.weightOf σ.target_participation)) := rfl

/-- [spec 1235–1236] The SimplexFG progress guard; target has priority. -/
def progReady [Fintype V] (E : Electorate V) (cfg : FGConfig) (σ : State V) : Bool :=
  targetQuorum E σ ||
    (decide (σ.T_h.slot + cfg.timeoutDelay ≤ σ.s) &&
      decide (E.q ≤ E.weightOf σ.progress))

theorem progReady_def [Fintype V] (E : Electorate V) (cfg : FGConfig) (σ : State V) :
    progReady E cfg σ =
  (targetQuorum E σ ||
    (decide (σ.T_h.slot + cfg.timeoutDelay ≤ σ.s) &&
      decide (E.q ≤ E.weightOf σ.progress))) := rfl

/-- [spec 1220–1242] Finality first, then target before mature progress.
Capacity eviction drops entries from the front and does not finalize them. -/
def process_height_events [Fintype V] (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (σ : State V) : State V :=
  let afterFinality := finalizeWindow E σ
  if targetQuorum E afterFinality then
    let entries := afterFinality.W ++ [⟨afterFinality.h, afterFinality.T_h, ∅⟩]
    advance_height { afterFinality with
      J := afterFinality.T_h
      h_j := afterFinality.h
      W := entries.drop (entries.length - K) }
  else if progReady E cfg afterFinality then
    advance_height afterFinality
  else afterFinality

theorem process_height_events_def [Fintype V] (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (σ : State V) :
    process_height_events E cfg K σ =
  (let afterFinality := finalizeWindow E σ
  if targetQuorum E afterFinality then
    let entries := afterFinality.W ++ [⟨afterFinality.h, afterFinality.T_h, ∅⟩]
    advance_height { afterFinality with
      J := afterFinality.T_h
      h_j := afterFinality.h
      W := entries.drop (entries.length - K) }
  else if progReady E cfg afterFinality then
    advance_height afterFinality
  else afterFinality) := rfl

/-- [spec 1186–1200] Raw evaluation on the original block. Admission checks
belong to the wrapper; this function does not perform them. -/
def transition [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (K : Nat) (σ : State V)
    (B : FGBlock V) (rows : List (Row V)) : State V :=
  process_height_events E cfg K
    { rows.foldl process_row { σ with s := B.slot } with L := B }

theorem transition_def [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (K : Nat) (σ : State V)
    (B : FGBlock V) (rows : List (Row V)) :
    transition E cfg K σ B rows =
  (process_height_events E cfg K
    { rows.foldl process_row { σ with s := B.slot } with L := B }) := rfl

/-- [spec 1186–1200; bp.heightBridge.v1] Fold the original decoded block tree. -/
def derive [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (K : Nat) : FGBlock V → State V
  | .genesis => initial
  | .node q s r_s x rs => transition E cfg K (derive E cfg K q) (.node q s r_s x rs) rs

theorem derive_def [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (K : Nat) (B : FGBlock V) :
    derive E cfg K B =
      match B with
      | .genesis => initial
      | .node q s r_s x rs => transition E cfg K (derive E cfg K q) (.node q s r_s x rs) rs := by
  cases B <;> rfl

/-- [spec 782] Match the parent height and entry. -/
def heightMatch [RowCodec V] (σ : State V) (a : Row V) : Bool :=
  a.height_pair.matchesEntry σ.h σ.T_h.root

theorem heightMatch_def [RowCodec V] (σ : State V) (a : Row V) :
    heightMatch σ a =
  (a.height_pair.matchesEntry σ.h σ.T_h.root) := rfl

/-- [spec 783–784] Match a retained finality pair. -/
def windowMatch [RowCodec V] (σ : State V) (a : Row V) : Bool :=
  σ.W.any (fun e => decide (a.finality_pair = some ⟨e.j, e.X.root⟩))

theorem windowMatch_def [RowCodec V] (σ : State V) (a : Row V) :
    windowMatch σ a =
  (σ.W.any (fun e => decide (a.finality_pair = some ⟨e.j, e.X.root⟩))) := rfl

/-- [spec 785–787] A nonempty stale height pair with useful finality. -/
def staleUseful [RowCodec V] (σ : State V) (a : Row V) : Bool :=
  match a.height_pair, a.finality_pair with
  | .vote h _ _, some fp => decide (fp.height < h ∧ h < σ.h) && windowMatch σ a
  | _, _ => false

theorem staleUseful_def [RowCodec V] (σ : State V) (a : Row V) :
    staleUseful σ a =
  (match a.height_pair, a.finality_pair with
  | .vote h _ _, some fp => decide (fp.height < h ∧ h < σ.h) && windowMatch σ a
  | _, _ => false) := rfl

/-- [spec 788–795] R6-window, on decoded rows and the parent state. -/
def r6w [RowCodec V] (σ : State V) (a : Row V) : Bool :=
  heightMatch σ a || staleUseful σ a

theorem r6w_def [RowCodec V] (σ : State V) (a : Row V) :
    r6w σ a =
  (heightMatch σ a || staleUseful σ a) := rfl

/-- [spec 605–607] Read the latest pair bit set, or empty when absent. -/
def latestQfin [DecidableEq V] (σ : State V) : Finset V :=
  ((σ.W.find? (fun e => decide (e.j = σ.h_j ∧ e.X = σ.J))).map Entry.Q).getD ∅

theorem latestQfin_def [DecidableEq V] (σ : State V) :
    latestQfin σ =
  (((σ.W.find? (fun e => decide (e.j = σ.h_j ∧ e.X = σ.J))).map Entry.Q).getD ∅) := rfl

end AvailableChain.SimplexFG.Window
end
