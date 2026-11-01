module
public import AvailableChainFGSAClaims.Statements.Join -- shake: keep (source declarations)
public import AvailableChainFGSA.Statements.FinalityView

@[expose] public section

/-! P3 §4.10; blueprint 01 §1.1 (200c9c07), spec 8ef4ed3b.
The five joint selections are `FGSA.liveRoot`, `FGSA.eligible`, `jointSource`,
`proposerHead`, and `FGSA.fgHead`. The live root and C_fg read no vote argument;
the proposer reads the previous-slot pool and the finality head reads the
current-slot pool. `FGSA.fgInputs` supplies the finality head triple.
All reads factor through `Node.st`; only the emitted pair can read Λ.
-/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.2: bp.sourceDiscipline.v1(b,c), 01 §8.4, 02 §§3.3–3.5.
C1: path justifications, finalizations, and strictly crossed entries. -/
def certified (W : FGBlock (Fin p.n)) : Set (FGBlock (Fin p.n)) :=
  {e | ∃ U, FGBlock.Preceq U W ∧
    (e = (heightView p U).J ∨ e = (finalityView p U).F ∨
      (e = (heightView p U).T_h ∧
        (heightView p U).h < (heightView p W).h))}

-- equation export required by BUILD §7.2 B3a
theorem certified_def (W : FGBlock (Fin p.n)) : certified p W =
  {e | ∃ U, FGBlock.Preceq U W ∧
    (e = (heightView p U).J ∨ e = (finalityView p U).F ∨
      (e = (heightView p U).T_h ∧
        (heightView p U).h < (heightView p W).h))} := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The admitted FG tree (bp.store.v1, 00:516–527). -/
def treeT (st : State p.n) : Finset (FGBlock (Fin p.n)) := st.fg.TF
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The substrate tree in its stored base-list order. -/
def treeErased (st : State p.n) : List Block := st.base.blocks
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The live FJ controls (bp.frame.v1, 00:581–587). -/
def frameR (st : State p.n) : Controls (Fin p.n) := FGSA.controls p st
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
D(X) uses the controls of the current store, also for a smaller X. -/
def domainR (st : State p.n) (X : Finset (FGBlock (Fin p.n))) :
    Finset (FGBlock (Fin p.n)) := KitFG.filteredFromView (heightView p) (frameR p st) X
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The FG output before erasure. -/
def finR (st : State p.n) : FGBlock (Fin p.n) := st.fg.F
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A strict change of the finalized block. -/
def FAdvance (st st' : State p.n) : Prop := st.fg.F ≠ st'.fg.F
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The AC candidates of the scheduled gate: fast-write members with a live lease.
The set has no older-label fallback (01 §1.1, T-SRC). -/
def sourceCandidates (st : State p.n) : Finset Block :=
  ((fastWriteAt st (p.round (st.slot p) * p.R)).getD []).toFinset.filter (fun B =>
    (leaseOf st B).any (fun d => decide (st.base.now < d)))
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
C_fg is the deepest candidate in D(Σ.T) (01:59–79). -/
def jointSource (st : State p.n) : Option (FGBlock (Fin p.n)) :=
  FGSA.deepest ((domainR p st (treeT p st)).filter
    (fun B => decide (eraseFG B ∈ sourceCandidates p st)))
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The proposer head reads the previous-slot pool and its resolved support. -/
def proposerHead (st : State p.n) (s : Slot) : Block :=
  FGSA.getHead p st (FGSA.proposerVotes st s) (FGSA.proposerSupport st s)
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The AC output S (01 §1.2; T7.3 `fgsaOutputs`). -/
def outputS (st : State p.n) : Block := st.base.stableRecord

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem outputS_def (st : State p.n) :
    outputS p st = st.base.stableRecord := rfl

-- equation export required by BUILD §7.2 B3a
theorem frameR_def (st : State p.n) : frameR p st = FGSA.controls p st := by rw [frameR]
-- equation export required by BUILD §7.2 B3a
theorem jointSource_def (st : State p.n) :
    jointSource p st = FGSA.deepest ((domainR p st (treeT p st)).filter
      (fun B => decide (eraseFG B ∈ sourceCandidates p st))) := by rw [jointSource]
-- equation export required by BUILD §7.2 B3a
theorem sourceCandidates_def (st : State p.n) : sourceCandidates p st =
    ((fastWriteAt st (p.round (st.slot p) * p.R)).getD []).toFinset.filter (fun B =>
      (leaseOf st B).any (fun d => decide (st.base.now < d))) := by rw [sourceCandidates]
-- equation export required by BUILD §7.2 B3a
theorem domainR_def (st : State p.n) (X : Finset (FGBlock (Fin p.n))) :
    domainR p st X = KitFG.filteredFromView (heightView p) (frameR p st) X := by rw [domainR]
-- equation export required by BUILD §7.2 B3a
theorem treeT_def (st : State p.n) : treeT p st = st.fg.TF := by rw [treeT]
-- equation export required by BUILD §7.2 B3a
theorem proposerHead_def (st : State p.n) (s : Slot) : proposerHead p st s =
    FGSA.getHead p st (FGSA.proposerVotes st s) (FGSA.proposerSupport st s) := by
  rw [proposerHead]
-- equation export required by BUILD §7.2 B3a
theorem FAdvance_def (st st' : State p.n) :
    FAdvance p st st' = (st.fg.F ≠ st'.fg.F) := by rw [FAdvance]

variable {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

def R_at (i : Nat) (x : V) : Controls (Fin p.n) := frameR p (storeAt p c E rho i x)
def D_at (i : Nat) (x : V) (X : Finset (FGBlock (Fin p.n))) :
    Finset (FGBlock (Fin p.n)) := domainR p (storeAt p c E rho i x) X
def FAdvanceAt (i : Nat) (x : V) : Prop :=
  (∃ o t, rho.events[i]? = some (.deliver x o t)) ∧
    FAdvance p (storeAt p c E rho i x) (storeAt p c E rho (i + 1) x)
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The erased candidates at the post-clock FG action read. -/
def candidatesAt (x : V) (r : Nat) : Option (Finset Block) :=
  (postClock E rho x (p.actionTime r)).map (fun nd => sourceCandidates p nd.st)
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The proposer's post-clock head at t_s. -/
def proposalHeadAt (s : Slot) : Option Block :=
  (postClock E rho (V2.D.proposerOf rho (fgsaInterface p c) s)
    (V2.D.proposalTime (fgsaInterface p c) s)).map (fun nd => proposerHead p nd.st s)
def actionHead (x : V) (r : Nat) : Option Block :=
  (postClock E rho x (p.actionTime r)).map (fun nd => FGSA.fgHead p nd.st)
def actionTriple (x : V) (r : Nat) : Option HeadFields :=
  (postClock E rho x (p.actionTime r)).map (fun nd => (FGSA.fgInputs p nd.st).2)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A row names a height and root, never an FG block (01 §8.4). -/
def namedEntry : NamedHeightPair → Option (Height × BlockId)
  | .empty => none
  | .vote h e _ => some (h, e)
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The named height and root are those of an ancestor of B. -/
def EntryBelow (e : Height × BlockId) (B : FGBlock (Fin p.n)) : Prop :=
  ∃ X, FGBlock.Preceq X B ∧ ((heightView p X).h, X.root) = e
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The FG seat of the signed row a belongs to x (S3c §2.7, M13). -/
def RowSigner (a : RowWire p.n) (x : V) : Prop :=
  ∃ i, a.auth = .seat .fg i ∧ rho.seatOf (RunLabel.base .fg) i = x
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Honest y emitted the signed row a at action r and event j. -/
def HonestRowAt (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) : Prop :=
  y ∈ rho.honest ∧ rho.events[j]? = some (.tick y (p.actionTime r)) ∧
    ofRow p a ∈ V2.D.Run.emitsAt E rho j
def HonestRowBefore (k : Nat) (y : V) (r : Nat) (a : RowWire p.n) : Prop :=
  ∃ j < k, HonestRowAt p c E rho j y r a
-- equation export required by BUILD §7.2 B3a
theorem HonestRowBefore_def (k : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    HonestRowBefore p c E rho k y r a = (∃ j < k, HonestRowAt p c E rho j y r a) := rfl
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A valid signed row with the specified holder. -/
def RowComplete (x : V) (a : RowWire p.n) : Prop :=
  a.valid = true ∧ RowSigner p c rho a x
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The honest proposal and the exact signed rows of its emitted wire. -/
def HonestCarrier (s : Slot) (Q : Block) (rows : List (RowWire p.n)) : Prop :=
  HonestProposal E rho (fgsaInterface p c) s Q ∧
    ∃ o N, V2.D.Run.emits E rho (V2.D.proposerOf rho (fgsaInterface p c) s) o
        (V2.D.proposalTime (fgsaInterface p c) s) ∧ o.payload = .proposal N ∧ N.erase = Q ∧
          N.rows = rows
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The one held-block domain for later finality channels (S3 D25). -/
def HeldAt (i : Nat) (x : V) (W : FGBlock (Fin p.n)) : Prop :=
  x ∈ rho.honest ∧ W ∈ (storeAt p c E rho i x).fg.TF
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A block held at an honest read strictly before index i. -/
def BlockInRunBefore (i : Nat) (W : FGBlock (Fin p.n)) : Prop :=
  ∃ j < i, ∃ x, HeldAt p c E rho j x W

-- equation export required by BUILD §7.2 B3a
omit [DecidableEq V] in
theorem RowSigner_def (a : RowWire p.n) (x : V) : RowSigner p c rho a x =
    (∃ i, a.auth = .seat .fg i ∧ rho.seatOf (RunLabel.base .fg) i = x) := by
  rw [RowSigner]
-- equation export required by BUILD §7.2 B3a
theorem HonestRowAt_def (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    HonestRowAt p c E rho j y r a = (y ∈ rho.honest ∧
      rho.events[j]? = some (.tick y (p.actionTime r)) ∧ ofRow p a ∈ V2.D.Run.emitsAt E rho j) := by
  rw [HonestRowAt]


/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-ROWS (21 H.22:3072–3080; P3 A.6). Consumers: TRowsSelect and TRowsSync. -/
def rowHeld (st : FGSA.State p.n) (a : RowWire p.n) : Prop :=
  a ∈ st.rowPool ∨ a ∈ FGSA.blockWireRows st
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Proposal read at t_s, after the clock (01:95–101). Consumer: T-ROWS. -/
def proposalStateAt (s : Slot) : Option (FGSA.State p.n) :=
  (postClock E rho (V2.D.proposerOf rho (fgsaInterface p c) s)
    (V2.D.proposalTime (fgsaInterface p c) s)).map (·.st)
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Exact signed row at the proposal read (21:3072–3076). Consumer: TRowsSelect. -/
def heldAtProposal (s : Slot) (a : RowWire p.n) : Prop :=
  ∃ st, proposalStateAt p c E rho s = some st ∧ rowHeld p st a
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Exact signed row on the parent's chain (21:3072–3084). Consumer: T-ROWS. -/
def onParentChain (s : Slot) (Q : Block) (a : RowWire p.n) : Prop :=
  ∃ st, proposalStateAt p c E rho s = some st ∧ a ∈ FGSA.chainWireRows st Q.parent
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Strict receipt cut (01:101–106; 21:3076–3080). Consumer: TRowsSync. -/
def HeldBefore (x : V) (a : RowWire p.n) (d : Time) : Prop :=
  Gen.V2.Duty.HoldsBefore E rho (fun nd => rowHeld p nd.st a) d x
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
R6 checks the row against the proposal parent's state at slot s. -/
def ValidForParent (s : Slot) (Q : Block) (a : RowWire p.n) : Prop :=
  ∃ st H, proposalStateAt p c E rho s = some st ∧
    FGSA.fgBlockOf st Q.parent = some H ∧
    FGSA.Window.rowValidW (FGSA.parentFoldState p s H) a = true

-- equation export required by BUILD §7.2 B3a
theorem ValidForParent_def (s : Slot) (Q : Block) (a : RowWire p.n) :
    ValidForParent p c E rho s Q a =
      (∃ st H, proposalStateAt p c E rho s = some st ∧
    FGSA.fgBlockOf st Q.parent = some H ∧
    FGSA.Window.rowValidW (FGSA.parentFoldState p s H) a = true) := rfl
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The height pair matches the current target of the proposal parent.
DC: SAME height entry; INTENTIONAL explicit consumer premise for the fold switch. -/
def HeightMatch (s : Slot) (Q : Block) (a : RowWire p.n) : Prop :=
  ∃ st H, proposalStateAt p c E rho s = some st ∧
    FGSA.fgBlockOf st Q.parent = some H ∧
    namedEntry a.payload.height_pair =
      some ((FGSA.parentFoldState p s H).h, (FGSA.parentFoldState p s H).T_h.root)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME defining equation for the height-entry premise. -/
theorem HeightMatch_def (s : Slot) (Q : Block) (a : RowWire p.n) :
    HeightMatch p c E rho s Q a =
      (∃ st H, proposalStateAt p c E rho s = some st ∧
        FGSA.fgBlockOf st Q.parent = some H ∧
        namedEntry a.payload.height_pair =
          some ((FGSA.parentFoldState p s H).h, (FGSA.parentFoldState p s H).T_h.root)) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Label-s HEAD on the post-clock state at v_s (01:150–157).
Consumers: H2.A, H2′, H3, H5 and H6. -/
def headAtLabel (x : V) (s : Slot) : Option Block :=
  (postClock E rho x (SA.voteTime p.toParams s)).map (fun nd => FGSA.headVote p nd.st s)

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
omit [DecidableEq V] in
theorem RowComplete_def (x : V) (a : RowWire p.n) :
    RowComplete p c rho x a = (a.valid = true ∧ RowSigner p c rho a x) := rfl
-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem HonestCarrier_def (s : Slot) (Q : Block) (rows : List (RowWire p.n)) :
    HonestCarrier p c E rho s Q rows = (HonestProposal E rho (fgsaInterface p c) s Q ∧
      ∃ o N, V2.D.Run.emits E rho (V2.D.proposerOf rho (fgsaInterface p c) s) o
          (V2.D.proposalTime (fgsaInterface p c) s) ∧ o.payload = .proposal N ∧ N.erase = Q ∧
            N.rows = rows) := rfl
-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem HeldAt_def (i : Nat) (x : V) (W : FGBlock (Fin p.n)) :
    HeldAt p c E rho i x W = (x ∈ rho.honest ∧ W ∈ (storeAt p c E rho i x).fg.TF) := rfl
-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem namedEntry_def (e : NamedHeightPair) :
    namedEntry e = match e with
      | .empty => none
      | .vote h r _ => some (h, r) := by
  cases e <;> rfl

end AvailableChain.FGSA.Run
end
