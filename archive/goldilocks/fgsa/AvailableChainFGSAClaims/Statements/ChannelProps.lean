module
public import AvailableChainFGSAClaims.Statements.Witness
public import AvailableChainFGSA.Statements.Invariants
public import AvailableChainFGSARun.Statements.Roots

@[expose] public section

/-! Safety channels, P3 App. A.2–A.5 (F0.8a). Each predicate describes one
run. The claim forms supply regimes. F0.8b adds Witness and the healing tier.
The property kernel remains Gen.Pure.CompatOn, MonoOn, BelowOn, ServedOn. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.carrier.v1 (00:493–501, especially 496), 01 §2: admitted-view root injectivity.
Consumers: all lanes and KitFG frame lemmas. Producer: F1.1 via `viewRootInj_TF`.
The claim has no Base premise; the existing run root premise is local here.
ROOT-DIGEST W1: The local view proof uses the store invariant; DC body scope is separate. -/
def RCarrierView : Prop := V2.D.RootInjective E (fgsaInterface p c) rho →
  ∀ i x, x ∈ rho.honest → ViewRootInj (storeAt p c E rho i x).fg.TF

theorem RCarrierView_def : RCarrierView p c E rho =
  (V2.D.RootInjective E (fgsaInterface p c) rho →
  ∀ i x, x ∈ rho.honest → ViewRootInj (storeAt p c E rho i x).fg.TF) := by
  rw [RCarrierView]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.store.v1 (00:516–527), bp.activeView.v1 (00:529–536); 01 §§4–5.
Consumers: all lanes. Producer: T7.5 and F1.1. This is a snapshot;
`RStoreCumul` states the temporal part. -/
def RStore : Prop := ∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  FGSA.CStoreInv p st ∧
  (∀ b, b ∈ (FGSA.actView st).blocks ↔
    b ∈ st.base.blocks ∧ Block.Compatible b (eraseFG st.fg.F)) ∧
  Block.genesis ∈ (FGSA.actView st).blocks ∧
  eraseFG st.fg.F ∈ (FGSA.actView st).blocks ∧
  (∀ b ∈ (FGSA.actView st).blocks, ∀ a, Block.Preceq a b →
    a ∈ (FGSA.actView st).blocks) ∧
  (FGSA.actView st).votes = st.base.votes ∧
  (FGSA.actView st).blockStamp = st.base.blockStamp ∧
  (FGSA.actView st).voteStamp = st.base.voteStamp

-- equation export required by BUILD §7.2 B3a
theorem RStore_def :
    RStore p c E rho = (∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  FGSA.CStoreInv p st ∧
  (∀ b, b ∈ (FGSA.actView st).blocks ↔
    b ∈ st.base.blocks ∧ Block.Compatible b (eraseFG st.fg.F)) ∧
  Block.genesis ∈ (FGSA.actView st).blocks ∧
  eraseFG st.fg.F ∈ (FGSA.actView st).blocks ∧
  (∀ b ∈ (FGSA.actView st).blocks, ∀ a, Block.Preceq a b →
    a ∈ (FGSA.actView st).blocks) ∧
  (FGSA.actView st).votes = st.base.votes ∧
  (FGSA.actView st).blockStamp = st.base.blockStamp ∧
  (FGSA.actView st).voteStamp = st.base.voteStamp) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.activeView.v1 (00:529–536), 01 §5: the remaining active-view laws.
Consumers: all lanes, P3:3263. Producer: F1.1 via `actView_antitone`,
`actView_path`, `blockExcluded_stable`, `actView_blocks`, and `actView_fields`.
The run clause excludes a conflicting block after any descendant F move. -/
def RActive : Prop := (∀ i x, x ∈ rho.honest →
    let st := storeAt p c E rho i x
    (∀ F' : FGBlock (Fin p.n), FGBlock.Preceq st.fg.F F' →
      ∀ b ∈ (FGSA.actView { st with fg := { st.fg with F := F' } }).blocks,
        b ∈ (FGSA.actView st).blocks) ∧
    (∀ B K, K ∈ st.base.blocks → Block.Preceq (eraseFG st.fg.F) B →
      Block.Preceq B K → K ∈ (FGSA.actView st).blocks ∧ B ∈ (FGSA.actView st).blocks) ∧
    (FGSA.actView st).proposals = st.base.proposals) ∧
  (∀ i j x b, x ∈ rho.honest → i ≤ j →
    let st := storeAt p c E rho i x
    let st' := storeAt p c E rho j x
    FGBlock.Preceq st.fg.F st'.fg.F →
    ¬ Block.Compatible b (eraseFG st.fg.F) → b ∉ (FGSA.actView st').blocks)

theorem RActive_def : RActive p c E rho =
  ((∀ i x, x ∈ rho.honest →
    let st := storeAt p c E rho i x
    (∀ F' : FGBlock (Fin p.n), FGBlock.Preceq st.fg.F F' →
      ∀ b ∈ (FGSA.actView { st with fg := { st.fg with F := F' } }).blocks,
        b ∈ (FGSA.actView st).blocks) ∧
    (∀ B K, K ∈ st.base.blocks → Block.Preceq (eraseFG st.fg.F) B →
      Block.Preceq B K → K ∈ (FGSA.actView st).blocks ∧ B ∈ (FGSA.actView st).blocks) ∧
    (FGSA.actView st).proposals = st.base.proposals) ∧
  (∀ i j x b, x ∈ rho.honest → i ≤ j →
    let st := storeAt p c E rho i x
    let st' := storeAt p c E rho j x
    FGBlock.Preceq st.fg.F st'.fg.F →
    ¬ Block.Compatible b (eraseFG st.fg.F) → b ∉ (FGSA.actView st').blocks)) := by
  rw [RActive]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.store.v1 (00:517–518): cumulative T and unchanged old stamps.
Consumers: all lanes, 02 §5.2, 21 H.12. Producer: F1.1 via
`process_cumulative` and `clock_cumulative`. Restarts reset the store. -/
def RStoreCumul : Prop := V2.D.NoRestart rho → ∀ i j x, x ∈ rho.honest →
  i ≤ j → j ≤ rho.events.length →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  st.fg.TF ⊆ st'.fg.TF ∧ st.base.blocks <+: st'.base.blocks ∧
  st.base.blockStamp <+: st'.base.blockStamp ∧ st.base.voteStamp <+: st'.base.voteStamp

-- equation export required by BUILD §7.2 B3a
theorem RStoreCumul_def :
    RStoreCumul p c E rho = (V2.D.NoRestart rho → ∀ i j x, x ∈ rho.honest →
  i ≤ j → j ≤ rho.events.length →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  st.fg.TF ⊆ st'.fg.TF ∧ st.base.blocks <+: st'.base.blocks ∧
  st.base.blockStamp <+: st'.base.blockStamp ∧ st.base.voteStamp <+: st'.base.voteStamp) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.store.v1 (00:516–527), last sentence: F, the lex pair, and H increase.
Consumers: 02 §5.3, 03 F′ cases, 22 FF2. Producer: F1.1 via `fMonotone`,
`process_pair_mono`, and `process_hmax_mono`. -/
def RMono : Prop := V2.D.NoRestart rho → ∀ i j x, x ∈ rho.honest → i ≤ j →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  FGBlock.Preceq st.fg.F st'.fg.F ∧
  lexKey (st.fg.h_j, st.fg.J) ≤ lexKey (st'.fg.h_j, st'.fg.J) ∧
  st.fg.h_max ≤ st'.fg.h_max

-- equation export required by BUILD §7.2 B3a
theorem RMono_def :
    RMono p c E rho = (V2.D.NoRestart rho → ∀ i j x, x ∈ rho.honest → i ≤ j →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  FGBlock.Preceq st.fg.F st'.fg.F ∧
  lexKey (st.fg.h_j, st.fg.J) ≤ lexKey (st'.fg.h_j, st'.fg.J) ∧
  st.fg.h_max ≤ st'.fg.h_max) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.frame.v1 (00:581–587), 01 §1.1 and §4.3: cached controls and D(Σ.T).
Consumers: 02 §4.1, 22 F6/F8/FL-T7, 21 H.17. Producer: F1.1 via `storeControls_eq`. -/
def RFrameExact : Prop := ∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  FGSA.controls p st = KitFG.fjControlsView (heightView p) st.fg.F st.fg.TF ∧
  FGSA.fullTree p st = domainR p st st.fg.TF

-- equation export required by BUILD §7.2 B3a
theorem RFrameExact_def :
    RFrameExact p c E rho = (∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  FGSA.controls p st = KitFG.fjControlsView (heightView p) st.fg.F st.fg.TF ∧
  FGSA.fullTree p st = domainR p st st.fg.TF) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.frame.v1 (00:581–587), 01 §4.3 (435–458): the FG projection and metadata.
Consumers: 02 §4.1, 22 F6/F8/FL-T7, 21 H.17. Producer: F1.1 via
`admitBlock_accepted_eq`, `onView_fg`, `clock_fg`, `admitBlock_refused`,
`reconcile_frame`, `metadataInvariant`, and `process_cumulative`.
The tree-read inventory is 00 §2.4 (219–239); 01:454–455 preserves its metadata.
SA changes use the existing operations. Only temporal metadata needs NoRestart. -/
def RFrame : Prop := ∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  (∀ s N P, namedParentHeld st N = true → parentFG st N.erase = some P →
    blockAccepted p st s N P = true →
    (admitBlock p st s N).fg = Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)) ∧
  ((∀ f : GridCO.State p.n .root → GridCO.State p.n .root, (onView f st).fg = st.fg) ∧
    (∀ s k b, (admitHead p st s k b).fg = st.fg) ∧
    (∀ a, (admitRow p st a).fg = st.fg) ∧
    (∀ t, (FGSA.clock p st t).fg = st.fg) ∧
    (∀ s N,
      (namedParentHeld st N = false ∨ parentFG st N.erase = none ∨
        ∃ P, parentFG st N.erase = some P ∧ blockAccepted p st s N P = false) →
      (admitBlock p st s N).fg = st.fg) ∧
    (∀ o, o.decode = none → (FGSA.process p st o).fg = st.fg)) ∧
  (FGSA.controls p (FGSA.reconcile st) = FGSA.controls p st ∧
    ∀ X, domainR p (FGSA.reconcile st) X = domainR p st X) ∧
  (MetaInv p st ∧
    (∀ s, proposalsAt st s = st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => if N.slot = s then some (N.raw, N.support) else none
      | _ => none)) ∧
    (∀ H, chainWireRows st H = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => if Block.preceq N.erase H then some N.rows else none
      | _ => none)).flatten) ∧
    (blockWireRows st = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => some N.rows
      | _ => none)).flatten) ∧
    (∀ s, voterBlocks p st s = st.fg.TF.filter (fun B =>
      decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
      decide (∃ P ∈ st.fg.TF, P.slot = s ∧ FGBlock.Preceq B P))) ∧
    (∀ s, headVotes p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))) ++
        (((proposalsAt st s).flatMap (fun row => row.1.map baseVote)).filter
          (fun o => GridCO.headLabel? o == some (s - 1)))).eraseDups) ∧
    (∀ s, headSupport p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        GridCO.resolvedBefore (FGSA.actView st) o (SA.freezeTime p.toParams (s - 1)))) ++
        (((proposalsAt st s).flatMap (fun row => row.2.map baseVote)).filter (fun o =>
          GridCO.headLabel? o == some (s - 1) && match GridCO.resolvedHead? st.base o with
          | some h => decide (h.slot ≤ s - 1)
          | none => false))).eraseDups) ∧
    (∀ H, proposalRows p st H =
      match fgBlockOf st H with
      | none => []
      | some P =>
          (st.rowPool ++ blockWireRows st).eraseDups.filter (fun a =>
            Window.rowValidW (parentFoldState p (st.slot p) P) a &&
              !decide (a ∈ chainWireRows st H))) ∧
    (V2.D.NoRestart rho → ∀ j, i ≤ j → j ≤ rho.events.length →
      let st' := storeAt p c E rho j x
      st.proposals <+: st'.proposals ∧ st.rowPool <+: st'.rowPool ∧
      st.base.blockStamp <+: st'.base.blockStamp ∧ st.base.voteStamp <+: st'.base.voteStamp))

theorem RFrame_def : RFrame p c E rho =
  (∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  (∀ s N P, namedParentHeld st N = true → parentFG st N.erase = some P →
    blockAccepted p st s N P = true →
    (admitBlock p st s N).fg = Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)) ∧
  ((∀ f : GridCO.State p.n .root → GridCO.State p.n .root, (onView f st).fg = st.fg) ∧
    (∀ s k b, (admitHead p st s k b).fg = st.fg) ∧
    (∀ a, (admitRow p st a).fg = st.fg) ∧
    (∀ t, (FGSA.clock p st t).fg = st.fg) ∧
    (∀ s N,
      (namedParentHeld st N = false ∨ parentFG st N.erase = none ∨
        ∃ P, parentFG st N.erase = some P ∧ blockAccepted p st s N P = false) →
      (admitBlock p st s N).fg = st.fg) ∧
    (∀ o, o.decode = none → (FGSA.process p st o).fg = st.fg)) ∧
  (FGSA.controls p (FGSA.reconcile st) = FGSA.controls p st ∧
    ∀ X, domainR p (FGSA.reconcile st) X = domainR p st X) ∧
  (MetaInv p st ∧
    (∀ s, proposalsAt st s = st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => if N.slot = s then some (N.raw, N.support) else none
      | _ => none)) ∧
    (∀ H, chainWireRows st H = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => if Block.preceq N.erase H then some N.rows else none
      | _ => none)).flatten) ∧
    (blockWireRows st = (st.proposals.filterMap (fun o => match o.decode with
      | some (.block _ N) => some N.rows
      | _ => none)).flatten) ∧
    (∀ s, voterBlocks p st s = st.fg.TF.filter (fun B =>
      decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
      decide (∃ P ∈ st.fg.TF, P.slot = s ∧ FGBlock.Preceq B P))) ∧
    (∀ s, headVotes p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))) ++
        (((proposalsAt st s).flatMap (fun row => row.1.map baseVote)).filter
          (fun o => GridCO.headLabel? o == some (s - 1)))).eraseDups) ∧
    (∀ s, headSupport p st s =
      (((GridCO.votesAt st.base (s - 1)).filter (fun o =>
        GridCO.resolvedBefore (FGSA.actView st) o (SA.freezeTime p.toParams (s - 1)))) ++
        (((proposalsAt st s).flatMap (fun row => row.2.map baseVote)).filter (fun o =>
          GridCO.headLabel? o == some (s - 1) && match GridCO.resolvedHead? st.base o with
          | some h => decide (h.slot ≤ s - 1)
          | none => false))).eraseDups) ∧
    (∀ H, proposalRows p st H =
      match fgBlockOf st H with
      | none => []
      | some P =>
          (st.rowPool ++ blockWireRows st).eraseDups.filter (fun a =>
            Window.rowValidW (parentFoldState p (st.slot p) P) a &&
              !decide (a ∈ chainWireRows st H))) ∧
    (V2.D.NoRestart rho → ∀ j, i ≤ j → j ≤ rho.events.length →
      let st' := storeAt p c E rho j x
      st.proposals <+: st'.proposals ∧ st.rowPool <+: st'.rowPool ∧
      st.base.blockStamp <+: st'.base.blockStamp ∧ st.base.voteStamp <+: st'.base.voteStamp))) := by
  rw [RFrame]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.chainCertificates.v1 (00:503–514): path heights and entries.
Consumers: 02 §3.1, 21 H.9(a), 22 I2. Producer: F1.1 from KitFG
`h_mono`, `derive_node_height_cases`, `entry_same_height`, `entry_eq_on_plateau`. -/
def RGeo : Prop := ∀ i x W, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
  (heightView p (.genesis : FGBlock (Fin p.n))).h = 1 ∧
  (∀ A B, FGBlock.Preceq A B → FGBlock.Preceq B W → (heightView p A).h ≤ (heightView p B).h) ∧
  (∀ B, FGBlock.Preceq B W → (heightView p B).h ≤ (heightView p B.parent).h + 1) ∧
  (∀ B, FGBlock.Preceq B W →
    FGBlock.Preceq (heightView p B).T_h B ∧
    (heightView p (heightView p B).T_h).h = (heightView p B).h) ∧
  (∀ A B, FGBlock.Preceq A B → FGBlock.Preceq B W →
    (heightView p A).h = (heightView p B).h → (heightView p A).T_h = (heightView p B).T_h)

-- equation export required by BUILD §7.2 B3a
theorem RGeo_def :
    RGeo p c E rho = (∀ i x W, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
  (heightView p (.genesis : FGBlock (Fin p.n))).h = 1 ∧
  (∀ A B, FGBlock.Preceq A B → FGBlock.Preceq B W → (heightView p A).h ≤ (heightView p B).h) ∧
  (∀ B, FGBlock.Preceq B W → (heightView p B).h ≤ (heightView p B.parent).h + 1) ∧
  (∀ B, FGBlock.Preceq B W →
    FGBlock.Preceq (heightView p B).T_h B ∧
    (heightView p (heightView p B).T_h).h = (heightView p B).h) ∧
  (∀ A B, FGBlock.Preceq A B → FGBlock.Preceq B W →
    (heightView p A).h = (heightView p B).h → (heightView p A).T_h = (heightView p B).T_h)) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.chainCertificates.v1 (00:503–514), 01 §3: stored-block certificates.
Consumers: P3:3259–3261, 02 §3.1, 21 H.9(a), 22 I2.
Producer: F1.1 via KitFG `height_crossing`, `justification_certificate`,
`finality_certificate`, and `provenance_finality`; `J_is_entry` identifies
its justified entry. No run premise is needed. -/
def RCert : Prop := ∀ i x W, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
  (∀ m, 1 ≤ m → m < (heightView p W).h →
    ∃ X : FGBlock (Fin p.n), FGBlock.Preceq X W ∧ (heightView p X).h = m ∧
      ∃ Q : Finset (Fin p.n), p.E.IsQuorum Q ∧
        ∀ k ∈ Q, ∃ carrier : FGBlock (Fin p.n), ∃ a : Row (Fin p.n),
          FGBlock.Preceq carrier W ∧ a ∈ carrier.rows ∧ a.signer = k ∧
          a.height_pair.matchesEntry m X.root = true) ∧
  ((heightView p W).h_j ≠ 0 →
    ∃ Q : Finset (Fin p.n), p.E.IsQuorum Q ∧ ∀ k ∈ Q, ∃ carrier a,
      FGBlock.Preceq carrier W ∧ a ∈ carrier.rows ∧ a.signer = k ∧
      a.height_pair = .vote (heightView p W).h_j (heightView p W).J.root false) ∧
  ((finalityView p W).h_F ≠ 0 →
    ∃ F : FGBlock (Fin p.n), FGBlock.Preceq F W ∧ F = (finalityView p W).F ∧
      ∃ Q : Finset (Fin p.n), p.E.IsQuorum Q ∧
        ∀ k ∈ Q, ∃ carrier : FGBlock (Fin p.n), ∃ a : Row (Fin p.n),
          FGBlock.Preceq carrier W ∧ a ∈ carrier.rows ∧ a.signer = k ∧
          a.finality_pair = some ⟨(finalityView p W).h_F, F.root⟩) ∧
  ((finalityView p W).h_F ≠ 0 →
    ∃ C, FGBlock.Preceq C W ∧ (heightView p C).J = (finalityView p W).F ∧
      (heightView p C).h_j = (finalityView p W).h_F)

theorem RCert_def : RCert p c E rho =
  (∀ i x W, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
  (∀ m, 1 ≤ m → m < (heightView p W).h →
    ∃ X : FGBlock (Fin p.n), FGBlock.Preceq X W ∧ (heightView p X).h = m ∧
      ∃ Q : Finset (Fin p.n), p.E.IsQuorum Q ∧
        ∀ k ∈ Q, ∃ carrier : FGBlock (Fin p.n), ∃ a : Row (Fin p.n),
          FGBlock.Preceq carrier W ∧ a ∈ carrier.rows ∧ a.signer = k ∧
          a.height_pair.matchesEntry m X.root = true) ∧
  ((heightView p W).h_j ≠ 0 →
    ∃ Q : Finset (Fin p.n), p.E.IsQuorum Q ∧ ∀ k ∈ Q, ∃ carrier a,
      FGBlock.Preceq carrier W ∧ a ∈ carrier.rows ∧ a.signer = k ∧
      a.height_pair = .vote (heightView p W).h_j (heightView p W).J.root false) ∧
  ((finalityView p W).h_F ≠ 0 →
    ∃ F : FGBlock (Fin p.n), FGBlock.Preceq F W ∧ F = (finalityView p W).F ∧
      ∃ Q : Finset (Fin p.n), p.E.IsQuorum Q ∧
        ∀ k ∈ Q, ∃ carrier : FGBlock (Fin p.n), ∃ a : Row (Fin p.n),
          FGBlock.Preceq carrier W ∧ a ∈ carrier.rows ∧ a.signer = k ∧
          a.finality_pair = some ⟨(finalityView p W).h_F, F.root⟩) ∧
  ((finalityView p W).h_F ≠ 0 →
    ∃ C, FGBlock.Preceq C W ∧ (heightView p C).J = (finalityView p W).F ∧
      (heightView p C).h_j = (finalityView p W).h_F)) := by
  rw [RCert]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.reconcile.v1 (00:559–567), 01 §6: the exact AC edits at an F move.
The displayed record update isolates reconcile from the other admission writes.
Consumers: 02 §5.3, 03 F′ cases, 21 IF.7, 22 I5. Producer: F1.4 via
`reconcile_frame`, `reconcile_harmless_origin`, `admitBlock_reconcile_harmless`. -/
def RRec : Prop := ∀ i x, x ∈ rho.honest → FAdvanceAt p c E rho i x →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho (i + 1) x
  st'.base.obligations = st.base.obligations.filter (fun row => FGSA.activeCompatible st' row.1) ∧
  st'.base.genuine = st.base.genuine.map
    (fun row => (row.1, row.2.filter (FGSA.activeCompatible st'))) ∧
  st'.fastWrite = st.fastWrite.map
    (fun row => (row.1, row.2.filter (FGSA.activeCompatible st'))) ∧
  st'.base.stableRecord =
    (if Block.preceq (eraseFG st'.fg.F) st.base.stableRecord then st.base.stableRecord
     else eraseFG st'.fg.F) ∧
  (V2.D.Run.stateBefore E rho (i + 1) x).record = (V2.D.Run.stateBefore E rho i x).record ∧
  (∀ u : State p.n, FGSA.reconcile u = { u with
    base := { u.base with
      obligations := u.base.obligations.filter (fun row => FGSA.activeCompatible u row.1)
      genuine := u.base.genuine.map (fun row => (row.1, row.2.filter (FGSA.activeCompatible u)))
      stableRecord := if Block.preceq (eraseFG u.fg.F) u.base.stableRecord then
        u.base.stableRecord else eraseFG u.fg.F }
    fastWrite := u.fastWrite.map (fun row => (row.1, row.2.filter (FGSA.activeCompatible u))) })

-- equation export required by BUILD §7.2 B3a
theorem RRec_def :
    RRec p c E rho = (∀ i x, x ∈ rho.honest → FAdvanceAt p c E rho i x →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho (i + 1) x
  st'.base.obligations = st.base.obligations.filter (fun row => FGSA.activeCompatible st' row.1) ∧
  st'.base.genuine = st.base.genuine.map
    (fun row => (row.1, row.2.filter (FGSA.activeCompatible st'))) ∧
  st'.fastWrite = st.fastWrite.map
    (fun row => (row.1, row.2.filter (FGSA.activeCompatible st'))) ∧
  st'.base.stableRecord =
    (if Block.preceq (eraseFG st'.fg.F) st.base.stableRecord then st.base.stableRecord
     else eraseFG st'.fg.F) ∧
  (V2.D.Run.stateBefore E rho (i + 1) x).record = (V2.D.Run.stateBefore E rho i x).record ∧
  (∀ u : State p.n, FGSA.reconcile u = { u with
    base := { u.base with
      obligations := u.base.obligations.filter (fun row => FGSA.activeCompatible u row.1)
      genuine := u.base.genuine.map (fun row => (row.1, row.2.filter (FGSA.activeCompatible u)))
      stableRecord := if Block.preceq (eraseFG u.fg.F) u.base.stableRecord then
        u.base.stableRecord else eraseFG u.fg.F }
    fastWrite := u.fastWrite.map (fun row => (row.1, row.2.filter (FGSA.activeCompatible u))) })) :=
  rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
01 §1.1 T-SRC (74–79), bp.sourceDiscipline.v1(a) (00:689–697).
Consumers: CPPrefix in 02 §5.4 and 03 §8, 21 H.11, 22 kernel.
Producer: F1.5(a) via `FastOrigin`, `fastOrigin_gateStep`, `deepest_spec`. -/
def TSrc : Prop := ∀ x r C, x ∈ rho.honest →
  actionSource p c E rho x r = some (some C) →
  ∃ X G, candidatesAt p c E rho x r = some X ∧ C ∈ X ∧
    gateResult p c E rho x (r * p.R) = some (some G) ∧
    (∀ B ∈ X, Block.Preceq B G) ∧ (∀ B ∈ X, fastAt p c E rho x (r * p.R) B) ∧
    ∃ j, IsGateTick p c rho j x (r * p.R) ∧ gatePassedAt p c E rho j

-- equation export required by BUILD §7.2 B3a
theorem TSrc_def :
    TSrc p c E rho = (∀ x r C, x ∈ rho.honest →
  actionSource p c E rho x r = some (some C) →
  ∃ X G, candidatesAt p c E rho x r = some X ∧ C ∈ X ∧
    gateResult p c E rho x (r * p.R) = some (some G) ∧
    (∀ B ∈ X, Block.Preceq B G) ∧ (∀ B ∈ X, fastAt p c E rho x (r * p.R) B) ∧
    ∃ j, IsGateTick p c rho j x (r * p.R) ∧ gatePassedAt p c E rho j) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
01 §8.4 (795–801): earlier honest row sources have bounded gate labels.
This also applies to every such row used by a duty. At q_s the bound is s−1;
at a positive-slot proposal or HEAD it is s−2. Consumers: TimingContract.label
and BelowLabel in the Clean induction. Producer: F1.5(d). -/
def LabelBound : Prop := ∀ i x y r a t, x ∈ rho.honest →
  rho.events[i]? = some (.tick x t) → HonestRowBefore p c E rho i y r a →
  r * p.R ≤ labelBoundAt p c rho i ∧
  (∀ s, t = SA.releaseTime p.toParams s → r * p.R ≤ s - 1) ∧
  (∀ s, 1 ≤ s → (t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s) →
    r * p.R ≤ s - 2)

-- equation export required by BUILD §7.2 B3a
theorem LabelBound_def :
    LabelBound p c E rho = (∀ i x y r a t, x ∈ rho.honest →
  rho.events[i]? = some (.tick x t) → HonestRowBefore p c E rho i y r a →
  r * p.R ≤ labelBoundAt p c rho i ∧
  (∀ s, t = SA.releaseTime p.toParams s → r * p.R ≤ s - 1) ∧
  (∀ s, 1 ≤ s → (t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s) →
    r * p.R ≤ s - 2)) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.cleanHistory.v1 (00:767–775): honest raw results through b₀ lie on
one chain; each nonempty emitted name through b₀ lies below such a result.
Consumers: no lane assumes this; F2 proves it as the Clean composition result. -/
def TChain (b₀ : Time) : Prop :=
  (∀ x y s r B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ b₀ → SA.gateTime p.toParams r ≤ b₀ →
    gateResult p c E rho x s = some (some B) → gateResult p c E rho y r = some (some C) →
    Block.Compatible B C) ∧
  (∀ i x r a e t, HonestRowAt p c E rho i x r a →
    rho.events[i]? = some (.tick x t) → t ≤ b₀ → namedEntry a.payload.height_pair = some e →
    ∃ s B X, SA.gateTime p.toParams s ≤ b₀ ∧ gateResult p c E rho x s = some (some B) ∧
      ((heightView p X).h, X.root) = e ∧ Block.Preceq (eraseFG X) B)

-- equation export required by BUILD §7.2 B3a
theorem TChain_def (b₀ : Time) :
    TChain p c E rho b₀ = ((∀ x y s r B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ b₀ → SA.gateTime p.toParams r ≤ b₀ →
    gateResult p c E rho x s = some (some B) → gateResult p c E rho y r = some (some C) →
    Block.Compatible B C) ∧
  (∀ i x r a e t, HonestRowAt p c E rho i x r a →
    rho.events[i]? = some (.tick x t) → t ≤ b₀ → namedEntry a.payload.height_pair = some e →
    ∃ s B X, SA.gateTime p.toParams s ≤ b₀ ∧ gateResult p c E rho x s = some (some B) ∧
      ((heightView p X).h, X.root) = e ∧ Block.Preceq (eraseFG X) B)) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
03 §8.3 (702–726): after arming at d_j, honest sources are compatible
with protected B. Vocabulary: no claim asserts or consumes this predicate;
a bounded form (actionTime r < b₁) stays private to stage-5 O-INDUCT. -/
def TCompat (B : Block) (j : Slot) : Prop := ∀ x r C, x ∈ rho.honest →
  SA.gateTime p.toParams j ≤ p.actionTime r → actionSource p c E rho x r = some (some C) →
  Block.Compatible C B

-- equation export required by BUILD §7.2 B3a
theorem TCompat_def (B : Block) (j : Slot) :
    TCompat p c E rho B j = (∀ x r C, x ∈ rho.honest →
  SA.gateTime p.toParams j ≤ p.actionTime r → actionSource p c E rho x r = some (some C) →
  Block.Compatible C B) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
S3 D09, P3 App. A.10: the source-frame predicate is closed under ancestors.
Consumers: F1.5 source frame, then F2–F5 via SrcFrameAboveStmt. -/
structure AncestorClosed (Φ : FGBlock (Fin p.n) → Prop) : Prop where
  down : ∀ X Y, FGBlock.Preceq X Y → Φ Y → Φ X

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.10: bp.cleanFrame.v1, 02 §3; lead FB1.
Each frame block above the threshold satisfies Φ. -/
def FrameBelow (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat)
    (R : Controls (Fin p.n)) : Prop :=
  (c₀ ≤ (heightView p R.F).h → Φ R.F) ∧
  (c₀ ≤ (heightView p R.J).h → Φ R.J) ∧
  (c₀ ≤ (heightView p R.Z).h → Φ R.Z)

-- equation export required by BUILD §7.2 B3a
theorem FrameBelow_def (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat)
    (R : Controls (Fin p.n)) :
    FrameBelow p Φ c₀ R = ((c₀ ≤ (heightView p R.F).h → Φ R.F) ∧
  (c₀ ≤ (heightView p R.J).h → Φ R.J) ∧
  (c₀ ≤ (heightView p R.Z).h → Φ R.Z)) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.2: bp.sourceDiscipline.v1(b,c), 01 §8.4, 02 §§3.3–3.5.
Each non-genesis certified entry has an earlier honest row at its height. -/
def RStrat : Prop := ∀ i x W, x ∈ rho.honest →
  W ∈ (storeAt p c E rho i x).fg.TF →
  ∀ e ∈ certified p W, e ≠ .genesis →
    ∃ y r, ∃ a : RowWire p.n, HonestRowBefore p c E rho i y r a ∧
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root)

-- equation export required by BUILD §7.2 B3a
theorem RStrat_def :
    RStrat p c E rho = (∀ i x W, x ∈ rho.honest →
  W ∈ (storeAt p c E rho i x).fg.TF →
  ∀ e ∈ certified p W, e ≠ .genesis →
    ∃ y r, ∃ a : RowWire p.n, HonestRowBefore p c E rho i y r a ∧
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root)) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.sourceDiscipline.v1 (00:689–697, especially 691–695), 01 §8.4 (788–793).
Consumers: F2–F5 through SourceDisciplineAt. Producer: F1.5 via certificate-row
lifting, the honest action source proof, and KitFG `provenance_finality`.
SourceDisciplinePrem.quorum supplies FaultQ; no extra count hypothesis is needed.
Every selected QC has an exact honest row with an earlier source. Finalization
uses a target QC of its prior justification, with no finality-row height test. -/
def RQCOrigin : Prop := ∀ i x W, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
  let origin := fun (carrier : FGBlock (Fin p.n)) (a : Row (Fin p.n)) =>
    ∃ y r, ∃ wire : RowWire p.n, HonestRowBefore p c E rho i y r wire ∧
      wire.toRow? = some a ∧
      (∃ s N, N.erase = eraseFG carrier ∧
        (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
          (storeAt p c E rho i x).proposals ∧ wire ∈ N.rows) ∧
      ∃ C G, actionSourceFG p c E rho y r = some (some C) ∧
        namedEntry a.height_pair = some ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C)
  (∀ m X (Q : Finset (Fin p.n)) (rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)),
    1 ≤ m → m < (heightView p W).h →
    FGBlock.Preceq X W → (heightView p X).h = m → p.E.IsQuorum Q →
    (∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
      (rows k).2.signer = k ∧ (rows k).2.height_pair.matchesEntry m X.root = true) →
    ∃ k ∈ Q, origin (rows k).1 (rows k).2) ∧
  (∀ (Q : Finset (Fin p.n)) (rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)),
    (heightView p W).h_j ≠ 0 → p.E.IsQuorum Q →
    (∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
      (rows k).2.signer = k ∧
      (rows k).2.height_pair = .vote (heightView p W).h_j (heightView p W).J.root false) →
    ∃ k ∈ Q, origin (rows k).1 (rows k).2) ∧
  ((finalityView p W).F ≠ .genesis →
    ∃ C, FGBlock.Preceq C W ∧ (heightView p C).J = (finalityView p W).F ∧
      (heightView p C).h_j = (finalityView p W).h_F ∧
      ∃ (Q : Finset (Fin p.n)) (rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)),
        p.E.IsQuorum Q ∧
        (∀ k ∈ Q, FGBlock.Preceq (rows k).1 C ∧ (rows k).2 ∈ (rows k).1.rows ∧
          (rows k).2.signer = k ∧
          (rows k).2.height_pair =
            .vote (heightView p C).h_j (heightView p C).J.root false) ∧
        ∃ k ∈ Q, origin (rows k).1 (rows k).2)

theorem RQCOrigin_def : RQCOrigin p c E rho =
  (∀ i x W, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
  let origin := fun (carrier : FGBlock (Fin p.n)) (a : Row (Fin p.n)) =>
    ∃ y r, ∃ wire : RowWire p.n, HonestRowBefore p c E rho i y r wire ∧
      wire.toRow? = some a ∧
      (∃ s N, N.erase = eraseFG carrier ∧
        (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
          (storeAt p c E rho i x).proposals ∧ wire ∈ N.rows) ∧
      ∃ C G, actionSourceFG p c E rho y r = some (some C) ∧
        namedEntry a.height_pair = some ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C)
  (∀ m X (Q : Finset (Fin p.n)) (rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)),
    1 ≤ m → m < (heightView p W).h →
    FGBlock.Preceq X W → (heightView p X).h = m → p.E.IsQuorum Q →
    (∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
      (rows k).2.signer = k ∧ (rows k).2.height_pair.matchesEntry m X.root = true) →
    ∃ k ∈ Q, origin (rows k).1 (rows k).2) ∧
  (∀ (Q : Finset (Fin p.n)) (rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)),
    (heightView p W).h_j ≠ 0 → p.E.IsQuorum Q →
    (∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
      (rows k).2.signer = k ∧
      (rows k).2.height_pair = .vote (heightView p W).h_j (heightView p W).J.root false) →
    ∃ k ∈ Q, origin (rows k).1 (rows k).2) ∧
  ((finalityView p W).F ≠ .genesis →
    ∃ C, FGBlock.Preceq C W ∧ (heightView p C).J = (finalityView p W).F ∧
      (heightView p C).h_j = (finalityView p W).h_F ∧
      ∃ (Q : Finset (Fin p.n)) (rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)),
        p.E.IsQuorum Q ∧
        (∀ k ∈ Q, FGBlock.Preceq (rows k).1 C ∧ (rows k).2 ∈ (rows k).1.rows ∧
          (rows k).2.signer = k ∧
          (rows k).2.height_pair =
            .vote (heightView p C).h_j (heightView p C).J.root false) ∧
        ∃ k ∈ Q, origin (rows k).1 (rows k).2)) := by
  rw [RQCOrigin]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.10, S3 D09: bp.sourceDiscipline.v1, 01 §8.4.
T1 names an FG block by its height and root.
genesis case: P3 r3.5.6 form refutable at index 0; lead G1. -/
def SrcFrameAbove (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat) : Prop :=
  (c₀ ≤ (heightView p (.genesis : FGBlock (Fin p.n))).h → Φ .genesis) →
  ∀ i x, x ∈ rho.honest →
    (∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
      HonestRowBefore p c E rho i y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      c₀ ≤ (heightView p e).h → Φ e) →
    (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
      c₀ ≤ (heightView p e).h → Φ e) ∧ FrameBelow p Φ c₀ (R_at p c E rho i x)

-- equation export required by BUILD §7.2 B3a
theorem SrcFrameAbove_def (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat) :
    SrcFrameAbove p c E rho Φ c₀ =
      ((c₀ ≤ (heightView p (.genesis : FGBlock (Fin p.n))).h → Φ .genesis) →
  ∀ i x, x ∈ rho.honest →
    (∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
      HonestRowBefore p c E rho i y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      c₀ ≤ (heightView p e).h → Φ e) →
    (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
      c₀ ≤ (heightView p e).h → Φ e) ∧ FrameBelow p Φ c₀ (R_at p c E rho i x)) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.10, S3 D09: source frame at threshold zero. -/
abbrev SrcFrame (Φ : FGBlock (Fin p.n) → Prop) : Prop :=
  SrcFrameAbove p c E rho Φ 0

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.10, G30: source frame for each ancestor-closed predicate and threshold.
Blueprint bp.sourceDiscipline.v1, 01 §8.4. -/
def SrcFrameAboveStmt : Prop :=
  ∀ (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat),
    AncestorClosed p Φ → SrcFrameAbove p c E rho Φ c₀

-- equation export required by BUILD §7.2 B3a
theorem SrcFrameAboveStmt_def :
    SrcFrameAboveStmt p c E rho = (∀ (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat),
    AncestorClosed p Φ → SrcFrameAbove p c E rho Φ c₀) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 App. A.3: bp.cleanFrame.v1 (00:733–741), 02 §3.
The EntryBelow premise and prefix conclusion are frozen. -/
def CPPrefix : Prop := ∀ i x (B : FGBlock (Fin p.n)), x ∈ rho.honest →
  RootBlockInRun p c E rho (eraseFG B) →
  (∀ y r (a : RowWire p.n) e, HonestRowBefore p c E rho i y r a →
    namedEntry a.payload.height_pair = some e → EntryBelow p e B) →
  (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W, FGBlock.Preceq e B) ∧
  (let R := R_at p c E rho i x
   FGBlock.Preceq R.F B ∧ FGBlock.Preceq R.J B ∧ FGBlock.Preceq R.Z B ∧
   R.contest = false ∧ R.lo ≤ (heightView p B).h)

-- equation export required by BUILD §7.2 B3a
theorem CPPrefix_def :
    CPPrefix p c E rho = (∀ i x (B : FGBlock (Fin p.n)), x ∈ rho.honest →
  RootBlockInRun p c E rho (eraseFG B) →
  (∀ y r (a : RowWire p.n) e, HonestRowBefore p c E rho i y r a →
    namedEntry a.payload.height_pair = some e → EntryBelow p e B) →
  (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W, FGBlock.Preceq e B) ∧
  (let R := R_at p c E rho i x
   FGBlock.Preceq R.F B ∧ FGBlock.Preceq R.J B ∧ FGBlock.Preceq R.Z B ∧
   R.contest = false ∧ R.lo ≤ (heightView p B).h)) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.3: bp.outageCompatibility.v1 (00:850–859), 03 §7.
Every contest witness extends B (lead-approved universal form). -/
def CPCompat : Prop := ∀ i x (B : FGBlock (Fin p.n)), x ∈ rho.honest →
  (∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
    HonestRowBefore p c E rho i y r a →
    namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
    FGBlock.Preceq e B ∨ FGBlock.Preceq B e) →
  (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
    FGBlock.Preceq e B ∨ FGBlock.Preceq B e) ∧
  (let st := storeAt p c E rho i x
   let R := R_at p c E rho i x
   (FGBlock.Preceq R.F B ∨ FGBlock.Preceq B R.F) ∧
   (FGBlock.Preceq R.J B ∨ FGBlock.Preceq B R.J) ∧
   (B ∈ st.fg.TF → FGBlock.Preceq R.F B →
     FGBlock.Preceq B R.Z ∨ B ∈ domainR p st st.fg.TF) ∧
   (R.contest = true → FGBlock.Preceq B R.J ∧
     ∀ W ∈ st.fg.TF, (heightView p W).h = R.H → ¬ FGBlock.Preceq R.J W →
       FGBlock.Preceq B W))

-- equation export required by BUILD §7.2 B3a
theorem CPCompat_def :
    CPCompat p c E rho = (∀ i x (B : FGBlock (Fin p.n)), x ∈ rho.honest →
  (∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
    HonestRowBefore p c E rho i y r a →
    namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
    FGBlock.Preceq e B ∨ FGBlock.Preceq B e) →
  (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
    FGBlock.Preceq e B ∨ FGBlock.Preceq B e) ∧
  (let st := storeAt p c E rho i x
   let R := R_at p c E rho i x
   (FGBlock.Preceq R.F B ∨ FGBlock.Preceq B R.F) ∧
   (FGBlock.Preceq R.J B ∨ FGBlock.Preceq B R.J) ∧
   (B ∈ st.fg.TF → FGBlock.Preceq R.F B →
     FGBlock.Preceq B R.Z ∨ B ∈ domainR p st st.fg.TF) ∧
   (R.contest = true → FGBlock.Preceq B R.J ∧
     ∀ W ∈ st.fg.TF, (heightView p W).h = R.H → ¬ FGBlock.Preceq R.J W →
       FGBlock.Preceq B W))) := rfl


/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
R-XING, fg.finalLock.v2 (01:209–217; 00:643–650), P3 A.4.
Consumers: 21 H.4, H.6, H.14, H.18; 22 Q0. Lead ruling 2026-09-30:
quantify every accepted carrier of the current F and use its certificate h_F.
The claim producer supplies FaultX; there is no height function on F. -/
def RXing : Prop := ∀ i i' x y K W, x ∈ rho.honest → i ≤ i' →
  K ∈ (storeAt p c E rho i x).fg.TF →
  (finalityView p K).F = (storeAt p c E rho i x).fg.F →
  HeldAt p c E rho i' y W → (finalityView p K).h_F < (heightView p W).h →
  FGBlock.Preceq (storeAt p c E rho i x).fg.F W

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
R-CAP (01:219–233), P3 A.4. Consumers: 21 H.11–H.15; 22 FF1-A.
The producer requires FaultQ. This is causal row carriage, not finality lag. -/
def RCap : Prop := ∀ y i x W, HeldAt p c E rho i x W → y + 2 ≤ (heightView p W).h →
  ∃ j z r, ∃ (a : RowWire p.n) (e : BlockId), j < i ∧
    HonestRowAt p c E rho j z r a ∧
    namedEntry a.payload.height_pair = some (y + 1, e) ∧
    a ∈ FGSA.chainWireRows (storeAt p c E rho i x) (eraseFG W)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
H1/T-HIGH (21 H.22:3059–3065), P3 A.6.
Consumers: 22 FF2, F9, HP. The claim supplies H0 and HealingSet. -/
def THigh (w : HealingWitness) : Prop := ∀ x y r r' C C',
  x ∈ rho.honest → y ∈ rho.honest →
  actionSourceFG p c E rho x r = some (some C) →
  actionSourceFG p c E rho y r' = some (some C') → high p w C → high p w C' →
  Block.Compatible (eraseFG C) (eraseFG C') ∧ Block.Compatible (eraseFG C) w.CStar ∧
    w.sStar ≤ r * p.R
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
H2/T-XFER (21 H.22:3067–3070; 01:80–91), P3 A.6.
Consumers: 22 FF1-A, F2, F5, F8, FF7. Includes faulty openings. -/
def TCarrier (w : HealingWitness) : Prop := ∀ x r K v Q,
  x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) → high p w K →
  HonestProposal E rho (fgsaInterface p c) v Q → r * p.R + 2 ≤ v →
  Block.Preceq (eraseFG K) Q.parent
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-ROWS selector (21:3072–3076; 01:83–86,95–101), P3 A.6.
Consumers: 22 F1–F5, F9, FF3–FF4, FL-W, FL-RF, FL-D. Exact signed rows.
INTENTIONAL: exact-row service. The modeled proposer carries every valid held
non-ancestor row (full inclusion, Model/Frame.lean proposalRows), so the exact-row
disjunction is the modeled policy. The blueprint also permits an optional
effect-preserving selection (22:323, 22:695; 01:83–86); that selection is not
modeled, and paper T-ROWS must not be used to inhabit this stronger exact-row contract. -/
def TRowsSelect : Prop := ∀ s Q rows j y r (a : RowWire p.n),
  HonestCarrier p c E rho s Q rows → HonestRowAt p c E rho j y r a →
  ValidForParent p c E rho s Q a → heldAtProposal p c E rho s a →
  a ∈ rows ∨ onParentChain p c E rho s Q a
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-ROWS post-GST receipt and parent-valid carriage, including sleepers.
DC: SAME strict receipt; INTENTIONAL independent row delay and R6 selection.
INTENTIONAL: exact-row service. The modeled proposer carries every valid held
non-ancestor row (full inclusion, Model/Frame.lean proposalRows), so the exact-row
disjunction is the modeled policy. The blueprint also permits an optional
effect-preserving selection (22:323, 22:695; 01:83–86); that selection is not
modeled, and paper T-ROWS must not be used to inhabit this stronger exact-row contract. -/
def TRowsSync (ΔF : Time) : Prop := ∀ j y r (a : RowWire p.n),
  HonestRowAt p c E rho j y r a → E.t_GST ≤ p.actionTime r →
  (p.actionTime r + ΔF ≤ rho.horizon →
    ∀ x ∈ rho.honest, HeldBefore p c E rho x a (p.actionTime r + ΔF)) ∧
  (∀ s Q rows, HonestCarrier p c E rho s Q rows →
    ValidForParent p c E rho s Q a →
    p.actionTime r + ΔF ≤ SA.proposalTime p.toParams s →
    a ∈ rows ∨ onParentChain p c E rho s Q a)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-ROWS all-emissions receipt, including pre-GST sends and sleepers.
DC: SAME strict max deadline and full horizon; INTENTIONAL row delay ΔF. -/
def TRowsReceipt (ΔF : Time) : Prop := ∀ j y r (a : RowWire p.n),
  HonestRowAt p c E rho j y r a →
  max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
  ∀ x ∈ rho.honest,
    HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME defining equation of strict receipt. -/
theorem TRowsReceipt_def (ΔF : Time) :
    TRowsReceipt p c E rho ΔF =
      (∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
        max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF)) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-ROWS (21 H.22:3072–3084), P3 A.6. Consumers: HealT and height coverage.
DC: SAME transport clauses; INTENTIONAL held-row/R6 interface and row delay. -/
structure TRows (ΔF : Time) : Prop where
  select : TRowsSelect p c E rho
  sync : TRowsSync p c E rho ΔF
  receipt : TRowsReceipt p c E rho ΔF

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Source of an earlier emitted height row (21 H.13:2487–2585), P3 A.3.
Consumers: RExcl, RKeep, RFProv. Only sources whose actions emitted a nonempty height pair. -/
def SourceBefore (i : Nat) (C : FGBlock (Fin p.n)) (s : Slot) : Prop :=
  ∃ j y r, ∃ (a : RowWire p.n), j < i ∧ HonestRowAt p c E rho j y r a ∧
    actionSourceFG p c E rho y r = some (some C) ∧
    s = r * p.R
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Kept path (21 H.14:2633–2641), P3 A.3. Consumers: RKeep, H.2, F1b.8.
X is the duty's own view, so a full-store witness cannot replace a HEAD witness. -/
def Kept (i : Nat) (x : V) (X : Finset (FGBlock (Fin p.n)))
    (B : FGBlock (Fin p.n)) : Prop :=
  FGBlock.Preceq B (R_at p c E rho i x).Z ∨ B ∈ D_at p c E rho i x X ∨
    FGBlock.Preceq B (storeAt p c E rho i x).fg.F
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Descent alternatives (fj.descent.v2, 00:950–960; 21:2585–2627), P3 A.3.
Consumers: RExcl and the first-failure proof H.13. -/
def KeepOrCause (i : Nat) (x : V) (X : Finset (FGBlock (Fin p.n)))
    (C : FGBlock (Fin p.n)) : Prop :=
  Kept p c E rho i x X C ∨
  (∃ C' s, SourceBefore p c E rho i C' s ∧
    ¬ Block.Compatible (eraseFG C) (eraseFG C') ∧ (heightView p C).h ≤ (heightView p C').h) ∨
  (∃ C₁ C₂ s₁ s₂, SourceBefore p c E rho i C₁ s₁ ∧ SourceBefore p c E rho i C₂ s₂ ∧
    (heightView p C₁).h = (heightView p C₂).h ∧ (heightView p C).h < (heightView p C₁).h ∧
    (heightView p C₁).T_h.root ≠ (heightView p C₂).T_h.root)
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
fj.descent.v2 (00:950–960; 21 H.13:2487,2585), P3 A.3.
Consumer: H.13. The view holds every earlier honest source unless F covers it. -/
def RExcl : Prop := ∀ i x (X : Finset (FGBlock (Fin p.n))) C,
  x ∈ rho.honest → X ⊆ (storeAt p c E rho i x).fg.TF →
  (∀ B, FGBlock.Preceq B C → B ∈ X) →
  Block.Compatible (eraseFG C) (F_at p c E rho i x) →
  (∀ C' s, SourceBefore p c E rho i C' s →
    C' ∈ X ∨ FGBlock.Preceq C' (storeAt p c E rho i x).fg.F) →
  KeepOrCause p c E rho i x X C

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.postResetKeep.v1 (00:1055–1064; 21 H.14:2633–2651), P3 A.3.
Consumers: H.12, H.14–H.17. H0 is a premise, as in TDelReset (ruling B32);
X is HEAD or full view. -/
def RKeep (w : HealingWitness) : Prop := H0 p c E rho w →
  ∀ i x (X : Finset (FGBlock (Fin p.n))) C,
  x ∈ rho.honest → X ⊆ (storeAt p c E rho i x).fg.TF →
  (∃ t, rho.events[i]? = some (.tick x t) ∧ SA.releaseTime p.toParams w.sStar ≤ t) →
  C ∈ X → eraseFG C = w.CStar →
  (∀ K s, SourceBefore p c E rho i K s → high p w K → K ∈ X) →
  (∀ K s, SourceBefore p c E rho i K s → high p w K →
    Block.Compatible (eraseFG K) w.CStar) →
  (∀ K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
    high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K')) →
  let st := storeAt p c E rho i x
  let R := R_at p c E rho i x
  w.M + 1 ≤ st.fg.h_max ∧ (R.contest = true → st.fg.h_max = w.M + 1) ∧
  R.lo ≤ max (w.M + 1) (st.fg.h_max - 1) ∧
  (∀ B ∈ [R.Z, st.fg.F], FGBlock.Preceq B C ∨
    ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧ FGBlock.Preceq B K) ∧
  (∃ B ∈ X, (heightView p B).h = max (w.M + 1) (st.fg.h_max - 1)) ∧
  (∀ B, (∀ A, FGBlock.Preceq A B → A ∈ X) → Block.Compatible (eraseFG B) w.CStar →
    (∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K)) → Kept p c E rho i x X B)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
R-FPROV (21 H.17:2764; H.18:2867), P3 A.3.
Consumers: H.15, H.17–H.19. Event order is explicit; times need not be strict.
H0 is a premise, as in TDelReset; without it w is arbitrary (ruling B31). -/
def RFProv (w : HealingWitness) : Prop := H0 p c E rho w → ∀ i x,
  x ∈ rho.honest → afterTicksIdx rho (p.actionTime w.rStar) ≤ i →
  let t := (storeAt p c E rho i x).base.now
  (Block.Preceq (F_at p c E rho i x) w.CStar ∨
    ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧
      SA.gateTime p.toParams s + P p ≤ t ∧
      Block.Preceq (F_at p c E rho i x) (eraseFG K)) ∧
  (high p w (storeAt p c E rho i x).fg.J →
    ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧
      SA.gateTime p.toParams s ≤ t ∧
      Block.Preceq (J_at p c E rho i x) (eraseFG K))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-DEL (21 H.12:2456–2463), P3 A.8. Consumers: H.12 and H.14.
Pre-reset: no witness. Strict receipt includes the path through cumulative storage.
As IF.5 (21:548; statement 21:550–557), the receipt is stated only for a prefix compatible
with the receiver's F. -/
def TDel : Prop := ∀ y r K, y ∈ rho.honest →
  actionSourceFG p c E rho y r = some (some K) →
  recoveryStart p E ≤ SA.voteTime p.toParams (r * p.R) →
  SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon →
  ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho (fun nd =>
    Block.Compatible (eraseFG K) (eraseFG nd.st.fg.F) →
      (∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF) ∨ FGBlock.Preceq K nd.st.fg.F)
      (SA.freezeTime p.toParams (r * p.R)) x

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-DEL reset (21 H.12:2456–2463; H.14), P3 A.8. Consumer: H.14.
Only this T-delivery clause takes H0. Reset-only facts suffice, but P3 retains full H0. -/
def TDelReset (w : HealingWitness) : Prop := H0 p c E rho w →
  SA.releaseTime p.toParams w.sStar ≤ rho.horizon →
  ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho (fun nd =>
    ∃ C ∈ nd.st.fg.TF, eraseFG C = w.CStar)
      (SA.releaseTime p.toParams w.sStar) x
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-GEOM (21 H.6:749–756; H.7:918–1012; H.9(b):1148–1252), P3 A.8.
Consumers: H.7, H.9(b), HG.3. No reset witness. -/
def TGeom : Prop :=
  (∀ s Q st, HonestProposal E rho (fgsaInterface p c) s Q →
    proposalStateAt p c E rho s = some st → (FGSA.fullTree p st).Nonempty →
    ∃ B ∈ FGSA.fullTree p st, eraseFG B = Q.parent ∧ (frameR p st).lo ≤ (heightView p B).h) ∧
  (∀ x r C, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some C) → C.slot ≤ r * p.R)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Exact gate service (21 H.22:3109–3114), P3 A.9.
Consumers: H3, TExact, and phase service. The gate is inside the finite horizon. -/
def ExactService (v : Slot) (Q : Block) : Prop :=
  (SA.voteTime p.toParams v ≤ rho.horizon →
    ∀ x ∈ rho.honest, joinedAt p E rho x v (SA.voteTime p.toParams v) →
      headAtLabel p c E rho x v = some Q) ∧
  (SA.gateTime p.toParams v ≤ rho.horizon → ∀ x ∈ rho.honest,
    confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams v)) (SA.gateTime p.toParams v) →
    gateResult p c E rho x v = some (some Q) ∧
    (∃ j, enabledGateAt p c E rho j x v ∧ gatePassedAt p c E rho j) ∧
    (∃ nd, postClock E rho x (SA.gateTime p.toParams v) = some nd ∧
      Q ∈ (fastWriteAt nd.st v).getD []) ∧
    (fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams v) x) = Q ∧
    (∀ r, v = r * p.R → actionSource p c E rho x r = some (some Q)))


/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A settled fixed phase on an inclusive interval (21 H.7:1003–1012;
H.8:967–975), P3 A.8. Consumers: TPerm, TRepair, TCommon, TFrontier.
The common root is J in a top-J phase. In an F-root phase each local F may move.
This read does not assert a certificate height for F. Frontier m ≥ 1 (H.10 at m = 1,
21:1467–1468, 2570–2571; ruling B21). The lower cut is idxBefore u, so the interval includes the
states read before events at u: a HEAD at v_s = u reads stateBefore its tick (bp 754–755, 824,
1151–1162; ruling B25). -/
def PhaseInterval (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n)))
    (contested : Bool) : Prop := u ≤ v ∧ v ≤ rho.horizon ∧ 1 ≤ m ∧
  ∀ i x, V2.D.Run.idxBefore rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
    let R := R_at p c E rho i x
    R.H = m ∧ R.contest = contested ∧
      (match J with | some B => R.rootIsJ = true ∧ R.J = B | none => R.rootIsJ = false)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
S1–S3 of H.2 (21:521–580), P3 A.8. Consumers: permanence and frontier service.
All HEAD, parent and output clauses stop at the interval's end. S3 applies only when its
gate cut is within the interval (ruling B31; 21:717). -/
def Transfers (s : Slot) (B : Block) (v : Time) : Prop :=
  (∀ x i H, x ∈ rho.honest → s + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
    headAtLabel p c E rho x i = some H → Block.Preceq B H) ∧
  (∀ i Q, s + 2 ≤ i → SA.proposalTime p.toParams i ≤ v →
    HonestProposal E rho (fgsaInterface p c) i Q → Block.Preceq B Q.parent) ∧
  (∀ i x, x ∈ rho.honest → SA.gateTime p.toParams s + 4 * p.Δ ≤ v →
    afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i →
    i ≤ timeIdx rho v → Block.Preceq B (S_at p c E rho i x))
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Successful fast or synchronous-window slow body (21 H.4:628–650;
H.4-S:650–680), P3 A.8. Consumer: TPerm. -/
def PhaseBody (s : Slot) (B : Block) : Prop :=
  ∃ x, x ∈ rho.honest ∧
    ((∃ nd, postClock E rho x (SA.gateTime p.toParams s) = some nd ∧
      B ∈ (fastWriteAt nd.st s).getD []) ∨
    (E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k) ∧
      ∃ st C j, gateIn p c E rho x s = some st ∧
        gateResult p c E rho x s = some (some C) ∧ B ≠ .genesis ∧ Block.Preceq B C ∧
        GridCO.slowEligible p.toParams.engine (actView st) s B = true ∧
        IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j))
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-PERM, bp.phaseSourcePermanence.v1 (00:962–966; 21 H.4/H.4-S:628–680),
P3 A.8. Consumers: H.6, H.9. H.4-S permits earlier window labels in other phases. -/
def TPerm : Prop := ∀ u v m J contested s B,
  recoveryStart p E ≤ u → PhaseInterval p c E rho u v m J contested →
  u ≤ SA.voteTime p.toParams s → SA.gateTime p.toParams s ≤ v →
  PhaseBody p c E rho s B → Transfers p c E rho s B v

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The gap predicate, not a regime (21 §2:274–282), P3 A.8.
Consumer: repair bounds. Recovery₂.gap supplies it. -/
def ProposalGap (G : Time) : Prop := ∀ t, recoveryStart p E ≤ t → t + G ≤ rho.horizon →
  ∃ s, t < V2.D.proposalTime (fgsaInterface p c) s ∧
    V2.D.proposalTime (fgsaInterface p c) s ≤ t + G ∧
    Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Later-proposal service after a repair threshold (21 H.6:749–756), P3 A.8.
Consumer: TRepair. -/
def RepairAfter (l : Slot) (v : Time) : Prop := ∀ s Q,
  SA.proposalTime p.toParams l < SA.proposalTime p.toParams s →
  SA.gateTime p.toParams s ≤ v → HonestProposal E rho (fgsaInterface p c) s Q →
  ExactService p c E rho s Q
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-REPAIR, bp.phaseRepair.v1 (00:968–978; 21 H.6:749–756;
H.6-S:821–834), P3 A.8. Consumers: H.9, H.10, HG.3.
Each budget is used only when the phase and finite horizon include it. -/
def TRepair : Prop := ∀ G u v m J contested,
  ProposalGap p c E rho G → 4 * p.Δ ≤ G → recoveryStart p E ≤ u →
  PhaseInterval p c E rho u v m J contested →
  (∀ β, u < SA.proposalTime p.toParams β →
    (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) →
    RepairAfter p c E rho (β + 2 * p.k - 1) v ∧
    (u + ρΓ p G ≤ v → ∃ s Q,
      SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s ∧
      SA.gateTime p.toParams s ≤ u + ρΓ p G ∧
      HonestProposal E rho (fgsaInterface p c) s Q ∧ ExactService p c E rho s Q)) ∧
  (∀ b, u ≤ SA.voteTime p.toParams b →
    (∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i) →
    p.k ≤ b + 1 → E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) →
    RepairAfter p c E rho (b + p.k) v ∧
    (u + ρ₁ p G ≤ v → ∃ s Q,
      SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s ∧
      SA.gateTime p.toParams s < u + ρ₁ p G ∧
      HonestProposal E rho (fgsaInterface p c) s Q ∧ ExactService p c E rho s Q))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Nonempty sources and signed rows at an opening (21 H.9:1131–1144), P3 A.8.
Consumer: common-entry and frontier service.
SO-COV earlier-or-current coverage. DC: INTENTIONAL send-once source coverage. -/
def OpeningCovered (r : Nat) (Q : Block) : Prop := ∀ x ∈ rho.honest,
  ∃ K nd j rSent a, postClock E rho x (p.actionTime r) = some nd ∧
    actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
    Block.Preceq Q (eraseFG K) ∧ rSent ≤ r ∧
    HonestRowAt p c E rho j x rSent a ∧
    namedEntry a.payload.height_pair =
      some ((heightView p K).h, (heightView p K).T_h.root)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
One state-height entry at an opening (21 H.9:1140–1144), P3 A.8.
Consumer: TCommon. Bodies at one state height can differ. -/
def OpeningEntry (r m : Nat) : Prop := ∃ e, ∀ x K, x ∈ rho.honest →
  actionSourceFG p c E rho x r = some (some K) →
  (heightView p K).h = m ∧ (heightView p K).T_h.root = e
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-COMMON, bp.commonEntry.v1 (00:1001–1010; 21 H.9:1100–1144),
P3 A.8. Consumers: H.9 and HG.2. The second opening has its own phase premise.
SO-COV. DC: INTENTIONAL earlier-or-current source coverage. -/
def TCommon : Prop := ∀ u m J contested q Q Qfg r,
  recoveryStart p E ≤ u → HonestProposal E rho (fgsaInterface p c) q Q → eraseFG Qfg = Q →
  ExactService p c E rho q Q → u ≤ SA.proposalTime p.toParams q → q ≤ r * p.R →
  (∀ r', q ≤ r' * p.R → r ≤ r') →
  PhaseInterval p c E rho u (p.actionTime r) m J contested →
  0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
  p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ ∧
  OpeningCovered p c E rho r Q ∧
  (∀ x y K K', x ∈ rho.honest → y ∈ rho.honest →
    actionSourceFG p c E rho x r = some (some K) →
    actionSourceFG p c E rho y r = some (some K') → Block.Compatible (eraseFG K) (eraseFG K')) ∧
  ((heightView p Qfg).h = m → OpeningEntry p c E rho r m) ∧
  ((heightView p Qfg).h = m - 1 → OpeningEntry p c E rho r (m - 1) ∨
    ((∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
        (heightView p K).h = m) ∧
      (PhaseInterval p c E rho u (p.actionTime (r + 1)) m J contested →
        OpeningEntry p c E rho (r + 1) m)))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-FRONTIER (21 HG.1:1333–1350), P3 A.8. Consumers: HG.1–HG.5.
The initial proposal is served in its phase. Subsequent service stops at frontier rise.
SO-COV. DC: INTENTIONAL earlier-or-current source coverage.
Re-freeze 2026-10-03 (user decision): the seed q carries DC's HG.1 qualification, "H.6 or
H.6-S service through its gate" (21 H.6 statement, 21 H.6-S statement).
q follows the H.6 threshold β + 2k − 1
of the first label β after u, or the H.6-S threshold b + k of the first HEAD label b after u,
with the synchronous window. These are TRepair's branch conditions. -/
def TFrontier : Prop := ∀ u v m J contested q Q Qfg,
  recoveryStart p E ≤ u → HonestProposal E rho (fgsaInterface p c) q Q → eraseFG Qfg = Q →
  (heightView p Qfg).h = m → ExactService p c E rho q Q →
  ((∃ β : Slot,
    u < SA.proposalTime p.toParams β ∧
    (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
    SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q) ∨
  (∃ b : Slot,
    u ≤ SA.voteTime p.toParams b ∧
    (∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i) ∧
    p.k ≤ b + 1 ∧
    E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) ∧
    SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q)) →
  u ≤ SA.proposalTime p.toParams q →
  PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested →
  SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon →
  (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
    (storeAt p c E rho i x).fg.h_max ≤ m) →
  Transfers p c E rho q Q v ∧ RepairAfter p c E rho q v ∧
  (∀ r, q ≤ r * p.R → p.actionTime r ≤ v →
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
    (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
      (heightView p K).T_h = (heightView p Qfg).T_h) ∧
    ((∀ r', q ≤ r' * p.R → r ≤ r') →
      p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Raw wire origin under the honest-holder implication.
DC: SAME honest origin; INTENTIONAL fixed FG seat and emission action. -/
def FinalityRowCarriage (A : Finset (Row (Fin p.n))) : Prop :=
  ∀ u ∈ A, ∃ a : RowWire p.n,
    a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
    ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
      ∃ j r, HonestRowAt p c E rho j z r a

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME equation for raw wire origin. -/
theorem FinalityRowCarriage_def (A : Finset (Row (Fin p.n))) :
    FinalityRowCarriage p c E rho A =
      (∀ u ∈ A, ∃ a : RowWire p.n,
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
          ∃ j r, HonestRowAt p c E rho j z r a) := by rfl

def RMonoAll : Prop := ∀ i j x, x ∈ rho.honest → i ≤ j →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  FGBlock.Preceq st.fg.F st'.fg.F ∧
  lexKey (st.fg.h_j, st.fg.J) ≤ lexKey (st'.fg.h_j, st'.fg.J) ∧
  st.fg.h_max ≤ st'.fg.h_max


theorem RMonoAll_def : RMonoAll p c E rho =
  (∀ i j x, x ∈ rho.honest → i ≤ j →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  FGBlock.Preceq st.fg.F st'.fg.F ∧
  lexKey (st.fg.h_j, st.fg.J) ≤ lexKey (st'.fg.h_j, st'.fg.J) ∧
  st.fg.h_max ≤ st'.fg.h_max) := rfl


def RStoreDurable : Prop := ∀ i j x, x ∈ rho.honest →
  i ≤ j → j ≤ rho.events.length →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  st.fg.TF ⊆ st'.fg.TF ∧ st.base.blocks <+: st'.base.blocks ∧
  st.proposals <+: st'.proposals ∧ st.rowPool <+: st'.rowPool


theorem RStoreDurable_def : RStoreDurable p c E rho =
  (∀ i j x, x ∈ rho.honest →
  i ≤ j → j ≤ rho.events.length →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  st.fg.TF ⊆ st'.fg.TF ∧ st.base.blocks <+: st'.base.blocks ∧
  st.proposals <+: st'.proposals ∧ st.rowPool <+: st'.rowPool) := rfl


def RStoreEpoch : Prop := ∀ i j x, x ∈ rho.honest →
  i ≤ j → j ≤ rho.events.length → V2.D.restartFree rho x i j →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  st.base.blockStamp <+: st'.base.blockStamp ∧
  st.base.voteStamp <+: st'.base.voteStamp


theorem RStoreEpoch_def : RStoreEpoch p c E rho =
  (∀ i j x, x ∈ rho.honest →
  i ≤ j → j ≤ rho.events.length → V2.D.restartFree rho x i j →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  st.base.blockStamp <+: st'.base.blockStamp ∧
  st.base.voteStamp <+: st'.base.voteStamp) := rfl

end AvailableChain.FGSA.Run
end
