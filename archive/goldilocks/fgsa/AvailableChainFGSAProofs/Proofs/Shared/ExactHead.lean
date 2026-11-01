module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAProofs.Proofs.Shared.ScoreRun
public import AvailableChainFGSAProofs.Proofs.Shared.KeepExact

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
G11 store bridge; S1b E3–E5:126–132 and 21 H.17:2820–2824.
DC: Goldfish/ProposalWalkTransportCore.lean:189–198, source-step extraction.
SAME extraction ingredient at the actual HEAD anchor. The domain is exactly
G11's voter storeFrame. An emitted proposal supplies the nonzero slot.
The target-start guard is required even when the pivot is below the start. -/
theorem fgsa_headVote_best_ancestry_of_cover (p : Params) (st : State p.n)
    (s : Slot) (hs : s ≠ 0) (T P : Block)
    (hcover : Block.Preceq P (headVote p st s)) :
    ∀ X, Block.Preceq T X → Block.Preceq (liveRoot p st) X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧
        C ∈ erasedList st (domainR p st (voterBlocks p st s)) ∧
        eligible p st (headVotes p st s) (headSupport p st s) C = true ∧
        ∀ D ∈ erasedList st (domainR p st (voterBlocks p st s)),
          D.parent? = some X →
          eligible p st (headVotes p st s) (headSupport p st s) D = true →
          GridCO.goldfishScore st.base.blocks (headVotes p st s) (headSupport p st s) D ≤
            GridCO.goldfishScore st.base.blocks (headVotes p st s) (headSupport p st s) C ∧
          (GridCO.goldfishScore st.base.blocks (headVotes p st s) (headSupport p st s) D =
            GridCO.goldfishScore st.base.blocks (headVotes p st s) (headSupport p st s) C →
              D.root ≤ C.root) := by
  rw [fgsa_headVote_eq_filtered] at hcover
  rw [ite_eq_right hs] at hcover
  intro X _ hAX hXP
  simpa only [fgsa_domainR_eq_filtered] using
    walk_best_ancestry_of_cover _ _ _ _ _ hcover X hAX hXP

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Terminal consumer obligations; S1b E6:133–134, 21 H.17:2824–2825.
DC: Goldfish/Walk.lean:433, final step and stop in `ghost_reaches`.
INTENTIONAL: FG-SA's live voter domain can change after the proposal read.
The consumer supplies the unique eligible proposal child and its leaf condition.
G11 covers the strict parent suffix; it does not assert this terminal uniqueness. -/
structure ExactHeadGeometry (p : Params) (st : State p.n) (s : Slot) (b : Block) : Prop where
  last : b ∈ erasedList st (domainR p st (voterBlocks p st s)) ∧
    b.parent? = some b.parent ∧
    eligible p st (headVotes p st s) (headSupport p st s) b = true ∧
    ∀ C ∈ erasedList st (domainR p st (voterBlocks p st s)),
      C.parent? = some b.parent →
      eligible p st (headVotes p st s) (headSupport p st s) C = true → C = b
  stop : NoEligibleChild (erasedList st (domainR p st (voterBlocks p st s)))
    (eligible p st (headVotes p st s) (headSupport p st s)) b

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. G33 at the HEAD read; S1b E1–E6:118–134, 21 H.17:2798–2825.
DC: Goldfish/Walk.lean:433 and ProposalWalkTransportCore.lean:162–198.
INTENTIONAL: compose actual HEAD coverage with the FJ pivot start disjunction
and the explicit terminal obligations. Both start orders are permitted.
The covered walk itself supplies the guarded ancestry; no source-store bridge
or extra score premise is required. -/
theorem fgsa_headVote_exact_of_covered_parent (p : Params) (st : State p.n)
    (s : Slot) (hs : s ≠ 0) (T b : Block)
    (hroot : ∀ A ∈ erasedList st (domainR p st (voterBlocks p st s)),
      ∀ B ∈ erasedList st (domainR p st (voterBlocks p st s)), A.root = B.root → A = B)
    (hstart : (Block.Preceq (liveRoot p st) T ∧
      DominatedSuffix (liveRoot p st) T
        (erasedList st (domainR p st (voterBlocks p st s)))
        (GridCO.goldfishScore st.base.blocks (headVotes p st s) (headSupport p st s))
        (eligible p st (headVotes p st s) (headSupport p st s))) ∨
      (Block.Preceq T (liveRoot p st) ∧ Block.Preceq (liveRoot p st) b.parent))
    (hTP : Block.Preceq T b.parent)
    (hcover : Block.Preceq b.parent (headVote p st s))
    (hgeom : ExactHeadGeometry p st s b) : headVote p st s = b := by
  have hancestry := fgsa_headVote_best_ancestry_of_cover p st s hs T b.parent hcover
  rw [fgsa_headVote_eq_filtered]
  rw [ite_eq_right hs]
  simpa only [fgsa_domainR_eq_filtered] using
    exactHead_of_pivot_ancestry p st (voterBlocks p st s)
    (headVotes p st s) (headSupport p st s) T b.parent b hroot hstart hTP
    hancestry (Or.inr hgeom.last) hgeom.stop

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. G25/G11 followed by G33; 21 H.17:2794–2830, S1b E1–E6:118–134.
DC: Goldfish/ProposalWalkTransportCore.lean:162 and Walk.lean:433.
INTENTIONAL: FG-SA supplies actual tick reads, two LabelSync intervals and
live-frame geometry. Admission and terminal geometry are consumer premises.
The landed G11 geometry supplies the lower E1 branch and the pivot-parent path.
No lane theorem supplies geometry here; the proposal rows remain opaque.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactHead_of_proposal_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hScoreSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.proposalTime p.toParams s))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D)
    (hterminal : ExactHeadGeometry p
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s N.erase)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    headVote p dst s = N.erase := by
  intro dst
  let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hmem
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hDP : Block.Preceq (eraseFG D) N.erase.parent := by
    rw [hparent.2.2]
    exact walk_covers_of_dominated_suffix _ _ _ _ _
      (block_compatible_of_common hgeom.source_anchor (block_preceq_refl _))
      hgeom.source_prefix
  have hcover := fgsa_ghost_transfer_sfx_on_run (hroots := hroots)
    E rho hE hN hDelta s hScoreSync hSync
    hx hy hip hih hseat N hem hadm D hgeom
  exact fgsa_headVote_exact_of_covered_parent p dst s (Nat.ne_of_gt hparent.1)
    (eraseFG D) N.erase
    (erasedList_rootInj p dst (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _) _)
    (Or.inl ⟨hgeom.target_anchor, by
      simpa only [fgsa_domainR_eq_filtered] using hgeom.target_prefix⟩)
    hDP hcover hterminal

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Per-reader obligations for the HEAD clause of J2; 21 H.22:3100–3120.
DC: Goldfish/PreparedV4CanonicalProposalDuty.lean:867–887, honest voter heads.
INTENTIONAL: Shared names the FG-SA admission, E1–E5 walk geometry and E6
terminal obligations. A consumer supplies them at each actual HEAD tick
(21 H.17:2794–2830; S1b E1–E6:118–134). No exact HEAD is a bundle field. -/
structure ExactHeadRunGeometry
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ip : Nat) (x : V) (s : Slot) (D : FGBlock (Fin p.n)) (b : Block) : Prop where
  admitted : ∀ y ∈ rho.honest, ∀ ih,
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      b ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks
  walk : ∀ y ∈ rho.honest, ∀ ih,
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      WalkRunGeometry p
        (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D
  terminal : ∀ y ∈ rho.honest, ∀ ih,
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ExactHeadGeometry p
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s b

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. The HEAD clause of J2 ExactService, before freeze; 21 H.22:3109–3114.
DC: Goldfish/PreparedV4CanonicalProposalDuty.lean:867–887.
INTENTIONAL: FG-SA uses the option-valued post-clock reader and the finite
HEAD horizon. The schedule supplies every honest reader, including a reader
that emits no HEAD vote. H3 and TExact must supply `ExactHeadRunGeometry`
from 21 H.17:2794–2830 and S1b E1–E6:118–154. Gate clauses are separate.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_head_of_proposal
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hScoreSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.proposalTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : ExactHeadRunGeometry E rho ip x s D N.erase)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  intro hhorizon y hy hjoined
  have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
    push_cast
    ring
  obtain ⟨ih, hih, _⟩ := fgsa_tick_total E rho hE.toScheduleWellFormed hDelta y hy
    (4 * s + 1) (hvt ▸ hhorizon)
    (by simpa only [hvt] using hjoined.1)
  rw [hvt] at hih
  have he := exactHead_of_proposal_on_run (hroots := hroots) E rho hE hN hDelta s hScoreSync hSync
    hx hy hip hih hseat N hem (hgeom.admitted y hy ih hih) D
    (hgeom.walk y hy ih hih) (hgeom.terminal y hy ih hih)
  have ht := fgsa_tickIdx_of_event p c E rho hE.toScheduleWellFormed hih
  change (postClock E rho y (SA.voteTime p.toParams s)).map _ = some N.erase
  rw [postClock_def, preTick_def, ht]
  change some (headVote p (clock p (V2.D.Run.stateBefore E rho ih y).st
    (SA.voteTime p.toParams s)) s) = some N.erase
  exact congrArg some he

theorem exactHead_of_proposal_on_run_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D)
    (hterminal : ExactHeadGeometry p
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s N.erase)
    (hScope : ScoreServiceScope E rho ip ih x y s (eraseFG D))
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    headVote p dst s = N.erase := by
  intro dst
  let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hmem
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hDP : Block.Preceq (eraseFG D) N.erase.parent := by
    rw [hparent.2.2]
    exact walk_covers_of_dominated_suffix _ _ _ _ _
      (block_compatible_of_common hgeom.source_anchor (block_preceq_refl _))
      hgeom.source_prefix
  have hcover := fgsa_ghost_transfer_sfx_on_run_on (hroots := hroots)
    E rho hE s hx hy hip hih hseat N hem hadm D hgeom hScope
  exact fgsa_headVote_exact_of_covered_parent p dst s (Nat.ne_of_gt hparent.1)
    (eraseFG D) N.erase
    (erasedList_rootInj p dst (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _) _)
    (Or.inl ⟨hgeom.target_anchor, by
      simpa only [fgsa_domainR_eq_filtered] using hgeom.target_prefix⟩)
    hDP hcover hterminal

theorem exactService_head_of_proposal_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : ExactHeadRunGeometry E rho ip x s D N.erase)
    (hScopes : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ScoreServiceScope E rho ip ih x y s (eraseFG D))
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  intro hhorizon y hy hjoined
  have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
    push_cast
    ring
  obtain ⟨ih, hih, _⟩ := fgsa_tick_total E rho hE.toScheduleWellFormed hDelta y hy
    (4 * s + 1) (hvt ▸ hhorizon)
    (by simpa only [hvt] using hjoined.1)
  rw [hvt] at hih
  have he := exactHead_of_proposal_on_run_on (hroots := hroots) E rho hE s
    hx hy hip hih hseat N hem (hgeom.admitted y hy ih hih) D
    (hgeom.walk y hy ih hih) (hgeom.terminal y hy ih hih) (hScopes y hy ih hih hjoined)
  have ht := fgsa_tickIdx_of_event p c E rho hE.toScheduleWellFormed hih
  change (postClock E rho y (SA.voteTime p.toParams s)).map _ = some N.erase
  rw [postClock_def, preTick_def, ht]
  change some (headVote p (clock p (V2.D.Run.stateBefore E rho ih y).st
    (SA.voteTime p.toParams s)) s) = some N.erase
  exact congrArg some he

end AvailableChain.FGSA.Run
end
