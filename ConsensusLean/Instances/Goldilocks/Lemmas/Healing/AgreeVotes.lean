module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSuffix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeLater
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin

public section

/-! # Goldilocks Healing, HS.3: frozen-tree agreement

`hs234-exact-interface.md` §4 (HS.3 (a) with the restored settled premise of #95, and (b)), by
the walk comparison of `Compose/Service/Agree` (workbench#12): the proposal walk (the full viable
tree, the slot-`(s−1)` pool view `pay`, from its unlocked anchor `d.start`) ends at `Q = d.head =
parent(P)`, and each honest slot-`s` voter's walk (the viable voter block tree, the merged view,
from its unlocked anchor) is compared with it, by induction on the cut of the first honest
slot-`s` vote that is not `P` (`votes_eq_of_pass`):

* the voter passes a block of the path from `d.start` through `Q` to `P` (`voters_pass`): its
  anchor is below `P` (`voter_anchor_below`: the lock premise for the earlier labels, an honest
  earlier slot-`s` supporter of a slot-`s` optimistic lock, `fc_root ⪯ P`), and a voter whose
  anchor is below `d.start` passes `d.start` (`voter_reaches_start_unlocked` under (a)'s premises
  with #101's start premise, modulo `voter_unlock_keeps_lock`; `voter_reaches_start_clean` under
  (b)'s);
* at every block of that path at or above the voter's anchor, the proposer's best child is the
  voter's best child (`proposal_suffix`, `AgreeSuffix`); at `Q` the voter's only eligible child
  is `P` (`proposal_frozen_viable`, `AgreeFrozen`; `proposal_only_child`, `AgreeSuffix`), and
  the walk stops at `P` (`proposal_stop`).

The frozen conjuncts of (a) follow from `P` being in the viable voter block tree
(`frozen_of_viableTree`, `proposal_frozen_viable`). (b) takes HS.2 (`CleanLockDrain`) as a
hypothesis: its fourth clause is (a)'s lock premise; the later votes and proposal parents are
`later_extend` (open, the common-batch transfer of §2). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF w : Time} {i₀ i m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} {p : Fin sp.n} {kP s : Nat}
  {P : SA.Blk sp.n (List (FG.Att sp.n))} {iP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}

/-! ### Frame facts -/

/-- The anchor of a walk is a block of the frame tree. -/
private theorem getAnchor_mem {FGP : Type} {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ)
    (A : SA.SAState sp.n) (t : Time) : SA.getAnchor sp A Φ t ∈ Φ.tree := by
  unfold SA.getAnchor
  rcases hD : SA.deepest Φ (SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with _ | D
  · exact hΦ.fcRoot_mem
  · rcases (SA.deepest_mem hD).1 with h | h
    · exact h.1
    · exact (Set.mem_singleton_iff.1 h) ▸ hΦ.fcRoot_mem

/-- A block between the root `Φ.F` and a block of the tree (in `U`) is in the tree, below it. -/
private theorem mem_of_between {FGP : Type} {U : Set (SA.Blk sp.n FGP)} (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {X B : SA.Blk sp.n FGP}
    (hFX : Anc U Φ.F X) (hXB : Anc U X B) (hB : B ∈ Φ.tree) : X ∈ Φ.tree ∧ Φ.Anc X B := by
  induction hXB with
  | refl => exact ⟨hB, .refl⟩
  | @tail b b' hXb e ih =>
    by_cases hbF : b' = Φ.F
    · subst hbF
      have h1 : Anc U b Φ.F := Relation.ReflTransGen.single e
      obtain rfl := Anc.antisymm hU (hFX.trans hXb) h1
      exact absurd (hU.2 _ e.1 _ e.2.1 e.2.2) (lt_irrefl _)
    obtain rfl | ⟨q, -, hq⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 b' hB)
    · exact absurd rfl hbF
    obtain rfl : q = b := hU.1 (hΦU hq.1) e.1 (Option.some_injective _ (hq.2.2.symm.trans e.2.2))
    obtain ⟨hXt, hXq⟩ := ih hq.1
    exact ⟨hXt, hXq.tail hq⟩

/-- The duty head of a proposal is the walk of the full viable tree from its start, with the
payload's view; the start is the anchor of the unlocked state. -/
private theorem acProposal_spec {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {t : Time} {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) :
    (∃ A₁ : SA.SAState sp.n, d.start = SA.getAnchor sp A₁ Φ t) ∧
      d.head = SA.ghost sp (Φ.viableTree Φ.tree)
        (SA.goldfishScore sp Φ (SA.View.ofLists pay) ((sp.slot t : Int) - 1))
        (SA.goldfishEligible sp Φ t (SA.View.ofLists pay) ((sp.slot t : Int) - 1))
        Φ.tree.ncard d.start := by
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨⟨_, rfl⟩, rfl⟩

/-- The proposal walk: `d.start` and `d.head` are in the proposer's frame tree, `d.start ⪯
d.head` there, and `d.head` is in `U`. -/
private theorem proposal_walk
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay) :
    d.start ∈ ℓp.frame.tree ∧ d.head ∈ ℓp.frame.tree ∧ ℓp.frame.Anc d.start d.head := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr
    proposer hS.run hS.shared.noColl).localRun
  have hΦ := (SA.frameIn_of_callAt hr hS.ready.1 hS.call).1
  obtain ⟨⟨A₁, hst⟩, hhd⟩ := acProposal_spec hS.payload
  have hst' : d.start ∈ ℓp.frame.tree := hst ▸ getAnchor_mem hΦ A₁ _
  have hT : ℓp.frame.viableTree ℓp.frame.tree ⊆ ℓp.frame.tree := fun _ h => h.1
  have ha : ℓp.frame.Anc d.start d.head := hhd ▸ SA.anc_ghost hT _ hst'
  refine ⟨hst', ?_, ha⟩
  rcases eq_or_ne d.start d.head with h | h
  exacts [h ▸ hst', (Anc.mem ha h).2]

/-! ### The walk contracts (`hs234-exact-interface.md` §4) -/

/-- **The voter's anchor is below `P`** (`hs234-exact-interface.md` §4, "with anchors on the
parent path"; "a first-violating slot-`s` vote excludes a new exempt optimistic anchor"): at an
honest slot-`s` vote, before which every honest slot-`s` vote is `P`, the anchor of the voter's
walk is an ancestor of `P`: a read-point lock of a label `< s` sits below a stored live lock of
that label (`readPoint_locks_below_stored`), below `P` or at or below `fc_root` (the lock
premise); a lock of a label `≥ s` sits below a block of three quarters of the committee in a
pool of earlier votes (`lock_origin_readPoint`), which has an honest supporter (`3f < n`), of
slot `s` (no earlier vote is of a later slot), so `P`; and `fc_root ⪯ P`
(`proposal_frozen_viable`). -/
theorem voter_anchor_below
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hlock : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
        ∀ L ∈ ℓ.frame.tree, L.root = l.block →
          Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s)
    (hIH : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
      e'.msg.head = P.root) :
    Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr
    proposer hS.run hS.shared.noColl).localRun
  obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hfP : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot P :=
    (proposal_frozen_viable hS hy hcy hes).2.1.mono hΦU
  have hlk := readPoint_lockBlocks_below hS hlock hy hcy hes hIH
  -- the anchor is a live lock block or `fc_root`
  unfold SA.getAnchor
  rcases hD : SA.deepest ℓy.frame
      (SA.liveLockBlocks sp e.readPoint.locks ℓy.frame (tr.time j) ∪ {ℓy.frame.fcRoot}) with
    _ | D
  · exact hfP
  · rcases (SA.deepest_mem hD).1 with h | h
    · exact hlk D h
    · exact (Set.mem_singleton_iff.1 h) ▸ hfP

/-- The proposal walk's start is below `P` (`d.start ⪯ d.head`, the parent of `P`). -/
private theorem start_anc_proposal
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) : Anc (tr.HonestBlocks H) d.start P := by
  have hr' := (Compose.goldilocks_ac_projection sp ro dg H tr
    proposer hS.run hS.shared.noColl).localRun
  obtain ⟨-, hdt, hsd⟩ := proposal_walk hS
  obtain ⟨-, hΦpU⟩ := SA.frameIn_of_callAt hr' hS.ready.1 hS.call
  obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr' hy hcy.1
  have hPU : P ∈ tr.HonestBlocks H := hΦU (proposal_frozen_viable hS hy hcy hes).1.1
  exact (Anc.mono hΦpU hsd).tail ⟨hΦpU hdt, hPU, hS.parent⟩

/-- A vote extending the proposal walk's start, whose anchor is below `P` and not above the
start, passes the start: the anchor is strictly below it (both are below `P`), and the start is
between the frame's `Σ.F` and the head. -/
private theorem walk_passes_start
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) (hext : SA.VoteExtends (tr.HonestBlocks H) e.msg d.start)
    (hbelow : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P)
    (hlow : ¬ Anc (tr.HonestBlocks H) d.start (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))) :
    ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) d.start ∧
      ℓy.frame.Anc d.start (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  have hrun := hS.run
  have hnc := hS.shared.noColl
  have hr' := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr' hy hcy.1
  have hsP := start_anc_proposal hS hy hcy hes
  obtain ⟨Hd, hHd, hHdr, hsH⟩ := hext
  have hGt : SA.getHead sp e.readPoint ℓy.frame (tr.time j)
      (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) ∈ ℓy.frame.tree :=
    SA.getHead_mem hΦ (fun _ hB => hB.1.1) _ _ _ _
  have hhead := SA.castAt_head_of_viable hr' hy hcy
    (hes ▸ ⟨P, proposal_frozen_viable hS hy hcy hes⟩)
  rw [hes] at hhead
  obtain rfl := hU.1 hHd (hΦU hGt) (hHdr.trans hhead)
  -- `d.start ⪯ P`, so the anchor is below `d.start`
  have hat := getAnchor_mem hΦ e.readPoint (tr.time j)
  have haS := (SA.anc_total hU hbelow hsP).resolve_right hlow
  obtain ⟨hst, hsG⟩ :=
    mem_of_between hU hΦ hΦU (((hΦ.rooted.2 _ hat).mono hΦU).trans haS) hsH hGt
  exact ⟨SA.anc_tree_of_anc_U hU hΦ hΦU hat haS hst, hsG⟩

/-- **A voter below the proposal walk's start reaches it, under HS.3 (a)'s premises**
(`hs234-exact-interface.md` §4, "the unequal-root prefix", "induction on child comparisons reaches
`P`"; #100/#101). At an honest slot-`s` vote whose anchor is below `P` and not above the proposal
walk's start `d.start`, the voter's walk passes `d.start`. `d.start` is the deepest of the
proposer's `fc_root` `R` and its live lock blocks after `unlock` (`proposal_start_cases`):

* `d.start = R`: the vote extends `R` (`voter_passes_proposer_root`: every viable head of the
  voter block tree extends `R`, so below `R` the child towards `R` is the only eligible viable
  child);
* a lock block: it is at or below the voter's anchor (`lock_start_below_anchor`, through the
  start premise and `voter_unlock_keeps_lock`, open), against the premise. -/
theorem voter_reaches_start_unlocked
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hlock : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
        ∀ L ∈ ℓ.frame.tree, L.root = l.block →
          Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot)
    (hstart : ∀ kq ℓP, tr.projAC.CallAt p kq ℓP → ℓP.call = .proposal → tr.time kq = sp.ts s →
      ∀ l ∈ SA.liveLocks sp (tr.post kq).ac.locks ℓP.frame (tr.time kq), l.slot < s →
        ∀ L ∈ ℓP.frame.tree, L.root = l.block →
          ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
            (∃ l' ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k),
              ∃ L' ∈ ℓ.frame.tree, L'.root = l'.block ∧ Anc (tr.HonestBlocks H) L L') ∨
            Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s)
    (hIH : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
      e'.msg.head = P.root)
    (hbelow : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P)
    (hlow : ¬ Anc (tr.HonestBlocks H) d.start (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))) :
    ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) d.start ∧
      ℓy.frame.Anc d.start (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  have hsP := start_anc_proposal hS hy hcy hes
  refine walk_passes_start hS hy hcy hes ?_ hbelow hlow
  rcases proposal_start_cases hS with h | h
  · rw [h] at hlow hsP ⊢
    exact voter_passes_proposer_root hS hlock hy hcy hes hIH hsP hbelow hlow
  · exact absurd (lock_start_below_anchor hS hlock hstart hy hcy hes hIH hbelow h) hlow

/-- **A voter below the proposal walk's start reaches it, under HS.3 (b)'s premises**
(`hs234-exact-interface.md` §3 "the proposal-boundary helper", §4 (b)): as
`voter_reaches_start_unlocked`, with `t_s ≥ r` in place of the start premise. `d.start` is the
proposer's `fc_root` `R` (`voter_passes_proposer_root`) or a live lock block of the proposer,
clean (HS.2 (3)), whose origin every later in-phase honest vote extends
(`proposer_lock_extends`). -/
theorem voter_reaches_start_clean {Gp : Time}
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (_hp : PropPlus tr H proposer g Gp) (hr : rTime sp w ≤ sp.ts s) (_hdrain : CleanLockDrain)
    (hlock : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
        ∀ L ∈ ℓ.frame.tree, L.root = l.block →
          Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s)
    (hIH : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
      e'.msg.head = P.root)
    (hbelow : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P)
    (hlow : ¬ Anc (tr.HonestBlocks H) d.start (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))) :
    ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) d.start ∧
      ℓy.frame.Anc d.start (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  have hsP := start_anc_proposal hS hy hcy hes
  refine walk_passes_start hS hy hcy hes ?_ hbelow hlow
  rcases proposal_start_cases hS with h | h
  · rw [h] at hlow hsP ⊢
    exact voter_passes_proposer_root hS hlock hy hcy hes hIH hsP hbelow hlow
  · exact proposer_lock_extends hS hr h hy hcy hes

/-- **The stop at `P`** (`hs234-exact-interface.md` §4; workbench#12 §3): at `Q` the voter's only
eligible child is `P` (`proposal_frozen_viable`, eligible as of the current slot;
`proposal_only_child`), and its walk has no best child at `P`: a child of `P` would be of a slot
above `s`, and the voter block tree of slot `s` has none (`voterBlockTree_slot_le`). -/
theorem proposal_stop
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) :
    (P ∈ {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} ∧
      ∀ B ∈ {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
          B.parent = some d.head.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
            (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B}, B = P) ∧
    ¬ ∃ C, SA.IsBest sp
      (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
        ((s : Int) - 1))
      {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
        B.parent = some P.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} C := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr
    proposer hS.run hS.shared.noColl).localRun
  have hU := Compose.honest_blocks_coherent hS.run.toLocalRun hS.shared.noColl
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hPs : P.slot = s := hS.ready.2.2.2.2.1
  have hPv := proposal_frozen_viable hS hy hcy hes
  obtain ⟨-, hys, -, -⟩ := SA.castAt_spec hr hy hcy
  refine ⟨⟨⟨hPv, hS.parent, Or.inr (Or.inl (by rw [hPs, ← hes, hys]; rfl))⟩,
    proposal_only_child hS hy hcy hes⟩, fun ⟨C, hC⟩ => ?_⟩
  have hgen : ∀ X ∈ ℓy.frame.tree, X.root = sp.genesisRoot → X.slot = 0 := by
    intro X hX hXg
    have hG := Store.genesis_mem (Compose.fg_reachable hS.run.toLocalRun hy j)
    obtain rfl := hU.1 (hΦU hX) ⟨y, hy, j, hG⟩ hXg
    simp [Params.genesisBlock]
  have hCs := voterBlockTree_slot_le hr hy hcy hgen hC.1.1.1
  have hlt := hΦ.coherent.2 P hPv.1.1 C hC.1.1.1.1 hC.1.2.1
  omega

/-- **The later votes and proposal parents** (`hs234-exact-interface.md` §2.2 "for subsequent
slots use the unanimous honest batch", §4 (b); open): under (b)'s premises, with every honest
slot-`s` vote exactly `P`, every honest in-phase vote of a later slot extends `P`, and every
honest in-phase proposal of a later slot has a parent extending `P` (the honest batch, `n − f >
2f`, beats every conflicting child and releases every older conflicting lock, by induction on the
slot and the cut; each later event bounded by its own `PhaseOn i₀`). -/
theorem later_extend {Gp : Time}
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (_hp : PropPlus tr H proposer g Gp) (hr : rTime sp w ≤ sp.ts s) (_hdrain : CleanLockDrain)
    (hvotes : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = P.root ∧
      ((P ∈ ℓ.frame.viableHeads ∧
          P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) ∨
        Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot) ∧
      ∀ X, Anc (tr.HonestBlocks H) X P →
        X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) X ℓ.frame.fcRoot) :
    (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P) ∧
    ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
      tr.ProposesAt (proposer s') k' P' → proposer s' ∈ H →
      PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) P Pr :=
  later_extend_of_setting hS hr fun y hy k ℓ e hv hs => (hvotes y hy k ℓ e hv hs).1

/-- A slot-`s` block in the viable voter tree of slot `s` is a viable head
(`hs234-exact-interface.md` §4, "cannot have an earlier-slot descendant"): its viable head
witness `W ⪰ P` in the voter block tree has no slot above `s` (`voterBlockTree_slot_le`), so it
is `P`. -/
theorem viableHead_of_viableTree {y : Fin sp.n} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓ e)
    (hPs : P.slot = s) (hP : P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) :
    P ∈ ℓ.frame.viableHeads := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  obtain ⟨-, -, W, hW, hWv, hPW⟩ := hP
  have hgen : ∀ X ∈ ℓ.frame.tree, X.root = sp.genesisRoot → X.slot = 0 := by
    intro X hX hXg
    have hG := Store.genesis_mem (Compose.fg_reachable hrun.toLocalRun hy j)
    obtain rfl := hU.1 (hΦU hX) ⟨y, hy, j, hG⟩ hXg
    simp [Params.genesisBlock]
  have hWs := voterBlockTree_slot_le hr hy hcy hgen hW
  by_contra hne
  have hlt := (Anc.slot_le hΦ.coherent hPW).2 fun h => hne (h ▸ hWv)
  omega

/-! ### Assembly -/

/-- **The frozen conjuncts** of HS.3 (a) from `P` in the viable voter block tree: `P` is a viable
head there (`viableHead_of_viableTree`), and every ancestor of `P` is in the viable voter block
tree (the same viable head witnesses it; the voter block tree is closed under ancestors) or at or
below `fc_root`. -/
theorem frozen_of_viableTree {y : Fin sp.n} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓ e) (hes : e.msg.slot = s)
    (hPs : P.slot = s) (hP : P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) :
    ((P ∈ ℓ.frame.viableHeads ∧
        P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) ∨
      Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot) ∧
    ∀ X, Anc (tr.HonestBlocks H) X P →
      X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
      Anc (tr.HonestBlocks H) X ℓ.frame.fcRoot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  refine ⟨Or.inl ⟨viableHead_of_viableTree hrun hnc hy hcy hPs hP, hP⟩, fun X hXP => ?_⟩
  obtain ⟨hPv, hfP, W, hW, hWv, hPW⟩ := hP
  rcases SA.anc_total hU hXP (hfP.mono hΦU) with h | h
  · exact Or.inr h
  · left
    obtain ⟨hXt, hXP'⟩ := mem_of_between hU hΦ hΦU (((hΦ.F_anc_fcRoot).mono hΦU).trans h) hXP
      hPv.1
    have hes' := hes
    rw [← hes'] at hPv ⊢
    exact ⟨SA.voterBlockTree_anc hr hy hcy P hPv X hXP',
      SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem h hXt, W, by rw [hes']; exact hW, hWv,
      hXP'.trans hPW⟩

/-- **Every voter passes the path from `d.start` through `Q` to `P`**: its anchor `a` is below
`P`; if `d.start ⪯ a`, then `a` itself is on the path (`a = P` or `a ⪯ Q`); otherwise it passes
`d.start`. -/
theorem voters_pass
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hbelow : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P)
    (hreach : ¬ Anc (tr.HonestBlocks H) d.start
        (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) →
      ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) d.start ∧
        ℓy.frame.Anc d.start (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
          (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
          (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1))) :
    ∃ X, (X = P ∨ (ℓp.frame.Anc d.start X ∧ ℓp.frame.Anc X d.head)) ∧
      ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
      ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr
    proposer hS.run hS.shared.noColl).localRun
  have hU := Compose.honest_blocks_coherent hS.run.toLocalRun hS.shared.noColl
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hS.ready.1 hS.call
  obtain ⟨hΦy, -⟩ := SA.frameIn_of_callAt hr hy hcy.1
  obtain ⟨hst, hhd, hsd⟩ := proposal_walk hS
  set a := SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)
  by_cases hsa : Anc (tr.HonestBlocks H) d.start a
  · refine ⟨a, ?_, .refl, SA.anc_ghost (fun _ h => h.1.1) _ (getAnchor_mem hΦy _ _)⟩
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hbelow with h | ⟨Y, haY, hYP⟩
    · exact Or.inl h.symm
    obtain rfl : Y = d.head := hU.1 hYP.1 (hΦpU hhd)
      (Option.some_injective _ (hYP.2.2.symm.trans hS.parent))
    obtain ⟨hat, haQ⟩ := mem_of_between hU hΦp hΦpU
      (((hΦp.rooted.2 _ hst).mono hΦpU).trans hsa) haY hhd
    exact Or.inr ⟨SA.anc_tree_of_anc_U hU hΦp hΦpU hst hsa hat, haQ⟩
  · obtain ⟨h1, h2⟩ := hreach hsa
    exact ⟨d.start, Or.inr ⟨.refl, hsd⟩, h1, h2⟩

/-- **Every honest slot-`s` vote is `P`** given that every voter passes the path from `d.start`
through `Q` to `P` (workbench#12 §2–§3, as `Compose.honest_votes_eq_proposal`), by induction on
the vote's cut: from the passed block `X` the voter's walk follows the proposal walk to `Q`
(`proposal_suffix`) and steps to `P`, where it stops (`proposal_stop`, `ghost_follow`); with its
full fuel it has stopped (`ghost_stopped`), so it ends at `P`. -/
theorem votes_eq_of_pass
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hpass : ∀ y ∈ H, ∀ j ℓy e, SA.CastAt tr.projAC y j ℓy e → e.msg.slot = s →
      (∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
        e'.msg.head = P.root) →
      ∃ X, (X = P ∨ (ℓp.frame.Anc d.start X ∧ ℓp.frame.Anc X d.head)) ∧
        ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
        ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
          (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
          (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1))) :
    ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s → e.msg.head = P.root := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr
    proposer hS.run hS.shared.noColl).localRun
  have hU := Compose.honest_blocks_coherent hS.run.toLocalRun hS.shared.noColl
  have hc := hS.call
  have hd := hS.payload
  have hti := hS.time
  have hp := hS.ready.1
  obtain ⟨-, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨-, -, hsD⟩ := proposal_walk hS
  suffices main : ∀ j, (∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' →
      e'.msg.slot = s → e'.msg.head = P.root) →
      ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y j e → e.msg.slot = s → e.msg.head = P.root by
    intro x hx j
    induction j using Nat.strong_induction_on generalizing x with
    | _ j ih => exact main j (fun x' hx' j' hj' => ih j' hj' x' hx') x hx
  intro j hIH y hy e ⟨ℓy, hcy, hey⟩ hes
  have hcast : SA.CastAt tr.projAC y j ℓy e := ⟨hcy, hey⟩
  have hsl_i : sp.slot (tr.time iP) = s := by
    rw [hti]
    have := (SA.slot_arithmetic sp s).1 0 (by omega)
    simpa using this
  -- the proposal walk: from its start to `Q`, where it stops
  have hΦp := (SA.frameIn_of_callAt hr hp hc).1
  set W₁ := SA.ghost sp (ℓp.frame.viableTree ℓp.frame.tree)
    (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
    (SA.goldfishEligible sp ℓp.frame (tr.time iP) (SA.View.ofLists pay) ((s : Int) - 1))
    with hW₁
  have hTp : ℓp.frame.viableTree ℓp.frame.tree ⊆ ℓp.frame.tree := fun _ h => h.1
  have hQ : d.head = W₁ ℓp.frame.tree.ncard d.start := by
    rw [(acProposal_spec hd).2, hsl_i]
  have hstop₀ := SA.ghost_stopped hΦp.coherent hTp (hΦp.finite.subset hTp)
    (sc := SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
    (el := SA.goldfishEligible sp ℓp.frame (tr.time iP) (SA.View.ofLists pay) ((s : Int) - 1))
    (Set.ncard_le_ncard hTp hΦp.finite) d.start
  rw [← hW₁] at hstop₀
  have hstop₁ := hstop₀
  rw [← hQ] at hstop₁
  have hW₁add : ∀ a b x, W₁ (a + b) x = W₁ b (W₁ a x) := fun a b x => by
    rw [hW₁]; exact SA.ghost_add a b x
  have hstopQ : ∀ m, W₁ m d.head = d.head := fun m => by
    have h0 : W₁ 0 d.head = d.head := by rw [hW₁]; rfl
    rw [hW₁] at h0 ⊢
    exact (SA.ghost_fuel_stable (f := 0) (Nat.zero_le m) (by rw [h0]; exact hstop₁)).trans h0
  -- the proposal walk from a block `X` of its path from `d.start` ends at `Q`
  have hXQend : ∀ {X}, ℓp.frame.Anc d.start X → ℓp.frame.Anc X d.head →
      W₁ ℓp.frame.tree.ncard X = d.head := by
    intro X hDX hXQ
    obtain ⟨kx, -, hkx⟩ := SA.ghost_visits hΦp.coherent hTp _ hDX (hQ ▸ hXQ)
    rw [← hW₁] at hkx
    rw [← hkx, ← hW₁add, add_comm, hW₁add, ← hQ, hstopQ]
  -- the voter's walk passes a block `X` of the path from `d.start` through `Q` to `P`
  obtain ⟨hstep₀, hP₀⟩ := proposal_stop hS hy hcast hes
  have hsuf := proposal_suffix hS .refl hsD hy hcast hes
  have hΦy := (SA.frameIn_of_callAt hr hy hcy).1
  have hΦyU := (SA.frameIn_of_callAt hr hy hcy).2
  obtain ⟨X, hXc, haX, hXend⟩ := hpass y hy j ℓy e hcast hes hIH
  set W₂ := SA.ghost sp (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
    (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1))
    (SA.goldfishEligible sp ℓy.frame (tr.time j) (SA.mergedVoteView sp e.readPoint ℓy.frame s)
      ((s : Int) - 1)) with hW₂
  -- from `X`, the voter's walk ends at `P`
  have hXP : ∃ fX, W₂ fX X = P := by
    rcases hXc with rfl | ⟨hDX, hXQ⟩
    · exact ⟨0, rfl⟩
    refine ⟨ℓp.frame.tree.ncard + 1, SA.ghost_follow _ X ?_ hstop₁ ?_ hstep₀ hP₀⟩
    · exact hXQend hDX hXQ
    · intro m hm hne
      by_cases hXQ' : X = d.head
      · exact absurd (by rw [hXQ']; exact hstopQ m) hne
      have hXt : X ∈ ℓp.frame.tree := (Anc.mem hXQ hXQ').1
      have hXm : ℓp.frame.Anc X (W₁ m X) := by rw [hW₁]; exact SA.anc_ghost hTp m hXt
      have hQm : ℓp.frame.Anc (W₁ m X) d.head := by
        have hmem : W₁ m X ∈ ℓp.frame.tree := by
          rcases eq_or_ne (W₁ m X) X with h | h
          · rw [h]; exact hXt
          · exact (Anc.mem hXm (Ne.symm h)).2
        have hend : W₁ (ℓp.frame.tree.ncard - m) (W₁ m X) = d.head := by
          rw [← hW₁add, Nat.add_sub_cancel' hm.le]
          exact hXQend hDX hXQ
        rw [← hend, hW₁]
        exact SA.anc_ghost hTp _ hmem
      exact hsuf _ (hDX.trans hXm) hQm hne ((haX.mono hΦyU).trans (hXm.mono hΦpU))
  obtain ⟨fX, hfX⟩ := hXP
  have hspec := SA.castAt_head_of_viable hr hy hcast
    (hes ▸ ⟨P, proposal_frozen_viable hS hy hcast hes⟩)
  rw [hes] at hspec
  rw [hspec]
  congr 1
  have hTy : ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ⊆ ℓy.frame.tree :=
    fun B hB => hB.1.1
  change W₂ ℓy.frame.tree.ncard (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) = P
  obtain ⟨ky, -, hky⟩ := SA.ghost_visits hΦy.coherent hTy _ haX hXend
  have hP₂ : W₂ (ky + fX) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) = P := by
    rw [hW₂, SA.ghost_add, ← hW₂]
    rw [← hW₂] at hky
    rw [hky]; exact hfX
  have hstop₂ := SA.ghost_stopped hΦy.coherent hTy (hΦy.finite.subset hTy)
    (sc := SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
      ((s : Int) - 1))
    (el := SA.goldfishEligible sp ℓy.frame (tr.time j)
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1))
    (Set.ncard_le_ncard hTy hΦy.finite) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))
  rw [← hW₂] at hstop₂
  have hmax₁ := SA.ghost_fuel_stable (le_max_left (ℓy.frame.tree.ncard) (ky + fX)) hstop₂
  have hmax₂ := SA.ghost_fuel_stable (le_max_right (ℓy.frame.tree.ncard) (ky + fX)) (hP₂ ▸ hP₀)
  rw [← hW₂] at hmax₁ hmax₂
  rw [← hmax₁, hmax₂, hP₂]

/-- **The per-vote conclusion of HS.3 (a)** from the votes: every honest slot-`s` vote is `P`,
`P` is a viable head in the viable voter block tree, and its ancestors are retained. -/
theorem vote_conclusion
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hvotes : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s →
      e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e) (hes : e.msg.slot = s) :
    e.msg.head = P.root ∧
      ((P ∈ ℓ.frame.viableHeads ∧
          P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) ∨
        Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot) ∧
      ∀ X, Anc (tr.HonestBlocks H) X P →
        X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) X ℓ.frame.fcRoot :=
  ⟨hvotes y hy k e ⟨ℓ, hv⟩ hes, frozen_of_viableTree hS.run hS.shared.noColl hy hv hes
    hS.ready.2.2.2.2.1 (proposal_frozen_viable hS hy hv hes)⟩

/-- **HS.3 (a)** (`hs234-exact-interface.md` §4, with the start premise of #101), over the open
contracts (`voter_reaches_start_unlocked`, `proposal_suffix`, `proposal_only_child`). -/
theorem frozen_votes_unlocked
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hlock : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
        ∀ L ∈ ℓ.frame.tree, L.root = l.block →
          Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot)
    (hstart : ∀ kq ℓP, tr.projAC.CallAt p kq ℓP → ℓP.call = .proposal → tr.time kq = sp.ts s →
      ∀ l ∈ SA.liveLocks sp (tr.post kq).ac.locks ℓP.frame (tr.time kq), l.slot < s →
        ∀ L ∈ ℓP.frame.tree, L.root = l.block →
          ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
            (∃ l' ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k),
              ∃ L' ∈ ℓ.frame.tree, L'.root = l'.block ∧ Anc (tr.HonestBlocks H) L L') ∨
            Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot) :
    ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = P.root ∧
      ((P ∈ ℓ.frame.viableHeads ∧
          P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) ∨
        Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot) ∧
      ∀ X, Anc (tr.HonestBlocks H) X P →
        X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) X ℓ.frame.fcRoot := by
  have hvotes := votes_eq_of_pass hS fun y hy j ℓy e hcy hes hIH =>
    have hb := voter_anchor_below hS hlock hy hcy hes hIH
    voters_pass hS hy hcy hb
      (voter_reaches_start_unlocked hS hlock hstart hy hcy hes hIH hb)
  exact fun y hy k ℓ e hv hes => vote_conclusion hS hvotes hy hv hes

/-- **HS.3 (b)** (`hs234-exact-interface.md` §4 (b)), with HS.2 as a hypothesis: its fourth
clause is (a)'s lock premise (the voters' cuts are in the phase from `i₀`, `phaseOn_voter`); the
votes are `P` as in (a), with `voter_reaches_start_clean`; the later votes and parents are
`later_extend`. -/
theorem frozen_votes_clean {Gp : Time}
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hp : PropPlus tr H proposer g Gp) (hr : rTime sp w ≤ sp.ts s) (hdrain : CleanLockDrain) :
    (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = P.root ∧
      ((P ∈ ℓ.frame.viableHeads ∧
          P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) ∨
        Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot) ∧
      ∀ X, Anc (tr.HonestBlocks H) X P →
        X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) X ℓ.frame.fcRoot) ∧
    (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P) ∧
    ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
      tr.ProposesAt (proposer s') k' P' → proposer s' ∈ H →
      PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) P Pr := by
  have hPr := honestProposalRun_of_ready hS.run hS.shared.noColl hS.ready
  have hlock : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
        ∀ L ∈ ℓ.frame.tree, L.root = l.block →
          Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot :=
    fun y hy k ℓ e hv hes =>
      (hdrain sp ro proposer dg H tr g ΔF Gp w i₀ m c
        hS.run hS.shared hS.catchUp hp hS.settled).2.2.2 s P
        hPr hr y hy k ℓ e hv hes (phaseOn_voter hS.run hS.shared hS.settled
          (start_le_voter hS.run hS.shared.noColl hS.start_time hy hv hes)
          (hS.phase y hy k ℓ e hv hes))
  have hvotes := votes_eq_of_pass hS fun y hy j ℓy e hcy hes hIH =>
    have hb := voter_anchor_below hS hlock hy hcy hes hIH
    voters_pass hS hy hcy hb (voter_reaches_start_clean hS hp hr hdrain hlock hy hcy hes hIH hb)
  have hall := fun y hy k ℓ e hv hes => vote_conclusion hS hvotes (y := y) (k := k) (ℓ := ℓ)
    (e := e) hy hv hes
  exact ⟨hall, later_extend hS hp hr hdrain hall⟩

end Consensus.Goldilocks.Healing

end
