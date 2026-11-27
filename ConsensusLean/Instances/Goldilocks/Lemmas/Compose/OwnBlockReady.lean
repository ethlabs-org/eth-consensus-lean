module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers

public section

/-! # Finality preview and sealed proposal support

The preview reads the parent's chain state, slot and attestations, not a candidate
digest. Sealing changes only the support list, not the declarations or the walk.
Readiness below is the marked-head clause; backing all declarations is separate.
-/

namespace Consensus.Goldilocks

namespace FG.FGParams

/-- The finalized checkpoint of the attestation/height transition, before a
candidate root is available. No placeholder block is constructed. -/
def finalityPreview (gp : FGParams) (σ : ChainState gp.n) (slot : Nat)
    (atts : List (Att gp.n)) : Nat :=
  (gp.finalizePrune (atts.foldl ChainState.processAtt { σ with s := slot })).F

private theorem heightEvents_F (gp : FGParams) (σ : ChainState gp.n) :
    (gp.heightEvents σ).F = (gp.finalizePrune σ).F := by
  unfold heightEvents
  dsimp only
  split_ifs <;> rfl

private theorem finalizePrune_set_L (gp : FGParams) (σ : ChainState gp.n) (root : Nat) :
    (gp.finalizePrune { σ with L := root }).F = (gp.finalizePrune σ).F := by
  have hb : gp.bestFinal { σ with L := root } = gp.bestFinal σ := rfl
  simp only [finalizePrune, hb]
  cases gp.bestFinal σ <;> rfl

/-- Every successful transition has the previewed finality. In particular neither
the candidate root nor its proposer affects this checkpoint. -/
theorem stateTransition_finalityPreview (gp : FGParams) {σ σ' : ChainState gp.n}
    {B : FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    σ'.F = gp.finalityPreview σ B.slot B.atts := by
  unfold stateTransition at h
  split_ifs at h
  cases h
  rw [heightEvents_F, finalizePrune_set_L]
  rfl

/-- Refusal and finalized checkpoint are independent of the block root. -/
theorem stateTransition_finality_root_independent (gp : FGParams)
    (σ : ChainState gp.n) (B : FGBlock gp.n) (root : Nat) :
    (gp.stateTransition σ { B with root := root }).map ChainState.F =
      (gp.stateTransition σ B).map ChainState.F := by
  unfold stateTransition
  dsimp only
  split_ifs
  · simp only [Option.map_some, heightEvents_F, finalizePrune_set_L]
  · rfl

end FG.FGParams

namespace Store

/-- The finality update retains a held head above both the old store finality and
the block-chain checkpoint, whether the checkpoint's adoption guard passes or not. -/
theorem preview_head_retained {P : Params} {ACP : Type} (st : Store P ACP)
    (σ : FG.ChainState P.n) {F Hd : NodeBlock P ACP}
    (hF : st.blocks σ.F = some F) (hHd : Hd ∈ st.tree)
    (hold : st.Anc st.F Hd) (hnew : st.Anc F Hd) :
    Hd ∈ (st.updateFinality σ).toFrame.tree := by
  obtain ⟨hb, _, _, _, _, hf⟩ := updateFinality_spec st σ
  have ht : (st.updateFinality σ).tree = st.tree := by simp only [tree, hb]
  change Hd ∈ (st.updateFinality σ).tree ∧
    (st.updateFinality σ).Anc (st.updateFinality σ).F Hd
  refine ⟨ht ▸ hHd, ?_⟩
  change Goldilocks.Anc (st.updateFinality σ).tree _ Hd
  rw [ht]
  rcases hf with hf | ⟨hf, _⟩
  · rw [hf]; exact hold
  · have heq : (st.updateFinality σ).F = F := Option.some.inj (hf.symm.trans hF)
    rw [heq]; exact hnew

/-- Successful block import retains an already held head above old store finality
and the preview. The same statement applies to the proposer and any receiver;
accepting a block alone does not supply the head-availability premise. -/
theorem onBlock_preview_head_retained {P : Params} {ACP : Type}
    {st st' : Store P ACP} {B F Hd : NodeBlock P ACP} {pr : Nat}
    (h : st.onBlock B = some st') (hp : B.parent = some pr)
    (hroot : F.root = P.fg.finalityPreview (st.σ pr) B.slot B.fgPayload)
    (hF : F ∈ st.tree) (hHd : Hd ∈ st.tree)
    (hold : st.Anc st.F Hd) (hnew : st.Anc F Hd) : Hd ∈ st'.toFrame.tree := by
  obtain ⟨pr', σ', hp', hB, _, _, hσ, rfl⟩ := onBlock_eq_some h
  obtain rfl : pr' = pr := Option.some.inj (hp'.symm.trans hp)
  have hf : σ'.F = F.root := (P.fg.stateTransition_finalityPreview hσ).trans hroot.symm
  let added : Store P ACP :=
    { st with
      blocks := Function.update st.blocks B.root (some B)
      σ := Function.update st.σ B.root σ' }
  have hsub : st.tree ⊆ added.tree := by
    intro X hX
    have hne : X.root ≠ B.root := by
      intro he
      change st.blocks X.root = some X at hX
      rw [he, hB] at hX
      cases hX
    change Function.update st.blocks B.root (some B) X.root = some X
    rw [Function.update_of_ne hne]
    exact hX
  have hFa : added.blocks σ'.F = some F := by
    rw [hf]
    exact hsub hF
  have hm := preview_head_retained added σ' hFa (hsub hHd)
    (hold.mono hsub) (hnew.mono hsub)
  obtain ⟨atts, he⟩ := addAtts_eq (added.updateFinality σ') B.fgPayload
  rw [he]
  exact hm

end Store

namespace AC

variable {n : Nat} {FGP : Type}

/-- Keep only resolved support heads extending the block-chain finality root.
Ancestry is inclusive and declarations are deliberately not filtered. -/
noncomputable def sealSupport (Φ : Frm n FGP) (F : Blk n FGP)
    (pay : Payload n) : Payload n := by
  classical
  exact (pay.1, pay.2.filter (fun x => AncR Φ F x.head))

theorem sealSupport_declared (Φ : Frm n FGP) (F : Blk n FGP) (pay : Payload n) :
    (sealSupport Φ F pay).1 = pay.1 := by rfl

theorem mem_sealSupport {Φ : Frm n FGP} {F : Blk n FGP} {pay : Payload n} {x : Vote n} :
    x ∈ (sealSupport Φ F pay).2 ↔ x ∈ pay.2 ∧ AncR Φ F x.head := by
  classical
  simp [sealSupport]

/-- Filtering keeps the ordered support-sublist invariant, including both
declarations witnessing equivocation. -/
theorem sealSupport_sublist (Φ : Frm n FGP) (F : Blk n FGP) {pay : Payload n}
    (h : pay.2.Sublist pay.1) : (sealSupport Φ F pay).2.Sublist pay.1 := by
  classical
  exact List.filter_sublist.trans h

private theorem resolved_head {A : ACState n} {Φ : Frm n FGP} {x : Vote n}
    (h : resolutionTime A Φ x < ⊤) :
    ∃ Hd ∈ Φ.tree, Hd.root = x.head ∧ Hd.slot ≤ x.slot := by
  unfold resolutionTime at h
  split at h
  · exact absurd h (lt_irrefl _)
  · rename_i Hd hl
    obtain ⟨hm, hr⟩ := lookup_eq_some hl
    split_ifs at h with hs
    · exact absurd h (lt_irrefl _)
    · exact ⟨Hd, hm, hr, by omega⟩

/-- A sealed raw mark is usable in any post-block tree retaining the old heads
above the previewed checkpoint. This covers own import and each receiver without
assuming it adopts that checkpoint as its store finality. -/
theorem sealed_mark_usable {A : ACState n} {Φ Ψ : Frm n FGP} {F : Blk n FGP}
    {s : Nat} {x : Vote n} (hΦ : FrameOK Φ)
    (hkeep : ∀ Hd ∈ Φ.tree, Φ.Anc F Hd → Hd ∈ Ψ.tree)
    (hx : x ∈ (sealSupport Φ F (voteViewList A Φ (s : Int) ⊤)).2)
    (hslot : x.slot = s) :
    ∃ Hd ∈ Ψ.tree, Hd.root = x.head ∧ Hd.slot + 1 ≤ s + 1 := by
  obtain ⟨hraw, R, hR, hr, hFR⟩ := mem_sealSupport.mp hx
  have hres : resolutionTime A Φ x < ⊤ := (List.mem_filter.mp hraw).2 |> of_decide_eq_true
  obtain ⟨Hd, hHd, hroot, hs⟩ := resolved_head hres
  have heq : Hd = R := hΦ.coherent.1 hHd hR (hroot.trans hr.symm)
  subst R
  exact ⟨Hd, hkeep Hd hHd hFR, hroot, by omega⟩

/-- Full readiness follows once the unchanged declaration-backing requirement is
also supplied. No assumption that the reader adopts the preview is needed. -/
theorem voteReady_of_sealed {sp : ACParams} {A R : ACState sp.n}
    {Φ Ψ : Frm sp.n FGP} {F P : Blk sp.n FGP} {s : Nat}
    (hΦ : FrameOK Φ)
    (hkeep : ∀ Hd ∈ Φ.tree, Φ.Anc F Hd → Hd ∈ Ψ.tree)
    (hP : P ∈ Ψ.tree) (hslot : P.slot = s + 1)
    (hpay : P.acPayload = sealSupport Φ F (voteViewList A Φ (s : Int) ⊤))
    (hdecl : AllDeclaredVotesCounted sp R Ψ (s + 1)) :
    voteReady sp R Ψ (s + 1) := by
  refine ⟨⟨P, hP, hslot, ?_⟩, hdecl⟩
  intro x hx hs
  change x ∈ P.acPayload.2 at hx
  rw [hpay] at hx
  exact sealed_mark_usable hΦ hkeep hx (by omega)

/-- The exact additional coverage premise: every relevant raw mark extends the
preview. Equality of the two prior-slot trees alone says nothing about this. -/
theorem sealed_reader_coverage_iff (Φ : Frm n FGP) (F : Blk n FGP)
    (pay : Payload n) (needed : Vote n → Prop) :
    (∀ x ∈ pay.2, needed x → x ∈ (sealSupport Φ F pay).2) ↔
      ∀ x ∈ pay.2, needed x → AncR Φ F x.head := by
  simp only [mem_sealSupport]
  constructor
  · exact fun h x hx hn => (h x hx hn).2
  · exact fun h x hx hn => ⟨hx, h x hx hn⟩

/-- A vote-independent sufficient stable-finality premise: the preview is no
later than the pre-proposal frame root. It preserves every raw mark, so existing
raw-view comparisons can be reused without requiring a reader to adopt it. -/
theorem sealSupport_eq_of_preview_ancestor {Φ : Frm n FGP} (hΦ : FrameOK Φ)
    {F : Blk n FGP} (hF : Φ.Anc F Φ.F) {pay : Payload n}
    (hheads : ∀ x ∈ pay.2, InTree Φ x.head) : sealSupport Φ F pay = pay := by
  classical
  apply Prod.ext
  · rfl
  · change pay.2.filter _ = pay.2
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨Hd, hm, hr⟩ := hheads x hx
    exact decide_eq_true (show AncR Φ F x.head from
      ⟨Hd, hm, hr, hF.trans (hΦ.rooted.2 Hd hm)⟩)

end AC

namespace AC.OwnBlockCounterexample

abbrev gp : FG.FGParams := ⟨1, by decide, 1, 0⟩

abbrev sp : ACParams where
  toParams := {
    n := 1, hn := le_rfl, Δ := 1, hΔ := one_pos
    slotTime := fun s => 4 * (s : Int)
    slotTime_zero := by simp
    slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
    slotTime_public := fun _ => one_dvd _
    genesisRoot := 0, δt := 1 }
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; omega
  k := 2
  two_le_k := le_rfl
  c := 2
  two_le_c := le_rfl

def genesis : Blk 1 Unit := ⟨0, none, 0, 0, 0, (), ([], [])⟩
def checkpoint : Blk 1 Unit := ⟨1, some 0, 1, 0, 0, (), ([], [])⟩
def frame : Frm 1 Unit := ⟨{genesis, checkpoint}, genesis, checkpoint, {checkpoint}⟩
def vote : Vote 1 := ⟨0, 1, 0⟩
def state : ACState 1 :=
  { ACState.initial (n := 1) 0 with
    pool := fun s => if s = 1 then [vote] else []
    voteStamp := fun _ => ⊥
    blockStamp := fun _ => ⊥ }

/-- A concrete parent state with a pending quorum at the checkpoint. Its next
transition finalizes root `1`, independently of the candidate root. -/
def parentState : FG.ChainState 1 :=
  { FG.ChainState.init gp with
    L := 1
    s := 1
    h := 3
    pending := [(1, 1)]
    fin := fun _ => {0}
    J := 1
    hj := 1 }

private theorem raw_mark : vote ∈ (voteViewList state frame 1 ⊤).2 := by
  have hl : lookup frame vote.head = some genesis := by
    cases hl : lookup frame vote.head with
    | none => exact False.elim (lookup_eq_none hl ⟨genesis, by simp [frame], rfl⟩)
    | some R =>
      obtain ⟨hm, hr⟩ := lookup_eq_some hl
      congr 1
      simp only [frame, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with hm | hm
      · exact hm
      · rw [hm] at hr; simp [checkpoint, vote] at hr
  have hr : resolutionTime state frame vote < ⊤ := by
    simp only [resolutionTime, hl]
    simp [state, genesis, vote]
  simpa [voteViewList, ACState.poolAt, state] using (decide_eq_true hr)

private theorem not_above : ¬ AncR frame checkpoint vote.head := by
  rintro ⟨R, hR, hr, ha⟩
  have heq : R = genesis := by
    simp only [frame, Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    rcases hR with hR | hR
    · exact hR
    · subst hR; simp [checkpoint, vote] at hr
  subst R
  have hend : ∀ X : Blk 1 Unit, ¬ ParentIn frame.tree X genesis := by
    intro X h; simpa [genesis] using h.2.2
  rcases Relation.ReflTransGen.cases_tail ha with h | ⟨X, _, h⟩
  · have := congrArg Block.root h; simp [checkpoint, genesis] at this
  · exact hend X h

/-- Equal prior-slot trees do not ensure that a reader-visible raw mark survives
sealing. The reader can still need the genesis head while the block-chain
transition finalizes its child. This is a local coverage counterexample, not an
assertion that the supplied parent state realizes an entire AC execution. -/
theorem equal_prior_trees_do_not_cover :
    gp.finalityPreview parentState 2 [] = checkpoint.root ∧
    {X | X ∈ frame.tree ∧ X.slot ≤ 1} = {X | X ∈ frame.tree ∧ X.slot ≤ 1} ∧
    vote ∈ (voteViewList state frame 1 ⊤).2 ∧
    vote ∉ (sealSupport frame checkpoint (voteViewList state frame 1 ⊤)).2 := by
  refine ⟨by decide, rfl, raw_mark, ?_⟩
  exact fun h => not_above (mem_sealSupport.mp h).2

/-- The dropped mark is present in the reader's *frozen base*, not merely in a
raw pool. Hence equal prior trees alone cannot give sealed support equality. -/
theorem frozen_reader_support_not_covered :
    vote ∈ (mergedVoteView sp state frame 2).support ∧
    vote ∉ (sealSupport frame checkpoint (voteViewList state frame 1 ⊤)).2 := by
  refine ⟨Or.inl ?_, equal_prior_trees_do_not_cover.2.2.2⟩
  have hres : resolutionTime state frame vote < ⊤ := by
    exact of_decide_eq_true (List.mem_filter.mp raw_mark).2
  have hfinite : resolutionTime state frame vote = ⊥ := by
    unfold resolutionTime at hres ⊢
    split at *
    · exact absurd hres (lt_irrefl _)
    · split_ifs at hres ⊢
      · exact absurd hres (lt_irrefl _)
      · rfl
  change vote ∈ (voteViewList state frame (2 - 1) (ETime.of (freeze sp 2))).2
  simp only [voteViewList, List.mem_filter, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · simp [ACState.poolAt, state, ETime.of]
  · rw [hfinite]; exact WithBot.bot_lt_coe _

/-- The repair is not vacuous: inclusive ancestry keeps a mark at the checkpoint
itself, with a nonempty declaration and support list. -/
theorem checkpoint_mark_survives :
    let x : Vote 1 := ⟨0, 1, 1⟩
    x ∈ (sealSupport frame checkpoint ([x], [x])).2 := by
  dsimp only
  apply mem_sealSupport.mpr
  exact ⟨by simp, checkpoint, by simp [frame], rfl, .refl⟩

/-- A stronger nonvacuity control: stable finality at the frame root keeps a
nonempty support list even when its head is strictly above that root. -/
theorem stable_finality_mark_survives :
    let x : Vote 1 := ⟨0, 1, 1⟩
    x ∈ (sealSupport frame genesis ([x], [x])).2 := by
  dsimp only
  apply mem_sealSupport.mpr
  refine ⟨by simp, checkpoint, by simp [frame], rfl, ?_⟩
  exact Relation.ReflTransGen.single ⟨by simp [frame], by simp [frame], rfl⟩

def fork : Blk 1 Unit := ⟨2, some 0, 1, 0, 0, (), ([], [])⟩
def forkFrame : Frm 1 Unit := { frame with tree := {genesis, checkpoint, fork} }
def forkVote : Vote 1 := ⟨0, 1, 2⟩

private theorem leaf_anc {X Y : Blk 1 Unit}
    (hX : X = checkpoint ∨ X = fork) (h : Anc forkFrame.tree X Y) : Y = X := by
  induction h with
  | refl => rfl
  | @tail Z Y _ hZY ih =>
    have hm := hZY.2.1
    have hp := hZY.2.2
    rw [ih] at hp
    simp only [forkFrame, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hX with rfl | rfl <;> rcases hm with rfl | rfl | rfl <;>
      simp [genesis, checkpoint, fork] at hp

/-- A fork mark can affect opponents, unlike a dropped ancestor mark. With the
same prior tree at both cuts, sealing removes the sole opponent of the checkpoint.
This is a local view counterexample, not an `ACRun` reachability claim. -/
theorem fork_opponents_not_preserved :
    opponents sp forkFrame (View.ofLists ([forkVote], [forkVote])) 1 checkpoint ≠
      opponents sp forkFrame (View.ofLists (sealSupport forkFrame checkpoint
        ([forkVote], [forkVote]))) 1 checkpoint := by
  have hnc : ¬ Compatible forkFrame.tree fork checkpoint := by
    rintro (h | h)
    · have he := leaf_anc (Or.inr rfl) h
      have := congrArg Block.root he
      simp [checkpoint, fork] at this
    · have he := leaf_anc (Or.inl rfl) h
      have := congrArg Block.root he
      simp [checkpoint, fork] at this
  have hn : ¬ AncR forkFrame checkpoint forkVote.head := by
    rintro ⟨R, hR, hr, ha⟩
    have he := leaf_anc (Or.inl rfl) ha
    subst R
    simp [checkpoint, forkVote] at hr
  have hs : (sealSupport forkFrame checkpoint ([forkVote], [forkVote])).2 = [] := by
    classical
    simp [sealSupport, hn]
  have hl : (0 : Fin 1) ∈
      opponents sp forkFrame (View.ofLists ([forkVote], [forkVote])) 1 checkpoint := by
    exact Or.inr ⟨forkVote, by simp [View.ofLists], rfl, rfl,
      fork, by simp [forkFrame], rfl, hnc⟩
  intro he
  rw [he] at hl
  simp [opponents, View.ofLists, sealSupport_declared, hs, equivocators] at hl

end AC.OwnBlockCounterexample
end Consensus.Goldilocks

end
