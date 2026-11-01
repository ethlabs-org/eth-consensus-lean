module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Forwarding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Cuts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outbox
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Release
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
public import ConsensusLean.Lemmas.Model.Protection

set_option linter.style.longFile 2100

public section

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}

private theorem contained_parts_infix {n : Nat} {Role Item Body : Type}
    {o q : Model.Obj n Role Item Body} (h : Model.Obj.Contains o q) :
    ∃ pre post, o.parts = pre ++ q.parts ++ post := by
  rcases h.cases with rfl | ⟨c, hc, hcq⟩
  · exact ⟨[], [], by simp⟩
  · obtain ⟨pre, post, hp⟩ := contained_parts_infix hcq
    obtain ⟨before, after, he, _⟩ := List.eq_append_cons_of_mem hc
    refine ⟨o :: (before.flatMap Model.Obj.parts ++ pre),
      post ++ after.flatMap Model.Obj.parts, ?_⟩
    rw [Model.Obj.parts_eq, he, List.flatMap_append, List.flatMap_cons, hp]
    simp only [List.cons_append, List.append_assoc]
termination_by sizeOf o
decreasing_by exact lt_trans (List.sizeOf_lt_of_mem hc) (Model.Obj.carried_size_lt _)

/-- Splitting recursive receipt processing preserves the actual intermediate cut,
rather than replacing a processing occurrence by an arbitrary historical call. -/
theorem deliverSeq_append_split {proposer : Nat → Fin sp.n} {tr : GoldilocksTrace sp ro}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {hs : List (Header Info × Nat)}
    {y : Fin sp.n} {t : Time} (xs ys : List (Wire sp.n)) {j j' : Nat}
    (h : DeliverSeq proposer tr dg hs y t (xs ++ ys) j j') :
    ∃ m, DeliverSeq proposer tr dg hs y t xs j m ∧
      DeliverSeq proposer tr dg hs y t ys m j' := by
  induction xs generalizing j with
  | nil => exact ⟨j, .nil j, h⟩
  | cons x xs ih =>
    cases h with
    | event e he hg htail =>
      obtain ⟨m, hl, hr⟩ := ih htail
      exact ⟨m, .event e he hg hl, hr⟩
    | drop he htail =>
      obtain ⟨m, hl, hr⟩ := ih htail
      exact ⟨m, .drop he hl, hr⟩
    | noCut e he hz htail =>
      obtain ⟨m, hl, hr⟩ := ih htail
      exact ⟨m, .noCut e he hz hl, hr⟩

/-- A forwarding envelope itself has no node handler. -/
private theorem canonEvent_forward_none (hs : List (Header Info × Nat))
    (x : Fin sp.n) (t : Time) (p : Option (Wire sp.n)) (B : Blk sp) :
    canonEvent sp ro hs (forwardObj sp x t p B) = none := by
  simp [canonEvent, forwardObj, decodeBlock, decodeVoteObj, decodeAttObj]

/-- A forwarding chain processes the exact parent's entire subtree before the
child's canonical block and payload; the split retains the actual cut boundary. -/
theorem deliverSeq_forward_parent {proposer : Nat → Fin sp.n} {tr : GoldilocksTrace sp ro}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {hs : List (Header Info × Nat)}
    {y x : Fin sp.n} {u t : Time} {parent : Wire sp.n} {B : Blk sp} {j j' : Nat}
    (h : DeliverSeq proposer tr dg hs y u
      (forwardObj sp x t (some parent) B).parts j j') :
    ∃ m, DeliverSeq proposer tr dg hs y u parent.parts j m ∧
      DeliverSeq proposer tr dg hs y u (blockObj sp B).parts m j' := by
  rw [Model.Obj.parts_eq] at h
  have hz := canonEvent_forward_none (ro := ro) hs x t (some parent) B
  cases h with
  | event e he _ _ => rw [hz] at he; cases he
  | noCut e he _ _ => rw [hz] at he; cases he
  | drop _ htail =>
    have ht : DeliverSeq proposer tr dg hs y u
        (parent.parts ++ (blockObj sp B).parts) j j' := by
      simpa only [forwardObj, Model.Obj.carried, Option.toList_some, List.cons_append,
        List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] using htail
    exact deliverSeq_append_split _ _ ht

/-- The leaf wrapper processes its genesis-parent child at the same starting cut. -/
private theorem deliverSeq_forward_genesis {proposer : Nat → Fin sp.n}
    {tr : GoldilocksTrace sp ro} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {hs : List (Header Info × Nat)} {y x : Fin sp.n} {u t : Time} {B : Blk sp} {j j' : Nat}
    (h : DeliverSeq proposer tr dg hs y u (forwardObj sp x t none B).parts j j') :
    DeliverSeq proposer tr dg hs y u (blockObj sp B).parts j j' := by
  rw [Model.Obj.parts_eq] at h
  have hz := canonEvent_forward_none (ro := ro) hs x t none B
  cases h with
  | event e he _ _ => rw [hz] at he; cases he
  | noCut e he _ _ => rw [hz] at he; cases he
  | drop _ htail =>
    simpa only [forwardObj, Model.Obj.carried, Option.toList_none, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] using htail

/-- On one coherent ancestor chain, an unheld child above the receiver's finalized
tip can be attached to its held parent. No agreement between receivers is used. -/
private theorem receipt_ancestry {n : Nat} {FGP ACP : Type}
    {U T : Set (Block n FGP ACP)} {F A P B : Block n FGP ACP}
    (hU : Coherent U) (hF : F ∈ T) (hAB : Anc U A B) (hFB : Anc U F B)
    (hparent : ParentIn U P A) (hP : P ∈ T)
    (hlocal : ∀ {X Y}, Anc U X Y → Y ∈ T → Anc T X Y) :
    A ∈ T ∨ Anc (insert A T) F A := by
  rcases Anc.total hU hAB hFB with hAF | hFA
  · have h := hlocal hAF hF
    by_cases he : A = F
    · exact Or.inl (he ▸ hF)
    · exact Or.inl (h.mem he).1
  · by_cases he : F = A
    · exact Or.inl (he ▸ hF)
    · rcases hFA.cases_tail with heq | ⟨Q, hFQ, hQA⟩
      · exact False.elim (he heq.symm)
      · have hQP : Q = P := hU.1 hQA.1 hparent.1
          (Option.some.inj (hQA.2.2.symm.trans hparent.2.2))
        subst Q
        exact Or.inr (((hlocal hFQ hP).mono (Set.subset_insert _ _)).tail
          ⟨Or.inr hP, Or.inl rfl, hparent.2.2⟩)

/-- The observation's receiver guard bounds every earlier receipt cut. Once the
parent is held, the child is already held or satisfies the receiver's ancestry guard. -/
theorem receipt_held_or_ancestry {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {r j : Nat} (hrj : r ≤ j)
    {A P B : Blk sp} (hAB : Anc (tr.HonestBlocks H) A B)
    (hFB : Anc (tr.HonestBlocks H) (tr.state y j).fg.F B)
    (hparent : ParentIn (tr.HonestBlocks H) P A)
    (hP : P ∈ (tr.state y r).fg.tree) :
    A ∈ (tr.state y r).fg.tree ∨
      Anc (insert A (tr.state y r).fg.tree) (tr.state y r).fg.F A := by
  have hF := (Store.cache_invariants sp.toParams (SA.Payload sp.n) _ _
    (Compose.fg_reachable hrun.toLocalRun hy r)).1
  exact receipt_ancestry (Compose.honest_blocks_coherent hrun.toLocalRun hnc) hF hAB
    ((Healing.run_F_mono hrun.toLocalRun hy hrj).trans hFB) hparent hP
    (fun h hY => Compose.honest_held_anc hrun hnc hy h hY)

/-- The parent state needed by receiver transfer is independent of which honest
holder supplies it, including holders on opposite sides of a restart. -/
private theorem receipt_parent_state {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s : Nat} {P : Blk sp}
    (hPy : P ∈ (tr.state y r).fg.tree) (hPx : P ∈ (tr.state x s).fg.tree) :
    (tr.state y r).fg.σ P.root = (tr.state x s).fg.σ P.root := by
  have hp (z : Fin sp.n) (hz : z ∈ H) (i : Nat) :
      tr.projFG.store z i = (tr.state z i).fg := by
    change (tr.projFG.state z i).1 = _
    rw [Compose.projFG_state hrun.toLocalRun hz i]
  rw [← hp y hy r] at hPy ⊢
  rw [← hp x hx s] at hPx ⊢
  exact Store.σ_eq_of_held (Compose.projFG_localRun hrun hnc) hy hx hPy hPx

/-- Acceptance records its block in the honest tree at the following cut. -/
private theorem accepted_mem_succ {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) {x : Fin sp.n} (hx : x ∈ H)
    {k : Nat} {B : Blk sp} (ha : tr.AcceptAt x k B) :
    B ∈ (tr.state x (k + 1)).fg.tree := by
  rw [tr.state_succ_of_call ha,
    (Store.tree_grows sp.toParams _ _ _ (Compose.fg_reachable hrun.toLocalRun hx k)).1
      B _ (hrun.cutLaw x hx k _ ha).2.1]
  exact Set.mem_insert _ _

/-- A root occupied at an honest receiver is the exact already-accepted source
block, not merely a wire-equivalent block, under run-wide collision freedom. -/
private theorem received_root_absent {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {k r : Nat} {B : Blk sp}
    (ha : tr.AcceptAt x k B) (hnot : B ∉ (tr.state y r).fg.tree) :
    (tr.state y r).fg.blocks B.root = none := by
  cases hb : (tr.state y r).fg.blocks B.root with
  | none => rfl
  | some C =>
    have hroot := (Compose.fg_reachable hrun.toLocalRun hy r).blocks_root hb
    have hC : C ∈ (tr.state y r).fg.tree := by
      change (tr.state y r).fg.blocks C.root = some C
      rwa [hroot]
    have heq := Compose.tree_root_inj hrun.toLocalRun hnc hy hx hC
      (accepted_mem_succ hrun hx ha) hroot
    exact False.elim (hnot (heq ▸ hC))

/-- The exact parent of an accepted block was held at its source acceptance cut. -/
private theorem accepted_parent_held {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {B P : Blk sp}
    (ha : tr.AcceptAt x k B) (hp : B.parent = some P.root)
    (hP : P ∈ tr.HonestBlocks H) : P ∈ (tr.state x k).fg.tree := by
  obtain ⟨pr, _, hpr, _, hh, _⟩ := Store.onBlock_eq_some (hrun.cutLaw x hx k _ ha).2.1
  have heq : pr = P.root := Option.some.inj (hpr.symm.trans hp)
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hh
  have hroot := (Compose.fg_reachable hrun.toLocalRun hx k).blocks_root hQ
  have hQt : Q ∈ (tr.state x k).fg.tree := by
    change (tr.state x k).fg.blocks Q.root = some Q
    rwa [hroot]
  have hQP := (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1
    ⟨x, hx, k, hQt⟩ hP (hroot.trans heq)
  exact hQP ▸ hQt

/-- At an earlier receipt cut, a source-accepted ancestor with its parent held is
already held or passes the receiver store's full acceptance guard. -/
theorem receipt_held_or_transfer {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {k r j : Nat} (hrj : r ≤ j)
    {A P B : Blk sp} (ha : tr.AcceptAt x k A)
    (hAB : Anc (tr.HonestBlocks H) A B)
    (hFB : Anc (tr.HonestBlocks H) (tr.state y j).fg.F B)
    (hp : A.parent = some P.root) (hP : P ∈ (tr.state y r).fg.tree) :
    A ∈ (tr.state y r).fg.tree ∨ ∃ dst', (tr.state y r).fg.onBlock A = some dst' := by
  have hPu : P ∈ tr.HonestBlocks H := ⟨y, hy, r, hP⟩
  have hAu : A ∈ tr.HonestBlocks H := ⟨x, hx, k + 1, accepted_mem_succ hrun hx ha⟩
  rcases receipt_held_or_ancestry hrun hnc hy hrj hAB hFB ⟨hPu, hAu, hp⟩ hP with
    hheld | hanc
  · exact Or.inl hheld
  · by_cases hheld : A ∈ (tr.state y r).fg.tree
    · exact Or.inl hheld
    · apply Or.inr
      have hsrc := (hrun.cutLaw x hx k _ ha).2.1
      have hstate := receipt_parent_state hrun hnc hx hy hP
        (accepted_parent_held hrun hnc hx ha hp hPu)
      exact Store.onBlock_transfer hsrc hp (received_root_absent hrun hnc hx hy ha hheld)
        (Option.isSome_iff_exists.mpr ⟨P, hP⟩) hstate hanc

/-- A successful store transfer at the exact canonical receipt position yields
acceptance there; a future-slot empty handler is excluded explicitly. -/
private theorem deliverSeq_block_accepts {proposer : Nat → Fin sp.n}
    {tr : GoldilocksTrace sp ro} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {hs : List (Header Info × Nat)} {y : Fin sp.n} {u : Time} {B : Blk sp}
    {os : List (Wire sp.n)} {r e : Nat}
    (hd : decodeBlock sp hs (blockObj sp B) = some B)
    (hseq : DeliverSeq proposer tr dg hs y u (blockObj sp B :: os) r e)
    (ht : ¬ sp.toParams.slotOf u < B.slot)
    (hon : ∃ dst', (tr.state y r).fg.onBlock B = some dst') :
    tr.AcceptAt y r B ∧ r < e := by
  have hc : canonEvent sp ro hs (blockObj sp B) = some (.block B) := by
    simp only [canonEvent, hd]
  obtain ⟨dst', hon⟩ := hon
  cases hseq with
  | drop h _ => rw [hc] at h; cases h
  | noCut event h hz _ =>
    have heq := Option.some.inj (h.symm.trans hc)
    subst event
    simp [exec, onBlock, ht, hon] at hz
  | event event h hg htail =>
    have heq := Option.some.inj (h.symm.trans hc)
    subst event
    have hlen : 0 < (exec proposer dg y (tr.state y r) u (.block B)).2.length := by
      simp [exec, onBlock, ht, hon]
    obtain ⟨hn, _, _, _, hl⟩ := hg.2.1 0 hlen
    have hcall : tr.AcceptAt y r B := by
      refine ⟨by simpa using hn, ?_⟩
      simpa [exec, onBlock, ht, hon] using hl
    have hbound := (deliverSeq_cover htail).1
    exact ⟨hcall, by omega⟩

/-- Decoding a forwarding envelope identifies its canonical child using the supplied
digests and bounds the child's slot by the acceptance stamp. -/
theorem decodeForward_child {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) :
    decodeBlock sp hs (blockObj sp B) = some B ∧ sp.toParams.slotTime B.slot ≤ t := by
  unfold decodeForward at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, hc, h⟩ := h
    split at h
    · rename_i hp
      cases h
      exact ⟨by simpa only [hp.1] using hc, hp.2.2.2⟩
    · simp at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, hc, ⟨⟨y, pt, pp, A⟩, _, h⟩⟩ := h
    split at h
    · rename_i hp
      cases h
      exact ⟨by simpa only [hp.1] using hc, hp.2.2.2.2.2.2.2⟩
    · simp at h
  · simp at h

/-- Parsing a forwarding envelope authenticates its outer signer, independently of
whether its contained block was accepted by any receiver. -/
theorem decodeForward_signer {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) : o.signer? = some x := by
  rw [forwardObj_of_decodeForward hs o x t p B h]
  rfl

/-- The parser's recursive parent is authenticated by the same source, precedes the
child's slot and stamp, and names its exact parent root; the leaf names genesis. -/
theorem decodeForward_parent_cases {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) :
    (p = none ∧ B.parent = some sp.genesisRoot) ∨
      ∃ parent pt pp A, p = some parent ∧
        decodeForward sp hs parent = some (x, pt, pp, A) ∧
        B.parent = some A.root ∧ A.root ≠ sp.genesisRoot ∧ A.slot < B.slot ∧ pt ≤ t := by
  unfold decodeForward at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, h⟩ := h
    split at h
    · rename_i hp
      cases h
      exact Or.inl ⟨rfl, hp.2.1⟩
    · simp at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, ⟨⟨y, pt, pp, A⟩, hd, h⟩⟩ := h
    split at h
    · rename_i hp
      cases h
      exact Or.inr ⟨_, pt, pp, A, rfl, hp.2.1 ▸ hd,
        hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩
    · simp at h
  · simp at h

/-- Parent-first receipt traversal admits a source-accepted wrapper chain whenever
the final observation's receiver tip is below its child. Source provenance is kept
for every nested wrapper, not inferred from a possibly refused receiver call. -/
theorem forward_receipt_held {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {hs : List (Header Info × Nat)} {u : Time} {j : Nat} {B : Blk sp}
    (hFB : Anc (tr.HonestBlocks H) (tr.state y j).fg.F B) :
    ∀ (A : Blk sp) (o : Wire sp.n) (t : Time) (p : Option (Wire sp.n)) (r e : Nat),
      decodeForward sp hs o = some (x, t, p, A) →
      DeliverSeq proposer tr dg hs y u o.parts r e → e ≤ j → t ≤ u →
      Anc (tr.HonestBlocks H) A B →
      (∀ q tq pq C, Model.Obj.Contains o q →
        decodeForward sp hs q = some (x, tq, pq, C) → ∃ k, tr.AcceptAt x k C) →
      A ∈ (tr.state y e).fg.tree := by
  intro A
  induction hslot : A.slot using Nat.strong_induction_on generalizing A with
  | h n ih =>
    intro o t p r e hd hseq hej htu hAB hsource
    obtain ⟨k, ha⟩ := hsource o t p A (Model.Obj.Contains.refl _) hd
    have hre := (deliverSeq_cover hseq).1
    have child (m : Nat) (P : Blk sp) (hPe : P ∈ (tr.state y m).fg.tree)
        (hp : A.parent = some P.root)
        (hchild : DeliverSeq proposer tr dg hs y u (blockObj sp A).parts m e) :
        A ∈ (tr.state y e).fg.tree := by
      have hme := (deliverSeq_cover hchild).1
      rcases receipt_held_or_transfer hrun hnc hx hy (hme.trans hej) ha hAB hFB hp hPe with
        hheld | hon
      · exact Compose.tree_mono hrun.toLocalRun hy hme hheld
      · have htime := (decodeForward_child hd).2.trans htu
        have hslot' : A.slot ≤ sp.toParams.slotOf u := by
          apply Nat.le_findGreatest _ htime
          have hcast := (le_slotTime sp.toParams A.slot).trans htime
          exact (Int.le_toNat (le_trans (Int.natCast_nonneg _) hcast)).2 hcast
        rw [Model.Obj.parts_eq] at hchild
        obtain ⟨hacc, hlt⟩ := deliverSeq_block_accepts (decodeForward_child hd).1 hchild
          (not_lt.mpr hslot') hon
        exact Compose.tree_mono hrun.toLocalRun hy (Nat.succ_le_of_lt hlt)
          (accepted_mem_succ hrun hy hacc)
    rcases decodeForward_parent_cases hd with ⟨hp, hgen⟩ |
      ⟨parent, pt, pp, P, hp, hdec, hpar, _, hlt, hpt⟩
    · subst p
      have ho := forwardObj_of_decodeForward hs o x t none A hd
      rw [ho] at hseq
      apply child r (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)
      · exact (Store.accepted_tree sp.toParams _ _ _
          (Compose.fg_reachable hrun.toLocalRun hy r)).2.2.1
      · exact hgen
      · exact deliverSeq_forward_genesis hseq
    · subst p
      have ho := forwardObj_of_decodeForward hs o x t (some parent) A hd
      have hc : Model.Obj.Contains o parent := by
        rw [ho]
        exact Model.Obj.Contains.step (by simp [forwardObj, Model.Obj.carried])
          (Model.Obj.Contains.refl _)
      obtain ⟨kp, hpa⟩ := hsource parent pt pp P hc hdec
      have hPu : P ∈ tr.HonestBlocks H := ⟨x, hx, kp + 1, accepted_mem_succ hrun hx hpa⟩
      have hAu : A ∈ tr.HonestBlocks H := ⟨x, hx, k + 1, accepted_mem_succ hrun hx ha⟩
      have hPB : Anc (tr.HonestBlocks H) P B :=
        (Relation.ReflTransGen.single ⟨hPu, hAu, hpar⟩).trans hAB
      rw [ho] at hseq
      obtain ⟨m, hparent, hchild⟩ := deliverSeq_forward_parent hseq
      have hme := (deliverSeq_cover hchild).1
      have hheld := ih P.slot (by omega) P rfl parent pt pp r m hdec hparent
        (hme.trans hej) (hpt.trans htu) hPB
        (fun q tq pq C hq hqdec => hsource q tq pq C (hc.trans hq) hqdec)
      exact child m P hheld hpar hchild

/-- Decoding the same canonical block under two digest tables agrees when they agree
on that block's header; this is the root-sensitive replacement for wire injectivity. -/
theorem decodeBlock_transport {hs hs' : List (Header Info × Nat)} {o : Wire sp.n}
    {B : Blk sp} (hd : decodeBlock sp hs o = some B)
    (hr : rootOf hs' (headerOf sp B) = rootOf hs (headerOf sp B)) :
    decodeBlock sp hs' o = some B := by
  obtain rfl := eq_blockObj_of_decodeBlock hd
  unfold decodeBlock at hd ⊢
  simp only [blockObj] at hd ⊢
  rw [hr]
  exact hd

private theorem decodeForward_time_nonneg {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) : 0 ≤ t := by
  unfold decodeForward at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, h⟩ := h
    split at h
    · rename_i hp
      cases h
      exact hp.2.2.1
    · simp at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, ⟨⟨y, pt, pp, A⟩, _, h⟩⟩ := h
    split at h
    · rename_i hp
      cases h
      exact hp.2.2.2.2.2.2.1
    · simp at h
  · simp at h

/-- Forwarding decode is unchanged when both digest tables agree on every
canonical child carried by the envelope, including its recursive parent chain. -/
theorem decodeForward_transport {hs hs' : List (Header Info × Nat)} :
    ∀ (B : Blk sp) (o : Wire sp.n) (x : Fin sp.n) (t : Time) (p : Option (Wire sp.n)),
      decodeForward sp hs o = some (x, t, p, B) →
      (∀ C : Blk sp, Model.Obj.Contains o (blockObj sp C) →
        rootOf hs' (headerOf sp C) = rootOf hs (headerOf sp C)) →
      decodeForward sp hs' o = some (x, t, p, B) := by
  intro B
  induction hslot : B.slot using Nat.strong_induction_on generalizing B with
  | h n ih =>
    intro o x t p hd hr
    have ho := forwardObj_of_decodeForward hs o x t p B hd
    have hc : Model.Obj.Contains o (blockObj sp B) := by
      rw [ho]
      exact Model.Obj.Contains.step (List.mem_append_right _ (List.mem_singleton_self _))
        (Model.Obj.Contains.refl _)
    have hb := decodeBlock_transport (decodeForward_child hd).1 (hr B hc)
    have ht := decodeForward_time_nonneg hd
    have htime := (decodeForward_child hd).2
    rcases decodeForward_parent_cases hd with ⟨hp, hg⟩ |
      ⟨parent, pt, pp, A, hp, hpa, hpar, hng, hlt, hpt⟩
    · subst p
      rw [ho]
      exact decodeForward_genesis hs' x t B hb hg ht htime
    · subst p
      have hcp : Model.Obj.Contains o parent := by
        rw [ho]
        exact Model.Obj.Contains.step (by simp [forwardObj, Model.Obj.carried])
          (Model.Obj.Contains.refl _)
      have hpa' := ih A.slot (by omega) A rfl parent x pt pp hpa
        (fun C hC => hr C (hcp.trans hC))
      rw [ho]
      exact decodeForward_parent hs' x t pt B A parent pp hb hpa' hpar hng hlt hpt ht htime

/-- A durable-map update retains an old wrapper or records this exact acceptance.
This statement deliberately retains the accepted block, including its root; equality of
wire encodings alone does not recover that root. -/
theorem queueAccepted_wrapper_origin (st : State sp ro) (B : Blk sp)
    {root : Nat} {o : Wire sp.n}
    (h : (queueAccepted st B).wrappers root = some o) :
    st.wrappers root = some o ∨
      ∃ p, root = B.root ∧ o = forwardObj sp st.self st.now p B := by
  unfold queueAccepted at h
  split at h
  · exact Or.inl h
  · rename_i r hr
    generalize hp : (if r = sp.genesisRoot then some none else
      (st.wrappers r).map some) = parent at h
    cases parent with
    | none => exact Or.inl h
    | some p =>
      change Function.update st.wrappers B.root
        (some (forwardObj sp st.self st.now p B)) root = some o at h
      simp only [Function.update_apply] at h
      split_ifs at h with hr
      · exact Or.inr ⟨p, hr, (Option.some.inj h).symm⟩
      · exact Or.inl h

/-- Queueing a successful cut preserves the acceptance clock and local identity. -/
private theorem queueAccepted_self_now (st : State sp ro) (B : Blk sp) :
    (queueAccepted st B).self = st.self ∧ (queueAccepted st B).now = st.now := by
  unfold queueAccepted
  split
  · exact ⟨rfl, rfl⟩
  · rename_i r hr
    generalize (if r = sp.genesisRoot then some none else
      (st.wrappers r).map some) = parent
    cases parent <;> exact ⟨rfl, rfl⟩

/-- Every new durable wrapper in a handler result names a successful acceptance cut of
that handler. The old-map alternative preserves history across unrelated handlers. -/
theorem apply_wrapper_origin (st : State sp ro)
    (result : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    {root : Nat} {o : Wire sp.n} (h : (apply st result).wrappers root = some o) :
    st.wrappers root = some o ∨ ∃ B p,
      .fg (.block B true) ∈ result.2 ∧ root = B.root ∧
      o = forwardObj sp st.self st.now p B := by
  have aux : ∀ (cs : List (Cut (goldilocksNode sp ro))) (st : State sp ro),
      (cs.foldl (fun s c => match c with
        | .fg (.block B true) => queueAccepted s B
        | _ => s) st).wrappers root = some o →
      st.wrappers root = some o ∨ ∃ B p,
        .fg (.block B true) ∈ cs ∧ root = B.root ∧
        o = forwardObj sp st.self st.now p B := by
    intro cs
    induction cs with
    | nil => intro st h; exact Or.inl h
    | cons c cs ih =>
      intro st h
      cases c with
      | ac c =>
        rcases ih st h with h | ⟨B, p, hm, hr, ho⟩
        · exact Or.inl h
        · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, hr, ho⟩
      | fg c =>
        cases c with
        | block B ok =>
          cases ok with
          | false =>
            rcases ih st h with h | ⟨B, p, hm, hr, ho⟩
            · exact Or.inl h
            · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, hr, ho⟩
          | true =>
            rcases ih (queueAccepted st B) h with h | ⟨C, p, hm, hr, ho⟩
            · rcases queueAccepted_wrapper_origin st B h with h | ⟨p, hr, ho⟩
              · exact Or.inl h
              · exact Or.inr ⟨B, p, List.mem_cons_self, hr, ho⟩
            · rw [(queueAccepted_self_now st B).1, (queueAccepted_self_now st B).2] at ho
              exact Or.inr ⟨C, p, List.mem_cons_of_mem _ hm, hr, ho⟩
        | _ =>
          rcases ih st h with h | ⟨B, p, hm, hr, ho⟩
          · exact Or.inl h
          · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, hr, ho⟩
  exact aux result.2 st h

/-- Fresh queue entries retain an indexed successful cut of the very handler that
created them, ready to be embedded into the event's cut prefix. -/
theorem apply_forward_origin_index (st : State sp ro)
    (result : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    (q : Time × List (Wire sp.n)) (hq : q ∈ (apply st result).forwards) :
    q ∈ st.forwards ∨ ∃ B, ∃ p : Option (Wire sp.n), ∃ j : Nat,
      result.2[j]? = some (.fg (.block B true)) ∧
      q = (st.now, p.toList ++ [blockObj sp B]) := by
  rcases apply_forward_origin st result q hq with h | ⟨B, p, hm, he⟩
  · exact Or.inl h
  · obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hm
    exact Or.inr ⟨B, p, j, by simpa only [List.getElem?_eq_getElem hj] using congrArg some heq, he⟩

/-- A single delivered object can create a wrapper only through its actual canonical
handler. This keeps the handler state needed to locate the cut in recursive processing. -/
theorem processOne_forward_origin (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (st : State sp ro) (o : Wire sp.n)
    (q : Time × List (Wire sp.n)) (hq : q ∈ (processOne hs st o).forwards) :
    q ∈ st.forwards ∨ ∃ e B, ∃ p : Option (Wire sp.n),
      canonEvent sp ro hs o = some e ∧
      .fg (.block B true) ∈ (exec proposer dg st.self st.node st.now e).2 ∧
      q = (st.now, p.toList ++ [blockObj sp B]) := by
  have hrelay : ∀ (s : State sp ro) (c : Prop) [Decidable c],
      (relayIf s c o).forwards = s.forwards := by
    intro s c _
    unfold relayIf
    split <;> rfl
  rcases canonEvent_cases (ro := ro) hs o with he | ⟨B, he⟩ | ⟨v, he⟩ | ⟨a, he⟩
  · exact Or.inl (by simpa only [processOne, he] using hq)
  all_goals
    simp only [processOne, he, hrelay] at hq
    rcases apply_forward_origin _ _ q hq with h | ⟨C, p, hm, hq⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, C, p, he, hm, hq⟩

/-- A successful canonical handler cut names the exact decoded input block. -/
private theorem accepted_canonEvent_block (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (st : State sp ro) (o : Wire sp.n)
    {e : Event (goldilocksNode sp ro)} {B : Blk sp}
    (he : canonEvent sp ro hs o = some e)
    (hb : .fg (.block B true) ∈ (exec proposer dg st.self st.node st.now e).2) :
    decodeBlock sp hs o = some B := by
  rcases canonEvent_cases (ro := ro) hs o with h | ⟨C, h⟩ | ⟨v, h⟩ | ⟨a, h⟩
  · rw [h] at he
    cases he
  · have heq := Option.some.inj (he.symm.trans h)
    subst e
    simp only [exec, onBlock] at hb
    split at hb
    · exact False.elim (List.not_mem_nil hb)
    · split at hb
      · simp at hb
      · simp only [List.mem_cons, List.not_mem_nil, Cut.fg.injEq,
          FGLabel.block.injEq, and_true, acCall, reduceCtorEq, or_false] at hb
        subst C
        exact decodeBlock_of_canonEvent h
  · have heq := Option.some.inj (he.symm.trans h)
    subst e
    simp [exec, onMessage, acCall] at hb
  · have heq := Option.some.inj (he.symm.trans h)
    subst e
    simp [exec, onAttestation] at hb

/-- A fresh queue entry from recursive receipt has a successful record in that exact
delivery traversal, including its node and clock. -/
theorem foldl_processOne_forward_origin (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (i : Nat) (q : Time × List (Wire sp.n)) :
    ∀ (os : List (Wire sp.n)) (st : State sp ro) (sub : Nat),
    q ∈ (os.foldl (processOne hs) st).forwards →
    q ∈ st.forwards ∨ ∃ B, ∃ p : Option (Wire sp.n), ∃ r,
      r ∈ deliverRecs proposer dg hs st.self st.now i os st.node sub ∧
      r.label = .fg (.block B true) ∧ r.node = st.self ∧ r.time = st.now ∧
      q = (st.now, p.toList ++ [blockObj sp B]) ∧
      decodeBlock sp hs (blockObj sp B) = some B ∧ blockObj sp B ∈ os := by
  intro os
  induction os with
  | nil => intro st sub h; exact Or.inl h
  | cons o os ih =>
    intro st sub h
    rcases ih (processOne hs st o) (sub + 1) h with h | ⟨B, p, r, hm, hl, hn, ht, hq, hd, ho⟩
    · rcases processOne_forward_origin proposer dg hs st o q h with h | ⟨e, B, p, he, hm, hq⟩
      · exact Or.inl h
      · obtain ⟨j, hj, hlabel⟩ := List.getElem_of_mem hm
        have hj' : j <
            (groupRecs proposer dg st.self st.node st.now (Nat.pair i sub) e).length := by
          rwa [length_groupRecs]
        obtain ⟨hn, ht, _, _, hl⟩ :=
          getElem_groupRecs proposer dg st.self st.node st.now (Nat.pair i sub) e j hj'
        have hd := accepted_canonEvent_block proposer dg hs st o he hm
        have hd' : decodeBlock sp hs (blockObj sp B) = some B := by
          rwa [eq_blockObj_of_decodeBlock hd] at hd
        refine Or.inr ⟨B, p, _, ?_, hl.trans hlabel, hn, ht, hq, hd', ?_⟩
        · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
          exact List.mem_append_left _ (List.getElem_mem hj')
        · rw [eq_blockObj_of_decodeBlock hd]
          exact List.mem_cons_self
    · simp only [processOne_self, processOne_now] at hm hn ht hq
      rw [processOne_node proposer dg] at hm
      refine Or.inr ⟨B, p, r, ?_, hl, hn, ht, hq, hd, List.mem_cons_of_mem _ ho⟩
      cases he : canonEvent sp ro hs o with
      | none =>
        rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he]
        simpa only [he] using hm
      | some e =>
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
        exact List.mem_append_right _ (by simpa only [he] using hm)

/-- A canonical, nonfuture block in a recursive receipt produces an actual block-call
record even when the store refuses it. -/
theorem deliverRecs_block_call (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (B : Blk sp) (hslot : B.slot ≤ sp.toParams.slotOf t) :
    ∀ (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat),
    (∃ o ∈ os, canonEvent sp ro hs o = some (.block B)) →
    ∃ r ∈ deliverRecs proposer dg hs self t i os st sub,
      ∃ accepted, r.label = .fg (.block B accepted) := by
  intro os
  induction os with
  | nil => intro st sub h; simp at h
  | cons o os ih =>
    intro st sub ⟨x, hx, he⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
      have hcuts : ∃ accepted cs,
          (exec proposer dg self st t (.block B)).2 = .fg (.block B accepted) :: cs := by
        simp only [exec, onBlock, show ¬ sp.toParams.slotOf t < B.slot from not_lt.mpr hslot,
          ↓reduceIte]
        split <;> exact ⟨_, _, rfl⟩
      obtain ⟨accepted, cs, hcuts⟩ := hcuts
      have hlen : 0 < (groupRecs proposer dg self st t (Nat.pair i sub) (.block B)).length := by
        rw [length_groupRecs, hcuts]
        exact Nat.zero_lt_succ _
      refine ⟨_, List.mem_append_left _ (List.getElem_mem hlen), accepted, ?_⟩
      rw [(getElem_groupRecs proposer dg self st t (Nat.pair i sub) (.block B) 0 hlen).2.2.2.2]
      simp only [List.getElem_of_eq hcuts, List.getElem_cons_zero]
    · cases ho : canonEvent sp ro hs o with
      | none =>
        rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ ho]
        exact ih st (sub + 1) ⟨x, hx, he⟩
      | some e =>
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ ho]
        obtain ⟨r, hr, accepted, ha⟩ := ih (exec proposer dg self st t e).1
          (sub + 1) ⟨x, hx, he⟩
        exact ⟨r, List.mem_append_right _ hr, accepted, ha⟩

private def QueueStamped (t : Time) (st : State sp ro) : Prop :=
  st.now = t ∧ ∀ q ∈ st.forwards, q.1 = t

private theorem nodeTick_forwards (st : State sp ro) :
    (nodeTick st).forwards = st.forwards := by
  unfold nodeTick
  split
  · simp [apply, acCall]
  · rfl

private theorem stamped_apply (t : Time) (st : State sp ro) r
    (h : QueueStamped t st) : QueueStamped t (apply st r) := by
  refine ⟨h.1, ?_⟩
  intro q hq
  rcases apply_forward_origin st r q hq with hq | ⟨B, p, _, rfl⟩
  · exact h.2 q hq
  · exact h.1

private theorem stamped_recordOwn (t : Time) (st : State sp ro) o hs
    (h : QueueStamped t st) : QueueStamped t (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact h
  · split
    · exact stamped_apply t st _ h
    · exact h
  · exact h

private theorem stamped_propose (t : Time) (st : State sp ro) s
    (h : QueueStamped t st) : QueueStamped t (propose st s).1 := by
  unfold propose
  dsimp only
  split <;> exact h

private theorem stamped_nodeTick (t : Time) (st : State sp ro)
    (h : QueueStamped t st) : QueueStamped t (nodeTick st) := by
  unfold nodeTick
  split
  · exact stamped_apply t st _ h
  · exact h

private theorem stamped_poll (t : Time) (st : State sp ro) u
    (h : QueueStamped t st) : QueueStamped t (poll st u).1 := by
  refine ⟨(poll_now st u).trans h.1, ?_⟩
  intro q hq
  rw [poll_forwards] at hq
  exact False.elim (List.not_mem_nil hq)

private theorem stamped_process (t : Time) (st : State sp ro) o hs
    (h : QueueStamped t st) : QueueStamped t (process st o hs) := by
  refine ⟨(process_now st o hs).trans h.1, ?_⟩
  intro q hq
  rcases foldl_processOne_forward_origin (fun _ => st.self)
      (fun _ _ _ _ _ => 0) hs 0 q _ st 0 hq with
    hq | ⟨B, p, r, _, _, _, _, he, _⟩
  · exact h.2 q hq
  · rw [he]
    exact h.1

section Trace

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

private theorem atProposal_forwards_nil (hv : rho.ExecutionValid) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time) :
    (shapeOf S hn (atProposal S rho v nd t)).forwards = [] := by
  rw [atProposal_shape S rho hn v nd t (poll_selected S rho hv v), nodeTick_forwards,
    poll_forwards]

omit [DecidableEq V] in
/-- A proposal duty creates forwarding entries only for successful cuts of the
corresponding proposal step. Rejected release guards create no new entries. -/
theorem proposal_duty_forward_origin (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (s : Slot) (hs : 0 < s)
    (hsel : rho.sel (.proposer s) = {runProposer S rho hn s})
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hslot : (S.params (Model.pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now = s)
    (hst : (shapeOf S hn nd).now = (S.params (Model.pubOf E) hn).toParams.slotTime s)
    (q : Time × List (Wire (Fintype.card V)))
    (hq : q ∈ (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1).forwards) :
    q ∈ (shapeOf S hn nd).forwards ∨ ∃ B, ∃ p : Option (Wire (Fintype.card V)),
      .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (shapeOf S hn nd).node (shapeOf S hn nd).now
        (encodeTxs nd.st.2) .proposal).2 ∧
      q = ((shapeOf S hn nd).now, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) := by
  have hact2 := act_propose_snd S hn nd s hs
  have hact1 := shapeOf_act_propose S hn nd.st s hs
  unfold Model.Run.dutyStep at hq
  split at hq
  · rename_i hselected
    change rho.ownKey v ∈ rho.sel (.proposer s) at hselected
    have hp : Proposes (P := (S.params (Model.pubOf E) hn).toParams)
        (runProposer S rho hn) (rho.ownKey v) (shapeOf S hn nd).now := by
      rw [hst, proposes_iff S hn _ _ s hs]
      exact (Finset.mem_singleton.mp (hsel ▸ hselected)).symm
    generalize (Model.protoOf (compiled (family S)) E).act nd.st (.propose s hs) = a
      at hact1 hact2 hq
    dsimp only at hq
    simp only [propose] at hact1 hact2
    simp only [Node.tickStep, hp, ite_true]
    rcases hr : (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).2.2 with _ | ⟨d, p⟩
    · simp only [hr] at hact1 hact2
      erw [hact2] at hq
      simp only [Option.map_none, Option.toList_none, Model.Run.signedCandidate] at hq
      split at hq
      all_goals
        change q ∈ (a.1.1 hn).forwards at hq
        rw [hact1] at hq
        exact Or.inl hq
    · simp only [hr] at hact1 hact2
      erw [hact2] at hq
      have hrole : (Model.protoOf (compiled (family S)) E).role (.propose s hs) =
          .proposer s := rfl
      simp only [Option.map, Option.toList_some, Model.Run.signedCandidate, hrole,
        hselected, ↓reduceIte] at hq
      erw [List.map_cons, List.map_nil] at hq
      unfold Model.releaseAll at hq
      split at hq
      · change q ∈ (recordOwn (a.1.1 hn) _ _).forwards at hq
        rw [hact1] at hq
        simp only [recordOwn, decodeInfo_encodeInfo] at hq
        erw [rootOf_digests_item] at hq
        dsimp only at hq
        have hb := blockOf_eq_mkBlock S rho hn (rho.ownKey v)
          (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).1.fg
          (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p s hslot
        erw [hb] at hq
        rcases apply_forward_origin (sp := S.params (Model.pubOf E) hn) (ro := S.ro _)
            _ _ q hq with hq | ⟨B, parent, hB, hq⟩
        · exact Or.inl hq
        · refine Or.inr ⟨B, parent, ?_, hq⟩
          simp only [Node.proposeBlock]
          exact List.mem_cons_of_mem _ (by simpa only [hself] using hB)
      · exact Or.inl (by change q ∈ (a.1.1 hn).forwards at hq; simpa [hact1] using hq)
  · exact Or.inl hq

omit [DecidableEq V] in
/-- A decoded envelope's child is decoded identically inside any enclosing receipt.
Both roots are obtained from the engine hash of the child's header. -/
theorem decoded_forward_child_in_receipt
    {o receipt : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hc : Model.Obj.Contains receipt o)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    blockObj (S.params (Model.pubOf E) hn) B ∈ receipt.parts ∧
      decodeBlock (S.params (Model.pubOf E) hn) (Model.digests rho.hash receipt)
        (blockObj (S.params (Model.pubOf E) hn) B) = some B := by
  have hchild : Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) B) := by
    rw [forwardObj_of_decodeForward _ _ _ _ _ _ hd]
    apply Model.Obj.Contains.step (c := blockObj _ B)
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact Model.Obj.Contains.refl _
  have hreceipt := hc.trans hchild
  refine ⟨hreceipt, decodeBlock_transport (decodeForward_child hd).1 ?_⟩
  rw [rootOf_digests_of_mem S rho receipt _
    (List.mem_filterMap.mpr ⟨blockObj _ B, hreceipt, rfl⟩)]
  rw [rootOf_digests_of_mem S rho o _
    (List.mem_filterMap.mpr ⟨blockObj _ B, hchild, rfl⟩)]

omit [DecidableEq V] in
/-- A decodable forwarding candidate of a poll comes from its pre-duty forwarding
queue, not the ordinary outbox emission (which carries no child). -/
theorem poll_candidate_forward_queue (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (u : Nat)
    {o : Wire (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ rho.signedCandidate v (.poll u)
      ((Model.protoOf (compiled (family S)) E).act nd.st (.poll u)).2)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∈
      (shapeOf S hn nd).forwards := by
  obtain ⟨m, cs, hm, _, rfl⟩ := rho.mem_signedCandidate.mp ho
  rw [act_poll_snd S hn, (poll_outbox _ _).2] at hm
  rcases List.mem_append.mp hm with hm | hm
  swap
  · obtain ⟨⟨stamp, vote⟩, _, he⟩ := List.mem_map.mp hm
    cases he
    have heq := forwardObj_of_decodeForward _ _ _ _ _ _ hd
    have hmsg := congrArg Model.Obj.msg heq
    cases hmsg
  rcases List.mem_append.mp hm with hm | hm
  · cases hh : (pollPre (shapeOf S hn nd)).outbox.head? with
    | none =>
      simp only [hh, Option.map_none, Option.toList_none] at hm
      exact False.elim (List.not_mem_nil hm)
    | some b =>
      simp only [hh, Option.map_some, Option.toList_some] at hm
      have he := List.mem_singleton.mp hm
      cases he
      have heq := forwardObj_of_decodeForward _ _ _ _ _ _ hd
      have hc := congrArg Model.Obj.carried heq
      change [] = p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B] at hc
      cases p <;> simp at hc
  · obtain ⟨⟨stamp, children⟩, hq, he⟩ := List.mem_map.mp hm
    cases he
    have heq := forwardObj_of_decodeForward (Model.digests rho.hash
      (.mk (.signed (rho.ownKey v) .poll) (.data (.forward stamp)) children))
      _ _ _ _ _ hd
    simp [forwardObj] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact hq

omit [DecidableEq V] in
/-- A released poll envelope retains its pre-duty queue witness. -/
private theorem poll_release_forward_queue (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (u : Nat)
    {o : Wire (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ (rho.dutyStep v nd (.poll u)).2)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∈
      (shapeOf S hn nd).forwards := by
  unfold Model.Run.dutyStep at ho
  split at ho
  · exact poll_candidate_forward_queue S rho hn v nd u
      (Model.releaseAll_subset _ _ _ _ o ho) hd
  · exact False.elim (List.not_mem_nil ho)

/-- An honestly signed forwarding envelope in seen closure has an actual prior release
by that signer. This is authentication provenance, not yet an acceptance witness. -/
theorem decoded_forward_seen_released (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen)
    (hx : rho.key x ∈ rho.honest)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    ∃ j < i, ∃ u, rho.SendsAt (rho.key x) j u ∧ o ∈ rho.releasesAt j := by
  apply rho.signed_seen_released hv ho hx
  change o.signer?.map rho.key = some (rho.key x)
  rw [decodeForward_signer hd]
  rfl

omit [DecidableEq V] in
private theorem duty_forward_stamp (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (d : (Model.protoOf (compiled (family S)) E).Duty) (u : Time)
    (hs : QueueStamped u (shapeOf S hn nd))
    {o : Wire (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ rho.signedCandidate v d ((Model.protoOf (compiled (family S)) E).act nd.st d).2)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) : t = u := by
  cases d with
  | poll n => exact hs.2 _ (poll_candidate_forward_queue S rho hn v nd n ho hd)
  | act s k => exact k.elim
  | propose s hpos =>
    obtain ⟨m, cs, _, _, rfl⟩ := rho.mem_signedCandidate.mp ho
    have he := forwardObj_of_decodeForward _ _ _ _ _ _ hd
    have ha := congrArg Model.Obj.auth he
    change Model.Auth.signed (rho.ownKey v) (ShapeRole.proposer (Kind := Empty) s) =
      .signed (rho.ownKey v) ShapeRole.poll at ha
    cases ha
  | pollPropose n =>
    have hempty : ((Model.protoOf (compiled (family S)) E).act nd.st (.pollPropose n)).2 = [] := by
      simp only [Model.protoOf, compiled, compile, family, dite_eq_left hn, goldilocksShape]
      rfl
    obtain ⟨m, cs, hm, _, _⟩ := rho.mem_signedCandidate.mp ho
    rw [hempty] at hm
    exact False.elim (List.not_mem_nil hm)

omit [DecidableEq V] in
private theorem gossip_not_forward
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (u : Time)
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.gossipCandidates (Model.protoOf (compiled (family S)) E) nd.st u)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) : False := by
  obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp ho
  have hsign := decodeForward_signer hd
  change none = some x at hsign
  cases hsign

private theorem dutyBatches_forward_stamp (v : V) (u : Time) :
    ∀ (ds : List (Model.protoOf (compiled (family S)) E).Duty)
      (nd : Model.Node (Model.protoOf (compiled (family S)) E)),
    QueueStamped u (shapeOf S hn nd) →
    ∀ b ∈ dutyBatches rho v nd ds, ∀ o ∈ b.candidates,
    ∀ t p B, decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B) → t = u := by
  intro ds
  induction ds with
  | nil => intro nd hs b hb; rw [dutyBatches_nil] at hb; exact False.elim (List.not_mem_nil hb)
  | cons d ds ih =>
    intro nd hs b hb o ho t p B hd
    rw [dutyBatches_cons] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · split at ho
      · exact duty_forward_stamp S rho hn v nd d u hs ho hd
      · exact False.elim (List.not_mem_nil ho)
    · exact ih _ (dutyStep_pres S rho hn (QueueStamped u)
        (stamped_recordOwn u) (stamped_propose u) (stamped_nodeTick u) (stamped_poll u)
        v nd d hs) b hb o ho t p B hd

private theorem runDuties_candidate_batch (v : V) :
    ∀ ds (nd : Model.Node (Model.protoOf (compiled (family S)) E)) o,
    o ∈ (rho.runDuties v nd ds).2 →
    ∃ b ∈ dutyBatches rho v nd ds, o ∈ b.candidates := by
  intro ds
  induction ds with
  | nil => intro nd o ho; rw [rho.runDuties_nil] at ho; exact False.elim (List.not_mem_nil ho)
  | cons d ds ih =>
    intro nd o ho
    rw [rho.runDuties_cons] at ho
    rcases List.mem_append.mp ho with ho | ho
    · rw [dutyBatches_cons]
      unfold Model.Run.dutyStep at ho
      split at ho
      · rename_i hsel
        refine ⟨_, List.mem_cons_self, ?_⟩
        simp only [hsel, ↓reduceIte]
        exact Model.releaseAll_subset _ _ _ _ o ho
      · exact False.elim (List.not_mem_nil ho)
    · obtain ⟨b, hb, ho⟩ := ih _ o ho
      rw [dutyBatches_cons]
      exact ⟨b, List.mem_cons_of_mem _ hb, ho⟩

/-- Every engine release belongs to a concrete event batch. This inverse needs no
acceptance or provenance premise. -/
theorem released_candidate_batch {i : Nat} {v : V} {u : Time}
    (he : rho.SendsAt v i u) {o : Wire (Fintype.card V)} (ho : o ∈ rho.releasesAt i) :
    ∃ b ∈ eventBatches rho i, o ∈ b.candidates := by
  rcases he with he | ⟨receipt, he⟩
  · rw [eventBatches_eq, he]
    simp only [Model.Run.releasesAt, he, Model.Run.tick] at ho
    split at ho
    · rename_i hw
      simp only [hw, ↓reduceIte]
      rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨b, hb, ho⟩ := runDuties_candidate_batch S rho v _ _ o ho
        exact ⟨b, List.mem_append_left _ hb, ho⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self,
          Model.releaseAll_subset (P := Model.protoOf (compiled (family S)) E) _ _ _ _ o ho⟩
    · exact False.elim (List.not_mem_nil ho)
  · rw [eventBatches_eq, he]
    simp only [Model.Run.releasesAt, he, Model.Run.deliver] at ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨b, hb, ho⟩ := runDuties_candidate_batch S rho v _ _ o ho
      exact ⟨b, List.mem_append_left _ hb, ho⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self,
        Model.releaseAll_subset (P := Model.protoOf (compiled (family S)) E) _ _ _ _ o ho⟩

/-- A forwarding candidate in an actual event batch has that event's timestamp. -/
theorem eventBatches_forward_stamp (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {u : Time} (he : rho.SendsAt v i u)
    (b : ReleaseBatch (Model.protoOf (compiled (family S)) E))
    (hb : b ∈ eventBatches rho i) {o : Wire (Fintype.card V)} (ho : o ∈ b.candidates)
    {t : Time} {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) : t = u := by
  rcases he with he | ⟨receipt, he⟩
  · rw [eventBatches_eq, he] at hb
    simp only at hb
    split at hb
    · rcases List.mem_append.mp hb with hb | hb
      · apply dutyBatches_forward_stamp S rho hn v u _ _ ?_ b hb o ho t p B hd
        change QueueStamped u { stateAt S rho hn v i with now := u }
        refine ⟨rfl, ?_⟩
        intro q hq
        change q ∈ (stateAt S rho hn v i).forwards at hq
        rw [forwards_empty S rho hn hv v i] at hq
        exact False.elim (List.not_mem_nil hq)
      · have heq := List.mem_singleton.mp hb
        subst b
        exact False.elim (gossip_not_forward S rho hn _ u ho hd)
    · exact False.elim (List.not_mem_nil hb)
  · rw [eventBatches_eq, he] at hb
    rcases List.mem_append.mp hb with hb | hb
    · apply dutyBatches_forward_stamp S rho hn v u _ _ ?_ b hb o ho t p B hd
      change QueueStamped u
        (process (stateAt S rho hn v i) receipt (Model.digests rho.hash receipt))
      apply stamped_process
      refine ⟨(now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he), ?_⟩
      intro q hq
      rw [forwards_empty S rho hn hv v i] at hq
      exact False.elim (List.not_mem_nil hq)
    · have heq := List.mem_singleton.mp hb
      subst b
      exact False.elim (gossip_not_forward S rho hn _ u ho hd)

/-- An actually released forwarding envelope has the sending event's timestamp. -/
theorem released_forward_stamp (hv : rho.ExecutionValid) {i : Nat} {v : V} {u : Time}
    (he : rho.SendsAt v i u) {o : Wire (Fintype.card V)} (ho : o ∈ rho.releasesAt i)
    {t : Time} {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) : t = u := by
  obtain ⟨b, hb, ho⟩ := released_candidate_batch S rho he ho
  exact eventBatches_forward_stamp S rho hn hv he b hb ho hd

/-- Every actual forwarding publication bears its own event's time. -/
theorem publication_forward_stamp (hv : rho.ExecutionValid)
    (r : Publication (Model.protoOf (compiled (family S)) E))
    (hr : (publisherExecution S rho).actual r) {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash r.object) r.object =
      some (r.origin, t, p, B)) : t = (publisherExecution S rho).eventTime r.event := by
  apply released_forward_stamp S rho hn hv ((publisherExecution S rho).actual_event r hr)
    ((publisherExecution S rho).actual_release r hr) (p := p) (B := B)
  have hk : rho.ownKey (rho.key r.origin) = r.origin := rho.key.symm_apply_apply _
  rw [hk]
  exact hd

/-- An indexed successful canonical cut supplies acceptance at its actual recorded time.
In particular this bridge never turns a refused block call into acceptance. -/
theorem acceptAt_of_allCuts {k : Nat} {r : CutRec (S.params (Model.pubOf E) hn) (S.ro _)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hr : (allCuts S rho hn)[k]? = some r) (hb : r.label = .fg (.block B true)) :
    (simTrace S rho hn).AcceptAt r.node k B ∧ (simTrace S rho hn).time k = r.time := by
  constructor
  · exact ⟨by simp [simTrace_node, hr], by simp [simTrace_label, hr, hb]⟩
  · simp [simTrace_time, hr]

/-- An acceptance in an actual event's record list gives the required strict event-prefix
bound; no search for a merely similar successful label is involved. -/
theorem acceptAt_of_eventCuts {i : Nat} (hi : i < rho.events.length)
    {r : CutRec (S.params (Model.pubOf E) hn) (S.ro _)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt r.node k B ∧
      (simTrace S rho hn).time k = r.time := by
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hr
  have hk : (allCuts S rho hn)[cutMap S rho hn i + j]? = some r := by
    rw [allCuts_getElem?_add S rho hn i j hi hj, List.getElem?_eq_getElem hj, he]
  refine ⟨cutMap S rho hn i + j, ?_, acceptAt_of_allCuts S rho hn hk hb⟩
  rw [cutMap_succ]
  omega

/-- The processing phase of an actual delivery queues only wrappers for acceptances in
that delivery, at its actual time. The event-boundary queue is empty, not a premise. -/
theorem delivery_forward_acceptance_decoded (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : Wire (Fintype.card V)} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (q : Time × List (Wire (Fintype.card V)))
    (hq : q ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).forwards) :
    ∃ B, ∃ p : Option (Wire (Fintype.card V)), ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t ∧
      q = (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∧
      decodeBlock (S.params (Model.pubOf E) hn) (Model.digests rho.hash o)
        (blockObj (S.params (Model.pubOf E) hn) B) = some B ∧
      Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) B) := by
  have ht : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he)
  rcases foldl_processOne_forward_origin (runProposer S rho hn) (digestOf S rho)
      (Model.digests rho.hash o) i q _ (stateAt S rho hn v i) 0 hq with
    h | ⟨B, p, r, hr, hb, hn', ht', hq, hd, ho⟩
  · rw [forwards_empty S rho hn hv v i] at h
    exact False.elim (List.not_mem_nil h)
  · simp only [stateAt_self, ht] at hr hn' ht' hq
    have hr' : r ∈ eventCuts S rho hn i := by
      rw [eventCuts_deliver S rho hn i v o t he]
      exact hr
    obtain ⟨k, hk, ha, htime⟩ := acceptAt_of_eventCuts S rho hn
      (List.getElem?_eq_some_iff.mp he).1 hr' hb
    exact ⟨B, p, k, hk, hn' ▸ ha, htime.trans ht', hq, hd,
      contains_of_mem_delivered ho⟩

/-- The queue-only projection of exact delivery acceptance provenance. -/
theorem delivery_forward_acceptance (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : Wire (Fintype.card V)} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (q : Time × List (Wire (Fintype.card V)))
    (hq : q ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).forwards) :
    ∃ B, ∃ p : Option (Wire (Fintype.card V)), ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t ∧
      q = (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) := by
  obtain ⟨B, p, k, hk, ha, ht, hq, _⟩ :=
    delivery_forward_acceptance_decoded S rho hn hv he q hq
  exact ⟨B, p, k, hk, ha, ht, hq⟩

/-- Digest-backed decoding identifies the exact accepted block behind a delivery queue
entry. Wire equality supplies its header, not its root. -/
theorem delivery_decoded_forward_acceptance (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {receipt o : Wire (Fintype.card V)} {u t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hq : (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∈
      (process (stateAt S rho hn v i) receipt (Model.digests rho.hash receipt)).forwards)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t := by
  obtain ⟨C, p', k, hk, ha, ht, heq, hc, hcontains⟩ :=
    delivery_forward_acceptance_decoded S rho hn hv he _ hq
  have htime : t = u := congrArg Prod.fst heq
  have hwire : blockObj (S.params (Model.pubOf E) hn) B = blockObj _ C := by
    have hlast := congrArg List.getLast? (congrArg Prod.snd heq)
    cases p <;> cases p' <;> simpa using hlast
  have hBC : B = C := by
    have hchild : Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) C) := by
      rw [← hwire, forwardObj_of_decodeForward _ _ _ _ _ _ hd]
      apply Model.Obj.Contains.step
        (List.mem_append_right _ (List.mem_singleton_self _)) (Model.Obj.Contains.refl _)
    have hroot (r : Wire (Fintype.card V))
        (h : Model.Obj.Contains r (blockObj (S.params (Model.pubOf E) hn) C)) :
        rootOf (Model.digests rho.hash r) (headerOf (S.params (Model.pubOf E) hn) C) =
          some (rho.hash (headerOf (S.params (Model.pubOf E) hn) C)) := by
      exact rootOf_digests_of_mem S rho r _ (List.mem_filterMap.mpr ⟨_, h, rfl⟩)
    have hc' := decodeBlock_transport hc ((hroot o hchild).trans (hroot receipt hcontains).symm)
    rw [← hwire, (decodeForward_child hd).1] at hc'
    exact Option.some.inj hc'
  subst C
  exact ⟨k, hk, ha, ht.trans htime.symm⟩

/-- A decoded forwarding object released by a delivery originates in an actual
acceptance in that delivery, with the same root and timestamp. -/
theorem delivery_released_forward_acceptance (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {receipt o : Wire (Fintype.card V)} {u t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (ho : o ∈ rho.releasesAt i)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t := by
  obtain ⟨b, hb, ho⟩ := released_candidate_batch S rho (Or.inr ⟨receipt, he⟩) ho
  rw [eventBatches_eq, he] at hb
  rcases List.mem_append.mp hb with hb | hb
  · have hu := (hv.in_horizon _ (List.mem_of_getElem? he)).1
    rw [deliverDuties_eq S u hu] at hb
    erw [dutyBatches_cons, dutyBatches_nil] at hb
    have hb' := List.mem_singleton.mp hb
    subst b
    split at ho
    · have hq := poll_candidate_forward_queue S rho hn v _ u.toNat ho hd
      exact delivery_decoded_forward_acceptance S rho hn hv he hq hd
    · exact False.elim (List.not_mem_nil ho)
  · have hb' := List.mem_singleton.mp hb
    subst b
    exact False.elim (gossip_not_forward S rho hn _ u ho hd)

/-- Receipt witnesses require only a block call, including a refused call. -/
theorem blockCallAt_of_allCuts {k : Nat}
    {r : CutRec (S.params (Model.pubOf E) hn) (S.ro _)}
    {B : Blk (S.params (Model.pubOf E) hn)} {accepted : Bool}
    (hr : (allCuts S rho hn)[k]? = some r)
    (hb : r.label = .fg (.block B accepted)) :
    (simTrace S rho hn).BlockCallAt r.node k B ∧
      (simTrace S rho hn).time k = r.time := by
  constructor
  · exact ⟨accepted, by simp [simTrace_node, hr], by simp [simTrace_label, hr, hb]⟩
  · simp [simTrace_time, hr]

/-- Once its authenticated stamp is no later than receipt, a forwarding envelope's
child has a real processing call in that receipt, whether accepted or refused. -/
theorem received_forward_blockCall {i : Nat} {v : V}
    {receipt o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t u : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt o)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) (htu : t ≤ u) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).BlockCallAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = u := by
  obtain ⟨hmem, hdecode⟩ := decoded_forward_child_in_receipt S rho hn hc hd
  have hs : (S.params (Model.pubOf E) hn).toParams.slotTime B.slot ≤ u :=
    (decodeForward_child hd).2.trans htu
  have hslot : B.slot ≤ (S.params (Model.pubOf E) hn).toParams.slotOf u := by
    apply Nat.le_findGreatest _ hs
    have hcast := (le_slotTime (S.params (Model.pubOf E) hn).toParams B.slot).trans hs
    exact (Int.le_toNat (le_trans (Int.natCast_nonneg _) hcast)).2 hcast
  obtain ⟨r, hr, accepted, hb⟩ := deliverRecs_block_call (runProposer S rho hn)
    (digestOf S rho) (Model.digests rho.hash receipt) (rho.ownKey v) u i B hslot
    (delivered _ receipt) (stateAt S rho hn v i).node 0
    ⟨blockObj _ B, hmem, by simp only [canonEvent, hdecode]⟩
  obtain ⟨hn', ht', _⟩ := mem_deliverRecs (sp := S.params (Model.pubOf E) hn)
    (ro := S.ro _) (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (Model.digests rho.hash receipt) u i hr
  have hr' : r ∈ eventCuts S rho hn i := by
    rw [eventCuts_deliver S rho hn i v receipt u he]
    exact hr
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hr'
  have hk : (allCuts S rho hn)[cutMap S rho hn i + j]? = some r := by
    rw [allCuts_getElem?_add S rho hn i j (List.getElem?_eq_some_iff.mp he).1 hj,
      List.getElem?_eq_getElem hj, heq]
  obtain ⟨hcall, htime⟩ := blockCallAt_of_allCuts S rho hn hk hb
  refine ⟨cutMap S rho hn i + j, ?_, hn' ▸ hcall, htime.trans ht'⟩
  rw [cutMap_succ]
  omega

/-- Authentication and event order bound an honest forwarding envelope's stamp by
its receipt time, even when the envelope is nested inside the delivered object. -/
theorem received_forward_stamp_le (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {receipt o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t u : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∈ rho.honest)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) : t ≤ u := by
  have hsign : rho.signerOf o = some (rho.key x) := by
    change o.signer?.map rho.key = some (rho.key x)
    rw [decodeForward_signer hd]
    rfl
  obtain ⟨j, s, hj, hs, ho⟩ := hv.unforgeable i v receipt u he o hc (rho.key x) hx hsign
  have hd' : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey (rho.key x), t, p, B) := by
    simpa only [Model.Run.ownKey, Equiv.symm_apply_apply] using hd
  have ht := released_forward_stamp S rho hn hv hs ho hd'
  rw [ht]
  obtain ⟨hi, hei⟩ := List.getElem?_eq_some_iff.mp he
  rcases hs with hs | ⟨receipt', hs⟩
  all_goals
    obtain ⟨hj', hej⟩ := List.getElem?_eq_some_iff.mp hs
    have horder := List.pairwise_iff_getElem.mp hv.sorted j i hj' hi hj
    rw [hej, hei] at horder
    rcases horder with hlt | ⟨heq, _⟩
    · exact le_of_lt hlt
    · exact le_of_eq heq

omit [DecidableEq V] in
private theorem batch_closure_source (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (cs)
    {o : Wire (Fintype.card V)}
    (ho : o ∈ Model.closure (Model.releaseAll (Model.protoOf (compiled (family S)) E)
      rho.hash (rho.ownKey v) nd cs).1.seen) :
    o ∈ Model.closure nd.seen ∨
      o ∈ (Model.releaseAll (Model.protoOf (compiled (family S)) E)
        rho.hash (rho.ownKey v) nd cs).2 := by
  let Q := fun c => c = o → o ∈ Model.closure nd.seen ∨
    o ∈ (Model.releaseAll (Model.protoOf (compiled (family S)) E)
      rho.hash (rho.ownKey v) nd cs).2
  have h := Model.releaseAll_preserves rho.hash (rho.ownKey v) Q nd cs
    (fun c hc b hb he => Or.inl (he ▸ (Model.mem_closure_iff _ _).mpr ⟨c, hc, hb⟩))
    (fun c hc he => Or.inr (he ▸ hc))
  obtain ⟨c, hc, hco⟩ := (Model.mem_closure_iff _ _).mp ho
  exact h.1 c hc o hco rfl

omit [DecidableEq V] in
private theorem duties_closure_source (v : V) :
    ∀ ds (nd : Model.Node (Model.protoOf (compiled (family S)) E))
      (o : Wire (Fintype.card V)),
    o ∈ Model.closure (rho.runDuties v nd ds).1.seen →
      o ∈ Model.closure nd.seen ∨ o ∈ (rho.runDuties v nd ds).2 := by
  intro ds
  induction ds with
  | nil => intro nd o ho; exact Or.inl ho
  | cons d ds ih =>
    intro nd o ho
    rw [rho.runDuties_cons] at ho ⊢
    rcases ih _ o ho with ho | ho
    · unfold Model.Run.dutyStep at ho ⊢
      split at ho
      · rename_i hsel
        simp only [hsel, ↓reduceIte]
        rcases batch_closure_source S rho v _ _ ho with ho | ho
        · exact Or.inl ho
        · exact Or.inr (List.mem_append_left _ ho)
      · rename_i hsel
        exact Or.inl ho
    · exact Or.inr (List.mem_append_right _ ho)

/-- A held object originates in an exact local release or an enclosing receipt. Nested
release payloads do not create a third case: the release guard required them earlier. -/
theorem held_release_or_receipt {v : V} {i : Nat} {o : Wire (Fintype.card V)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen) :
    ∃ j < i, ∃ t, (rho.SendsAt v j t ∧ o ∈ rho.releasesAt j) ∨
      ∃ receipt, rho.events[j]? = some (.deliver v receipt t) ∧
        Model.Obj.Contains receipt o := by
  induction i with
  | zero => exact False.elim (List.not_mem_nil ho)
  | succ i ih =>
    have old (h : o ∈ Model.closure (rho.stateBefore i v).seen) :
        ∃ j < i + 1, ∃ t, (rho.SendsAt v j t ∧ o ∈ rho.releasesAt j) ∨
          ∃ receipt, rho.events[j]? = some (.deliver v receipt t) ∧
            Model.Obj.Contains receipt o := by
      obtain ⟨j, hj, t, h⟩ := ih h
      exact ⟨j, by omega, t, h⟩
    cases he : rho.events[i]? with
    | none =>
      have hh : rho.stateBefore (i + 1) = rho.stateBefore i := by
        simp [Model.Run.stateBefore, List.take_add_one, he]
      exact old (hh ▸ ho)
    | some ev =>
      rw [rho.stateBefore_succ he] at ho
      by_cases hnode : ev.node = v
      · cases ev with
        | restart w t =>
          simp only [Model.Event.node] at hnode
          subst w
          exact old (by simpa only [Model.Run.step, Function.update_self] using ho)
        | tick w t =>
          simp only [Model.Event.node] at hnode
          subst w
          simp only [Model.Run.step, Function.update_self, Model.Run.tick] at ho
          split at ho
          · rcases batch_closure_source S rho v _ _ ho with ho | ho
            · rcases duties_closure_source S rho v _ _ o ho with ho | ho
              · exact old ho
              · refine ⟨i, by omega, t, Or.inl ⟨Or.inl he, ?_⟩⟩
                simp only [Model.Run.releasesAt, he, Model.Run.tick]
                split
                · exact List.mem_append_left _ ho
                · contradiction
            · refine ⟨i, by omega, t, Or.inl ⟨Or.inl he, ?_⟩⟩
              simp only [Model.Run.releasesAt, he, Model.Run.tick]
              split
              · exact List.mem_append_right _ ho
              · contradiction
          · exact old ho
        | deliver w receipt t =>
          simp only [Model.Event.node] at hnode
          subst w
          simp only [Model.Run.step, Function.update_self, Model.Run.deliver] at ho
          rcases batch_closure_source S rho v _ _ ho with ho | ho
          · rcases duties_closure_source S rho v _ _ o ho with ho | ho
            · rw [Model.closure_append] at ho
              rcases List.mem_append.mp ho with ho | ho
              · exact old ho
              · obtain ⟨r, hr, hc⟩ := (Model.mem_closure_iff _ _).mp ho
                have hr' := List.mem_singleton.mp hr
                subst r
                exact ⟨i, by omega, t, Or.inr ⟨receipt, he, hc⟩⟩
            · refine ⟨i, by omega, t, Or.inl ⟨Or.inr ⟨receipt, he⟩, ?_⟩⟩
              simp only [Model.Run.releasesAt, he, Model.Run.deliver]
              exact List.mem_append_left _ ho
          · refine ⟨i, by omega, t, Or.inl ⟨Or.inr ⟨receipt, he⟩, ?_⟩⟩
            simp only [Model.Run.releasesAt, he, Model.Run.deliver]
            exact List.mem_append_right _ ho
      · cases ev with
        | tick w t | deliver w receipt t | restart w t =>
          simp only [Model.Event.node] at hnode
          exact old (by
            simpa only [Model.Run.step, Function.update_of_ne (Ne.symm hnode)] using ho)

/-- Held honest forwarding envelopes either were released locally, or already have a
real receipt call before the requested cut. The latter may be a refused block call. -/
theorem held_forward_release_or_call (hv : rho.ExecutionValid) {v : V} {i : Nat}
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen) (hx : rho.key x ∈ rho.honest)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    (∃ j < i, ∃ u, rho.SendsAt v j u ∧ o ∈ rho.releasesAt j) ∨
      ∃ k < cutMap S rho hn i, t ≤ (simTrace S rho hn).time k ∧
        (simTrace S rho hn).BlockCallAt (rho.ownKey v) k B := by
  obtain ⟨j, hj, u, h⟩ := held_release_or_receipt S rho ho
  rcases h with ⟨he, hr⟩ | ⟨receipt, he, hc⟩
  · exact Or.inl ⟨j, hj, u, he, hr⟩
  · have htu := received_forward_stamp_le S rho hn hv he hc hx hd
    obtain ⟨k, hk, hcall, htime⟩ := received_forward_blockCall S rho hn he hc hd htu
    exact Or.inr ⟨k, hk.trans_le (cutMap_mono S rho hn (Nat.succ_le_of_lt hj)),
      htime ▸ htu, hcall⟩

private theorem dutyBatches_signer (v : V) :
    ∀ ds (nd : Model.Node (Model.protoOf (compiled (family S)) E)) b,
    b ∈ dutyBatches rho v nd ds → ∀ o ∈ b.candidates,
      o.signer? = some (rho.ownKey v) := by
  intro ds
  induction ds with
  | nil => intro nd b hb; rw [dutyBatches_nil] at hb; exact False.elim (List.not_mem_nil hb)
  | cons d ds ih =>
    intro nd b hb o ho
    rw [dutyBatches_cons] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · split at ho
      · obtain ⟨m, cs, _, _, rfl⟩ := rho.mem_signedCandidate.mp ho
        rfl
      · exact False.elim (List.not_mem_nil ho)
    · exact ih _ b hb o ho

/-- A signed forwarding object released locally is signed by that node. Carried
forwarding objects are deliberately not claimed to have the local signer. -/
theorem released_forward_signer {i : Nat} {v : V} {u : Time}
    (he : rho.SendsAt v i u) {o : Wire (Fintype.card V)} (ho : o ∈ rho.releasesAt i)
    {x : Fin (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) : x = rho.ownKey v := by
  obtain ⟨b, hb, ho⟩ := released_candidate_batch S rho he ho
  have hsign : o.signer? = some (rho.ownKey v) := by
    rcases he with he | ⟨receipt, he⟩
    all_goals
      rw [eventBatches_eq, he] at hb
      simp only at hb
    · split at hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact dutyBatches_signer S rho v _ _ b hb o ho
        · have heq := List.mem_singleton.mp hb
          subst b
          obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp ho
          have hsign := decodeForward_signer hd
          change none = some x at hsign
          cases hsign
      · exact False.elim (List.not_mem_nil hb)
    · rcases List.mem_append.mp hb with hb | hb
      · exact dutyBatches_signer S rho v _ _ b hb o ho
      · have heq := List.mem_singleton.mp hb
        subst b
        obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp ho
        have hsign := decodeForward_signer hd
        change none = some x at hsign
        cases hsign
  exact Option.some.inj ((decodeForward_signer hd).symm.trans hsign)

/-- Holdings of another honest node's forwarding envelope always have an earlier
receipt call; only the self-signed case needs the own-publication acceptance join. -/
theorem held_other_forward_call (hv : rho.ExecutionValid) {v : V} {i : Nat}
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen) (hx : rho.key x ∈ rho.honest)
    (hne : x ≠ rho.ownKey v)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    ∃ k < cutMap S rho hn i, t ≤ (simTrace S rho hn).time k ∧
      (simTrace S rho hn).BlockCallAt (rho.ownKey v) k B := by
  rcases held_forward_release_or_call S rho hn hv ho hx hd with ⟨j, _, u, he, hr⟩ | h
  · exact False.elim (hne (released_forward_signer S rho hn he hr hd))
  · exact h

/-- The only remaining origin case for held honest forwarding envelopes is a local
tick publication. All receipts and local delivery publications already have trace witnesses. -/
theorem held_forward_tick_or_processed (hv : rho.ExecutionValid) {v : V} {i : Nat}
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen) (hx : rho.key x ∈ rho.honest)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    (x = rho.ownKey v ∧ ∃ j < i, ∃ u,
      rho.events[j]? = some (.tick v u) ∧ o ∈ rho.releasesAt j) ∨
    ∃ k < cutMap S rho hn i, t ≤ (simTrace S rho hn).time k ∧
      ((simTrace S rho hn).BlockCallAt (rho.ownKey v) k B ∨
        x = rho.ownKey v ∧ (simTrace S rho hn).AcceptAt (rho.ownKey v) k B) := by
  rcases held_forward_release_or_call S rho hn hv ho hx hd with ⟨j, hj, u, he, hr⟩ | h
  · have hxv := released_forward_signer S rho hn he hr hd
    subst x
    rcases he with he | ⟨receipt, he⟩
    · exact Or.inl ⟨rfl, j, hj, u, he, hr⟩
    · obtain ⟨k, hk, ha, ht⟩ := delivery_released_forward_acceptance S rho hn hv he hr hd
      exact Or.inr ⟨k, hk.trans_le (cutMap_mono S rho hn (Nat.succ_le_of_lt hj)),
        le_of_eq ht.symm, Or.inr ⟨rfl, ha⟩⟩
  · obtain ⟨k, hk, ht, hc⟩ := h
    exact Or.inr ⟨k, hk, ht, Or.inl hc⟩

private theorem tick_forward_queue (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {u t : Time} {o : Wire (Fintype.card V)} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.tick v u)) (ho : o ∈ rho.releasesAt i)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    ∃ s hs, (skeleton (Model.pubOf E)).proposeAt u = [.propose s hs] ∧
      (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∈
        (shapeOf S hn (rho.dutyStep v
          (atProposal S rho v (rho.stateBefore i v) u) (.propose s hs)).1).forwards := by
  have hu := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v u (List.mem_of_getElem? he)
  have hsel := poll_selected S rho hv v
  have noPoll (nd : Model.Node (Model.protoOf (compiled (family S)) E))
      (hempty : (shapeOf S hn nd).forwards = [])
      (h : o ∈ (rho.dutyStep v nd (.poll u.toNat)).2) : False := by
    have hq := poll_release_forward_queue S rho hn v nd u.toNat h hd
    rw [hempty] at hq
    exact List.not_mem_nil hq
  have noGossip (nd : Model.Node (Model.protoOf (compiled (family S)) E))
      (h : o ∈ (Model.releaseAll (Model.protoOf (compiled (family S)) E)
        rho.hash (rho.ownKey v) nd
        (Model.gossipCandidates (Model.protoOf (compiled (family S)) E) nd.st u)).2) : False :=
    gossip_not_forward S rho hn nd u (Model.releaseAll_subset _ _ _ _ o h) hd
  have hclock : (shapeOf S hn
      (⟨(Model.protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st u
        (Model.mempool rho.inbox v u), (rho.stateBefore i v).seen⟩ :
        Model.Node (Model.protoOf (compiled (family S)) E))).forwards = [] :=
    forwards_empty S rho hn hv v i
  have hpoll (nd : Model.Node (Model.protoOf (compiled (family S)) E)) :
      (shapeOf S hn (rho.dutyStep v nd (.poll u.toNat)).1).forwards = [] := by
    rw [dutyStep_poll S rho hn v nd u.toNat hsel, poll_forwards]
  simp only [Model.Run.releasesAt, he] at ho
  rcases Skeleton.proposeAt_cases (skeleton (Model.pubOf E)) u with
    ⟨hnil, _⟩ | ⟨s, hs, hone, _⟩
  · obtain ⟨N1, N3, N5, N6, rfl, rfl, rfl, rfl, hrel⟩ :=
      tick_unroll_nil S rho v (rho.stateBefore i v) u hu hw hnil
    rw [hrel] at ho
    rcases List.mem_append.mp ho with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · exact False.elim (noPoll _ hclock h)
            · exact False.elim (noPoll _ (hpoll _) h)
          · rw [dutyStep_pollPropose_snd S rho hn] at h
            exact False.elim (List.not_mem_nil h)
        · have hz := atProposal_forwards_nil S rho hn hv v (rho.stateBefore i v) u
          rw [atProposal_eq] at hz
          exact False.elim (noPoll _ hz h)
      · exact False.elim (noPoll _ (hpoll _) h)
    · exact False.elim (noGossip _ h)
  · obtain ⟨N1, N3, N4, N5, N6, rfl, rfl, rfl, rfl, rfl, hrel⟩ :=
      tick_unroll_propose S rho v (rho.stateBefore i v) u hu hw s hs hone
    rw [hrel] at ho
    rcases List.mem_append.mp ho with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · rcases List.mem_append.mp h with h | h
              · exact False.elim (noPoll _ hclock h)
              · exact False.elim (noPoll _ (hpoll _) h)
            · rw [dutyStep_pollPropose_snd S rho hn] at h
              exact False.elim (List.not_mem_nil h)
          · unfold Model.Run.dutyStep at h
            split at h
            · obtain ⟨m, cs, _, _, ho⟩ := rho.mem_signedCandidate.mp
                (Model.releaseAll_subset _ _ _ _ o h)
              have ha := congrArg Model.Obj.auth
                (ho.symm.trans (forwardObj_of_decodeForward _ _ _ _ _ _ hd))
              cases ha
            · exact False.elim (List.not_mem_nil h)
        · refine ⟨s, hs, hone, ?_⟩
          rw [atProposal_eq]
          exact poll_release_forward_queue S rho hn v _ u.toNat h hd
      · exact False.elim (noPoll _ (hpoll _) h)
    · exact False.elim (noGossip _ h)

private theorem tick_forward_acceptance_wire (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {u t : Time} {o : Wire (Fintype.card V)} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.tick v u)) (ho : o ∈ rho.releasesAt i)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    ∃ C, ∃ parent : Option (Wire (Fintype.card V)),
      .fg (.block C true) ∈ (exec (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (stateAt S rho hn v i).node u
        (.tick (encodeTxs (Model.mempool rho.inbox v u)))).2 ∧
      (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) =
        (u, parent.toList ++ [blockObj (S.params (Model.pubOf E) hn) C]) ∧
      (S.params (Model.pubOf E) hn).toParams.IsPublic u := by
  obtain ⟨s, hs, hone, hq⟩ := tick_forward_queue S rho hn hv he ho hd
  have htime : u = (S.params (Model.pubOf E) hn).toParams.slotTime s := by
    rcases Skeleton.proposeAt_cases (skeleton (Model.pubOf E)) u with
      ⟨hno, _⟩ | ⟨s', hs', hyes, ht⟩
    · rw [hno] at hone
      cases hone
    · have hh := List.singleton_inj.mp (hone.symm.trans hyes)
      cases hh
      exact ht.trans (slotTime_eq S hn s).symm
  have hpub : (S.params (Model.pubOf E) hn).toParams.IsPublic u := by
    rw [htime]
    exact (S.params (Model.pubOf E) hn).toParams.slotTime_public s
  have hsel := poll_selected S rho hv v
  have hself : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) u)).self =
      rho.ownKey v := by
    rw [atProposal_self S rho hn v _ u hsel]
    exact self_eq_ownKey S rho hn v i
  have hnow := atProposal_now S rho hn v (rho.stateBefore i v) u hsel
  rcases proposal_duty_forward_origin S rho hn v _ s hs
      (selValid_proposer S rho hn hv.selValid s) hself
      (by rw [hnow, htime]; exact slotOf_slotTime _ s) (hnow.trans htime) _ hq with
    hq | ⟨C, parent, hc, hq⟩
  · rw [atProposal_forwards_nil S rho hn hv] at hq
    exact False.elim (List.not_mem_nil hq)
  · rw [hnow] at hc hq
    rw [atProposal_mempool] at hc
    have hnode : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) u)).node =
        (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node u .tick).1 := by
      rw [atProposal_node S rho hn v _ u (fgDue_eq_false S rho hn v i) hsel,
        nodeTick_node_public _ hpub]
      exact congrArg (fun k => (Node.acCall k _ u .tick).1) (self_eq_ownKey S rho hn v i)
    rw [hnode] at hc
    refine ⟨C, parent, ?_, hq, hpub⟩
    change _ ∈ (Node.onTick _ _ _ _ _ _).2
    rw [onTick_cuts (sp := S.params (Model.pubOf E) hn) (ro := S.ro _)]
    exact List.mem_append_left _ (List.mem_append_right _ hc)

private theorem tick_accepted_root {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    {B : Blk sp}
    (hm : .fg (.block B true) ∈ (exec proposer dg self st t (.tick x)).2) :
    B.RootOk dg ∧ B.parent ≠ none := by
  change _ ∈ (onTick (A := goldilocksNode sp ro) proposer dg self st t x).2 at hm
  rw [onTick_cuts (sp := sp) (ro := ro)] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · simp [tickStep, acCall] at hm
    · simp only [tickStep] at hm
      split_ifs at hm
      · split at hm
        · simp [acProposal] at hm
        · simp only [proposeBlock, onBlock] at hm
          split_ifs at hm
          · simp [acProposal] at hm
          · split at hm <;> simp [acCall, acProposal] at hm
            obtain ⟨rfl, _⟩ := hm
            exact ⟨rfl, by simp [mkBlock]⟩
      · simp at hm
  · simp only [tickStep] at hm
    split at hm
    · simp [acToFG] at hm
    · simp only [attest, List.mem_cons, acToFG, reduceCtorEq, false_or] at hm
      split at hm <;> simp [onAttestation] at hm

omit [DecidableEq V] in
private theorem decoded_block_root {o : Wire (Fintype.card V)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hc : Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) B))
    (hd : decodeBlock (S.params (Model.pubOf E) hn) (Model.digests rho.hash o)
      (blockObj (S.params (Model.pubOf E) hn) B) = some B) :
    B.RootOk (digestOf S rho) ∧ B.parent ≠ none := by
  obtain ⟨hroot, hpar, _, _⟩ := decodeBlock_wire hd
  have hh := rootOf_digests_of_mem S rho o _ (List.mem_filterMap.mpr ⟨_, hc, rfl⟩)
  rw [hh, Option.map_some, Option.some.injEq] at hroot
  refine ⟨?_, hpar⟩
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hpar
  change B.root = dgOf rho.hash S.genesisRoot B.parent B.slot B.input B.fgPayload B.acPayload
  rw [← hroot]
  simp only [headerOf, hr]
  rfl

omit [DecidableEq V] in
private theorem rooted_block_eq {B C : Blk (S.params (Model.pubOf E) hn)}
    (hB : B.parent ≠ none) (hC : C.parent ≠ none)
    (hrB : B.RootOk (digestOf S rho)) (hrC : C.RootOk (digestOf S rho))
    (he : blockObj (S.params (Model.pubOf E) hn) B = blockObj _ C) : B = C := by
  have hh := congrArg Model.Obj.msg he
  have ha := congrArg Model.Obj.auth he
  simp only [blockObj, Model.Obj.msg, Model.Msg.item.injEq] at hh
  simp only [blockObj, Model.Obj.auth, Model.Auth.signed.injEq] at ha
  have hp := congrArg (fun h => parentRoot S.genesisRoot h.parent) hh
  have hs := congrArg Header.pos hh
  have hx := congrArg Header.input hh
  have hi := congrArg (fun h => decodeInfo (Fintype.card V) h.info) hh
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hB
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hC
  simp only [headerOf, hb, hc, parentRoot_parentRef] at hp
  simp only [headerOf, decodeInfo_encodeInfo, Option.some.injEq, Prod.mk.injEq] at hi
  have hparent : B.parent = C.parent := by simpa [hb, hc] using hp
  change B.slot = C.slot at hs
  change B.input = C.input at hx
  have hroot : B.root = C.root := by
    change B.root = digestOf S rho B.parent B.slot B.input B.fgPayload B.acPayload at hrB
    rw [hrB, hparent, hs, hx, hi.1, hi.2]
    exact hrC.symm
  have hv := ha.1
  cases B; cases C
  simp_all

/-- A forwarding release during a tick identifies an actual successful proposal cut,
including the digest-backed root rather than just the serialized block fields. -/
theorem tick_released_forward_acceptance (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {u t : Time} {o : Wire (Fintype.card V)} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.tick v u)) (ho : o ∈ rho.releasesAt i)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t := by
  obtain ⟨C, parent, hc, hq, hpub⟩ := tick_forward_acceptance_wire S rho hn hv he ho hd
  have ht : t = u := congrArg Prod.fst hq
  have hw : blockObj (S.params (Model.pubOf E) hn) B = blockObj _ C := by
    have hlast := congrArg List.getLast? (congrArg Prod.snd hq)
    cases p <;> cases parent <;> simpa using hlast
  have hcontains : Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) B) := by
    rw [forwardObj_of_decodeForward _ _ _ _ _ _ hd]
    exact Model.Obj.Contains.step (List.mem_append_right _ (List.mem_singleton_self _))
      (Model.Obj.Contains.refl _)
  obtain ⟨hrB, hpB⟩ := decoded_block_root S rho hn hcontains (decodeForward_child hd).1
  obtain ⟨hrC, hpC⟩ := tick_accepted_root _ _ _ _ _ _ hc
  have hBC := rooted_block_eq S rho hn hpB hpC hrB hrC hw
  subst C
  obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
  have hm' : m < (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node u (Nat.pair i 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v u)))).length := by
    rw [length_groupRecs]; exact hm
  have hf := getElem_groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
    (stateAt S rho hn v i).node u (Nat.pair i 0)
    (.tick (encodeTxs (Model.mempool rho.inbox v u))) m hm'
  have hmrec := List.getElem_mem hm'
  have hr := (congrArg (fun rs =>
    (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node u (Nat.pair i 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v u))))[m]'hm' ∈ rs)
    (eventCuts_tick_public S rho hn i v u he hpub)).mpr hmrec
  obtain ⟨k, hk, ha, htime⟩ := acceptAt_of_eventCuts S rho hn
    (List.getElem?_eq_some_iff.mp he).1 hr (hf.2.2.2.2.trans hcm)
  exact ⟨k, hk, hf.1 ▸ ha, htime.trans (hf.2.1.trans ht.symm)⟩

/-- Every actual publication has a successful source acceptance at its stamped time. -/
theorem simTrace_forwardOrigin (hv : rho.ExecutionValid) :
    ForwardOrigin S rho hn (simTrace S rho hn) (cutMap S rho hn)
      (publisherExecution S rho) := by
  apply (forwardOrigin_iff S rho hn _ _ _).mpr
  intro r hr _ t p B hd
  have hk : rho.ownKey (rho.key r.origin) = r.origin := rho.key.symm_apply_apply _
  have hd' := hd
  rw [← hk] at hd'
  have he := (publisherExecution S rho).actual_event r hr
  have ho := (publisherExecution S rho).actual_release r hr
  have hacc : ∃ k < cutMap S rho hn (r.event + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey (rho.key r.origin)) k B ∧
      (simTrace S rho hn).time k = t := by
    rcases he with he | ⟨receipt, he⟩
    · exact tick_released_forward_acceptance S rho hn hv he ho hd'
    · exact delivery_released_forward_acceptance S rho hn hv he ho hd'
  obtain ⟨k, hbound, ha, ht⟩ := hacc
  exact ⟨k, hk ▸ ha, ht, hbound, publication_forward_stamp S rho hn hv r hr hd⟩

/-- Every authenticated wrapper in an actual receipt has a successful source cut
before that receipt's event boundary, with the exact decoded block and stamp. -/
theorem received_forward_source_acceptance (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {receipt o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t u : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∈ rho.honest)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    ∃ k < cutMap S rho hn i, (simTrace S rho hn).AcceptAt x k B ∧
      (simTrace S rho hn).time k = t := by
  have hsign : rho.signerOf o = some (rho.key x) := by
    change o.signer?.map rho.key = some (rho.key x)
    rw [decodeForward_signer hd]
    rfl
  obtain ⟨j, s, hj, hs, ho⟩ := hv.unforgeable i v receipt u he o hc (rho.key x) hx hsign
  have hkx : rho.ownKey (rho.key x) = x := rho.key.symm_apply_apply _
  have hd' := hd
  rw [← hkx] at hd'
  have hacc : ∃ k < cutMap S rho hn (j + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey (rho.key x)) k B ∧
      (simTrace S rho hn).time k = t := by
    rcases hs with hs | ⟨receipt', hs⟩
    · exact tick_released_forward_acceptance S rho hn hv hs ho hd'
    · exact delivery_released_forward_acceptance S rho hn hv hs ho hd'
  obtain ⟨k, hk, ha, ht⟩ := hacc
  exact ⟨k, hk.trans_le (cutMap_mono S rho hn (Nat.succ_le_of_lt hj)), hkx ▸ ha, ht⟩

omit [DecidableEq V] in
/-- A nested forwarding parse uses the same digest-backed roots whether decoded
under its enclosing receipt's digests or its own recursively collected digests. -/
theorem decodeForward_receipt_iff {receipt o : Wire (Fintype.card V)}
    {x : Fin (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)} (hc : Model.Obj.Contains receipt o) :
    decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash receipt) o =
      some (x, t, p, B) ↔
    decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B) := by
  have roots (C : Blk (S.params (Model.pubOf E) hn))
      (hC : Model.Obj.Contains o (blockObj _ C)) :
      rootOf (Model.digests rho.hash o) (headerOf _ C) =
        rootOf (Model.digests rho.hash receipt) (headerOf _ C) := by
    rw [rootOf_digests_of_mem S rho o _ (List.mem_filterMap.mpr ⟨_, hC, rfl⟩),
      rootOf_digests_of_mem S rho receipt _ (List.mem_filterMap.mpr ⟨_, hc.trans hC, rfl⟩)]
  exact ⟨fun hd => decodeForward_transport B o x t p hd roots,
    fun hd => decodeForward_transport B o x t p hd (fun C hC => (roots C hC).symm)⟩

/-- An actual honest receiver's historical receipt gives acceptance before the
observation whenever the observation's finalized tip is below the received block.
This uses the actual parent-first traversal and source provenance, not a historical
possibly refused `BlockCallAt`. Previously accepted blocks persist across restart. -/
theorem received_forward_accepted (hv : rho.ExecutionValid)
    (hrun : GoldilocksRun (runProposer S rho hn) (digestOf S rho)
      (honestKeys S rho) (simTrace S rho hn))
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {i j : Nat} {v : V} {receipt o : Wire (Fintype.card V)}
    {x : Fin (Fintype.card V)} {u t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u)) (hy : v ∈ rho.honest)
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∈ rho.honest)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hij : cutMap S rho hn (i + 1) ≤ j)
    (hFB : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).state (rho.ownKey v) j).fg.F B) :
    ∃ k < j, (simTrace S rho hn).AcceptAt (rho.ownKey v) k B := by
  have hy' : rho.ownKey v ∈ honestKeys S rho := by
    change rho.key (rho.ownKey v) ∈ rho.honest
    simpa only [Model.Run.ownKey, Equiv.apply_symm_apply] using hy
  have hseq := simTrace_deliver S rho hn hv v hy i receipt u he
  obtain ⟨pre, post, hparts⟩ := contained_parts_infix hc
  change DeliverSeq (sp := S.params (Model.pubOf E) hn) (ro := S.ro _)
    _ _ _ _ _ _ receipt.parts _ _ at hseq
  rw [hparts, List.append_assoc] at hseq
  obtain ⟨r, _, htail⟩ := deliverSeq_append_split _ _ hseq
  obtain ⟨e, hsub, hpost⟩ := deliverSeq_append_split _ _ htail
  have hej := (deliverSeq_cover hpost).1.trans hij
  have hd' := (decodeForward_receipt_iff S rho hn hc).mpr hd
  have hsource : ∀ q tq pq C, Model.Obj.Contains o q →
      decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash receipt) q =
        some (x, tq, pq, C) → ∃ k, (simTrace S rho hn).AcceptAt x k C := by
    intro q tq pq C hq hdec
    obtain ⟨k, _, ha, _⟩ := received_forward_source_acceptance S rho hn hv he (hc.trans hq) hx
      ((decodeForward_receipt_iff S rho hn (hc.trans hq)).mp hdec)
    exact ⟨k, ha⟩
  have hheld := forward_receipt_held hrun hnc hx hy' hFB B o t p r e hd' hsub hej
    (received_forward_stamp_le S rho hn hv he hc hx hd) .refl hsource
  rcases Compose.tree_cases hrun.toLocalRun hy' hheld with hgen | ⟨k, hk, ha⟩
  · have hp := (decodeBlock_wire (decodeForward_child hd).1).2.1
    exact False.elim (hp (hgen ▸ rfl))
  · exact ⟨k, hk.trans_le hej, ha⟩

/-- A historical receipt before a strict deadline gives an acceptance before that
deadline. The acceptance is bounded by its actual source event, never by the time
of the next cut (which may belong to a later event or terminal filler). -/
theorem received_forward_accepted_before (hv : rho.ExecutionValid)
    (hrun : GoldilocksRun (runProposer S rho hn) (digestOf S rho)
      (honestKeys S rho) (simTrace S rho hn))
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {i j : Nat} {v : V} {receipt o : Wire (Fintype.card V)}
    {x : Fin (Fintype.card V)} {u t deadline : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u)) (hy : v ∈ rho.honest)
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∈ rho.honest)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hij : cutMap S rho hn (i + 1) ≤ j)
    (hFB : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).state (rho.ownKey v) j).fg.F B)
    (hu : u < deadline) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k ≤ u ∧ (simTrace S rho hn).time k < deadline := by
  have hy' : rho.ownKey v ∈ honestKeys S rho := by
    change rho.key (rho.ownKey v) ∈ rho.honest
    simpa only [Model.Run.ownKey, Equiv.apply_symm_apply] using hy
  have hFB' := (Healing.run_F_mono hrun.toLocalRun hy' hij).trans hFB
  obtain ⟨k, hk, ha⟩ := received_forward_accepted S rho hn hv hrun hnc
    he hy hc hx hd le_rfl hFB'
  obtain ⟨r, q, ev, _, hq, hstart, _, _, _, ht, _⟩ :=
    simTrace_cut S rho hn (by rw [ha.2]; simp)
  have hqi : q ≤ i := by
    by_contra h
    have hm : cutMap S rho hn (i + 1) ≤ cutMap S rho hn q :=
      cutMap_mono S rho hn (by omega)
    exact (not_lt_of_ge (hm.trans hstart)) hk
  have htime : (simTrace S rho hn).time k ≤ u := by
    rw [ht]
    rcases hqi.lt_or_eq with hlt | rfl
    · rcases keyLe_of_index_lt S rho hv hq he hlt with h | h
      · exact h.le
      · exact h.1.le
    · rw [he] at hq
      cases hq
      exact le_rfl
  exact ⟨k, hk, ha, htime, htime.trans_lt hu⟩

/-- Prior authenticated holdings give a prior receipt call or an own acceptance.
The receipt alternative deliberately retains refusal as a possibility. -/
theorem simTrace_forwardHeldProcessed (hv : rho.ExecutionValid) :
    ForwardHeldProcessed S rho hn (simTrace S rho hn) (cutMap S rho hn) := by
  apply (forwardHeldProcessed_iff S rho hn _ _).mpr
  intro y _ i x t p B o hx ho hd
  have hy : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  rcases held_forward_tick_or_processed S rho hn hv ho hx hd with
    ⟨hxy, j, hj, u, he, hr⟩ | ⟨k, hk, ht, hc⟩
  · rw [hxy] at hd
    obtain ⟨k, hk, ha, ht⟩ := tick_released_forward_acceptance S rho hn hv he hr hd
    refine ⟨k, hk.trans_le (cutMap_mono S rho hn (Nat.succ_le_of_lt hj)),
      le_of_eq ht.symm, Or.inr ⟨(hxy.trans hy).symm, hy ▸ ha⟩⟩
  · refine ⟨k, hk, ht, ?_⟩
    rcases hc with hc | ⟨hxy, ha⟩
    · exact Or.inl (hy ▸ hc)
    · exact Or.inr ⟨(hxy.trans hy).symm, hy ▸ ha⟩

/-- A top-level signed vote envelope can only be released by its signer. Other nodes may
carry it in unsigned gossip, but cannot account for an earlier top-level release of it. -/
theorem voteForward_release_sender {i : Nat} {x : Fin (Fintype.card V)} {t : Time}
    {m : SA.Vote (Fintype.card V)}
    (h : Model.Obj.mk (.signed x .poll) (.data (.voteForward t (encodeVote m))) [voteObj m] ∈
      rho.releasesAt i) : ∃ u, rho.SendsAt (rho.key x) i u := by
  cases he : rho.events[i]? with
  | none =>
    simp only [Model.Run.releasesAt, he] at h
    exact False.elim (List.not_mem_nil h)
  | some ev =>
    cases ev with
    | restart v u =>
      simp only [Model.Run.releasesAt, he] at h
      exact False.elim (List.not_mem_nil h)
    | tick v u =>
      simp only [Model.Run.releasesAt, he] at h
      rcases rho.tick_auth _ _ _ h with ha | ⟨r, ha, _⟩
      · cases ha
      · have hx : x = rho.ownKey v := (Model.Auth.signed.inj ha).1
        subst x
        have hk : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
        exact ⟨u, Or.inl (by rw [hk]; exact he)⟩
    | deliver v o u =>
      simp only [Model.Run.releasesAt, he] at h
      rcases rho.deliver_auth _ _ _ _ h with ha | ⟨r, ha, _⟩
      · cases ha
      · have hx : x = rho.ownKey v := (Model.Auth.signed.inj ha).1
        subst x
        have hk : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
        exact ⟨u, Or.inr ⟨o, by rw [hk]; exact he⟩⟩

end Trace

end Consensus.Goldilocks.Refinement
