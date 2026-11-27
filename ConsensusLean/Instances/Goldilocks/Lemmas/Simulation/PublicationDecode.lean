module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Forwarding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Cuts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
public import ConsensusLean.Lemmas.Model.Protection
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReceiptTraversal

public section

/-! # Forwarding decoding and recursive receipt provenance -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node

variable {binding : VoteBinding}

variable {sp : AC.ACParams}

/-- Splitting recursive receipt processing preserves the actual intermediate cut,
rather than replacing a processing occurrence by an arbitrary historical call. -/
theorem deliverSeq_append_split {proposer : Nat → Fin sp.n} {tr : GoldilocksTrace sp}
    {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {hs : List (Header Info × Nat)}
    {io : VoteAuth sp.n binding}
    {y : Fin sp.n} {t : Time} (xs ys : List (Wire sp.n binding)) {j j' : Nat}
    (h : DeliverSeq proposer tr dg io hs y t (xs ++ ys) j j') :
    ∃ m, DeliverSeq proposer tr dg io hs y t xs j m ∧
      DeliverSeq proposer tr dg io hs y t ys m j' := by
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
private theorem canonEvent_forward_none (io : VoteAuth sp.n binding)
    (hs : List (Header Info × Nat))
    (x : Fin sp.n) (t : Time) (p : Option (Wire sp.n binding)) (B : Blk sp) :
    canonEvent sp io hs (forwardObj sp x t p B) = none := by
  cases hp : binding.participationKind <;>
    simp [canonEvent_eq, forwardObj, decodeBlock_eq, decodeVoteObj, decodeAttObj, presented]

/-- A forwarding chain processes the parent's visit before the visit of the child's canonical
block (with its payload when it is accepted); the split retains the actual cut boundary. -/
theorem deliverSeq_forward_parent {proposer : Nat → Fin sp.n} {tr : GoldilocksTrace sp}
    {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {hs : List (Header Info × Nat)}
    {io : VoteAuth sp.n binding}
    {y x : Fin sp.n} {u t : Time} {parent : Wire sp.n binding} {B : Blk sp} {j j' : Nat}
    {σ : State sp binding}
    (h : DeliverSeq proposer tr dg io hs y u
      (visit io hs σ (forwardObj sp x t (some parent) B)).1 j j') :
    ∃ (m : Nat) (σ₁ σ₂ : State sp binding),
      DeliverSeq proposer tr dg io hs y u (visit io hs σ₁ parent).1 j m ∧
      DeliverSeq proposer tr dg io hs y u
        (visit io hs σ₂ (blockObj sp (binding := binding) B)).1 m j' := by
  have hz := canonEvent_forward_none io hs x t (some parent) B
  rcases visit_cases io hs σ (forwardObj sp x t (some parent) B) with ⟨hr, -⟩ | ⟨-, hv⟩
  · exact absurd hr (not_refuses_of_data _ _ rfl)
  rw [hv] at h
  cases h with
  | event e he _ _ => rw [hz] at he; cases he
  | noCut e he _ _ => rw [hz] at he; cases he
  | drop _ htail =>
    simp only [forwardObj, Model.Obj.carried, Option.toList_some, List.cons_append,
      List.nil_append, visitList_cons] at htail
    rw [visitList_nil_eq, List.append_nil] at htail
    obtain ⟨m, h1, h2⟩ := deliverSeq_append_split _ _ htail
    exact ⟨m, _, _, h1, h2⟩

/-- Parsing a forwarding envelope authenticates its outer signer, independently of
whether its contained block was accepted by any receiver. -/
theorem decodeForward_signer {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n binding)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) : o.signer? = some x := by
  rw [forwardObj_of_decodeForward hs o x t p B h]
  rfl

/-- Decoding the same canonical block under two digest tables agrees when they agree
on that block's header; this is the root-sensitive replacement for wire injectivity. -/
theorem decodeBlock_transport {hs hs' : List (Header Info × Nat)} {o : Wire sp.n binding}
    {B : Blk sp} (hd : decodeBlock sp hs o = some B)
    (hr : rootOf hs' (headerOf sp B) = rootOf hs (headerOf sp B)) :
    decodeBlock sp hs' o = some B := by
  obtain rfl := eq_blockObj_of_decodeBlock hd
  rw [decodeBlock_eq] at hd ⊢
  simp only [blockObj_eq] at hd ⊢
  rw [hr]
  exact hd

/-- Forwarding decode is unchanged when both digest tables agree on every
canonical child carried by the envelope, including its recursive parent chain. -/
theorem decodeForward_transport {hs hs' : List (Header Info × Nat)} :
    ∀ (B : Blk sp) (o : Wire sp.n binding) (x : Fin sp.n) (t : Time) (p : Option
        (Wire sp.n binding)),
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

/-- A single delivered object can create a wrapper only through its actual canonical
handler. This keeps the handler state needed to locate the cut in recursive processing. -/
private theorem processOne_forward_origin (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n))
    (io : VoteAuth sp.n binding)
    (hs : List (Header Info × Nat)) (st : State sp binding) (o : Wire sp.n binding)
    (q : Time × List (Wire sp.n binding)) (hq : q ∈ (processOne io hs st o).forwards) :
    q ∈ st.forwards ∨ ∃ e B, ∃ p : Option (Wire sp.n binding),
      canonEvent sp io hs o = some e ∧
      .fg (.block B true) ∈ (exec proposer dg st.self st.node st.now e).2 ∧
      q = (st.now, p.toList ++ [blockObj sp B]) := by
  have hrelay : ∀ (s : State sp binding) (c : Prop) [Decidable c],
      (relayIf s c o).forwards = s.forwards := by
    intro s c _
    unfold relayIf
    split <;> rfl
  rcases canonEvent_cases io hs o with he | ⟨B, he⟩ | ⟨v, he⟩ | ⟨a, he⟩
  · exact Or.inl (by simpa only [AsChainShape.processOne_eq, he] using hq)
  all_goals
    simp only [AsChainShape.processOne_eq, he, hrelay] at hq
    rcases apply_forward_origin _ _ _ q hq with h | ⟨C, p, hm, hq⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, C, p, he, hm, hq⟩

/-- A successful canonical handler cut names the exact decoded input block. -/
private theorem accepted_canonEvent_block (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n))
    (io : VoteAuth sp.n binding)
    (hs : List (Header Info × Nat)) (st : State sp binding) (o : Wire sp.n binding)
    {e : Event (goldilocksNode sp)} {B : Blk sp}
    (he : canonEvent sp io hs o = some e)
    (hb : .fg (.block B true) ∈ (exec proposer dg st.self st.node st.now e).2) :
    decodeBlock sp hs o = some B := by
  rcases canonEvent_cases io hs o with h | ⟨C, h⟩ | ⟨v, h⟩ | ⟨a, h⟩
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
    (dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n))
    (io : VoteAuth sp.n binding)
    (hs : List (Header Info × Nat)) (i : Nat) (q : Time × List (Wire sp.n binding)) :
    ∀ (os : List (Wire sp.n binding)) (st : State sp binding) (sub : Nat),
    q ∈ (os.foldl (processOne io hs) st).forwards →
    q ∈ st.forwards ∨ ∃ B, ∃ p : Option (Wire sp.n binding), ∃ r,
      r ∈ deliverRecs io proposer dg hs st.self st.now i os st.node sub ∧
      r.label = .fg (.block B true) ∧ r.node = st.self ∧ r.time = st.now ∧
      q = (st.now, p.toList ++ [blockObj sp B]) ∧
      decodeBlock sp (binding := binding) hs (blockObj sp B) = some B ∧ blockObj sp B ∈ os := by
  intro os
  induction os with
  | nil => intro st sub h; exact Or.inl h
  | cons o os ih =>
    intro st sub h
    rcases ih (processOne io hs st o) (sub + 1) h with h | ⟨B, p, r, hm, hl, hn, ht, hq, hd, ho⟩
    · rcases processOne_forward_origin proposer dg io hs st o q h with h | ⟨e, B, p, he, hm, hq⟩
      · exact Or.inl h
      · obtain ⟨j, hj, hlabel⟩ := List.getElem_of_mem hm
        have hj' : j <
            (groupRecs proposer dg st.self st.node st.now (Nat.pair i sub) e).length := by
          rwa [length_groupRecs]
        obtain ⟨hn, ht, _, _, hl⟩ :=
          getElem_groupRecs proposer dg st.self st.node st.now (Nat.pair i sub) e j hj'
        have hd := accepted_canonEvent_block proposer dg io hs st o he hm
        have hd' : decodeBlock sp (binding := binding) hs (blockObj sp B) = some B := by
          rwa [eq_blockObj_of_decodeBlock hd] at hd
        refine Or.inr ⟨B, p, _, ?_, hl.trans hlabel, hn, ht, hq, hd', ?_⟩
        · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ _ he]
          exact List.mem_append_left _ (List.getElem_mem hj')
        · rw [eq_blockObj_of_decodeBlock hd]
          exact List.mem_cons_self
    · simp only [processOne_self, processOne_now] at hm hn ht hq
      rw [processOne_node proposer dg] at hm
      refine Or.inr ⟨B, p, r, ?_, hl, hn, ht, hq, hd, List.mem_cons_of_mem _ ho⟩
      cases he : canonEvent sp io hs o with
      | none =>
        rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ _ he]
        simpa only [he] using hm
      | some e =>
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ _ he]
        exact List.mem_append_right _ (by simpa only [he] using hm)

end Consensus.Goldilocks.Simulation
