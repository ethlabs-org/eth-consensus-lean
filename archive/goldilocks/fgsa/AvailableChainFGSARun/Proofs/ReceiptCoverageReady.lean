module
public import AvailableChainFGSARun.Statements.ReceiptCoverage
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainFGSARun.Proofs.Content -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.Head -- shake: keep (re-export)
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem t712_cumulative (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hNR : V2.D.NoRestart rho) (x : V) {i j : Nat} (hij : i ≤ j) :
    let a := (V2.D.Run.stateBefore E rho i x).st
    let b := (V2.D.Run.stateBefore E rho j x).st
    a.fg.TF ⊆ b.fg.TF ∧ a.base.votes ⊆ b.base.votes ∧
      a.base.voteStamp <+: b.base.voteStamp := by
  let a := (V2.D.Run.stateBefore E rho i x).st
  apply V2.D.Engine.stateBefore_stable (P := fgsa p c)
    (fun nd => a.fg.TF ⊆ nd.st.fg.TF ∧ a.base.votes ⊆ nd.st.base.votes ∧
      a.base.voteStamp <+: nd.st.base.voteStamp)
    ?_ ?_ (fun _ _ h => h) E rho hij x (hNR.restartFree x i j)
    ⟨subset_rfl, List.Subset.refl _, List.prefix_refl _⟩
  · intro nd t h
    change a.fg.TF ⊆ (clock p nd.st t).fg.TF ∧
      a.base.votes ⊆ (clock p nd.st t).base.votes ∧
      a.base.voteStamp <+: (clock p nd.st t).base.voteStamp
    rw [(clock_cumulative p nd.st t).1, (clock_vn nd.st t).1,
      (clock_cumulative p nd.st t).2.2.2.1]
    exact h
  · intro nd o h
    have hc := process_cumulative p nd.st (toWire p o)
    exact ⟨(fun _ hm => hc.1 (h.1 hm)),
      List.Subset.trans h.2.1 (process_votes_subset nd.st (toWire p o)),
      h.2.2.trans hc.2.2.2.1⟩

private theorem t712_stamp_kept (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (i j : Nat) (v : GridCO.Wire p.n .root)
    (hm : v ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes)
    (hp : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp <+:
      (V2.D.Run.stateBefore E rho j x).st.base.voteStamp) :
    GridCO.stampVote (V2.D.Run.stateBefore E rho j x).st.base v =
      GridCO.stampVote (V2.D.Run.stateBefore E rho i x).st.base v := by
  rw [← fgsa_vote_stamp_keys E rho i x] at hm
  obtain ⟨⟨v', t⟩, ht, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst v'
  obtain ⟨tail, htail⟩ := hp
  unfold GridCO.stampVote
  rw [← htail, List.find?_append]
  cases hf : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.find?
      (fun row => row.1 == v) with
  | none =>
      have hn := List.find?_eq_none.mp hf (v, t) ht
      simp only [beq_self_eq_true] at hn
      contradiction
  | some row => rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[P23-A] Ready K8 receipt coverage at the strict deadline read (bp00:700–713;
bp01:858–930). Each path vertex and HEAD keeps its own receipt deadline. -/
theorem fgsa_receiptCoverage_ready :
  ∀ {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop),
    NamedReceiptRootCollisionFree p c E rho → E.Δ = p.Δ → V2.D.ExecutionValid E rho
      → V2.D.NoRestart rho
      → x ∈ rho.honest →
    (∀ o t, required o t → ∀ u, t ≤ u → u < dl t → E.awake x u = true) →
    ReceiptCoveragePremises E rho dl cut D first x B required paths →
    let st := (V2.D.Run.stateBeforeTime E rho D x).st
    ((Block.Preceq B (eraseFG st.fg.F) ∧
      Block.Preceq B st.base.stableRecord ∧
      (∀ s, 0 < s → Block.Preceq B (headVote p st s)) ∧
      (∀ raw sup, Block.Preceq B (getHead p st raw sup)) ∧
      Block.Preceq B (fgHead p st) ∧
      (∀ lease ∈ st.base.obligations, Block.Compatible B lease.1)) ∨
     (Block.Preceq (eraseFG st.fg.F) B ∧
      (∀ o t s N, required o t →
        (toWire p o).decode = some (.block s N) →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.fg.TF, eraseFG Y = N.erase) ∧
      (∀ K d, paths K d → ∀ b, Block.Preceq b K →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF, eraseFG Y = b))) ∧
    (∀ o t s a K, required o t → (toWire p o).decode = some (.vote s a K) →
      let v := baseVote (⟨.seat (.head s) a, K⟩ : HeadWire p.n)
      (v ∈ st.base.votes ∧ GridCO.stampVote st.base v < dl t) ∨
      ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
        v₁ ≠ v₂ ∧ GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
        GridCO.headSeat? v₁ = some a ∧ GridCO.headSeat? v₂ = some a ∧
        GridCO.stampVote st.base v₁ < dl t ∧ GridCO.stampVote st.base v₂ < dl t) := by
  intro p In V inst c E rho dl cut D first x B required paths hRoots hDelta hExecution hNR
    hx hAwake h
  have hS := hExecution.toScheduleWellFormed
  have hidx : Monotone (V2.D.Run.idxBefore rho) := by
    intro a b hab
    rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    exact decide_eq_true (lt_of_lt_of_le (of_decide_eq_true he) hab)
  have hc (a b : Time) (hab : a ≤ b) :
      let sa := (V2.D.Run.stateBeforeTime E rho a x).st
      let sb := (V2.D.Run.stateBeforeTime E rho b x).st
      sa.fg.TF ⊆ sb.fg.TF ∧ sa.base.votes ⊆ sb.base.votes ∧
        sa.base.voteStamp <+: sb.base.voteStamp := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho a hS,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho b hS]
    exact t712_cumulative E rho hNR x (hidx hab)
  have hf (a : Time) (ha : a ≤ D) :
      Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho a x).st.fg.F)
        (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho a hS,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho D hS]
    have hm := fgsa_monoAlong_preceq_F p c (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho a) x).st.fg.F
    rw [Gen.V2.Duty.MonoAlong_def] at hm
    exact eraseFG_preceq (V2.D.Engine.stateBefore_stable _ hm.1 hm.2.1 hm.2.2
      E rho (hidx ha) x (hNR.restartFree x _ _) (KitFG.preceq_refl _))
  have hstore := storeBundle_stateBeforeTime E rho D x
  constructor
  · have hcompat := h.compat _ h.deadline.2.2.2.1 (le_refl _)
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hS] at hcompat
    change (Block.preceq B (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) ||
      Block.preceq (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) B) = true at hcompat
    simp only [Bool.or_eq_true] at hcompat
    rcases hcompat with hBF | hFB
    · left
      refine ⟨hBF, Gen.Pure.block_preceq_trans hBF hstore.nest,
        (fun s hs => preceq_headVote_of_preceq_F p _ hstore.cstore hBF hs),
        preceq_getHead_of_preceq_F p _ hstore.cstore hBF,
        preceq_fgHead_of_preceq_F p _ hstore.cstore hBF, ?_⟩
      intro lease hl
      have hlc := hstore.cstore.saCompat.1 lease hl
      change Block.compatible lease.1 _ = true at hlc
      rw [Gen.Pure.block_compatible_comm] at hlc
      exact Gen.Pure.block_compatible_of_preceq_compatible hBF hlc
    · right
      have hproposal : ∀ o t s N, required o t →
          (toWire p o).decode = some (.block s N) →
          ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.fg.TF, eraseFG Y = N.erase := by
        intro o t s N hr hd
        obtain ⟨K, d, hk, hbK⟩ := h.deadline.2.2.2.2.2.2 o t s N hr hd
        have hBK := (h.deadline.2.2.2.2.2.1 K d hk).1
        have ht := h.deadline.2.2.2.2.1 o t hr
        have hFK := Gen.Pure.block_preceq_trans
          (Gen.Pure.block_preceq_trans (hf (dl t) ht.2.2.2) hFB) hBK
        have hbF := Gen.Pure.block_compatible_of_common hbK hFK
        have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
          apply toWire_injective
          rw [toWire_ofWire]
          exact decode_eq_block.mp hd
        have htrigger := (h.slotWindow o t hr).1
        rw [ho] at htrigger
        exact fgsa_proposal_receipt E rho hRoots hDelta hExecution hNR dl cut s N t x
          h.within htrigger hx (ht.2.2.2.trans h.deadline.2.1) ht.2.2.1 hbF
          (ht.2.2.2.trans (h.deadline.2.1.trans h.deadline.2.2.1))
          (hAwake o t hr)
      refine ⟨hFB, hproposal, ?_⟩
      intro K d hk b hb
      by_cases hg : b = .genesis
      · subst b
        exact ⟨.genesis, (storeBundle_stateBeforeTime E rho d x).cstore.fg.gen, rfl⟩
      · obtain ⟨o, t, s, N, heN, hr, hd, htd⟩ :=
          (h.deadline.2.2.2.2.2.1 K d hk).2.2 b hb hg
        obtain ⟨Y, hY, he⟩ := hproposal o t s N hr hd
        exact ⟨Y, (hc (dl t) d htd).1 hY, he.trans heN⟩
  · intro o t s a K hr hd
    have ht := h.deadline.2.2.2.2.1 o t hr
    have hw := h.slotWindow o t hr
    have ho : o = ofHead p ⟨.seat (.head s) a, K⟩ := by
      apply toWire_injective
      rw [toWire_ofHead]
      exact decode_eq_vote.mp hd
    have htrigger := hw.1
    rw [ho] at htrigger
    have hreceipt := fgsa_head_receipt E rho hDelta hExecution hNR dl cut s a K t x
      h.within htrigger hx (ht.2.2.2.trans h.deadline.2.1) ht.2.2.1
      (hw.2.2 s a K hd).1
      (ht.2.2.2.trans (h.deadline.2.1.trans h.deadline.2.2.1)) (hAwake o t hr)
    have hcum := hc (dl t) D ht.2.2.2
    have hstamp (v : GridCO.Wire p.n .root)
        (hm : v ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.base.votes) :
        GridCO.stampVote (V2.D.Run.stateBeforeTime E rho D x).st.base v =
          GridCO.stampVote (V2.D.Run.stateBeforeTime E rho (dl t) x).st.base v := by
      have hp := hcum.2.2
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hS] at hm hp ⊢
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho D hS] at hp ⊢
      exact t712_stamp_kept E rho x _ _ v hm hp
    rcases hreceipt with ⟨hm, hs⟩ | ⟨v₁, h₁, v₂, h₂, hn, hl₁, hl₂, ha₁, ha₂, hs₁, hs₂⟩
    · exact Or.inl ⟨hcum.2.1 hm, (hstamp _ hm).trans_lt hs⟩
    · exact Or.inr ⟨v₁, hcum.2.1 h₁, v₂, hcum.2.1 h₂, hn, hl₁, hl₂, ha₁, ha₂,
        (hstamp _ h₁).trans_lt hs₁, (hstamp _ h₂).trans_lt hs₂⟩

end AvailableChain.FGSA.Run
