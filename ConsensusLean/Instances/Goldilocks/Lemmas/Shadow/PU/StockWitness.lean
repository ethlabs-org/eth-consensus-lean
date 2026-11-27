module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.OptimisticWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.StockWindow
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The early-witness family over the stock window (interface)

Route (i) for the stock window: the later-heads family of `WitnessFamily` and
`OptimisticWitness`, read over the stock `Generic.FrameWindow … floor kindJ J` with the stock
witness `floor ≤ σ(Q).h ∧ (kindJ → J ⪯ Q)` in place of P-U viability (`hvQ`). The stock witness
is P-U viable at every honest reader of the window: `floor ≥ h_max − 1` at each reader, and at a
top reader at height `h_max − 1` the window is in its J-kind, where `J` is pinned. So no window
is split and no constant `h_max` or top is read. The `hvQ` forms are kept.

The stock window and witness give a `WindowWitness` (`windowWitness_of_stock`), and each stock form
is the window-free core of its `hvQ` form (`…_of_windowWitness_at'`) at it.

`optimistic_supporter_later_heads_stock_at'` is open: its witness is a P-U viable head of the
supporter's cast frame (the anchor's viable descendant), not a stock witness. At a contesting
caster (`h_max = floor`) it can sit at `floor − 1`, below the stock witness's floor. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- A stock window's witness `floor ≤ σ(X).h ∧ (kindJ → J ⪯ X)` places every honest finalized tip in
the window below an independently held descendant (`FrameWindow'.finalized_below_descendant_at'`
with the stock window and witness). -/
theorem finalized_below_descendant_stock_at {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x z : Fin sp.n} {j i c : Nat}
    (hy : y ∈ H (tr.time j)) (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    (hf : (H (max (tr.time j) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hjlo : lo ≤ tr.time j) (hjhi : tr.time j ≤ hi)
    {X W : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hwit : floor ≤ ((tr.state z c).fg.σ X.root).h ∧
      (kindJ → Anc (tr.HonestBlocksAt H) J X))
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocksAt H) X W) :
    Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F W := by
  have hjt := hrun.time_nonneg j
  have hbj : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hrun.time_mono hq.le
  have hr := Compose.Growing.reachable_at' hrun hjt hy hbj
  have hfl := hframe.floor_eq y j hy hjlo hjhi
  have hkind := hframe.kind_iff y j hy hjlo hjhi
  have hjm := Store.hj_lt_hmax_of_reachable_with Store.finalitySpec_updateFinality
    hr.reachableWith
  by_cases hk : kindJ
  · have hFJ := (Store.cache_invariants' hr).2.2.1
    rw [hframe.root_eq y j hy hjlo hjhi hk] at hFJ
    exact (hFJ.mono (Compose.Growing.tree_held_at' hjt hy hbj)).trans ((hwit.2 hk).trans hXW)
  have hWh := Growing.le_height_of_honest_ancestor_at hrun hnc hx hz hX le_rfl hW hXW
  refine Growing.finalized_below_of_hj_lt_at hrun hnc hy hx hf hW ?_
  have hlt : (tr.state y j).fg.hj < floor := by
    by_cases hC : (tr.state y j).fg.Contest
    · rw [Store.headHeightFloor, ite_eq_left hC] at hfl
      have := hC.1
      omega
    · rw [Store.headHeightFloor, ite_eq_right hC] at hfl
      have htop : (tr.state y j).fg.hmax ≠ (tr.state y j).fg.hj + 1 :=
        fun h => hk (hkind.1 ⟨h, hC⟩)
      omega
  have := hwit.1
  omega

/-- The stock witness of a held block is a witness of a stock window: at every honest reader of
the window holding it, `F ⪯ Q` (`finalized_below_descendant_stock_at'`) and `Q` is P-U viable,
since `h_max − 1 ≤ floor` at each reader and a top reader at `h_max − 1` is in the J-kind. -/
theorem windowWitness_of_stock
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))} (hframe : Generic.FrameWindow tr H lo hi floor kindJ J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c)) {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hwit : floor ≤ ((tr.state z c).fg.σ Q.root).h ∧ (kindJ → Anc (tr.HonestBlocksAt H) J Q)) :
    WindowWitness tr H lo hi Q := by
  refine ⟨fun y j hy hlo hhi hm hQy =>
    ⟨finalized_below_descendant_stock_at hframe hrun hnc hy hy hz (by rwa [max_self]) hlo hhi
      hQ hwit hQy .refl, ?_⟩⟩
  have hjt := hrun.time_nonneg j
  have hbj : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hrun.time_mono hq.le
  have hr := Compose.Growing.reachable_at' hrun hjt hy hbj
  have hσ := Growing.σ_eq_honest_at' hrun hnc (hrun.time_nonneg c)
    (fun _ hq => hrun.time_mono hq.le) hz hjt hbj hy hQ hQy
  have hfl := hframe.floor_eq y j hy hlo hhi
  have hkind := hframe.kind_iff y j hy hlo hhi
  have hjm := Store.hj_lt_hmax_of_reachable_with Store.finalitySpec_updateFinality
    hr.reachableWith
  have hh := hwit.1
  rw [hσ] at hh
  rw [Store.isViable_iff]
  by_cases hC : (tr.state y j).fg.Contest
  · rw [Store.headHeightFloor, ite_eq_left hC] at hfl
    exact Or.inl (by omega)
  rw [Store.headHeightFloor, ite_eq_right hC] at hfl
  rcases Nat.lt_or_ge ((tr.state y j).fg.σ Q.root).h (tr.state y j).fg.hmax with hlt | hge
  · refine Or.inr ⟨by omega, ?_⟩
    by_cases htop : (tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1
    · right
      have hk := hkind.1 ⟨htop, hC⟩
      rw [hframe.root_eq y j hy hlo hhi hk]
      exact Growing.store_anc_of_honest_anc_at' hrun hnc hjt hbj hy (hwit.2 hk) hQy
    · left
      omega
  · exact Or.inl hge

/-- **A stock witness above a floor anchor**: a block held at an honest reader of a stock window,
above its finalized tip and above an honestly held anchor `P` with
`floor ≤ σ(P).h ∧ (kindJ → floor < σ(P).h)` (`warm_proposal_bounds_at'` for a warm proposal), is a
stock witness: heights grow along held ancestry, and in the J-kind its height is `h_max`, where no
contest puts it off `J`. The shared floor-anchor premise of the stock later-head suppliers. -/
theorem stock_witness_of_floor_anchor_at {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {kP : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hp : p ∈ H (tr.time kP))
    (hPp : P ∈ (tr.state p kP).fg.tree)
    (hPfl : floor ≤ ((tr.state p kP).fg.σ P.root).h ∧
      (kindJ → floor < ((tr.state p kP).fg.σ P.root).h))
    {y : Fin sp.n} {a : Nat} (hy : y ∈ H (tr.time a)) (hlo : lo ≤ tr.time a)
    (hhi : tr.time a ≤ hi) {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ (tr.state y a).fg.tree) (hFQ : (tr.state y a).fg.Anc (tr.state y a).fg.F Q)
    (hPQ : Anc (tr.HonestBlocksAt H) P Q) :
    floor ≤ ((tr.state y a).fg.σ Q.root).h ∧ (kindJ → Anc (tr.HonestBlocksAt H) J Q) := by
  refine ⟨Growing.le_height_of_honest_ancestor_at hrun hnc hy hp hPp hPfl.1 hQ hPQ, fun hk => ?_⟩
  have ht0 := hrun.time_nonneg a
  have hba : ∀ q < a, tr.time q ≤ tr.time a := fun q hq => hrun.time_mono hq.le
  have hr := Compose.Growing.reachable_at' hrun ht0 hy hba
  have hgt := Growing.le_height_of_honest_ancestor_at hrun hnc hy hp hPp (hPfl.2 hk) hQ hPQ
  obtain ⟨htop, hnC⟩ := (hframe.kind_iff y a hy hlo hhi).2 hk
  have hfl := hframe.floor_eq y a hy hlo hhi
  rw [Store.headHeightFloor, ite_eq_right hnC] at hfl
  have hle := (Store.cache_invariants' hr).2.2.2.2.1 Q hQ
  have hJy : (tr.state y a).fg.Anc (tr.state y a).fg.J Q := by
    by_contra hnJ
    exact hnC ⟨htop, Q, hQ, hFQ, by omega, hnJ⟩
  rw [← hframe.root_eq y a hy hlo hhi hk]
  exact hJy.mono (Compose.Growing.tree_held_at' ht0 hy hba)

/-- The frame geometry of a stock witness at a reader's cut (`witness_frame_at'` with the stock
window and witness): the stock witness is P-U viable at every honest reader of the window. -/
theorem witness_frame_stock_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))} (hframe : Generic.FrameWindow tr H lo hi floor kindJ J)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hlo : lo ≤ tr.time i) (hhi : tr.time i ≤ hi)
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQy : Q ∈ (tr.state y i).fg.tree)
    (hwit : floor ≤ ((tr.state y i).fg.σ Q.root).h ∧
      (kindJ → Anc (tr.HonestBlocksAt H) J Q))
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) :
    Anc (tr.HonestBlocksAt H) X ell.frame.F ∨
      (Anc (tr.HonestBlocksAt H) ell.frame.F X ∧ X ∈ ell.frame.tree ∧
        ell.frame.Anc ell.frame.fcRoot X ∧ Q ∈ ell.frame.tree ∧ Q ∈ ell.frame.viableHeads ∧
        ell.frame.Anc X Q) := by
  obtain ⟨hFQ, hv⟩ := (windowWitness_of_stock hrun hnc hframe hy hQy hwit).held y i hy hlo hhi
    hf hQy
  exact witness_frame_of_held hrun hnc hy hc hQy hFQ hv hXQ

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {hold : Time}

/-- `unanimous_next_votes_of_witness_at'` with the stock window and witness. -/
theorem unanimous_next_votes_of_stock_witness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m floor : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) floor kindJ J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hwit : floor ≤ ((tr.state z c).fg.σ Q.root).h ∧
      (kindJ → Anc (tr.HonestBlocksAt H) J Q))
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hheld : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → Q ∈ (tr.state y i).fg.tree ∧
        e.readPoint.blockStamp Q.root < AC.ETime.of (AC.freeze sp (m + 1)))
    (hG : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  exact unanimous_next_votes_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb
    (Healing.windowWitness_of_stock hrun hnc hframe hz hQ hwit) hXQ hheld hG hK

/-- `unanimous_next_proposal_of_witness_at'` with the stock window and witness. -/
theorem unanimous_next_proposal_of_stock_witness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m floor : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) floor kindJ J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hwit : floor ≤ ((tr.state z c).fg.σ Q.root).h ∧
      (kindJ → Anc (tr.HonestBlocksAt H) J Q))
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hG : ∀ x j e, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j e →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (m + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hQy : Q ∈ (tr.state y i).fg.tree) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  exact unanimous_next_proposal_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb
    (Healing.windowWitness_of_stock hrun hnc hframe hz hQ hwit) hXQ hG hy hc hcall hti hd hQy hK

/-- `next_votes_of_early_witness_at'` with the stock window and the stock witness at the early
writer. -/
theorem next_votes_of_stock_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} {hi : Time} (hm : gbar g ≤ sp.ts s)
    (hnext : sp.ts (s + 1 : Nat) + sp.Δ ≤ hi) (hmb : hi ≤ b)
    {kindJ : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s) hi floor kindJ J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (_halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (htransfer : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      e.msg.slot = s + 1 → tr.time i ≤ hi →
      Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).F X →
      AC.ViableAtVote ell e (s + 1) X →
      (∀ z k ev, k < i → z ∈ H (tr.time k) → AC.VoteAt tr.projAC z k ev →
        ev.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X) →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hahi : tr.time a ≤ hi := by
    linarith only [hat, AC.ts_succ s (sp := sp), hnext, sp.toParams.hΔ]
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    have h := hQw
    rw [frame_of_projAC_at hrun hw hcw, Node.frame_eq, Store.toFrame_tree] at h
    exact h.1
  exact next_votes_of_windowWitness_at hrun hnc hsvc _hawake hf hcatch hm hnext hmb hw hat hcw
    hQw (Healing.windowWitness_of_stock hrun hnc hframe hw hQ ⟨hh, hJ⟩)
    (fun y i hy hlo hhi => Healing.finalized_below_descendant_stock_at hframe hrun hnc hy hw hw
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le (hhi.trans hmb)
          (hahi.trans hmb)))) hlo hhi hQ ⟨hh, hJ⟩ hQ .refl) hXQ htransfer

/-- `later_heads_of_early_witness_at'` with the stock window and the stock witness at the early
writer. -/
theorem later_heads_of_stock_witness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s) (sp.ts N + sp.Δ) floor kindJ J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (_halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hbase : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (s + 2 ≤ r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  intro r hrlo hrN
  have hsN : sp.ts (s + 1 : Nat) ≤ sp.ts N :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hrlo.trans hrN)
  have hahi : tr.time a ≤ sp.ts N + sp.Δ := by
    linarith only [hat, AC.ts_succ s (sp := sp), hsN, sp.toParams.hΔ]
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    have h := hQw
    rw [frame_of_projAC_at hrun hw hcw, Node.frame_eq, Store.toFrame_tree] at h
    exact h.1
  exact later_heads_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb hw hat hcw
    hQw (Healing.windowWitness_of_stock hrun hnc hframe hw hQ ⟨hh, hJ⟩)
    (fun y i hy hlo hhi => Healing.finalized_below_descendant_stock_at hframe hrun hnc hy hw hw
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le (hhi.trans hmb)
          (hahi.trans hmb)))) hlo hhi hQ ⟨hh, hJ⟩ hQ .refl) hXQ hbase hK r hrlo hrN

/-- `optimistic_next_votes_of_early_witness_at'` with the stock window and witness. -/
theorem optimistic_next_votes_of_stock_witness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (_halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hahi : tr.time a ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
    linarith only [hat, AC.ts_succ s (sp := sp), sp.toParams.hΔ]
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    have h := hQw
    rw [frame_of_projAC_at hrun hw hcw, Node.frame_eq, Store.toFrame_tree] at h
    exact h.1
  exact optimistic_next_votes_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hm hmb hx hopt
    hXD hw hat hcw hQw (Healing.windowWitness_of_stock hrun hnc hframe hw hQ ⟨hh, hJ⟩)
    (fun y i hy hlo hhi => Healing.finalized_below_descendant_stock_at hframe hrun hnc hy hw hw
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le (hhi.trans hmb)
          (hahi.trans hmb)))) hlo hhi hQ ⟨hh, hJ⟩ hQ .refl) hXQ hK

/-- `optimistic_next_proposal_of_early_witness_at'` with the stock window and witness. -/
theorem optimistic_next_proposal_of_stock_witness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts (s + 1 : Nat) ≤ b)
    {kindJ : Prop} {J X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s) (sp.ts (s + 1 : Nat)) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (_halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (s + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  have hahi : tr.time a ≤ sp.ts (s + 1 : Nat) := by
    linarith only [hat, AC.ts_succ s (sp := sp), sp.toParams.hΔ]
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    have h := hQw
    rw [frame_of_projAC_at hrun hw hcw, Node.frame_eq, Store.toFrame_tree] at h
    exact h.1
  exact optimistic_next_proposal_of_windowWitness_at hrun hnc hsvc _hawake hf hcatch hm hmb hx
    hopt hXD hw hat hcw hQw (Healing.windowWitness_of_stock hrun hnc hframe hw hQ ⟨hh, hJ⟩)
    (fun y i hy hlo hhi => Healing.finalized_below_descendant_stock_at hframe hrun hnc hy hw hw
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le (hhi.trans hmb)
          (hahi.trans hmb)))) hlo hhi hQ ⟨hh, hJ⟩ hQ .refl) hXQ hy hc hcall hti hd hK

/-- `optimistic_later_heads_of_early_witness_at'` with the stock window and witness. -/
theorem optimistic_later_heads_of_stock_witness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s) (sp.ts N + sp.Δ) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (_halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  intro r hrlo hrN
  have hsN : sp.ts (s + 1 : Nat) ≤ sp.ts N :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hrlo.trans hrN)
  have hahi : tr.time a ≤ sp.ts N + sp.Δ := by
    linarith only [hat, AC.ts_succ s (sp := sp), hsN, sp.toParams.hΔ]
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    have h := hQw
    rw [frame_of_projAC_at hrun hw hcw, Node.frame_eq, Store.toFrame_tree] at h
    exact h.1
  exact optimistic_later_heads_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb
    hx hopt hXD hw hat hcw hQw (Healing.windowWitness_of_stock hrun hnc hframe hw hQ ⟨hh, hJ⟩)
    (fun y i hy hlo hhi => Healing.finalized_below_descendant_stock_at hframe hrun hnc hy hw hw
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le (hhi.trans hmb)
          (hahi.trans hmb)))) hlo hhi hQ ⟨hh, hJ⟩ hQ .refl) hXQ hK r hrlo hrN

/-- `optimistic_supporter_later_heads_at'` with the stock window. -/
theorem optimistic_supporter_later_heads_stock_at {s₀ s N floor : Nat}
    {kindJ : Prop} {J L D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s) (hs₀ : s₀ ≤ s) (hsN : s + 1 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} {i a : Nat} (hx : x ∈ H (tr.time i)) (hxa : x ∈ H (tr.time a))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC x i ell e) (hes : e.msg.slot = s)
    (hanchor : L = AC.getAnchor sp e.readPoint ell.frame (tr.time i))
    {CV : Set (AC.Vote sp.n)} (hop : AC.OptimisticLockAt tr.projAC x a s D CV)
    (hLD : Anc (tr.HonestBlocksAt H) L D) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y j ev, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j ev → ev.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg L) ∧
      (∀ y j ell', y ∈ H (tr.time j) → tr.projAC.CallAt y j ell' → ell'.call = .proposal →
        tr.time j = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y j) ell'.frame (tr.time j)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) L d.head) := by
  -- The supporter's witness is the anchor's P-U viable head in its cast frame, possibly at
  -- `floor − 1` at a contesting caster; route (i) needs `floor ≤ σ(Q).h`. Open.
  sorry

/-- **An optimistic supporter's anchor over the stock window, above a floor anchor**
(`optimistic_supporter_later_heads_at'` with the stock window): the anchor `L` extends an honestly
held `P` with `floor ≤ σ(P).h ∧ (kindJ → floor < σ(P).h)`, so the viable head above it is a stock
witness (`stock_witness_of_floor_anchor_at'`). -/
theorem optimistic_supporter_later_heads_floor_stock_at {s₀ s N floor : Nat}
    {kindJ : Prop} {J L D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s) (hs₀ : s₀ ≤ s) (hsN : s + 1 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} {i a : Nat} (hx : x ∈ H (tr.time i)) (hxa : x ∈ H (tr.time a))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC x i ell e) (hes : e.msg.slot = s)
    (hanchor : L = AC.getAnchor sp e.readPoint ell.frame (tr.time i))
    {CV : Set (AC.Vote sp.n)} (hop : AC.OptimisticLockAt tr.projAC x a s D CV)
    (hLD : Anc (tr.HonestBlocksAt H) L D)
    {p : Fin sp.n} {kP : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hp : p ∈ H (tr.time kP)) (hPp : P ∈ (tr.state p kP).fg.tree)
    (hPfl : floor ≤ ((tr.state p kP).fg.σ P.root).h ∧
      (kindJ → floor < ((tr.state p kP).fg.σ P.root).h))
    (hPL : Anc (tr.HonestBlocksAt H) P L) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y j ev, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j ev → ev.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg L) ∧
      (∀ y j ell', y ∈ H (tr.time j) → tr.projAC.CallAt y j ell' → ell'.call = .proposal →
        tr.time j = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y j) ell'.frame (tr.time j)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) L d.head) := by
  have hts : sp.ts s₀ ≤ sp.ts s := (AC.ts_le_iff sp).2 (by exact_mod_cast hs₀)
  have htN : sp.ts s ≤ sp.ts N :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast (show s ≤ N by omega))
  obtain ⟨hlo, hhi, Q, hQ, -, hLQ⟩ := supporter_anchor_viable_head_at hrun hnc hf
    (by linarith only [htN, hmb]) hx hc hes hanchor
  have hQt := hQ
  rw [frame_of_projAC_at hrun hx hc.1, Node.frame_eq, Store.toFrame_tree] at hQt
  obtain ⟨hh, hJ⟩ := Healing.stock_witness_of_floor_anchor_at hframe hrun hnc hp hPp hPfl hx
    (hts.trans hlo) (by linarith [sp.toParams.hΔ]) hQt.1 hQt.2 (hPL.trans hLQ)
  have hsub : Generic.FrameWindow tr H (sp.ts s) (sp.ts N + sp.Δ) floor kindJ J :=
    ⟨fun y j hy hl hh => hframe.floor_eq y j hy (hts.trans hl) hh,
     fun y j hy hl hh => hframe.kind_iff y j hy (hts.trans hl) hh,
     fun y j hy hl hh => hframe.root_eq y j hy (hts.trans hl) hh⟩
  exact optimistic_later_heads_of_stock_witness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb
    hsub hxa hop hLD hx hlo (by linarith [sp.toParams.hΔ]) hc.1 hQ hh hJ hLQ hK

end Consensus.Goldilocks.Shadow.PU.Growing

end
