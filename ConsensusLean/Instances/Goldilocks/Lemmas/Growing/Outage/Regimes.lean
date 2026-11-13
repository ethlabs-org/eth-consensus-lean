module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageReader
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageDelivery
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the extending majority and the delivery halves

* `ExtendingMajorityAt.anti` (in the block), `ExtendingMajorityAt.anti_time` (a majority charged
  at `d` is one at every `d' ≤ d`), and `extendingMajority_of_all_at` (L4: when every vote of
  label `q` by a node honest at its cast extends `B`, the committee slot count `f_d < h_{t_q + Δ}`
  of the slot-`q` committee charged at `d ≥ t_q + Δ` gives the majority at `d`);
* `ReceiverServiceAfterAt.upTo`: the receiver service, for a receiver honest at `d`, is the static
  receiver service of the prefix through `d`;
* the delivery halves at a receiver call `c` from `t_q + 2Δ` with no restart after `t_q`, under the
  receiver service from `g ≤ t_q + Δ`: D1 `accepted_held_before_early_at` (a block genesis or
  accepted by `t_q + Δ` by a node honest at its acceptance), D2 `vote_pooled_before_early_at` and
  D3 `vote_resolved_before_early_at` (a slot-`q` vote by a node honest at its cast and still
  honest at the receiver call, classified at the reading cut). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-! ### The extending majority -/

/-- A vote extending `B` extends every block below `B`. -/
private theorem voteExtends_anti {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} {v : Vote sp.n}
    (hBB' : Anc U B' B) (h : SA.VoteExtends U v B) : SA.VoteExtends U v B' := by
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := h
  exact ⟨Hd, hHd, hHdr, hBB'.trans hBHd⟩

/-- **Downward monotonicity in the block**: from the protected origin to any block below it. -/
theorem ExtendingMajorityAt.anti {K : SA.CommitteeDict sp.n}
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat} {d : Time}
    (hBB' : Anc (tr.HonestBlocksAt H) B' B) (h : ExtendingMajorityAt tr H K B q d) :
    ExtendingMajorityAt tr H K B' q d := by
  rw [extendingMajorityAt_iff] at h ⊢
  have hO : OpponentsAt tr H B' q d ⊆ OpponentsAt tr H B q d := by
    intro x hx
    rcases opponentsAt_iff.1 hx with hx | ⟨hx, k, e, hv, hs, hne⟩
    · exact opponentsAt_iff.2 (Or.inl hx)
    · exact opponentsAt_iff.2 (Or.inr ⟨hx, k, e, hv, hs, fun h => hne (voteExtends_anti hBB' h)⟩)
  have hE : ExtendingCastersAt tr H B q d ⊆ ExtendingCastersAt tr H B' q d := by
    intro x hx
    obtain ⟨hx, k, e, hv, hs, hext⟩ := extendingCastersAt_iff.1 hx
    exact extendingCastersAt_iff.2 ⟨hx, k, e, hv, hs, voteExtends_anti hBB' hext⟩
  exact (Set.ncard_le_ncard (Set.inter_subset_inter_right _ hO) (Set.toFinite _)).trans_lt
    (h.trans_le (Set.ncard_le_ncard hE (Set.toFinite _)))

/-- **Downward monotonicity in the charging time**: a majority charged at `d` is a majority
charged at every `d' ≤ d` (a caster honest at `d` is honest at `d'`; an opponent honest at `d'`
is an opponent at `d` or compromised by `d`). -/
theorem ExtendingMajorityAt.anti_time (hanti : Antitone H) {K : SA.CommitteeDict sp.n}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat} {d d' : Time} (hd : d' ≤ d)
    (h : ExtendingMajorityAt tr H K B q d) : ExtendingMajorityAt tr H K B q d' := by
  rw [extendingMajorityAt_iff] at h ⊢
  have hO : OpponentsAt tr H B q d' ⊆ OpponentsAt tr H B q d := by
    intro x hx
    by_cases hxd : x ∈ H d
    · rcases opponentsAt_iff.1 hx with hx | ⟨-, k, e, hv, hs, hne⟩
      · exact absurd (hanti hd hxd) hx
      · exact opponentsAt_iff.2 (Or.inr ⟨hxd, k, e, hv, hs, hne⟩)
    · exact opponentsAt_iff.2 (Or.inl hxd)
  have hE : ExtendingCastersAt tr H B q d ⊆ ExtendingCastersAt tr H B q d' := by
    intro x hx
    obtain ⟨hx, h⟩ := extendingCastersAt_iff.1 hx
    exact extendingCastersAt_iff.2 ⟨hanti hd hx, h⟩
  exact (Set.ncard_le_ncard (Set.inter_subset_inter_right _ hO) (Set.toFinite _)).trans_lt
    (h.trans_le (Set.ncard_le_ncard hE (Set.toFinite _)))

/-- **L4, charged at `d`**: when every vote of label `q` by a node honest at its cast extends `B`,
the opponents at `d` in the slot-`q` committee are its members compromised by `d`, and the
extending casters at `d` hold every member honest at `d` that is awake and joined at `t_q + Δ`
(permitted to vote by the gate); the committee slot count charged at `d ≥ t_q + Δ` gives the
majority. -/
theorem extendingMajority_of_all_at
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : SA.CommitteeDict sp.n}
    (hGate : ∀ t, 0 ≤ t → ∀ x, x ∈ H t → ∀ i, (∀ k < i, tr.time k ≤ t) → ∀ s,
      ((tr.state x i).ac.mayVote s = true ↔ x ∈ K.committee s))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat} {d : Time}
    (hall : ∀ x k e, HVoteAt tr H x k e → e.msg.slot = q →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg B)
    (hd : sp.ts q + sp.Δ ≤ d) (hfb : SA.FaultBoundK K q tr.projAC (H d) (sp.ts q + sp.Δ)) :
    ExtendingMajorityAt tr H K B q d := by
  rw [extendingMajorityAt_iff]
  have hO : K.committee q ∩ OpponentsAt tr H B q d ⊆ K.committee q ∩ (H d)ᶜ := by
    rintro x ⟨hxK, hx⟩
    rcases opponentsAt_iff.1 hx with hx | ⟨-, k, e, hv, hs, hne⟩
    · exact ⟨hxK, hx⟩
    · exact absurd (hall x k e hv hs) hne
  have hE : K.committee q ∩ {y | y ∈ H d ∧ tr.projAC.awake y (sp.ts q + sp.Δ) ∧
      SA.JoinedAt tr.projAC y (sp.ts q + sp.Δ)} ⊆ ExtendingCastersAt tr H B q d := by
    rintro x ⟨hxK, hx, hw', hj'⟩
    obtain ⟨hw, hj⟩ := (mem_awakeJoined_projAC hrun).1 ⟨hw', hj'⟩
    obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joined_at hrun hnc (hrun.antitone hd hx)
      (mayVote_of_committee hGate (ts_add_delta_nonneg _) (hrun.antitone hd hx) hxK) hw hj
    exact extendingCastersAt_iff.2 ⟨hx, k, e, hv, hs, hall x k e hv hs⟩
  exact (Set.ncard_le_ncard hO (Set.toFinite _)).trans_lt
    (lt_of_lt_of_le hfb (Set.ncard_le_ncard hE (Set.toFinite _)))

/-! ### The receiver service in the prefix -/

/-- **The receiver service in the prefix**: for a receiver honest at `d ≥ 0`, the service after
`g` is the static receiver service of the prefix through `d`, for the validators honest at `d`. -/
theorem ReceiverServiceAfterAt.upTo
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {g : Time}
    {y : Fin sp.n}
    (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC) {d : Time} (hd : 0 ≤ d)
    (hy : y ∈ H d) :
    ReceiverServiceAfter (H d) ((tr.upTo d).HonestBlocks (H d)) g y (tr.projAC.upTo d) := by
  have hm : Monotone tr.projAC.time := hrun.time_mono
  refine ⟨fun x hx i m hm' j ℓ hc hdl => ?_, fun x hx i B hB j ℓ hc hdl hF => ?_⟩
  · obtain ⟨hid, hm'⟩ := (ac_sendOrAdmit_upTo hm).mp hm'
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ac_deadline_upTo hm hjd] at hdl
    obtain ⟨k, hkj, hik, hp, hkdl⟩ := hS.message x i m (hrun.antitone hid hx) hm' j ℓ
      (hrun.antitone hjd hy) hc hdl
    have hkd : tr.projAC.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, hik, (ac_processAt_upTo _).mpr ⟨hkd, hp⟩,
      by rw [ac_deadline_upTo hm hkd]; exact hkdl⟩
  · obtain ⟨hid, hB⟩ := (ac_acceptAt_upTo _).mp hB
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ac_deadline_upTo hm hjd] at hdl
    obtain ⟨k, hkj, hk, hkdl⟩ := hS.relay x i B (hrun.antitone hid hx) hB j ℓ
      (hrun.antitone hjd hy) hc hdl (hF.mono (upTo_subset hrun hd))
    have hkd : tr.projAC.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (ac_acceptAt_upTo _).mpr ⟨hkd, hk⟩,
      by rw [ac_deadline_upTo hm hkd]; exact hkdl⟩

/-! ### The delivery halves -/

/-- The deadline from `g ≤ t + Δ` of an object of time at most `t + Δ`, with every restart at or
before `t`, is at most `t + 2Δ`. -/
private theorem deadline_le_two {P : Params} {FGP : Type} {A : ACInterface P FGP} {T : ACTrace A}
    {y : Fin P.n} {c : Nat} {t g : Time}
    (h : ∀ k ≤ c, T.RestartAt y k → T.time k ≤ t) (hg : g ≤ t + P.Δ) {τ : Time}
    (hτ : τ ≤ t + P.Δ) : T.deadline y c (max τ g) ≤ t + 2 * P.Δ := by
  have h₁ := ac_deadline_le_of_restarts h (max τ g)
  have hΔ : 0 < P.Δ := P.hΔ
  linarith [max_le (max_le hτ hg) (show t ≤ t + P.Δ by linarith)]

/-- The block of the tree with the root of one of its blocks. -/
private theorem lookup_of_mem {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ Φ.tree) : SA.lookup Φ B.root = some B := by
  have hin : SA.InTree Φ B.root := ⟨B, hB, rfl⟩
  unfold SA.lookup
  rw [dite_eq_left_of_eq_true (eq_true hin)]
  obtain ⟨h₁, h₂⟩ := hin.choose_spec
  rw [hΦ.coherent.1 h₁ hB h₂]

/-- **D1** (relay half). A block held while honest that is genesis, or that a node honest at its
acceptance accepted by `t_q + Δ`, and that is above the receiver's `Σ.F`, is in the receiver's
frame and stamped before `t_q + 2Δ`, at every call from `t_q + 2Δ` of a receiver honest then with
no restart after `t_q`. -/
theorem accepted_held_before_early_at
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} {q c : Nat} (hy : y ∈ H (tr.time c))
    (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC)
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} (hc : tr.projAC.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts q)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocksAt H)
    (hacc : B.root = sp.genesisRoot ∨
      ∃ x k, x ∈ H (tr.time k) ∧ tr.projAC.AcceptAt x k B ∧ tr.time k ≤ sp.ts q + sp.Δ)
    (hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    B ∈ ℓ.frame.tree ∧
      (tr.projAC.state y c).blockStamp B.root < SA.ETime.of (sp.ts q + 2 * sp.Δ) := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hd := hrun.time_nonneg c
  have hct' : sp.ts q + 2 * sp.Δ ≤ tr.projAC.time c := hct
  obtain ⟨hΦ, -⟩ := frameIn_at hrun hnc hy hc
  have hdl : ∀ k ≤ c, ∀ τ, τ ≤ sp.ts q + sp.Δ →
      tr.projAC.deadline y k (max τ g) ≤ sp.ts q + 2 * sp.Δ := fun k hk _ hτ =>
    deadline_le_two (fun k' hk' hr' => hres k' (hk'.trans hk) hr') hg hτ
  have hab : SA.AcceptedBefore tr.projAC y B (sp.ts q + 2 * sp.Δ) ∧ B ∈ ℓ.frame.tree := by
    rcases hacc with hgen | ⟨x, k, hx, hax, hkt⟩
    · refine ⟨Or.inl hgen, ?_⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp (acRun_upTo hrun hnc hd).localRun hy
        c ℓ ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
      obtain rfl : B = G := hU.1 hBU (upTo_subset hrun hd hGU) (hgen.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hF with h | ⟨Q, -, hQ⟩
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    · obtain ⟨ky, hky, hay, hkyt⟩ :=
        hS.relay x k B hx hax c ℓ hy hc (by linarith [hdl c le_rfl (tr.projAC.time k) hkt]) hF
      exact ⟨Or.inr ⟨ky, hay, hkyt.trans_le (hdl ky hky (tr.projAC.time k) hkt)⟩,
        mem_tree_of_acceptAt_at hrun hnc hy hay hky hc hF⟩
  obtain ⟨hab, hBt⟩ := hab
  exact ⟨hBt, blockStamp_lt_of_acceptedBefore_at hrun hnc hy hc hBt hab
    (fun k hk hrk => by linarith [hres k hk hrk]) hct⟩

/-- **D2** (message half). A slot-`q` vote by a node honest at its cast and still honest at the
receiver call is in the receiver's pool, with a stamp before `t_q + 2Δ`, at every call from
`t_q + 2Δ` of a receiver honest then with no restart after `t_q` (lifted at the call's time). -/
theorem vote_pooled_before_early_at
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} {q c : Nat} (hy : y ∈ H (tr.time c))
    (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC)
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} (hc : tr.projAC.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts q)
    {x : Fin sp.n} {j : Nat} {e : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x j e)
    (hx : x ∈ H (tr.time c)) (hes : e.msg.slot = q) :
    e.msg ∈ (tr.projAC.state y c).pool q ∧
      (tr.projAC.state y c).voteStamp e.msg < SA.ETime.of (sp.ts q + 2 * sp.Δ) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hd := hrun.time_nonneg c
  obtain ⟨hxj, ℓv, hcv, hev⟩ := hVoteAt_iff.1 hv
  have hjt := (cast_head_fcRoot_at hrun hnc hxj ⟨hcv, hev⟩).2
  rw [hes] at hjt
  have hjt' : tr.time j ≤ sp.ts q + sp.Δ := hjt
  have h := vote_pooled_before_early (acRun_upTo hrun hnc hd) hy (hS.upTo hrun hd hy)
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc) hct hg
    (fun k hk hrk => hres k hk ((ac_restartAt_upTo _).mp hrk).2) hx
    (sa_voteAt_upTo.mpr ⟨show tr.time j ≤ tr.time c by linarith, ℓv, hcv, hev⟩) hes
  rwa [projAC_upTo_state hrun le_rfl] at h

/-- **D3**. A slot-`q` vote by a node honest at its cast and still honest at the receiver call is
pooled, its head is framed, and the vote is resolved before `t_q + 2Δ`, given the head's slot
bound and its acceptance by the voter while honest by `t_q + Δ` (or genesis). -/
theorem vote_resolved_before_early_at
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} {q c : Nat} (hy : y ∈ H (tr.time c))
    (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC)
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} (hc : tr.projAC.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts q)
    {x : Fin sp.n} {j : Nat} {e : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x j e)
    (hx : x ∈ H (tr.time c)) (hes : e.msg.slot = q) {Hd : SA.Blk sp.n (List (FG.Att sp.n))}
    (hHdU : Hd ∈ tr.HonestBlocksAt H) (hHdr : Hd.root = e.msg.head) (hHds : Hd.slot ≤ q)
    (hHdacc : Hd.root = sp.genesisRoot ∨
      ∃ k, x ∈ H (tr.time k) ∧ tr.projAC.AcceptAt x k Hd ∧ tr.time k ≤ sp.ts q + sp.Δ)
    (hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F Hd) :
    e.msg ∈ (tr.projAC.state y c).pool q ∧ Hd ∈ ℓ.frame.tree ∧
      SA.resolutionTime (tr.projAC.state y c) ℓ.frame e.msg <
        SA.ETime.of (sp.ts q + 2 * sp.Δ) := by
  obtain ⟨hpool, hvst⟩ := vote_pooled_before_early_at hrun hnc hy hS hc hct hg hres hv hx hes
  obtain ⟨hHdt, hbst⟩ := accepted_held_before_early_at hrun hnc hy hS hc hct hg hres hHdU
    (hHdacc.imp_right fun ⟨k, h⟩ => ⟨x, k, h⟩) hF
  obtain ⟨hΦ, -⟩ := frameIn_at hrun hnc hy hc
  have hHs : Hd.slot ≤ e.msg.slot := by rw [hes]; exact hHds
  refine ⟨hpool, hHdt, ?_⟩
  unfold SA.resolutionTime
  rw [← hHdr, lookup_of_mem hΦ hHdt]
  dsimp only
  simp only [not_lt.2 hHs, ↓reduceIte]
  exact max_lt hvst hbst

end Consensus.Goldilocks.Compose.Growing

end
