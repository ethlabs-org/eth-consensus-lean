module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.LocalFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.FinalityPair
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Deadline
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Healing
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Deadline
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.RecordsCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.PreAdvanceFacts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

-- Keep the run-level leaves beside their independent-observation facts.
set_option linter.style.longFile 1800

/-! # Generic healing leaves

The healing leaves proved once over any node AC: a node run under growing faults
(`Growing.LocalRun`) from any starts `ini`. The Goldilocks originals are instances. The leaves over
a healing supplier (`ACHealing`) are in `HealingRounds`, which imports this module.

Held attestations: an attestation on a block held at an observation honest at `t`, with a signer
honest at `t`, was signed before the cut (`held_att_signed_at_from`); two such attestations, with
a signer honest at a time after both observations, are not slashable (`held_atts_safe_at_from`).

Leaf 2, lower bound (`HZ_le_hmax_at_from`): after its relay obligation is paid, a receiver honest
at its cut has at least the snapshot height `HZ`. Relay and catch-up carry a held block of
height at least the receiver's `h_max` to the receiver (`held_of_relay_le_at_from`), and the
block's state is the same at both holders (`σ_eq_honest_at_from`).

Leaf 3, the frame window: per-cut height range and relay calls give a frame window of the
requested length, by the sequential pigeonhole over the cuts of nodes honest at them with the
milestone key lag between independently honest observations (`HealingEdges`).

Proposal membership and leaf 5, the round crossing (`proposal_mem_at_from`,
`round_cross_at_from`): an honest proposal is held by its proposer after its cut, and delivered
historical rows (`rows_delivered_service_at_from`, under the signed-row service clause) or higher
reports raise the proposal one height above the crossed block.

Leaf 2, upper bound (`hmax_le_of_noAdvance_at_from`): before any height advance by a signer
honest at it and at `c_z`, an honest observer's `h_max` is at most `HZ + 1`; an honest
attestation above it would have been signed before the observation.

Leaf 1 (`reset_of_height_advance_at_from`): a signing above `HZ` by a signer honest at it and at
`c_z` gives a reset no later; an honest attestation at `HZ + 1` below it was signed first, and the
earliest such signing is the reset.

Leaf 6c (`reset_of_high_source_at_from`): a high `fg_attest` source of a caller honest at it and
at `c_z` forces a reset no later; with no earlier high signing, the client's record has no lock or
sent content at that height, so the call signs and leaf 1 applies.

Leaf 6 (`reset_of_high_report_at_from`): a report of height at least `HZ + 1`, by a reporter
honest at it and at `c_z`, is followed in the same tick by its `fg_attest` call with the same
store (`voteLatency_zero_from`), so leaf 6c gives a reset no later. Under a vote latency `D`
(`VoteLatencyAt`: the `fg_attest` call on a source at least as high follows within `D`), the reset
comes at most `D` after the report (`reset_of_high_report_within_from`).

Leaf 7 (`sign_from_report_at_from`): an honest signing comes from the report of the `ac_to_fg`
cut just before it, at the same time and with the same store; under the requirements of the
node's AC start the report is held (`Healing.toFG_source_mem_from`), and its entry is the signed
target at the signed height.

Leaf 14 (`high_entry_eq_at_from`): two self-entries of equal height below two compatible honest
blocks are the same block. Both lie below the later block, which some node holds at an honest
observation, and along that store's ancestry the entry is constant at one height
(`Healing.Th_eq_of_anc`). Its form over any `ACHealing` (`high_entry_eq_at_of_healing`, in
`HealingRounds`) compares the two high origins by `ACHealing.origins_comparable`.

Slot alignment (`exists_slot_align_of_grid`): on the four-delay grid, `s₀ = ⌈a_f / 4Δ⌉` has
`a_f ≤ t_{s₀}` and `4Δ·s₀ < a_f + 4Δ`.

Relay calls from wakefulness (`snapshotCall_of_awake_at_from`, `callLag_of_awake_at_from`): a
node awake on `[ḡ, b]` ticks at every public time there, and its restarts are at or before
`t_{slot(ḡ)+1} ≤ c_z`, so after `c_z` the call at a public time meets the relay deadline
(`Healing.callLag_of_awake`, `Healing.snapshotCall_of_awake` on the receiver's prefix, for any
node AC and any slot schedule).

Leaf 4 (`row_or_high_of_report_at_from`): a held report, before any height advance, either
supplies a row of a lower block of the same height signed while honest, or is strictly higher.
Its `fg_attest` call follows in the same tick with the same store; the lock at the height is
free (no advance) or names the entry (the client record's provenance, `Healing.record_facts`,
and its signed finality pairs, `Healing.signed_fin_justified`), so the client signs the row now or
signed it before (`Healing.client_progress_of_lock`).

Truncation after a horizon (`truncH_eq_of_le`, `truncH_antitone`, `honestBlocksAt_truncH_subset`,
`catchRun_truncH`, `HZ_truncH`, `isReset_truncH_iff`): the honest sets truncated after `b` agree
with `H` up to `b`; their honest blocks are a subset of those for `H`; catch-up transports to the
truncation; and under the stated bounds `H_z` and the reset by `b` agree with those for `H`.
-/

namespace Consensus.Goldilocks.Generic

/-- **Slot alignment** on the four-delay grid: `s₀ = ⌈a_f / 4Δ⌉` has `a_f ≤ t_{s₀}` and
`4Δ·s₀ < a_f + 4Δ`, for any schedule whose slot `s` starts at `s · 4Δ`. -/
theorem exists_slot_align_of_grid {P : Params} : exists_slot_align (P := P) := by
  intro hgrid af haf
  have h4D : 0 < 4 * P.Δ := by linarith only [P.hΔ]
  set s₀Z : ℤ := (af + 4 * P.Δ - 1) / (4 * P.Δ) with hs₀Z
  have hs₀lo := Int.ediv_mul_le (af + 4 * P.Δ - 1) h4D.ne'
  have hs₀hi := Int.lt_ediv_add_one_mul_self (af + 4 * P.Δ - 1) h4D
  rw [← hs₀Z] at hs₀lo hs₀hi
  have hs₀nn : 0 ≤ s₀Z := Int.ediv_nonneg (by linarith only [haf, h4D]) h4D.le
  have hs₀c : ((s₀Z.toNat : Nat) : ℤ) = s₀Z := Int.toNat_of_nonneg hs₀nn
  refine ⟨s₀Z.toNat, ?_, ?_⟩
  · rw [hgrid, hs₀c]
    linarith only [hs₀hi]
  · rw [hs₀c]
    linarith only [hs₀lo]

/-- An attestation on a block held at an observation honest at `t`, with a signer honest at `t`,
was signed before the cut, for any node run under growing faults from any starts `ini`. -/
theorem held_att_signed_at_from {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) {a : FG.Att P.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by rw [Trace.upTo_state tr y hle]; exact hX
  rcases Healing.tree_accepted (h.upTo ht) hy hXt with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
    obtain ⟨k', hk', hs'⟩ := h.att_unforgeable y k a
      (h.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
      (h.antitone (hle k hk) hav)
    exact ⟨k', hk'.trans hk, hs'⟩

/-- **Held attestations at independently honest observations are not slashable**, for any node
run under growing faults from any starts `ini`. Attestations on blocks held by `y` (observed while
honest at `u`) and by `x` (observed while honest at `t`), with a signer honest at a time `d` after
both observations, were signed by that signer's client run on the prefix up to `d`, which client
safety (G0.5) keeps free of slashable pairs. -/
theorem held_atts_safe_at_from {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y x : Fin P.n} {m i : Nat} {u t d : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t) (hud : u ≤ d) (htd : t ≤ d)
    (a b : FG.Att P.n) (ha : ∃ Y ∈ (tr.state y m).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state x i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H d) :
    ¬ FG.slashable a b := fun hab => by
  obtain ⟨k, hk, hka⟩ := held_att_signed_at_from h hu hytime hy ha (h.antitone hud hav)
  obtain ⟨l, hl, hlb⟩ := held_att_signed_at_from h ht hxtime hx hb
    (hab.1 ▸ h.antitone htd hav)
  rw [← hab.1] at hlb
  have hka' : (tr.upTo d).SignAt a.val k a :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans hud, hka⟩
  have hlb' : (tr.upTo d).SignAt a.val l b :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans htd, hlb⟩
  obtain ⟨inputs, hin, hs⟩ :=
    Store.signed_run_of_exec (Compose.fg_exec (h.upTo (hu.trans hud))) hav (max k l + 1)
  exact FG.client_safety P.fg a.val inputs hin
    a (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka'.choose_spec⟩)
    b (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb'.choose_spec⟩) hab

/-! ## Leaf 2, upper bound -/

/-- Before any height advance, an honest observer's cached height is at most the snapshot
height plus one, with the quorum budget charged at the later of the snapshot and observation. -/
theorem hmax_le_of_noAdvance_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {g T : Time} {y : Fin P.n} {i : Nat}
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hna : NoAdvance tr H g T) (hy : y ∈ H (tr.time i))
    (hq : (H (max (Healing.cutZ P g) (tr.time i)))ᶜ.ncard < P.fg.q)
    (hiT : tr.time i < T) :
    (tr.state y i).fg.hmax ≤ Healing.Growing.HZ tr H g + 1 := by
  have hr := hrun.upTo (hrun.time_nonneg i)
  have hs : (tr.upTo (tr.time i)).state y i = tr.state y i :=
    Trace.upTo_state tr y (fun _ hk => hrun.time_mono hk.le)
  have hR := Compose.fg_reachable hr hy i
  obtain ⟨_, _, _, _, _, ⟨X, hX, hXh⟩, _⟩ := Store.cache_invariants _ _ _ _ hR
  by_contra hlt
  rw [← hs] at hlt
  obtain ⟨Y, hYX, a, ha, haH, hah⟩ := Healing.Store.exists_honest_att_of_lt hR hq hX
    (Healing.Growing.HZ tr H g + 1) (by omega) (by omega)
  have hY : Y ∈ ((tr.upTo (tr.time i)).state y i).fg.tree := by
    by_cases he : Y = X
    · exact he ▸ hX
    · exact (Anc.mem hYX he).1
  rcases Healing.tree_accepted hr hy hY with rfl | ⟨k, hki, hA⟩
  · cases ha
  obtain ⟨j, hjk, hj⟩ := hr.att_unforgeable y hy k a
    (Or.inr ⟨Y, ⟨true, hA⟩, ha⟩) (hrun.antitone (le_max_right _ _) haH)
  have hjT : tr.time j < T := (hrun.time_mono (by omega)).trans_lt hiT
  obtain ⟨hjt, hj⟩ := (RunTrace.upTo_signAt tr).mp hj
  have := hna a.val j a (hrun.antitone (max_le_max le_rfl hjt) haH) hj hjT
  omega

/-! ## Leaf 1 -/

private theorem exists_honest_att_of_lt {P : Params} {ACP : Type} {acp₀ : ACP}
    {st : Store P ACP}
    (hr : st.Reachable acp₀) {H : Set (Fin P.n)}
    (hq : Hᶜ.ncard < P.fg.q) {X : NodeBlock P ACP} (hX : X ∈ st.tree) :
    ∀ h, 1 ≤ h → h < (st.σ X.root).h →
      ∃ Y, st.Anc Y X ∧ ∃ a ∈ Y.fgPayload, a.val ∈ H ∧ a.h = h := by
  suffices key : (∀ v ∈ (st.σ X.root).prog ∪ (st.σ X.root).target,
      ∃ Y, st.Anc Y X ∧ ∃ a ∈ Y.fgPayload, a.val = v ∧ a.h = (st.σ X.root).h) ∧
      ∀ h, 1 ≤ h → h < (st.σ X.root).h →
        ∃ Y, st.Anc Y X ∧ ∃ a ∈ Y.fgPayload, a.val ∈ H ∧ a.h = h from key.2
  have hg := (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.2.2 X hX
  clear hX
  induction hg with
  | refl =>
    change (∀ v ∈ (st.σ P.genesisRoot).prog ∪ (st.σ P.genesisRoot).target, _) ∧
      ∀ h, 1 ≤ h → h < (st.σ P.genesisRoot).h → _
    rw [Goldilocks.Store.Reachable.σ_genesis hr]
    refine ⟨fun v hv => ?_, fun h h1 h2 => ?_⟩
    · rcases Finset.mem_union.1 hv with hv | hv <;>
        exact absurd hv (Finset.notMem_empty _)
    simp only [FG.ChainState.init] at h2
    omega
  | @tail W' W _ hpar ih =>
    obtain ⟨hW', hW, hp⟩ := hpar
    obtain ⟨-, -, -, ht⟩ := Goldilocks.Store.Reachable.step_σ hr hW hp
    have hanc : st.Anc W' W := .single ⟨hW', hW, hp⟩
    have old : ∀ v, v ∈ (st.σ W'.root).prog ∪ (st.σ W'.root).target ∨
        (∃ a ∈ W.fgView.atts, a.val = v ∧ a.h = (st.σ W'.root).h) →
        ∃ Y, st.Anc Y W ∧ ∃ a ∈ Y.fgPayload, a.val = v ∧ a.h = (st.σ W'.root).h := by
      rintro v (hv | ⟨a, ha, hav, hah⟩)
      · obtain ⟨Y, hY, hYa⟩ := ih.1 v hv
        exact ⟨Y, hY.trans hanc, hYa⟩
      · exact ⟨W, .refl, a, ha, hav, hah⟩
    rcases Healing.stateTransition_bits ht with ⟨he, hbits⟩ | ⟨he, hnil, S, hS, hSv⟩
    · refine ⟨fun v hv => he ▸ old v (hbits v hv), fun h h1 h2 => ?_⟩
      obtain ⟨Y, hY, hYa⟩ := ih.2 h h1 (he ▸ h2)
      exact ⟨Y, hY.trans hanc, hYa⟩
    · obtain ⟨S, hS, hSv⟩ : ∃ S : Finset (Fin P.n), P.fg.q ≤ S.card ∧ ∀ v ∈ S,
          v ∈ (st.σ W'.root).prog ∪ (st.σ W'.root).target ∨
            ∃ a ∈ W.fgView.atts, a.val = v ∧ a.h = (st.σ W'.root).h := ⟨S, hS, hSv⟩
      refine ⟨fun v hv => absurd hv (Finset.eq_empty_iff_forall_notMem.1 hnil v),
        fun h h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 (he ▸ h2) with h2 | rfl
      · obtain ⟨Y, hY, hYa⟩ := ih.2 h h1 h2
        exact ⟨Y, hY.trans hanc, hYa⟩
      · obtain ⟨v, hvS, hvH⟩ : ∃ v ∈ S, v ∈ H := by
          by_contra hc
          have hsub : (↑S : Set (Fin P.n)) ⊆ Hᶜ := fun v hv h => hc ⟨v, hv, h⟩
          have hc' := Set.ncard_le_ncard hsub (Set.toFinite _)
          rw [Set.ncard_coe_finset] at hc'
          omega
        obtain ⟨Y, hY, a, ha, rfl, hah⟩ := old v (hSv v hvS)
        exact ⟨Y, hY, a, ha, hvH, hah⟩

/-- **Leaf 1**: a high signing by a signer honest at it and at `c_z` gives a reset no later. -/
theorem reset_of_height_advance_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {tr : RunTrace A} {ini : Fin P.n → A.State}
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {g : Time} {y : Fin P.n} {k : Nat} {att : FG.Att P.n}
    (hq : (H (max (Healing.cutZ P g) (tr.time k)))ᶜ.ncard < P.fg.q)
    (hyz : y ∈ H (max (Healing.cutZ P g) (tr.time k)))
    (hs : tr.SignAt y k att) (hh : Healing.Growing.HZ tr H g + 1 ≤ att.h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time k := by
  classical
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
  have hr := hrun.reachable_at (hrun.time_nonneg k) hle hy
  have hex₀ : ∃ j z a, z ∈ H (max (Healing.cutZ P g) (tr.time j)) ∧ tr.SignAt z j a ∧
      a.h = Healing.Growing.HZ tr H g + 1 ∧ tr.time j ≤ tr.time k := by
    rcases hh.lt_or_eq with hlt | heq
    · obtain ⟨E, hE, _, hEh⟩ := hrun.signAt_entry hy hs
      obtain ⟨Y, hYE, a, ha, haH, hah⟩ :=
        exists_honest_att_of_lt hr hq hE (Healing.Growing.HZ tr H g + 1) (by omega) (by omega)
      have hY : Y ∈ (tr.state y k).fg.tree := by
        by_cases he : Y = E
        · exact he ▸ hE
        · exact (Anc.mem hYE he).1
      obtain ⟨src, hc⟩ := hs
      obtain ⟨j, hj, hjk⟩ := hrun.signed_before_attest hy hc hY ha
        (hrun.antitone (le_max_right _ _) haH)
      exact ⟨j, a.val, a, hrun.antitone (max_le_max le_rfl hjk.le) haH, hj, hah, hjk.le⟩
    · exact ⟨k, y, att, hyz, hs, heq.symm, le_rfl⟩
  obtain ⟨j, z, att, hz, hs, hh, hjk⟩ := hex₀
  have hex : ∃ j z att, z ∈ H (max (Healing.cutZ P g) (tr.time j)) ∧ tr.SignAt z j att ∧
      att.h = Healing.Growing.HZ tr H g + 1 := ⟨j, z, att, hz, hs, hh⟩
  obtain ⟨v, c, hv, hc, hch⟩ := Nat.find_spec hex
  have hR : Healing.Growing.IsReset tr H g (tr.time (Nat.find hex)) :=
    ⟨⟨v, Nat.find hex, c, hv, hc, hch, rfl⟩, by
      intro v i c hv hc hch
      exact hrun.time_mono (Nat.find_min' hex ⟨v, c, hv, hc, hch⟩)⟩
  exact ⟨_, hR, (hR.2 z j att hz hs hh).trans hjk⟩

/-! ## Leaf 6c -/

/-- **Leaf 6c**: a high FG source of a node honest at it and at `c_z` forces a reset no later. -/
theorem reset_of_high_source_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {tr : RunTrace A} {ini : Fin P.n → A.State}
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {g : Time} {y : Fin P.n} {k : Nat} {C : A.Blk} {s : Option (FG.Att P.n)}
    (hyz : y ∈ H (max (Healing.cutZ P g) (tr.time k)))
    (hq : (H (max (Healing.cutZ P g) (tr.time k)))ᶜ.ncard < P.fg.q)
    (hc : tr.CallAt y k (.fg (.attest C s)))
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time k := by
  classical
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
  have hr := hrun.reachable_at (hrun.time_nonneg k) hle hy
  have he : ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h =
      ((tr.state y k).fg.σ C.root).h := by
    rcases hC : (tr.state y k).fg.blocks C.root with _ | X
    · rw [Healing.Store.σ_of_blocks_none hr hC]
      exact congrArg FG.ChainState.h (Goldilocks.Store.Reachable.σ_genesis hr)
    · have hXr := Goldilocks.Store.Reachable.blocks_root hr hC
      have hX : X ∈ (tr.state y k).fg.tree := by
        change (tr.state y k).fg.blocks X.root = some X
        rw [hXr]; exact hC
      obtain ⟨⟨E, _, hEr, _, hEh, _⟩, _⟩ := Goldilocks.Store.entry_state_of_source _ _ _ _ hr X hX
      rw [← hXr, ← hEr]
      exact hEh
  by_cases hprev : ∃ j < k, ∃ att, tr.SignAt y j att ∧
      Healing.Growing.HZ tr H g + 1 ≤ att.h
  · obtain ⟨j, hj, att, hs, hh⟩ := hprev
    have hjt := hrun.time_mono hj.le
    have hjz := max_le_max (le_refl (Healing.cutZ P g)) hjt
    have hqj : (H (max (Healing.cutZ P g) (tr.time j)))ᶜ.ncard < P.fg.q :=
      lt_of_le_of_lt (Set.ncard_le_ncard (Set.compl_subset_compl.mpr
        (hrun.antitone hjz)) (Set.toFinite _)) hq
    obtain ⟨a, ha, haj⟩ := reset_of_height_advance_at_from hrun hqj
      (hrun.antitone hjz hyz) hs hh
    exact ⟨a, ha, haj.trans hjt⟩
  have hlock : (tr.state y k).record.lock ((tr.state y k).fg.σ C.root).h = none := by
    by_contra hn
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hn
    obtain ⟨j, hj, att, hs, hfin⟩ :=
      (hrun.client_record_origin (hrun.time_nonneg k) hle hy _ r).2 hr
    have hw := (hrun.signAt_wellFormed (hrun.antitone (hrun.time_mono hj.le) hy) hs).2
      (((tr.state y k).fg.σ C.root).h, r) (by simp [hfin])
    exact hprev ⟨j, hj, att, hs, by omega⟩
  have hsent : ∀ b ∈ (tr.state y k).record.sent,
      b.1 ≠ ((tr.state y k).fg.σ C.root).h := by
    intro b hb hbh
    obtain ⟨j, hj, att, hs, heq⟩ := hrun.sent_origin (hrun.time_nonneg k) hle hy hb
    have hah : att.h = b.1 := congrArg Prod.fst heq
    exact hprev ⟨j, hj, att, hs, by omega⟩
  have hany (τ : Bool) : (tr.state y k).record.sent.any (fun b =>
      b.1 = ((tr.state y k).fg.σ C.root).h ∧ (!τ ∨ b.2.1 =
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th)) = false := by
    apply List.any_eq_false.2
    intro b hb
    simp [hsent b hb]
  cases s with
  | some att =>
    have hcl := (hrun.attest_some hc hy).1
    apply reset_of_height_advance_at_from hrun hq hyz ⟨C, hc⟩
    rw [(Healing.Store.createAtt_eq hcl).1, he]
    exact hh
  | none =>
    have hcl := (hrun.attest_none hc hy).1
    exfalso
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = none at hcl
    have hτ : ∃ τ, (tr.state y k).record.heightPair ((tr.state y k).fg.σ C.root).h
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th =
        some (((tr.state y k).fg.σ C.root).h,
          ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th, τ) := by
      unfold FG.Record.heightPair
      simp only [hlock, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨τ, hτ⟩ := hτ
    unfold FG.Record.createAtt at hcl
    rw [he, hτ] at hcl
    dsimp only at hcl
    rw [hany τ] at hcl
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hcl

/-! ## Leaf 6 -/

/-- **Vote latency `D`**: by `time i + D`, a reporter honest at that deadline calls `fg_attest`
on a source it reported at or after cut `i`. The signing source extends the report at `i` and is
at least as high in the signing store. The deadline bounds signing, not delivery. -/
structure VoteLatencyAt {P : Params} {A : NodeAC P} (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (D : Time) : Prop where
  attests : ∀ y i R, ReportAt tr y i R → y ∈ H (tr.time i + D) →
    ∃ k, i ≤ k ∧ tr.time k ≤ tr.time i + D ∧ ∃ C s, tr.CallAt y k (.fg (.attest C s)) ∧
      ((tr.state y i).fg.σ R.root).h ≤ ((tr.state y k).fg.σ C.root).h ∧
      Anc (tr.HonestBlocksAt H) R C ∧ ∃ j, i ≤ j ∧ j ≤ k ∧ ReportAt tr y j C

/-- Every node run meets latency `0`: the report's `fg_attest` call follows in the same tick, on
the same store. -/
theorem voteLatency_zero_from {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini) :
    VoteLatencyAt tr H 0 := by
  refine ⟨fun y i R hR hy => ?_⟩
  rw [add_zero] at hy
  have hr := hrun.upTo (hrun.time_nonneg i)
  have hst := Trace.upTo_state tr y (i := i) (fun q hq => hrun.time_mono hq.le)
  obtain ⟨ell, hc, hto, hres⟩ := hR
  have hc' : (tr.upTo (tr.time i)).CallAt y i (.ac ell) :=
    (Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩
  have hres' : (A.toFG ((tr.upTo (tr.time i)).state y i).ac
      ell.frame (tr.time i)).2 = some R := by rwa [hst]
  obtain ⟨s, hatt, ht, hfg⟩ := Healing.toFG_attest hr hy hc' hto hres'
  have ht' : tr.time (i + 1) = tr.time i := ht
  have hs1 := Trace.upTo_state tr (d := tr.time i) y (i := i + 1)
    (fun q hq => hrun.time_mono (by omega))
  rw [hs1, hst] at hfg
  exact ⟨i + 1, by omega, by rw [ht', add_zero], R, s, ((Trace.upTo_callAt tr).mp hatt).2,
    by rw [hfg], .refl, i, le_rfl, by omega, ell, hc, hto, hres⟩

/-- **Leaf 6 under vote latency `D`**: a report of height at least `HZ + 1`, by a reporter honest
at `D` after it and at `c_z`, with fewer than `q` faulty at that time, gives a reset no later than
`D` after the report. -/
theorem reset_of_high_report_within_from {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {tr : RunTrace A} {ini : Fin P.n → A.State} {g D : Time}
    {y : Fin P.n} {i : Nat} {R : A.Blk}
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hlat : VoteLatencyAt tr H D)
    (hyz : y ∈ H (max (Healing.cutZ P g) (tr.time i + D)))
    (hq : (H (max (Healing.cutZ P g) (tr.time i + D)))ᶜ.ncard < P.fg.q)
    (hR : ReportAt tr y i R)
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time i + D := by
  obtain ⟨k, -, hk, C, s, hc, hCh, -, -⟩ :=
    hlat.attests y i R hR (hrun.antitone (le_max_right _ _) hyz)
  have hmono : max (Healing.cutZ P g) (tr.time k) ≤ max (Healing.cutZ P g) (tr.time i + D) :=
    max_le_max le_rfl hk
  have hqk : (H (max (Healing.cutZ P g) (tr.time k)))ᶜ.ncard < P.fg.q :=
    lt_of_le_of_lt (Set.ncard_le_ncard
      (Set.compl_subset_compl.2 fun x hx => hrun.antitone hmono hx) (Set.toFinite _)) hq
  obtain ⟨a, ha, hat⟩ :=
    reset_of_high_source_at_from hrun (hrun.antitone hmono hyz) hqk hc (hh.trans hCh)
  exact ⟨a, ha, hat.trans hk⟩

/-- A high report gives a high FG source in the same tick, hence a reset no later
(`reset_of_high_report_within_from` at latency `0`). -/
theorem reset_of_high_report_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {g : Time} {y : Fin P.n} {i : Nat} {R : A.Blk}
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hyz : y ∈ H (max (Healing.cutZ P g) (tr.time i)))
    (hq : (H (max (Healing.cutZ P g) (tr.time i)))ᶜ.ncard < P.fg.q)
    (hR : ReportAt tr y i R)
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time i := by
  simpa using reset_of_high_report_within_from hrun (voteLatency_zero_from hrun)
    (by simpa using hyz) (by simpa using hq) hR hh

/-! ## Leaf 7 -/

/-- An honest signing comes from the report of the `ac_to_fg` cut just before it, at the same
time: the report is held, its entry is the signed target, and the signed height is its height. -/
theorem sign_from_report_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {y : Fin P.n} {k : Nat} {att : FG.Att P.n}
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hy : y ∈ H (tr.time k)) (hs : tr.SignAt y k att) :
    ∃ i < k, ∃ R, ReportAt tr y i R ∧ tr.time i = tr.time k ∧
      att.h ≤ ((tr.state y i).fg.σ R.root).h ∧
      ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E R ∧ E.root = att.T ∧
        ((tr.state y i).fg.σ E.root).h = att.h ∧ ((tr.state y i).fg.σ E.root).Th = E.root := by
  have hr := hrun.upTo (hrun.time_nonneg k)
  obtain ⟨C, hc⟩ := hs
  obtain ⟨i, rfl, ℓ, hci, hto, ht, hC, hfg⟩ :=
    Compose.attest_source hr hy ((Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩)
  have hCt := Healing.toFG_source_mem_from hr hy (hq y) hci hto hC
  have hreach := Compose.fg_reachable hr hy i
  have ht' : tr.time i = tr.time (i + 1) := ht
  have hsi := Trace.upTo_state tr (d := tr.time (i + 1)) y (i := i)
    (fun q hq => hrun.time_mono (by omega))
  have hsk := Trace.upTo_state tr (d := tr.time (i + 1)) y (i := i + 1)
    (fun q hq => hrun.time_mono (by omega))
  rw [hsi] at hC hCt hreach
  rw [hsk, hsi] at hfg
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hETh⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hreach C hCt
  obtain ⟨hah, haT⟩ := Healing.Store.createAtt_eq (hrun.cutLaw y (i + 1) _ hc hy).1
  rw [hfg, ← hEr] at hah haT
  have hETh' : ((tr.state y i).fg.σ E.root).Th = E.root := by rw [hETh, hEr]
  refine ⟨i, by omega, C, ⟨ℓ, ((Trace.upTo_callAt tr).mp hci).2, hto, hC⟩, ht',
    by rw [hah, hEh], E, hE, hEC, by rw [haT, hETh'], hah.symm, hETh'⟩

/-! ## Relay calls from wakefulness -/

section CallLag

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open AC (gbar)
open Healing (FirstCutAfter cutZ)

/-- Public ticks supply the snapshot and the snapshot relay call before an honest receiver's
cut at or after `c_z + Δ + 1`: the static `Healing.snapshot_of_awake` and
`Healing.snapshotCall_of_awake` on the receiver's prefix. -/
theorem snapshotCall_of_awake_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini) {g b : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    {z : Fin P.n} {m : Nat} (hz : z ∈ H (tr.time m))
    (hfit : cutZ P g + P.Δ + 1 ≤ tr.time m) (hmb : tr.time m ≤ b) :
    (∃ j, FirstCutAfter tr j (cutZ P g)) ∧
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (cutZ P g) g) P.Δ ≤ tr.time j := by
  have hr := hrun.upTo (hrun.time_nonneg m)
  have ha : ∀ y ∈ H (tr.time m), ∀ t, gbar g ≤ t → t ≤ tr.time m →
      (tr.upTo (tr.time m)).awake y t := fun y hy t ht htm =>
    ⟨hawake y t (hrun.antitone htm hy) ht (htm.trans hmb), htm⟩
  obtain ⟨j, hj, -⟩ := Healing.snapshot_of_awake hr ha ⟨z, hz⟩
    (show cutZ P g + P.Δ ≤ tr.time m by linarith)
  refine ⟨⟨j, hj⟩, ?_⟩
  obtain ⟨j, hjm, hc, hd⟩ := Healing.snapshotCall_of_awake hr ha hfit
    (T := tr.time m + 1) le_rfl z hz m le_rfl
    (show tr.time m < tr.time m + 1 by linarith)
  have hjt := ((RunTrace.upTo_isCall tr).mp hc).1
  refine ⟨j, hjm, ((RunTrace.upTo_isCall tr).mp hc).2, ?_⟩
  rwa [RunTrace.upTo_deadline hrun.time_mono hjt] at hd

/-- Wakefulness supplies a relay call before an independently honest receiver cut, at the
two-delay lag: the static `Healing.callLag_of_awake` on the receiver's prefix. -/
theorem callLag_of_awake_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini) {g b lo : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hlo : cutZ P g ≤ lo) {z : Fin P.n} {i m : Nat}
    (hz : z ∈ H (tr.time m)) (hi : lo ≤ tr.time i)
    (him : tr.time i + 2 * P.Δ ≤ tr.time m) (hmb : tr.time m ≤ b) :
    ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j := by
  have hr := hrun.upTo (hrun.time_nonneg m)
  have ha : ∀ y ∈ H (tr.time m), ∀ t, gbar g ≤ t → t ≤ tr.time m →
      (tr.upTo (tr.time m)).awake y t := fun y hy t ht htm =>
    ⟨hawake y t (hrun.antitone htm hy) ht (htm.trans hmb), htm⟩
  obtain ⟨j, hjm, hc, hd⟩ := Healing.callLag_of_awake hr ha hlo
    (T := tr.time m + 1) le_rfl z hz i m hi him
      (show tr.time m < tr.time m + 1 by linarith)
  have hjt := ((RunTrace.upTo_isCall tr).mp hc).1
  refine ⟨j, hjm, ((RunTrace.upTo_isCall tr).mp hc).2, ?_⟩
  rwa [RunTrace.upTo_deadline hrun.time_mono hjt] at hd

end CallLag

/-! ## Leaf 2, lower bound -/

section HZLowerBound

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State} {hold : Time}

open AC (gbar)
open Healing (FirstCutAfter cutZ)
open Healing.Growing (HZ CatchRun)

/-- Reachability at a held-state observation, not necessarily the time of cut `i`. -/
theorem fg_reachable_at_from (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) :
    (tr.state y i).fg.Reachable A.genesisPayload := by
  simpa only [Trace.upTo_state tr y hle] using Compose.fg_reachable (h.upTo ht) hy i

/-- Ancestry in a tree observed while honest lies in the historical honest universe. -/
theorem honest_anc_of_store_anc_at_from {y : Fin P.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {B C : A.Blk} (h : (tr.state y k).fg.Anc B C) :
    Anc (tr.HonestBlocksAt H) B C :=
  h.mono fun _ hB => ⟨y, k, t, ht, hle, hy, hB⟩

/-- Replay agreement at independent honest observations. -/
theorem σ_eq_honest_at_from
    {sg : A.Msg → Fin P.n} (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin P.n} {i j : Nat} {t u : Time}
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t)
    (hu : 0 ≤ u) (hle' : ∀ q < j, tr.time q ≤ u) (hz : z ∈ H u)
    {B : A.Blk} (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Healing.Store.σ_eq_of_mem (h.reachable_at ht hle hy)
    (h.reachable_at hu hle' hz) (h.coherent hnc).1
    (fun _ hX => ⟨y, i, t, ht, hle, hy, hX⟩)
    (fun _ hX => ⟨z, j, u, hu, hle', hz, hX⟩) hBy hBz

/-- Strict-height finalized ancestry for two independently honest held-state observations. -/
theorem F_anc_of_hmax_le_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin P.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * P.fg.q - P.n)
    {B : A.Blk} (hB : B ∈ (tr.state x i).fg.tree)
    (hle : (tr.state y m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h) :
    Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F B :=
  honest_anc_of_store_anc_at_from ht hxtime hx <| Store.F_anc_of_hmax_le_of_safe
    (fg_reachable_at_from h hu hytime hy) (fg_reachable_at_from h ht hxtime hx)
    (Compose.Growing.honest_blocks_coherent_local h hnc)
    (fun _ hX => ⟨y, m, u, hu, hytime, hy, hX⟩)
    (fun _ hX => ⟨x, i, t, ht, hxtime, hx, hX⟩) hf
    (held_atts_safe_at_from h hu hytime hy ht hxtime hx (le_max_left _ _) (le_max_right _ _))
    hB hle

/-- Relay and catch-up carry a held block to a receiver whose height has not passed it. -/
theorem held_of_relay_le_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ τ : Time}
    (hsvc : Service tr H g ΔF b hold) (hcatch : CatchRun tr H g κ)
    {x z : Fin P.n} {i m : Nat} (hτ0 : 0 ≤ τ) (hx : x ∈ H τ)
    (hz : z ∈ H (tr.time m))
    (hf : (H (max τ (tr.time m)))ᶜ.ncard < 2 * P.fg.q - P.n)
    {B : A.Blk} (hB : B ∈ (tr.state x i).fg.tree)
    (hh : (tr.state z m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h)
    (hτ : ∀ k < i, tr.time k ≤ τ)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max τ g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) : B ∈ (tr.state z m).fg.tree := by
  have hm0 := h.time_nonneg m
  have hm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => h.time_mono hk.le
  have hs : ∀ j ≤ m, (tr.upTo (tr.time m)).state z j = tr.state z j :=
    fun j hj => Trace.upTo_state tr z (fun k hk => h.time_mono (by omega))
  have hr := h.upTo hm0
  have hF : ∀ j ≤ m, Anc (tr.HonestBlocksAt H) (tr.state z j).fg.F B := by
    intro j hj
    have hheight := Healing.hmax_mono hr hz hj
    dsimp only at hheight
    rw [hs j hj, hs m le_rfl] at hheight
    apply F_anc_of_hmax_le_at_from h hnc hm0
      (fun k hk => h.time_mono (by omega)) hz hτ0 hτ hx
      (by rwa [max_comm]) hB (hheight.trans hh)
  have hlift : ∀ k, k + 1 ≤ m → tr.AcceptAt z k B → B ∈ (tr.state z m).fg.tree := by
    intro k hkm ha
    have ha' : (tr.upTo (tr.time m)).AcceptAt z k B :=
      (RunTrace.upTo_acceptAt tr).mpr ⟨h.time_mono (by omega), ha⟩
    have hmem := Healing.accept_mem_from hr hz ha'
    have := Compose.tree_mono hr hz hkm hmem
    rwa [hs m le_rfl] at this
  have hB' : B ∈ ((tr.upTo τ).state x i).fg.tree := by
    rwa [Trace.upTo_state tr x hτ]
  rcases Healing.tree_accepted (h.upTo hτ0) hx hB' with he | ⟨k, hk, ha⟩
  · rw [he]
    exact Healing.Store.genesis_mem (fg_reachable_at_from h hm0 hm hz)
  have ha := ((RunTrace.upTo_acceptAt tr).mp ha).2
  have hxk := h.antitone (hτ k hk) hx
  by_cases hg : g ≤ tr.time k
  · obtain ⟨j, hjm, hcj, hdl⟩ := hcall
    have hdl' := (tr.deadline_mono z j (max_le_max (hτ k hk) le_rfl) P.Δ).trans hdl
    obtain ⟨k', hk'j, ha', -⟩ := hsvc.relay x k B hxk ha hg z j
      (h.antitone (h.time_mono hjm.le) hz) hcj hdl' (hF j hjm.le)
    exact hlift k' (by omega) ha'
  · obtain ⟨k', hk', ha', _⟩ := Healing.accept_before_snapshot hcm fun q hq hfirst =>
      hcatch x k B hxk ha (lt_of_lt_of_le (not_le.mp hg) (le_max_left _ _)) z q
        (h.antitone hcm hz) hfirst (hF q hq)
    exact hlift k' hk' ha'

/-- The snapshot height is attained by a member of its own honest cohort. -/
theorem exists_HZ_holder_at_from {g : Time} (hH : (H (cutZ P g)).Nonempty) {j : Nat}
    (hj : FirstCutAfter tr j (cutZ P g)) :
    ∃ x ∈ H (cutZ P g), (tr.state x j).fg.hmax = HZ tr H g := by
  obtain ⟨y, hy⟩ := hH
  have hne : {h | ∃ y ∈ H (cutZ P g), ∃ j,
      FirstCutAfter tr j (cutZ P g) ∧ (tr.state y j).fg.hmax = h}.Nonempty :=
    ⟨_, y, hy, j, hj, rfl⟩
  obtain ⟨x, hx, j', hj', he⟩ := Nat.sSup_mem hne
    (((Set.finite_range fun z => (tr.state z j).fg.hmax).subset (by
      rintro _ ⟨z, -, j', hj', rfl⟩
      obtain rfl := hj'.unique hj
      exact ⟨z, rfl⟩)).bddAbove)
  obtain rfl := hj'.unique hj
  exact ⟨x, hx, he⟩

/-- **Leaf 2, lower bound.** After its relay obligation is paid, a receiver honest at its cut
has at least the snapshot height, for any node run under growing faults from any starts `ini`. -/
theorem HZ_le_hmax_at_from (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hsvc : Service tr H g ΔF b hold) (hcatch : CatchRun tr H g κ)
    (hH : (H (cutZ P g)).Nonempty) (hsnap : ∃ j, FirstCutAfter tr j (cutZ P g))
    {z : Fin P.n} {m : Nat} (hz : z ∈ H (tr.time m))
    (hf : (H (max (cutZ P g) (tr.time m)))ᶜ.ncard < 2 * P.fg.q - P.n)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (cutZ P g) g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) : HZ tr H g ≤ (tr.state z m).fg.hmax := by
  obtain ⟨j, hj⟩ := hsnap
  obtain ⟨x, hx, hxe⟩ := exists_HZ_holder_at_from hH hj
  have hc0 : 0 ≤ cutZ P g := by
    have := P.slotTime_strictMono.monotone (Nat.zero_le (P.slotOf (gbar g) + 3))
    rwa [P.slotTime_zero] at this
  have hRx := fg_reachable_at_from h hc0 hj.1 hx
  have hm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => h.time_mono hk.le
  have hRz := fg_reachable_at_from h (h.time_nonneg m) hm hz
  obtain ⟨-, -, -, -, -, ⟨B, hB, hBh⟩, -⟩ := Store.cache_invariants _ _ _ _ hRx
  by_cases hle : HZ tr H g ≤ (tr.state z m).fg.hmax
  · exact hle
  have hBz := held_of_relay_le_at_from h hnc hsvc hcatch hc0 hx hz hf hB
    (by omega) hj.1 hcall hcm
  have he := σ_eq_honest_at_from h hnc hc0 hj.1 hx (h.time_nonneg m) hm hz hB hBz
  have hh := (Store.cache_invariants _ _ _ _ hRz).2.2.2.2.1 B hBz
  rw [← he] at hh
  omega

end HZLowerBound

/-! ## Store ancestry below honest blocks -/

section StoreAnc

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- Historical ancestry descends into the reader's actual held tree, for any node run under
growing faults from any starts `ini`. -/
theorem store_anc_of_honest_anc_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {B C : A.Blk} (hBC : Anc (tr.HonestBlocksAt H) B C) (hC : C ∈ (tr.state y k).fg.tree) :
    (tr.state y k).fg.Anc B C := by
  have hs := Trace.upTo_state tr y hle
  have hc : C ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, k, by rwa [hs]⟩
  have hanc := RunTrace.anc_upTo_of_right h hnc ht hc hBC
  rw [← hs]
  exact Healing.store_anc_of_honest_anc_from (h.upTo ht)
    (Compose.NoCollRun.upTo hnc t) hy hanc (by rwa [hs])

end StoreAnc

/-! ## Leaf 3, the frame window -/

section FrameWindowLeaf

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State} {hold : Time}

open AC (gbar)
open Healing.Growing (CatchRun)

/-- Four-key arithmetic bounds the deficit below the maximum height minus one. -/
theorem pred_add_riseRounds_of_key {HZ M j v : Nat}
    (hkey : v = 2 * M + if M = j + 1 then 1 else 0) (hv : 2 * HZ ≤ v) :
    HZ + 1 ≤ M - 1 + riseRounds HZ v := by
  classical
  rw [riseRounds]
  split_ifs at hkey <;> omega

end FrameWindowLeaf

/-! ## Proposal membership and leaf 5, the round crossing -/

section RoundCross

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open AC (gbar)
open Healing.Growing (NoRestartAfter)

/-- An honestly signed row is processed strictly before a sufficiently late honest proposal,
even if the signer has been compromised by then, under the signed-row service clause
(`Service.signedRow`, `Healing.Growing.ResetService.signedRow`) at a hold within `ΔF`. -/
theorem rows_delivered_service_at_from
    {g ΔF b v hold : Time}
    (hrows : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
      (∀ k ≤ i, tr.SignAt x k att → tr.time k = tr.time i → hold ≠ 0 →
        x ∈ H (max (tr.time i) g + hold)) →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
        tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
        ∃ k ≤ j, tr.ProcessAttAt y k att ∧
          tr.time k < tr.deadline y k (max (tr.time i) g) ΔF)
    (hhold : hold ≤ ΔF) (hnr : NoRestartAfter tr H (gbar g))
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hv : gbar g ≤ v) {p : Fin P.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {X : A.Blk} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b) {y : Fin P.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {att : FG.Att P.n} (hsig : tr.SignAt y k att)
    (hk : tr.time k ≤ v) (hyX : y ∈ H (tr.time kX)) : ∃ k' < kX, tr.ProcessAttAt p k' att := by
  have hdl0 : ∀ j ≤ kX, ∀ τ : Time,
      tr.deadline p j τ ΔF ≤ max τ (gbar g) + ΔF := fun j hj τ =>
    Compose.deadline_le_of_restarts
      (fun k' hk' hr => hnr p k' (hrun.antitone (hrun.time_mono (hk'.trans hj)) hp) hr) τ ΔF
  have hg : max (tr.time k) g ≤ v := max_le hk ((Healing.le_gbar g).trans hv)
  have hdl : ∀ j ≤ kX,
      tr.deadline p j (max (tr.time k) g) ΔF ≤ v + ΔF := by
    intro j hj
    have := hdl0 j hj (max (tr.time k) g)
    have := max_le hg hv
    linarith
  obtain ⟨acc, hcall⟩ := hX.1.1
  obtain ⟨k', hk', hproc, hlt⟩ := hrows y k att hy hsig (fun _ _ _ _ _ =>
    hrun.antitone (by linarith) hyX) p kX hp ⟨_, hcall⟩ hkb (by linarith [hdl kX le_rfl])
  refine ⟨k', lt_of_le_of_ne hk' fun h => ?_, hproc⟩
  subst h
  linarith only [hdl k' le_rfl, hlt, hvx]

/-- A proposal's immediate acceptance is held while its proposer is honest, for a run from starts
`ini` at which the AC meets the requirements, with the genesis root: the middle component of
`Healing.accept_of_proposesAt_from` on the proposer's prefix. -/
theorem proposal_mem_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hnc : Compose.NoCollRun dg tr) {p : Fin P.n} {k : Nat}
    (hp : p ∈ H (tr.time k)) {B : A.Blk}
    (hB : tr.ProposesAt p k B) : B ∈ (tr.state p (k + 1)).fg.tree := by
  have hr := hrun.upTo (hrun.time_nonneg k)
  have hB' : (tr.upTo (tr.time k)).ProposesAt p k B :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hB.1⟩, hB.2.1, hB.2.2⟩
  have hm := (Healing.accept_of_proposesAt_from hr hroot (hnc.upTo _) hp (hq p) hB').2.1
  rwa [Trace.upTo_state tr p (fun q hq => hrun.time_mono (by omega))] at hm

private theorem ThSlot_eq_of_anc {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀)
    {B W : NodeBlock P ACP} (h : st.Anc B W)
    (hh : (st.σ W.root).h = (st.σ B.root).h) :
    (st.σ W.root).ThSlot = (st.σ B.root).ThSlot := by
  induction h with
  | refl => rfl
  | @tail Y Y' hBY hYY' ih =>
    obtain ⟨-, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Goldilocks.Store.Reachable.step_σ hr hY' hp
    have h₁ := Healing.h_le_of_store_anc hr hBY
    rcases P.fg.stateTransition_ThSlot ht with ⟨e, e', -⟩ | ⟨e, -, -⟩
    · rw [e']; exact ih (by rw [← e]; exact hh)
    · omega

private theorem ThSlot_le_slot {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀)
    {Z : NodeBlock P ACP} (hZ : Z ∈ st.tree) : (st.σ Z.root).ThSlot ≤ Z.slot := by
  obtain ⟨hcoh, -, hg⟩ := (Goldilocks.Store.accepted_tree _ _ _ _ hr).2
  induction hg Z hZ with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl,
      Goldilocks.Store.Reachable.σ_genesis hr]
    exact Nat.zero_le _
  | @tail Y Y' hGY hYY' ih =>
    obtain ⟨hY, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Goldilocks.Store.Reachable.step_σ hr hY' hp
    have hsl : Y.slot < Y'.slot := hcoh.2 Y hY Y' hY' hp
    have := ih hY
    rcases P.fg.stateTransition_ThSlot ht with ⟨-, e, -⟩ | ⟨-, e, -⟩
    · rw [e]; omega
    · rw [e]; rfl

private theorem processAtt_prog {n : Nat} (σ : FG.ChainState n) (a : FG.Att n) :
    σ.prog ⊆ (σ.processAtt a).prog ∧
      (a.h = σ.h → a.T = σ.Th → a.val ∈ (σ.processAtt a).prog) := by
  unfold FG.ChainState.processAtt
  rcases a.fin with _ | pr
  · dsimp only
    split_ifs <;> simp_all
  · dsimp only
    split_ifs <;> simp_all

private theorem foldl_prog {n : Nat} (σ : FG.ChainState n) (atts : List (FG.Att n)) :
    σ.prog ⊆ (atts.foldl FG.ChainState.processAtt σ).prog ∧
      ∀ a ∈ atts, a.h = σ.h → a.T = σ.Th →
        a.val ∈ (atts.foldl FG.ChainState.processAtt σ).prog := by
  induction atts generalizing σ with
  | nil => exact ⟨subset_rfl, by simp⟩
  | cons b l ih =>
    obtain ⟨p1, r1⟩ := processAtt_prog σ b
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [b]
    have hh : (σ.processAtt b).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt b).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    obtain ⟨p2, r2⟩ := ih (σ.processAtt b)
    refine ⟨p1.trans p2, fun a ha hah haT => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact p2 (r1 hah haT)
    · exact r2 a ha (hah.trans hh.symm) (haT.trans hT.symm)

private theorem step_prog {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    (∀ a ∈ B.atts, a.h ≤ σ.h) ∧
      ((σ'.h = σ.h ∧ σ'.Th = σ.Th ∧
        σ'.prog = (B.atts.foldl FG.ChainState.processAtt { σ with s := B.slot }).prog) ∨
      σ'.h = σ.h + 1) := by
  obtain ⟨⟨-, hv⟩, he⟩ := gp.stateTransition_eq_some.1 h
  refine ⟨fun a ha => ?_, ?_⟩
  · rcases (hv a ha).2 with ⟨h1, -⟩ | ⟨pr, -, -, -, h2⟩
    · exact h1.le
    · exact h2.le
  obtain ⟨f, p, t, hf⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he ⊢
  subst he
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases _
  rcases hcase with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ <;> rw [he]
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨rfl, rfl, rfl⟩

private theorem rows_prog {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀)
    {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∀ X, st.Anc X W → ∀ r ∈ X.fgPayload, r.h ≤ (st.σ W.root).h ∧
      (r.h = (st.σ W.root).h → r.T = (st.σ W.root).Th →
        r.val ∈ (st.σ W.root).prog) := by
  have hg := (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    intro X hX r hrX
    rcases Relation.ReflTransGen.cases_tail hX with rfl | ⟨Z, -, -, -, hZ⟩
    · cases hrX
    · cases hZ
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    obtain ⟨-, -, -, ht⟩ := Goldilocks.Store.Reachable.step_σ hr h2 hp
    obtain ⟨hle, hcase⟩ := step_prog ht
    intro X hX r hrX
    have hX' := Store.anc_parent h1 hp hX
    have hrh : r.h ≤ (st.σ W'.root).h := by
      rcases hX' with rfl | hX'
      · exact hle r hrX
      · exact (ih X hX' r hrX).1
    rcases hcase with ⟨hh, hT, hpg⟩ | hh
    · refine ⟨hh ▸ hrh, fun hrh' hrT => ?_⟩
      rw [hh] at hrh'
      rw [hT] at hrT
      obtain ⟨bp, brow⟩ := foldl_prog { st.σ W'.root with s := W.slot } W.fgView.atts
      rw [hpg]
      rcases hX' with rfl | hX'
      · exact brow r hrX hrh' hrT
      · exact bp ((ih X hX' r hrX).2 hrh' hrT)
    · exact ⟨by omega, fun h' => by omega⟩

private theorem cross_height {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀)
    {X Pr : NodeBlock P ACP} (hX : X ∈ st.tree) (hPr : Pr ∈ st.tree)
    (hpar : X.parent = some Pr.root) (S : Finset (Fin P.n)) (hS : P.fg.q ≤ S.card)
    (hrow : ∀ v ∈ S, ∃ a : FG.Att P.n, a.val = v ∧ a.h = (st.σ Pr.root).h ∧
      a.T = (st.σ Pr.root).Th ∧ (a ∈ X.fgPayload ∨ st.OnChain Pr a))
    (hage : (st.σ Pr.root).ThSlot + P.fg.δt ≤ X.slot) :
    (st.σ X.root).h = (st.σ Pr.root).h + 1 := by
  classical
  obtain ⟨-, -, -, ht⟩ := Goldilocks.Store.Reachable.step_σ hr hX hpar
  obtain ⟨bp, brow⟩ := foldl_prog { st.σ Pr.root with s := X.slot } X.fgPayload
  have hq : P.fg.q ≤
      (X.fgView.atts.foldl FG.ChainState.processAtt { st.σ Pr.root with s := X.slot }).prog.card :=
    hS.trans (Finset.card_le_card fun v hv => by
      obtain ⟨a, rfl, hah, haT, hin | ⟨Z, -, hZ, haZ⟩⟩ := hrow v hv
      · exact brow a hin hah haT
      · exact bp ((rows_prog hr hPr Z hZ a haZ).2 hah haT))
  exact P.fg.cross_of_progress ht hq hage

/-- Delivered historical rows cross one height. -/
theorem round_cross_at_from
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b v hold : Time}
    (hrows : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
      (∀ k ≤ i, tr.SignAt x k att → tr.time k = tr.time i → hold ≠ 0 →
        x ∈ H (max (tr.time i) g + hold)) →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
        tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
        ∃ k ≤ j, tr.ProcessAttAt y k att ∧
          tr.time k < tr.deadline y k (max (tr.time i) g) ΔF)
    (hhold : hold ≤ ΔF) (hnr : NoRestartAfter tr H (gbar g))
    {B D X : A.Blk} (hBH : B ∈ tr.HonestBlocksAt H)
    (hBD : Anc (tr.HonestBlocksAt H) B D) (hpar : X.parent = some D.root)
    {p : Fin P.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    (hX : tr.ProposesAt p kX X) (hf : 3 * (H (tr.time kX))ᶜ.ncard ≤ P.n - 1)
    (hv : gbar g ≤ v) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hage : B.slot + P.δt ≤ X.slot)
    (hrow : ∀ y ∈ H (tr.time kX),
      (∃ w c, w ∈ H (tr.time c) ∧ B ∈ (tr.state w c).fg.tree ∧
        ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧
          tr.time k ≤ v ∧ att.h = ((tr.state w c).fg.σ B.root).h ∧
          att.T = ((tr.state w c).fg.σ B.root).Th) ∨
      ∃ R, Anc (tr.HonestBlocksAt H) R D ∧ ∃ w c, w ∈ H (tr.time c) ∧
        B ∈ (tr.state w c).fg.tree ∧ R ∈ (tr.state w c).fg.tree ∧
          ((tr.state w c).fg.σ B.root).h < ((tr.state w c).fg.σ R.root).h) :
    B ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ B.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h := by
  classical
  have hage' : B.slot + P.fg.δt ≤ X.slot := hage
  have hd := hrun.time_nonneg kX
  have hle : ∀ q < kX, tr.time q ≤ tr.time kX := fun q hq => hrun.time_mono hq.le
  have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun q hq =>
    hrun.time_mono (by omega)
  have hcoh := hrun.coherent hnc
  obtain ⟨Pr, hpar', hPr⟩ := hrun.proposal_parent_held hnc hroot hq hp hX
  obtain ⟨-, hXm, he⟩ := hrun.accept_of_proposesAt hnc hroot hq hp hX
  have hPrH : Pr ∈ tr.HonestBlocksAt H := ⟨p, kX, _, hd, hle, hp, hPr⟩
  have hDH : D ∈ tr.HonestBlocksAt H := by
    rcases Relation.ReflTransGen.cases_tail hBD with rfl | ⟨Z, -, hZ⟩
    · exact hBH
    · exact hZ.2.1
  obtain rfl : D = Pr := hcoh.1 hDH hPrH (Option.some_injective _ (hpar.symm.trans hpar'))
  have hR := hrun.reachable_at hd hle hp
  have hR1 := hrun.reachable_at hd hle1 hp
  have hBDs := hrun.held_anc_at hnc hd hle hp hBD hPr
  have hBst : B ∈ (tr.state p kX).fg.tree := by
    by_cases he : B = D
    · exact he ▸ hPr
    · exact (Anc.mem hBDs he).1
  have hBDh := Healing.h_le_of_store_anc hR hBDs
  have hmono := hrun.tree_mono_at hd hle1 hp (Nat.le_succ kX)
  have hDm := hmono hPr
  have hBm := hmono hBst
  have hσB := σ_eq_honest_at_from hrun hnc hd hle hp hd hle1 hp hBst hBm
  have hσD := σ_eq_honest_at_from hrun hnc hd hle hp hd hle1 hp hPr hDm
  have hle' := Healing.h_le_of_store_anc hR1 (.single ⟨hDm, hXm, hpar⟩)
  refine ⟨hBm, hXm, ?_⟩
  rw [← hσB]
  rw [← hσD] at hle'
  by_cases hlt : ((tr.state p kX).fg.σ B.root).h < ((tr.state p kX).fg.σ D.root).h
  · omega
  have hDh : ((tr.state p kX).fg.σ D.root).h = ((tr.state p kX).fg.σ B.root).h := by omega
  have hDTh := Healing.Th_eq_of_anc hR hBDs hDh
  have hThS : ((tr.state p kX).fg.σ D.root).ThSlot ≤ B.slot := by
    rw [ThSlot_eq_of_anc hR hBDs hDh]
    exact ThSlot_le_slot hR hBst
  let S := Finset.univ.filter (· ∈ H (tr.time kX))
  have hScard : P.fg.q ≤ S.card := by
    have hcard : S.card = (H (tr.time kX)).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp [S]
    rw [hcard]
    have hn : (H (tr.time kX)).ncard + (H (tr.time kX))ᶜ.ncard = P.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    change (2 * P.n + 2) / 3 ≤ _
    omega
  obtain ⟨hXt, hDt, -, hσD', hplace⟩ :=
    hrun.proposal_rows_placed hnc hroot hq hp hX hpar hPr
  have hcross := cross_height hR1 hXt hDt hpar S hScard ?_ ?_
  · have h1 := hcross
    rw [← hσD'] at h1
    omega
  · intro y hyS
    have hy : y ∈ H (tr.time kX) := (Finset.mem_filter.1 hyS).2
    rcases hrow y hy with ⟨w, c, hw, hBw, k, att, hyk, hsig, hk, hah, haT⟩ |
      ⟨R, hRD, w, c, hw, hBw, hRw, hhR⟩
    · have hσ := σ_eq_honest_at_from hrun hnc (hrun.time_nonneg c)
        (fun q hq => hrun.time_mono hq.le) hw hd hle hp hBw hBst
      rw [hσ] at hah haT
      have hproc :=
        rows_delivered_service_at_from hrows hhold hnr hrun hv hp hX hvx hkb hyk hsig hk hy
      have hval : att.val = y := by
        obtain ⟨src, hc⟩ := hsig
        have hc' := (hrun.attest_some hc hyk).1
        unfold Store.attest FG.Record.createAtt at hc'
        split at hc'
        · cases hc'
        · split_ifs at hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨rfl, -⟩ := hc'
          rfl
      rw [← hσD']
      refine ⟨att, hval, hah.trans hDh.symm, haT.trans hDTh.symm, ?_⟩
      exact hplace att hproc (hah.trans hDh.symm) (haT.trans hDTh.symm)
    · exfalso
      have hRDs := hrun.held_anc_at hnc hd hle hp hRD hPr
      have hRst : R ∈ (tr.state p kX).fg.tree := by
        by_cases he : R = D
        · exact he ▸ hPr
        · exact (Anc.mem hRDs he).1
      have hRDh := Healing.h_le_of_store_anc hR hRDs
      rw [σ_eq_honest_at_from hrun hnc (hrun.time_nonneg c)
          (fun q hq => hrun.time_mono hq.le) hw hd hle hp hBw hBst,
        σ_eq_honest_at_from hrun hnc (hrun.time_nonneg c)
          (fun q hq => hrun.time_mono hq.le) hw hd hle hp hRw hRst] at hhR
      omega
  · rw [← hσD']
    omega

end RoundCross

/-! ## Leaf 14 -/

section HighEntry

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- Leaf 14: two self-entries of equal height, each read at its own observation honest at a time
after its cuts, below two compatible honest blocks, are the same block. The generic leaf supplies
the compatibility of its high origins by `ACHealing.origins_comparable`. -/
theorem high_entry_eq_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {B B' Z₁ Z₂ : A.Blk}
    (hBB' : Compatible (tr.HonestBlocksAt H) B B')
    (h₁ : Anc (tr.HonestBlocksAt H) Z₁ B) (h₂ : Anc (tr.HonestBlocksAt H) Z₂ B')
    {y₁ y₂ : Fin P.n} {m₁ m₂ : Nat} {t₁ t₂ : Time}
    (ht₁ : 0 ≤ t₁) (hle₁ : ∀ q < m₁, tr.time q ≤ t₁) (hy₁ : y₁ ∈ H t₁)
    (ht₂ : 0 ≤ t₂) (hle₂ : ∀ q < m₂, tr.time q ≤ t₂) (hy₂ : y₂ ∈ H t₂)
    (hZ₁ : Z₁ ∈ (tr.state y₁ m₁).fg.tree) (hZ₂ : Z₂ ∈ (tr.state y₂ m₂).fg.tree)
    (hh : ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have hU := Compose.Growing.honest_blocks_coherent_local h hnc
  -- Both entries below one block `D` held at an honest observation: compare them in that store.
  have key : ∀ {D : A.Blk}, D ∈ tr.HonestBlocksAt H → Anc (tr.HonestBlocksAt H) Z₁ D →
      Anc (tr.HonestBlocksAt H) Z₂ D → Z₁.root = Z₂.root := by
    rintro D ⟨w, k, t, ht, hle, hw, hD⟩ hZ₁D hZ₂D
    have hr := fg_reachable_at_from h ht hle hw
    have mem : ∀ {Z : A.Blk}, Anc (tr.HonestBlocksAt H) Z D → Z ∈ (tr.state w k).fg.tree := by
      intro Z hZ
      by_cases he : Z = D
      · exact he ▸ hD
      · exact (Anc.mem (store_anc_of_honest_anc_at_from h hnc ht hle hw hZ hD) he).1
    have e₁ := σ_eq_honest_at_from h hnc ht₁ hle₁ hy₁ ht hle hw hZ₁ (mem hZ₁D)
    have e₂ := σ_eq_honest_at_from h hnc ht₂ hle₂ hy₂ ht hle hw hZ₂ (mem hZ₂D)
    rw [e₁] at hh hT₁
    rw [e₂] at hh hT₂
    rcases Anc.total hU hZ₁D hZ₂D with h12 | h21
    · have := Healing.Th_eq_of_anc hr
        (store_anc_of_honest_anc_at_from h hnc ht hle hw h12 (mem hZ₂D)) hh.symm
      rw [← hT₁, ← hT₂, this]
    · have := Healing.Th_eq_of_anc hr
        (store_anc_of_honest_anc_at_from h hnc ht hle hw h21 (mem hZ₁D)) hh
      rw [← hT₁, ← hT₂, this]
  -- The later of the two compatible blocks is held, unless all four blocks coincide.
  have top : ∀ {D D' Y Y' : A.Blk}, Anc (tr.HonestBlocksAt H) D D' →
      Anc (tr.HonestBlocksAt H) Y D → Anc (tr.HonestBlocksAt H) Y' D' →
      (Y = D ∧ D = D' ∧ Y' = D') ∨ D' ∈ tr.HonestBlocksAt H := by
    intro D D' Y Y' hDD' hY hY'
    by_cases e₁ : Y' = D'
    · by_cases e₂ : D = D'
      · by_cases e₃ : Y = D
        · exact Or.inl ⟨e₃, e₂, e₁⟩
        · exact Or.inr (e₂ ▸ (Anc.mem hY e₃).2)
      · exact Or.inr (Anc.mem hDD' e₂).2
    · exact Or.inr (Anc.mem hY' e₁).2
  rcases hBB' with hBB' | hB'B
  · rcases top hBB' h₁ h₂ with ⟨rfl, rfl, rfl⟩ | hB'
    · rfl
    · exact key hB' (h₁.trans hBB') h₂
  · rcases top hB'B h₂ h₁ with ⟨rfl, rfl, rfl⟩ | hB
    · rfl
    · exact key hB h₁ (h₂.trans hB'B)

end HighEntry

/-! ## Leaf 4 -/

section RowOrHigh

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open Healing (cutZ EntryOf)
open Healing.Growing (HZ)

/-- Parent closure at a held-state observation, for any node run under growing faults from any
starts `ini`. -/
theorem mem_of_honest_anc_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {B C : A.Blk} (h : Anc (tr.HonestBlocksAt H) B C) (hC : C ∈ (tr.state y k).fg.tree) :
    B ∈ (tr.state y k).fg.tree := by
  by_cases he : B = C
  · exact he ▸ hC
  · exact (Anc.mem (store_anc_of_honest_anc_at_from hrun hnc ht hle hy h hC) he).1

private theorem step_pending_just {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    ∀ p ∈ σ'.pending, p ∈ σ.pending ∨ p = (σ'.hj, σ'.J) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, pr, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := pr, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] <;> intro q hq
  · simp only [FG.ChainState.advance] at hq ⊢
    rcases List.mem_append.1 (List.mem_of_mem_drop hq) with hq | hq
    · exact Or.inl (List.mem_filter.1 hq).1
    · exact Or.inr (List.mem_singleton.1 hq)
  · simp only [FG.ChainState.advance] at hq
    exact Or.inl (List.mem_filter.1 hq).1
  · exact Or.inl (List.mem_filter.1 hq).1

private theorem pending_justified {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀)
    {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∀ p ∈ (st.σ W.root).pending, ∃ B ∈ st.tree, (st.σ B.root).hj = p.1 ∧
      (st.σ B.root).J = p.2 := by
  have hA := (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl,
      Goldilocks.Store.Reachable.σ_genesis hr]
    intro p hp
    simp [FG.ChainState.init] at hp
  | @tail Y W' _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := Goldilocks.Store.Reachable.step_σ hr hYW.2.1 hYW.2.2
    intro p hp
    rcases step_pending_just ht p hp with hp | rfl
    · exact ih p hp
    · exact ⟨W', hYW.2.1, rfl, rfl⟩

private theorem finalityPair_justified {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀)
    {W : NodeBlock P ACP} (hW : W ∈ st.tree) {Λ : FG.Record} {p : Nat × Nat}
    (hp : Λ.finalityPair (st.σ W.root) = some p) :
    ∃ B ∈ st.tree, (st.σ B.root).hj = p.1 ∧ (st.σ B.root).J = p.2 := by
  unfold FG.Record.finalityPair at hp
  split_ifs at hp
  · cases hp
    exact ⟨W, hW, rfl, rfl⟩
  · rcases FG.Record.foldl_newest_mem_or_initial hp with h' | h'
    · cases h'
    · exact pending_justified hr hW p (List.mem_filter.1 h').1

private theorem signed_fin_justified_at
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {k : Nat} (hy : y ∈ H (tr.time k)) {att : FG.Att P.n}
    (hs : tr.SignAt y k att) {h X : Nat} (hfin : att.fin = some (h, X)) :
    ∃ B ∈ (tr.state y k).fg.tree, ((tr.state y k).fg.σ B.root).hj = h ∧
      ((tr.state y k).fg.σ B.root).J = X := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hrun.attest_some hc hy).1
  have hr := hrun.reachable_at (hrun.time_nonneg k)
    (fun q hq => hrun.time_mono hq.le) hy
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨-, -, -, hfp, -⟩ := Healing.Client.createAtt_some hcl
  have hentry : ∃ W ∈ (tr.state y k).fg.tree,
      (tr.state y k).fg.σ ((tr.state y k).fg.σ src.root).Th =
        (tr.state y k).fg.σ W.root := by
    rcases hs : (tr.state y k).fg.blocks src.root with _ | B
    · have hg : ((tr.state y k).fg.σ src.root).Th = P.genesisRoot := by
        rw [Healing.Store.σ_of_blocks_none hr hs]
        rfl
      exact ⟨_, Healing.Store.genesis_mem hr, by rw [hg]; rfl⟩
    · have hBr := Goldilocks.Store.Reachable.blocks_root hr hs
      have hB : B ∈ (tr.state y k).fg.tree := by
        change (tr.state y k).fg.blocks B.root = some B
        rwa [hBr]
      obtain ⟨⟨E, hE, hEr, -⟩, -⟩ := Goldilocks.Store.entry_state_of_source _ _ _ _ hr B hB
      exact ⟨E, hE, by rw [hEr, hBr]⟩
  obtain ⟨W, hW, hWσ⟩ := hentry
  rw [hWσ, hfin] at hfp
  exact finalityPair_justified hr hW hfp.symm

/-- Finalized-cache ancestry under held-attestation safety. -/
private theorem F_anc_of_hj_lt_at
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    {B : A.Blk} (hB : B ∈ (tr.state y i).fg.tree)
    (hlt : (tr.state y i).fg.hj < ((tr.state y i).fg.σ B.root).h) :
    (tr.state y i).fg.Anc (tr.state y i).fg.F B :=
  have hR := hrun.reachable_at ht hle hy
  Healing.Store.F_anc_of_hj_lt_of_safe hR hR
    (Goldilocks.Store.accepted_tree _ _ _ _ hR).2.1 subset_rfl subset_rfl hf
    (hrun.held_atts_safe_at ht hle hy ht hle hy le_rfl le_rfl) hB hlt

/-- A finality lock is below the justified cache when that cache is maximal. -/
private theorem hj_ge_of_lock_at
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * P.fg.q - P.n) {h r : Nat}
    (hl : (tr.state y i).record.lock h = some r) : h ≤ (tr.state y i).fg.hj := by
  obtain ⟨k, hk, att, hsa, hfin⟩ := (hrun.client_record_origin ht hle hy h r).2 hl
  have hlek : ∀ q < k, tr.time q ≤ t := fun q hq => hle q (hq.trans hk)
  obtain ⟨B, hB, hBj, -⟩ := signed_fin_justified_at hrun
    (hrun.antitone (hle k hk) hy) hsa hfin
  refine le_trans ?_ (hrun.hj_mono_at ht hle hy hk.le)
  have hR := hrun.reachable_at ht hlek hy
  by_contra hlt
  have hlt' : (tr.state y k).fg.hj < ((tr.state y k).fg.σ B.root).h := by
    have := Healing.Store.hj_lt_h hR hB
    omega
  have hFB := F_anc_of_hj_lt_at hrun ht hlek hy hf hB hlt'
  obtain ⟨E, hE, hEr, hEB, -⟩ := Healing.Store.J_entry_of_reachable hR hB
  have hEh := Healing.Store.J_height_le hR hB hE hEr
  have hjm := hrun.jmax_at ht hlek hy B hB E hE hEr
  obtain ⟨-, hcoh, -, hgen⟩ := Goldilocks.Store.accepted_tree _ _ _ _ hR
  rcases Anc.total hcoh hFB hEB with hFE | hEF
  · have := hjm hFE
    omega
  · obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj', hBjJ, hBjhj⟩, -⟩ :=
      Goldilocks.Store.cache_invariants _ _ _ _ hR
    obtain ⟨E', hE', hEr', -, hEg⟩ := Healing.Store.J_entry_of_reachable hR hBj'
    have hEJ : E'.root = (tr.state y k).fg.J.root := hEr'.trans hBjJ
    have hFh := Healing.h_le_of_store_anc hR hFJ
    rcases hEg with rfl | ⟨hEh', -⟩
    · have he := hcoh.1 hE' hJm hEJ
      rw [← he] at hFJ
      have hFg := Anc.antisymm hcoh hFJ (hgen _ hFm)
      have := hjm (hFg ▸ hgen E hE)
      omega
    · rw [← hEJ, hEh', hBjhj] at hFh
      have := Healing.h_le_of_store_anc hR hEF
      omega

/-- A lock at the cache's justified height names the cache's justified root. -/
private theorem lock_root_eq_J_at
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * P.fg.q - P.n) {h r : Nat}
    (hl : (tr.state y i).record.lock h = some r) (hj : (tr.state y i).fg.hj = h) :
    r = (tr.state y i).fg.J.root := by
  obtain ⟨k, hk, att, hsa, hfin⟩ := (hrun.client_record_origin ht hle hy h r).2 hl
  obtain ⟨B, hB, hBj, hBJ⟩ := signed_fin_justified_at hrun
    (hrun.antitone (hle k hk) hy) hsa hfin
  have hB' := hrun.tree_mono_at ht hle hy hk.le hB
  have hlek : ∀ q < k, tr.time q ≤ t := fun q hq => hle q (hq.trans hk)
  have hσ := σ_eq_honest_at_from hrun hnc ht hlek hy ht hle hy hB hB'
  rw [hσ] at hBj hBJ
  have hR := hrun.reachable_at ht hle hy
  obtain ⟨-, -, -, ⟨Bj, hBjt, hBjJ, hBjhj⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hR
  have he := Goldilocks.Store.J_eq_of_hj_eq_of_safe hR hR hf
    (hrun.held_atts_safe_at ht hle hy ht hle hy le_rfl le_rfl) hB' hBjt (by omega)
  exact hBJ.symm.trans (he.trans hBjJ)

/-- No honest advance implies no finality lock at the frontier before the deadline. -/
private theorem lock_none_of_noAdvance_at
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {c T t : Time} {h : Nat}
    (hna : ∀ v k att, v ∈ H (max c (tr.time k)) → tr.SignAt v k att → tr.time k < T → att.h ≤ h)
    {y : Fin P.n} {i : Nat} (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t)
    (hyc : y ∈ H (max c t)) (htT : t < T) : (tr.state y i).record.lock h = none := by
  have hy := hrun.antitone (le_max_right _ _) hyc
  rcases hl : (tr.state y i).record.lock h with _ | r
  · rfl
  obtain ⟨k, hk, att, hs, hfin⟩ := (hrun.client_record_origin ht hle hy h r).2 hl
  have hwf := hrun.signAt_wellFormed (hrun.antitone (hle k hk) hy) hs
  have hbound := hna y k att (hrun.antitone (max_le_max le_rfl (hle k hk)) hyc) hs
    ((hle k hk).trans_lt htT)
  have := hwf.2 (h, r) (by simp [hfin])
  omega

/-- In kind F the source-height lock is free; in kind J it is free or the entry. -/
private theorem lock_free_or_entry_of_frame_at
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ i < k, tr.time i ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    {C E : A.Blk} {h : Nat}
    (hE : EntryOf (tr.state y k).fg C E h) (hCh : ((tr.state y k).fg.σ C.root).h = h)
    (hkind : (tr.state y k).fg.hj < h ∨
      ((tr.state y k).fg.hj = h ∧ (tr.state y k).fg.Anc (tr.state y k).fg.J C)) :
    (tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root := by
  rcases hkind with hlt | ⟨hj, hJC⟩
  · left
    rcases hl : (tr.state y k).record.lock h with _ | r
    · rfl
    · have := hj_ge_of_lock_at hrun ht hle hy hf hl
      omega
  rcases hl : (tr.state y k).record.lock h with _ | r
  · exact Or.inl rfl
  refine Or.inr (congrArg some ?_)
  rw [lock_root_eq_J_at hrun hnc ht hle hy hf hl hj]
  have hr := hrun.reachable_at ht hle hy
  obtain ⟨⟨-, hETh⟩, hEh, hEC⟩ := hE
  obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hr
  have hJh := Healing.Store.J_height_le hr hBj hJm hBjJ.symm
  have hJCh := Healing.h_le_of_store_anc hr hJC
  obtain ⟨E', hE', hE'r, -, hE'g⟩ := Healing.Store.J_entry_of_reachable hr hBj
  have hE'J : E' = (tr.state y k).fg.J := by
    have h1 : (tr.state y k).fg.blocks E'.root = some E' := hE'
    have h2 : (tr.state y k).fg.blocks (tr.state y k).fg.J.root = some (tr.state y k).fg.J := hJm
    rw [hE'r, hBjJ] at h1
    exact Option.some.inj (h1.symm.trans h2)
  subst hE'J
  have hJTh : ((tr.state y k).fg.σ (tr.state y k).fg.J.root).Th = (tr.state y k).fg.J.root := by
    rcases hE'g with he | ⟨-, hTh⟩
    · have hg : (P.genesisBlock A.genesisPayload).root = P.genesisRoot := rfl
      rw [he, hg, Goldilocks.Store.Reachable.σ_genesis hr]
      rfl
    · exact hTh
  have hJeq : ((tr.state y k).fg.σ C.root).h =
      ((tr.state y k).fg.σ (tr.state y k).fg.J.root).h := by omega
  have h1 := Healing.Th_eq_of_anc hr hJC hJeq
  have h2 := Healing.Th_eq_of_anc hr hEC (hCh.trans hEh.symm)
  rw [hJTh] at h1
  rw [hETh] at h2
  exact h1.symm.trans h2

/-- Client progress uses only its own prefix, with no global origin invariant. -/
private theorem client_progress_of_lock_at
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {k : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ i < k, tr.time i ≤ t) (hkt : tr.time k ≤ t) (hy : y ∈ H t)
    {C : A.Blk} {signed : Option (FG.Att P.n)}
    (hc : tr.CallAt y k (.fg (.attest C signed)))
    {E : A.Blk} {h : Nat}
    (hE : EntryOf (tr.state y k).fg C E h) (hCh : ((tr.state y k).fg.σ C.root).h = h)
    (hlock : (tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root) :
    (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
      ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root := by
  have hr := hrun.reachable_at ht hle hy
  have hyk := hrun.antitone hkt hy
  obtain ⟨⟨-, hETh⟩, hEh, hEC⟩ := hE
  have hCTh : ((tr.state y k).fg.σ C.root).Th = E.root := by
    rw [Healing.Th_eq_of_anc hr hEC (hCh.trans hEh.symm), hETh]
  have hσe : (tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th =
      (tr.state y k).fg.σ E.root := by rw [hCTh]
  cases signed with
  | some a =>
    have hcl := (hrun.attest_some hc hyk).1
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = some (a, _) at hcl
    rw [hσe] at hcl
    obtain ⟨-, hah, haT, -⟩ := Healing.Client.createAtt_some hcl
    exact Or.inl ⟨a, rfl, hah.trans hEh, haT.trans hETh⟩
  | none =>
    have hcl := (hrun.attest_none hc hyk).1
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = none at hcl
    rw [hσe] at hcl
    rcases Healing.Client.createAtt_none hcl with ⟨h1, h2⟩ | ⟨b, hb, hbh, hbT⟩
    · simp only [hEh, hETh] at h1 h2
      rcases hlock with hl | hl
      · exact absurd hl h1
      · exact absurd hl h2
    simp only [hEh, hETh] at hbh hbT
    have hbT' : b.2.1 = E.root := by
      rcases hbT with hbT | ⟨hto, htg⟩
      · exact hbT
      obtain ⟨h1, h2⟩ := hrun.record_sentOK ht hle hy b hb
      cases hτ : b.2.2.1
      · have := h2 hτ
        rw [hbh] at this
        rcases htg with htg | htg <;> rw [htg] at this
        · cases this
        · exact (Option.some.inj this).symm
      · have := h1 hτ
        rw [hbh, hto] at this
        simp at this
    obtain ⟨k', hk', att, hsa, rfl⟩ := hrun.sent_origin ht hle hy hb
    exact Or.inr ⟨k', hk', att, hsa, hbh, hbT'⟩

/-- **Row or high, at an `fg_attest` call**: an attest call at cut `k` on a held source `C`
above `B`, by a caller honest at it and at `c_z` before any height advance, with `B`'s kind at
`k`, has signed a row for `B`'s height and entry by `k`, or `C` is higher than `B`. The call need
not follow a report in the same tick, so a delayed vote uses this directly. -/
theorem row_or_high_of_attest_at_from
    {sg : A.Msg → Fin P.n} (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g T : Time}
    (hf : ∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ P.n - 1) (hna : NoAdvance tr H g T)
    {y : Fin P.n} {k : Nat} {C B : A.Blk} {s : Option (FG.Att P.n)}
    (hyz : y ∈ H (max (cutZ P g) (tr.time k)))
    (hc : tr.CallAt y k (.fg (.attest C s))) (hkT : tr.time k < T)
    (hCm : C ∈ (tr.state y k).fg.tree) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hkind : ((tr.state y k).fg.σ C.root).h = ((tr.state y k).fg.σ B.root).h →
      ((tr.state y k).fg.σ B.root).h = HZ tr H g ∨
      (tr.state y k).fg.hj < ((tr.state y k).fg.σ B.root).h ∨
      ((tr.state y k).fg.hj = ((tr.state y k).fg.σ B.root).h ∧
        (tr.state y k).fg.Anc (tr.state y k).fg.J C)) :
    B ∈ (tr.state y k).fg.tree ∧ C ∈ (tr.state y k).fg.tree ∧
      ((∃ j att, y ∈ H (tr.time j) ∧ tr.SignAt y j att ∧ tr.time j ≤ tr.time k ∧
        att.h = ((tr.state y k).fg.σ B.root).h ∧
        att.T = ((tr.state y k).fg.σ B.root).Th) ∨
        ((tr.state y k).fg.σ B.root).h < ((tr.state y k).fg.σ C.root).h) := by
  have hy := hrun.antitone (le_max_right _ _) hyz
  have ht0 := hrun.time_nonneg k
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
  have hreach := hrun.reachable_at ht0 hle hy
  have hBCs := hrun.held_anc_at hnc ht0 hle hy hBC hCm
  have hBm : B ∈ (tr.state y k).fg.tree := by
    by_cases he : B = C
    · exact he ▸ hCm
    · exact (Anc.mem hBCs he).1
  have hheight := Healing.h_le_of_store_anc hreach hBCs
  refine ⟨hBm, hCm, ?_⟩
  rcases hheight.lt_or_eq with hlt | heq
  · exact Or.inr hlt
  left
  have hf' : (H (tr.time k))ᶜ.ncard < 2 * P.fg.q - P.n := by
    have hbound := hf (tr.time k) ht0 hkT
    have hn := P.hn
    change (H (tr.time k))ᶜ.ncard < 2 * ((2 * P.n + 2) / 3) - P.n
    omega
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hETh⟩, -⟩ :=
    Goldilocks.Store.entry_state_of_source _ _ _ _ hreach C hCm
  have hEnt : EntryOf (tr.state y k).fg C E ((tr.state y k).fg.σ B.root).h :=
    ⟨⟨hE, hETh.trans hEr.symm⟩, hEh.trans heq.symm, hEC⟩
  have hTh : E.root = ((tr.state y k).fg.σ B.root).Th :=
    hEr.trans (Healing.Th_eq_of_anc hreach hBCs heq.symm)
  have hlock : (tr.state y k).record.lock ((tr.state y k).fg.σ B.root).h = none ∨
      (tr.state y k).record.lock ((tr.state y k).fg.σ B.root).h = some E.root := by
    rcases hkind heq.symm with hHZ | hk
    · rw [hHZ]
      exact Or.inl (lock_none_of_noAdvance_at hrun hna ht0 hle hyz hkT)
    · exact lock_free_or_entry_of_frame_at hrun hnc ht0 hle hy hf'
        hEnt heq.symm hk
  rcases client_progress_of_lock_at hrun ht0 hle le_rfl hy hc hEnt
      heq.symm hlock with
    ⟨att, rfl, hah, haT⟩ | ⟨j, hj, att, hsign, hah, haT⟩
  · exact ⟨k, att, hy, ⟨C, hc⟩, le_rfl, hah, haT.trans hTh⟩
  · have hjt := hle j hj
    exact ⟨j, att, hrun.antitone hjt hy, hsign, hjt, hah, haT.trans hTh⟩

/-- Leaf 4: a held report by a reporter honest at it and at `c_z`, before any height advance and
under the fault bound, either supplies a row of the lower block signed while honest, or is strictly
higher than it. -/
theorem row_or_high_of_report_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g T : Time}
    (hf : ∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ P.n - 1) (hna : NoAdvance tr H g T)
    {y : Fin P.n} {i : Nat} {R B : A.Blk} (hyz : y ∈ H (max (cutZ P g) (tr.time i)))
    (hR : ReportAt tr y i R) (hiT : tr.time i < T) (hRm : R ∈ (tr.state y i).fg.tree)
    (hBR : Anc (tr.HonestBlocksAt H) B R)
    (hkind : ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ B.root).h →
      ((tr.state y i).fg.σ B.root).h = HZ tr H g ∨
      (tr.state y i).fg.hj < ((tr.state y i).fg.σ B.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ B.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)) :
    B ∈ (tr.state y i).fg.tree ∧ R ∈ (tr.state y i).fg.tree ∧
      ((∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ tr.time i ∧
        att.h = ((tr.state y i).fg.σ B.root).h ∧
        att.T = ((tr.state y i).fg.σ B.root).Th) ∨
        ((tr.state y i).fg.σ B.root).h < ((tr.state y i).fg.σ R.root).h) := by
  have hy := hrun.antitone (le_max_right _ _) hyz
  have ht0 := hrun.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hr := hrun.upTo ht0
  have hs := Trace.upTo_state tr y hle
  obtain ⟨ell, hc, hto, hres⟩ := hR
  have hc' : (tr.upTo (tr.time i)).CallAt y i (.ac ell) :=
    (Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩
  have hres' : (A.toFG ((tr.upTo (tr.time i)).state y i).ac ell.frame (tr.time i)).2 =
      some R := by rwa [hs]
  obtain ⟨sg', hatt', ht, hfg'⟩ := Healing.toFG_attest hr hy hc' hto hres'
  have hatt := ((Trace.upTo_callAt tr).mp hatt').2
  have ht' : tr.time (i + 1) = tr.time i := ht
  have hle' : ∀ k < i + 1, tr.time k ≤ tr.time i := fun k hk =>
    hrun.time_mono (Nat.lt_succ_iff.mp hk)
  have hs' := Trace.upTo_state tr y hle'
  have hfg : (tr.state y (i + 1)).fg = (tr.state y i).fg := by
    simpa only [hs, hs'] using hfg'
  have := row_or_high_of_attest_at_from hrun hnc hf hna (by rwa [ht']) hatt (by rwa [ht'])
    (by rwa [hfg]) hBR (by rw [hfg]; exact hkind)
  rw [hfg, ht'] at this
  exact this

end RowOrHigh

/-! ## Honesty truncated after a horizon -/

section Truncation

variable {P : Params} {A : NodeAC P} {tr : RunTrace A} {H : Time → Set (Fin P.n)}

open Healing (cutZ)
open Healing.Growing (HZ IsReset CatchRun)

theorem truncH_eq_of_le {b t : Time} (ht : t ≤ b) : truncH H b t = H t :=
  Set.ext fun _ => and_iff_left ht

/-- The truncation of an antitone honest set is antitone: membership at `t'` gives `t' ≤ b`. -/
theorem truncH_antitone (hH : Antitone H) (b : Time) : Antitone (truncH H b) :=
  fun _ _ htt' _ hy => ⟨hH htt' hy.1, htt'.trans hy.2⟩

/-- Truncating honesty preserves the run laws without changing the trace or starts. -/
theorem _root_.Consensus.Goldilocks.Growing.LocalRun.truncH
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {sg : A.Msg → Fin P.n} {ini : Fin P.n → A.State}
    (hrun : Growing.LocalRun proposer dg H sg tr ini) (b : Time) :
    Growing.LocalRun proposer dg (truncH H b) sg tr ini where
  antitone := truncH_antitone hrun.antitone b
  init y hy := hrun.init y hy.1
  grouped y i c hc hy := hrun.grouped y i c hc hy.1
  cutLaw y i c hc hy := hrun.cutLaw y i c hc hy.1
  wire y j t e hy := hrun.wire y j t e hy.1
  proposerCredential y j t B hy := hrun.proposerCredential y j t B hy.1
  time_nonneg := hrun.time_nonneg
  time_mono := hrun.time_mono
  finite := hrun.finite
  phase_order y y' j j' t e e' hy hy' := hrun.phase_order y y' j j' t e e' hy.1 hy'.1
  tick_public y j t hy := hrun.tick_public y j t hy.1
  tick_unique y j j' t hy := hrun.tick_unique y j j' t hy.1
  tick_of_awake y t hy := hrun.tick_of_awake y t hy.1
  awake_in_horizon y t hy := hrun.awake_in_horizon y t hy.1
  awake_of_call y i hy := hrun.awake_of_call y i hy.1
  restart_of_sleep y i u hy := hrun.restart_of_sleep y i u hy.1
  restart_at_wake y u v hy := hrun.restart_at_wake y u v hy.1
  sleep_of_restart y i hy := hrun.sleep_of_restart y i hy.1
  block_unforgeable y i B hy hB hp := hrun.block_unforgeable y i B hy.1 hB hp.1
  att_unforgeable y i a hy ha hs := hrun.att_unforgeable y i a hy.1 ha hs.1
  msg_unforgeable y i m hy hm hs := hrun.msg_unforgeable y i m hy.1 hm hs.1

theorem honestBlocksAt_truncH_subset (b : Time) :
    tr.HonestBlocksAt (truncH H b) ⊆ tr.HonestBlocksAt H :=
  fun _ ⟨y, i, t, ht, hle, hy, hB⟩ => ⟨y, i, t, ht, hle, hy.1, hB⟩

theorem catchRun_truncH {g κ : Time} (hc : CatchRun tr H g κ) (b : Time) :
    CatchRun tr (truncH H b) g κ :=
  fun x i B hx hA hlt y j hy hfirst hF =>
    hc x i B hx.1 hA hlt y j hy.1 hfirst (Anc.mono (honestBlocksAt_truncH_subset b) hF)

/-- `H_z` is read at `c_z`, where the truncation is `H` itself. -/
theorem HZ_truncH {g b : Time} (hcz : cutZ P g ≤ b) : HZ tr (truncH H b) g = HZ tr H g := by
  simp only [HZ, truncH_eq_of_le hcz]

/-- With `c_z` and the reset by `b`, the reset on the truncation is the reset for `H`: its signing
is by `b`, where the truncation is `H`, and a signing after `b` is after the reset. -/
theorem isReset_truncH_iff {g a b : Time} (hcz : cutZ P g ≤ b) (hab : a ≤ b) :
    IsReset tr (truncH H b) g a ↔ IsReset tr H g a := by
  unfold IsReset
  rw [HZ_truncH hcz]
  constructor
  · rintro ⟨⟨y, k, att, hy, hs, hh, hk⟩, hmin⟩
    refine ⟨⟨y, k, att, hy.1, hs, hh, hk⟩, fun y' k' att' hy' hs' hh' => ?_⟩
    by_cases hk' : tr.time k' ≤ b
    · exact hmin y' k' att' ⟨hy', max_le hcz hk'⟩ hs' hh'
    · exact hab.trans (lt_of_not_ge hk').le
  · rintro ⟨⟨y, k, att, hy, hs, hh, hk⟩, hmin⟩
    exact ⟨⟨y, k, att, ⟨hy, max_le hcz (hk.le.trans hab)⟩, hs, hh, hk⟩,
      fun y' k' att' hy' hs' hh' => hmin y' k' att' hy'.1 hs' hh'⟩

end Truncation

end Consensus.Goldilocks.Generic
