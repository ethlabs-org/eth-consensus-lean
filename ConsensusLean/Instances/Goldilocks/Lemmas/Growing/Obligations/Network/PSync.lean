module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Network transport under growing faults: service after GST

The partial-synchrony (`PSync g`) service of the canonical growing trace, with senders honest at
their event and recipients honest at their call:

* `received_forward_stamp_le_of_stamp_at`: a received wrapper of a signer honest at its stamp is
  stamped no later than the receipt;
* `publication_held_before_gst_deadline_at`, `publication_acceptedBy_psync_any_at`,
  `acceptance_relay_psync_any_at`: acceptance relay at the effective `max(source, GST)` deadline;
* `held_forward_blockCall_before_at`, `publication_blockDeliveredBy_psync_at`,
  `ownBlockAt_accept_at`, `block_service_psync_at`: block service;
* `vote_message_service_psync_other_at`, `message_service_psync_at`: message service;
* `resetService_of_psync_at`: the reset service of a healthy run;
* `catchRun_of_psync_at`: old acceptances catch up by the first `2Δ` snapshot after GST. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)

/-- A received forwarding wrapper of a signer honest at its stamp carries a stamp no later than
the receipt: were the receipt earlier, the signer would be honest at it. -/
theorem received_forward_stamp_le_of_stamp_at (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {receipt o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t u : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∉ rho.faultyAt t)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) : t ≤ u := by
  by_contra h
  have hut : u ≤ t := (lt_of_not_ge h).le
  exact h (received_forward_stamp_le_at S rho hn hv he hc
    (fun hf => hx (rho.faultyAt_mono hut hf)) hd)

/-- GST holdings of an actual publication by an origin honest at its event, at a recipient
honest at its call, before the effective `max(source, GST)` deadline. -/
theorem publication_held_before_gst_deadline_at (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r)
    (hx : rho.key r.origin ∉ rho.faultyAt ((publisherExecution S rho).eventTime r.event))
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j) {τ : Time} (hτ : 0 ≤ τ)
    (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hb : (simTraceAt S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTraceAt S rho hn).time j) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧
      d < (simTraceAt S rho hn).deadline y j (max τ g) (S.params (Model.pubOf E) hn).Δ := by
  obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval_at S rho hn hv hy hj
    (hτ.trans (le_max_left τ g))
  rw [heq] at hb hd ⊢
  have hga : max a g = a := max_eq_left ((le_max_right τ g).trans ha)
  have hslack : a + E.ΔAC - 1 < a + (S.params (Model.pubOf E) hn).Δ := by
    change a + E.ΔAC - 1 < a + E.ΔAC
    exact sub_one_lt _
  have hbj : a + E.ΔAC - 1 ≤ (simTraceAt S rho hn).time j := hslack.le.trans hd
  have hbh : a + E.ΔAC - 1 ≤ rho.horizon := hslack.le.trans hb
  have hheld := (publication_held_psync_at S rho hn hnet r hr hx hrow
    (by rw [hga]; exact not_faulty_of_mem_honestKeysAt S rho hy hbj hbh)
    (ht ▸ (le_max_left τ g).trans ha)
    (by rw [hga]; exact hbh)
    (by rw [hga]; exact fun u hau hud => hw u hau (hud.trans hbj))).1
  rw [hga] at hheld
  exact ⟨a + E.ΔAC - 1, hheld, hslack⟩

/-- Acceptance service for an actual publication by an origin honest at its event, including a
pre-GST one, at the effective `max(source, GST)` deadline at the acceptance cut. -/
theorem publication_acceptedBy_psync_any_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r)
    {τ : Time} (hτ : 0 ≤ τ) (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hx : rho.key r.origin ∉ rho.faultyAt τ)
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hdecode : decodeForward (S.params (Model.pubOf E) hn)
      (Model.digests rho.hash r.object) r.object = some (r.origin, τ, p, B))
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j)
    (hb : (simTraceAt S rho hn).deadline y j (max τ g) (S.params (Model.pubOf E) hn).Δ
      ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max τ g) (S.params (Model.pubOf E) hn).Δ
      ≤ (simTraceAt S rho hn).time j)
    (hF : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state y j).fg.F B) :
    (simTraceAt S rho hn).BlockAcceptedBy y j (max τ g) B := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hrel : rho.releases (rho.key r.origin) r.object τ :=
    ht ▸ ⟨r.event, (publisherExecution S rho).actual_event r hr,
      (publisherExecution S rho).actual_release r hr⟩
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_gst_deadline_at S rho hn hv hnet
      r hr (ht ▸ hx) (not_isFGAtt_of_decodeForward hdecode) hy hj hτ ht hb hd
    obtain ⟨k, hkj, hacc, htime⟩ := held_forward_accepted_before_at S rho hn hv hnc
      (fun k hk => hrun.time_mono hk.le)
      (not_faulty_of_mem_honestKeysAt S rho hy le_rfl (isCall_time_le_horizon S rho hn hv hj))
      hx hrel hheld hdecode hlt hd hF
    by_cases hk : (simTraceAt S rho hn).time k <
        (simTraceAt S rho hn).deadline y k (max τ g) (S.params (Model.pubOf E) hn).Δ
    · exact ⟨k, hkj, hacc, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by
        intro heq
        subst k
        exact hk htime)
      have hmono := deadline_mono_cut_at S rho hn hv y (max τ g)
        (S.params (Model.pubOf E) hn).Δ hkj
      obtain ⟨l, hl, ha, ht'⟩ := ih k hkj' (hrun.antitone (hrun.time_mono hkj) hy) ⟨_, hacc⟩
        (hmono.trans hb) (le_of_not_gt hk) ((run_F_mono_at hrun hy hkj).trans hF)
      exact ⟨l, hl.trans hkj, ha, ht'⟩

/-- The acceptance-relay service for an acceptance by a node honest at its cut, including a
pre-GST one, at a recipient honest at its call within the horizon. -/
theorem acceptance_relay_psync_any_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {x : Fin (Fintype.card V)} {i : Nat}
    (hx : x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    {B : Blk (S.params (Model.pubOf E) hn)} (hi : (simTraceAt S rho hn).AcceptAt x i B)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j) (hb : (simTraceAt S rho hn).time j ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max ((simTraceAt S rho hn).time i) g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTraceAt S rho hn).time j)
    (hF : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state y j).fg.F B) :
    (simTraceAt S rho hn).BlockAcceptedBy y j (max ((simTraceAt S rho hn).time i) g) B := by
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptanceAt_iff S rho hn _ _ _).mp
      (forwardAtAcceptance_at S rho hn hv) x i B hx hi
  have hih : (simTraceAt S rho hn).time i ≤ rho.horizon :=
    isCall_time_le_horizon S rho hn hv ⟨_, hi⟩
  exact publication_acceptedBy_psync_any_at S rho hn hv hnc hnet r hr
    ((simTraceAt_goldilocksRun S rho hn hv).time_nonneg i) htime
    (horg ▸ not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih) (p := p)
    (by simpa only [horg] using hdecode) hy hj (hd.trans hb) hd hF

/-- Holdings of a decoded wrapper of a signer honest at its stamp give a block call after the
stamp. Local publication uses the actual acceptance; receipt uses recursive block processing. -/
theorem held_forward_blockCall_before_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y x : Fin (Fintype.card V)} {j : Nat} {o : Wire (Fintype.card V)} {t d D : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hx : rho.key x ∉ rho.faultyAt t)
    (hheld : rho.log.Held rho.point (rho.key y) o d)
    (hdecode : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hd : d < D) (hj : D ≤ (simTraceAt S rho hn).time j) :
    ∃ k ≤ j, t ≤ (simTraceAt S rho hn).time k ∧
      (simTraceAt S rho hn).BlockCallAt y k B ∧ (simTraceAt S rho hn).time k < D := by
  have hmono := (simTraceAt_goldilocksRun S rho hn hv).time_mono
  rw [simTraceAt_eq] at hj hmono ⊢
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  have before {k : Nat} (hk : (simTrace S rho hn).time k < D) : k ≤ j := by
    by_contra h
    have htime := hmono (show j ≤ k by omega)
    exact (not_lt_of_ge (hj.trans htime)) hk
  rcases hsource with hs | hr
  · obtain ⟨i, hi, ho⟩ := hs
    have hxy := released_forward_signer S rho hn hi ho hdecode
    rw [hxy] at hdecode
    have hstamp : t = u := released_forward_stamp S rho hn hv hi ho hdecode
    have hacc : ∃ k < cutMap S rho hn (i + 1),
        (simTrace S rho hn).AcceptAt (rho.ownKey (rho.key y)) k B ∧
        (simTrace S rho hn).time k = t := by
      rcases hi with he | ⟨receipt, he⟩
      · exact tick_released_forward_acceptance S rho hn hv he ho hdecode
      · exact delivery_released_forward_acceptance S rho hn hv he ho hdecode
    obtain ⟨k, _, ha, ht⟩ := hacc
    have hk : (simTrace S rho hn).time k < D := ht ▸ hstamp ▸ huD
    exact ⟨k, before hk, ht.ge, ⟨true, hkey ▸ ha⟩, hk⟩
  · obtain ⟨i, hi⟩ := hr
    have htu := received_forward_stamp_le_of_stamp_at S rho hn hv hi (.refl o) hx hdecode
    obtain ⟨k, _, hc, ht⟩ := received_forward_blockCall S rho hn hi (.refl o) hdecode htu
    have hk : (simTrace S rho hn).time k < D := ht ▸ huD
    exact ⟨k, before hk, ht ▸ htu, hkey ▸ hc, hk⟩

/-- A decoded publication by an origin honest at its event receives block service at the
processing cut's GST deadline, including publications before GST. -/
theorem publication_blockDeliveredBy_psync_at (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {g : Time} (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r)
    {τ : Time} (hτ : 0 ≤ τ) (ht : (publisherExecution S rho).eventTime r.event = τ)
    (hx : rho.key r.origin ∉ rho.faultyAt τ)
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hdecode : decodeForward (S.params (Model.pubOf E) hn)
      (Model.digests rho.hash r.object) r.object = some (r.origin, τ, p, B))
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j)
    (hb : (simTraceAt S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max τ g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTraceAt S rho hn).time j) :
    (simTraceAt S rho hn).BlockDeliveredBy y j τ (max τ g) B := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨d, hheld, hlt⟩ := publication_held_before_gst_deadline_at S rho hn hv hnet
      r hr (ht ▸ hx) (not_isFGAtt_of_decodeForward hdecode) hy hj hτ ht hb hd
    obtain ⟨k, hkj, hlo, hcall, htime⟩ := held_forward_blockCall_before_at S rho hn hv
      hx hheld hdecode hlt hd
    by_cases hk : (simTraceAt S rho hn).time k <
        (simTraceAt S rho hn).deadline y k (max τ g) (S.params (Model.pubOf E) hn).Δ
    · exact ⟨k, hkj, hlo, hcall, hk⟩
    · have hkj' : k < j := lt_of_le_of_ne hkj (by
        intro heq
        subst k
        exact hk htime)
      have hmono := deadline_mono_cut_at S rho hn hv y (max τ g)
        (S.params (Model.pubOf E) hn).Δ hkj
      obtain ⟨acc, hc⟩ := hcall
      obtain ⟨l, hl, hlo', hc', ht'⟩ := ih k hkj' (hrun.antitone (hrun.time_mono hkj) hy)
        ⟨_, hc⟩ (hmono.trans hb) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj, hlo', hc', ht'⟩

/-- An own-block call of a node honest at it is an acceptance under collision freedom. -/
theorem ownBlockAt_accept_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {y : Fin (Fintype.card V)} {i : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hown : (simTraceAt S rho hn).OwnBlockAt y i B) :
    (simTraceAt S rho hn).AcceptAt y i B := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  set d := (simTraceAt S rho hn).time i
  have run := hrun.upTo (hrun.time_nonneg i)
  have hnc' := Compose.NoCollRun.upTo hnc (d := d)
  obtain ⟨⟨acc, hc⟩, hpos⟩ := hown
  have hc' := (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  rcases Compose.blockCall_cases run.toLocalRun hy hc' with hg |
    ⟨j, x, rfl, hg, hp, dd, p, hdp, hB, hacc, _, _, _⟩
  · have h0 := (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1
    simp only [Nat.add_zero] at h0
    exact False.elim (hpos h0)
  · obtain ⟨cfg, hr, hst, hs⟩ := Compose.group_step run.toLocalRun hy hg
    have req := SA.interface_requirements (S.params (Model.pubOf E) hn)
      (List (FG.Att (Fintype.card V))) (S.ro _)
    have h := Compose.honest_block_accepted
      (A := goldilocksNode (S.params (Model.pubOf E) hn) (S.ro _))
      (runProposer S rho hn) (digestOf S rho) y
      ⟨req.1, req.2.1, req.2.2.1, req.2.2.2, SA.proposal_payload_valid _ _ _⟩
      run.genesis_root_ok cfg _ _ x hr hs hp dd p (by rw [hst]; exact hdp)
    simp only [hst] at h
    have key : Compose.NoCollOn (digestOf S rho)
        (insert B (((simTraceAt S rho hn).upTo d).state y j).fg.tree) →
        ∃ fg', (((simTraceAt S rho hn).upTo d).state y j).fg.onBlock B = some fg' := by
      rw [hB]
      exact fun hnc => (h.2.2.2.2.2.2 hnc).2
    have hon := key (hnc'.mono (Set.insert_subset_iff.2
      ⟨Or.inr ⟨y, j + 2, acc, hc'⟩, Compose.tree_subset_run run.toLocalRun hy j⟩))
    have he := hacc.mpr hon
    subst acc
    exact hc

/-- Finite GST block service for blocks accepted or proposed by a node honest at its cut, at a
recipient honest at its call within the horizon, with the source-time lower bound and the
effective `max(source, GST)` processing deadline. -/
theorem block_service_psync_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {x : Fin (Fintype.card V)} {i : Nat}
    (hx : x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hi : (simTraceAt S rho hn).AcceptAt x i B ∨ (simTraceAt S rho hn).OwnBlockAt x i B)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j) (hb : (simTraceAt S rho hn).time j ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max ((simTraceAt S rho hn).time i) g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTraceAt S rho hn).time j) :
    (simTraceAt S rho hn).BlockDeliveredBy y j ((simTraceAt S rho hn).time i)
      (max ((simTraceAt S rho hn).time i) g) B := by
  have ha := hi.elim id (ownBlockAt_accept_at S rho hn hv hnc hx)
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptanceAt_iff S rho hn _ _ _).mp
      (forwardAtAcceptance_at S rho hn hv) x i B hx ha
  have hih : (simTraceAt S rho hn).time i ≤ rho.horizon :=
    isCall_time_le_horizon S rho hn hv ⟨_, ha⟩
  exact publication_blockDeliveredBy_psync_at S rho hn hv hnet r hr
    ((simTraceAt_goldilocksRun S rho hn hv).time_nonneg i) htime
    (horg ▸ not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih) (p := p)
    (by simpa only [horg] using hdecode) hy hj (hd.trans hb) hd

/-- A first-release vote envelope of a sender honest at its release reaches a different recipient
honest at its call under PSync. The release time is the lower bound; GST changes only the service
deadline. -/
theorem vote_message_service_psync_other_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ : Time} {m : SA.Vote (Fintype.card V)}
    (hx : rho.key x ∉ rho.faultyAt τ) (hne : y ≠ x)
    (hτ : 0 ≤ τ) (hs : rho.SendsAt (rho.key x) source τ)
    (hrel : Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∈
      rho.releasesAt source)
    (hfirst : ∀ i < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt i)
    {j : Nat} (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j)
    (hb : (simTraceAt S rho hn).time j ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).projAC.deadline y j (max τ g) ≤ (simTraceAt S rho hn).time j) :
    ∃ k ≤ j, τ ≤ (simTraceAt S rho hn).time k ∧
      (simTraceAt S rho hn).projAC.ProcessAt y k m ∧
      (simTraceAt S rho hn).time k < (simTraceAt S rho hn).projAC.deadline y k (max τ g) := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval_at S rho hn hv hy hj
      (hτ.trans (le_max_left _ g))
    have heq' : (simTraceAt S rho hn).projAC.deadline y j (max τ g) =
        a + (S.params (Model.pubOf E) hn).Δ := by
      rw [Compose.projAC_deadline]
      exact heq
    have hslack : a + E.ΔAC - 1 < a + (S.params (Model.pubOf E) hn).Δ := by
      change a + E.ΔAC - 1 < a + E.ΔAC
      linarith
    have hbound := hslack.le.trans (heq' ▸ hd)
    have hag : max a g = a := max_eq_left ((le_max_right _ _).trans ha)
    have hheld := hnet.msgs (rho.key x)
      _ τ ⟨source, hs, hrel⟩ hx
      (by simp [log_fgAtt_iff, isFGAtt, IsAttObj]) (rho.key y)
      a ((le_max_left _ _).trans ha) (by rw [hag]; exact hbound.trans hb)
      (by rw [hag]; exact hbound.trans hb)
      (by rw [hag]; exact not_faulty_of_mem_honestKeysAt S rho hy hbound (hbound.trans hb))
      (by rw [hag]; exact fun u hau hud => hw u hau (hud.trans hbound))
    rcases held_voteForward_source_or_process_at S rho hn hv hx hs hfirst hheld with
      h | ⟨k, hp, hlo, hhi⟩
    · exact False.elim (hne h)
    rw [hag] at hhi
    have htime : (simTraceAt S rho hn).time k < (simTraceAt S rho hn).projAC.deadline y j
        (max τ g) := by rw [heq']; exact hhi.trans_lt hslack
    have hkj : k < j := by
      by_contra h
      have := hrun.time_mono (Nat.le_of_not_gt h)
      linarith only [this, htime, hd]
    by_cases hk : (simTraceAt S rho hn).time k <
        (simTraceAt S rho hn).projAC.deadline y k (max τ g)
    · exact ⟨k, hkj.le, hlo, hp, hk⟩
    · obtain ⟨l, hl, hlo', hp', hlt⟩ := ih k hkj (hrun.antitone (hrun.time_mono hkj.le) hy)
        ⟨_, Compose.projAC_callAt.mp hp.choose_spec.1⟩
        ((hrun.time_mono hkj.le).trans hb) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj.le, hlo', hp', hlt⟩

/-- SA sends and fresh admissions by a node honest at its cut are processed within the PSync
deadline by every recipient honest at its call within the horizon. The sender processes at the
source time; other nodes use the first-release envelope. -/
theorem message_service_psync_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {x : Fin (Fintype.card V)} {i : Nat}
    (hx : x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    {m : SA.Vote (Fintype.card V)} (hi : (simTraceAt S rho hn).SendOrAdmitAt x i m)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time j))
    (hj : (simTraceAt S rho hn).IsCall y j) (hb : (simTraceAt S rho hn).time j ≤ rho.horizon)
    (hd : (simTraceAt S rho hn).deadline y j (max ((simTraceAt S rho hn).time i) g)
      (S.params (Model.pubOf E) hn).Δ ≤ (simTraceAt S rho hn).time j) :
    (simTraceAt S rho hn).MsgDeliveredBy y j ((simTraceAt S rho hn).time i)
      (max ((simTraceAt S rho hn).time i) g) m := by
  have hr := simTraceAt_goldilocksRun S rho hn hv
  have hsim := simTraceAt_simulates S rho hn hv
  by_cases heq : y = x
  · subst y
    obtain ⟨k, hp, ht⟩ := sendOrAdmit_process_same_time_at S rho hn hv hx hi
    have hlt (l : Nat) : (simTraceAt S rho hn).time i <
        (simTraceAt S rho hn).deadline x l (max ((simTraceAt S rho hn).time i) g)
          (S.params (Model.pubOf E) hn).Δ := by
      unfold RunTrace.deadline
      change _ < Option.elim _ _ _ + E.ΔAC
      have := E.ΔAC_pos
      cases (simTraceAt S rho hn).lastWake x l with
      | bot => change _ < max _ g + E.ΔAC; simp only [Time] at *; omega
      | coe w => change _ < max (max _ g) w + E.ΔAC; simp only [Time] at *; omega
    refine ⟨k, ?_, ht.ge, ?_, ht ▸ hlt k⟩
    · by_contra h
      have := hr.time_mono (Nat.le_of_not_ge h)
      have := hlt j
      linarith
    · obtain ⟨l, hc, hm⟩ := hp
      exact hm.elim (fun h => Or.inl ⟨l, Compose.projAC_callAt.mp hc, h⟩)
        (fun h => Or.inr ⟨l, Compose.projAC_callAt.mp hc, h⟩)
  · have hproj : (simTraceAt S rho hn).projAC.SendOrAdmit x i m := by
      obtain ⟨l, hc, hs⟩ := hi
      refine ⟨l, Compose.projAC_callAt.mpr hc, ?_⟩
      rw [projAC_state_at hr hx]
      exact hs
    obtain ⟨source, _, _, hs, hrel, hfirst⟩ := hsim.vote_forwarded x i m hx
      (sendOrAdmit_forward_source_at hr hx hproj)
    have hih : (simTraceAt S rho hn).time i ≤ rho.horizon :=
      isCall_time_le_horizon S rho hn hv ⟨_, hi.choose_spec.1⟩
    obtain ⟨k, hkj, hlo, hp, hlt⟩ := vote_message_service_psync_other_at S rho hn hv hnet
      (not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih) heq (hr.time_nonneg i)
      hs hrel hfirst hy hj hb (by rw [Compose.projAC_deadline]; exact hd)
    refine ⟨k, hkj, hlo, ?_, ?_⟩
    · obtain ⟨l, hc, hm⟩ := hp
      exact hm.elim (fun h => Or.inl ⟨l, Compose.projAC_callAt.mp hc, h⟩)
        (fun h => Or.inr ⟨l, Compose.projAC_callAt.mp hc, h⟩)
    · rw [Compose.projAC_deadline] at hlt
      exact hlt

/-- The finite valid engine run supplies every reset-service field under growing faults, with
attestation service at a parametric `Δ_F` as a premise (`hrow`). Senders are honest at their
event, recipients at their call; actual recipient calls lie within the engine horizon. -/
theorem resetService_of_psync_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {g ΔF : Time} (hnet : rho.log.PSync rho.point g)
    (hrow : PSyncFGAttTransportAt S rho (simTraceAt S rho hn) (honestKeysAt S rho) ΔF)
    (hΔF : 0 < ΔF) :
    Healing.Growing.Pending.ResetService (simTraceAt S rho hn) (honestKeysAt S rho) g ΔF
      rho.horizon := by
  refine ⟨hΔF, ?_, ?_, ?_, ?_⟩
  · intro x i m hx hi y j hy hj hd
    exact message_service_psync_at S rho hn hv hnet hx hi hy hj
      (isCall_time_le_horizon S rho hn hv hj) hd
  · intro x i B hx hi y j hy hj hd
    exact block_service_psync_at S rho hn hv hnc hnet hx hi hy hj
      (isCall_time_le_horizon S rho hn hv hj) hd
  · intro x i B hx hi _ y j hy hj hd hF
    exact acceptance_relay_psync_any_at S rho hn hv hnc hnet hx hi hy hj
      (isCall_time_le_horizon S rho hn hv hj) hd hF
  · exact (psyncFGAttTransportAt_iff S rho _ _ _).mp hrow g hnet

/-- Old acceptances by nodes honest at their cut catch up before the first `2Δ` snapshot after GST
at every node honest at that snapshot, when every node honest at a time of `[max g 0, horizon]` is
awake then. The snapshot supplies the finite service horizon. -/
theorem catchRun_of_psync_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    (hawake : ∀ v u, max g 0 ≤ u → u ≤ rho.horizon → v ∉ rho.faultyAt u →
      E.awake v u = true) :
    Healing.Growing.CatchRun (simTraceAt S rho hn) (honestKeysAt S rho) g
      (2 * (S.params (Model.pubOf E) hn).Δ) := by
  intro x i B hx hi hbefore y j hy hfirst hF
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hstart := hfirst.1
  change max g 0 + 2 * E.ΔAC ≤ (simTraceAt S rho hn).time j at hstart
  have hbound : (simTraceAt S rho hn).time j ≤ rho.horizon + 1 := by
    rw [simTraceAt_eq]
    cases hj : (allCuts S rho hn)[j]? with
    | none => rw [(simTrace_of_getElem?_none S rho hn hj).2]
    | some r =>
      have hl : (simTrace S rho hn).label j ≠ none := by rw [simTrace_label, hj]; simp
      have hh := simTrace_labelled_time_le S rho hn hv hl
      linarith only [hh]
  have hservice : max g 0 + E.ΔAC - 1 ≤ rho.horizon := by
    linarith only [E.ΔAC_pos, hstart, hbound]
  have hih : (simTraceAt S rho hn).time i ≤ rho.horizon :=
    isCall_time_le_horizon S rho hn hv ⟨_, hi⟩
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptanceAt_iff S rho hn _ _ _).mp
      (forwardAtAcceptance_at S rho hn hv) x i B hx hi
  have hxt : rho.key r.origin ∉ rho.faultyAt ((publisherExecution S rho).eventTime r.event) := by
    rw [horg, htime]; exact not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih
  -- the snapshot time, clamped to the horizon: `y` is honest there
  set T := SA.gbar g + 2 * (S.params (Model.pubOf E) hn).Δ
  have hyT : rho.key y ∉ rho.faultyAt (min T rho.horizon) := by
    rw [mem_honestKeysAt_iff] at hy
    exact hy
  have hdlT : max g 0 + E.ΔAC - 1 ≤ min T rho.horizon := by
    refine le_min ?_ hservice
    change max g 0 + E.ΔAC - 1 ≤ max g 0 + 2 * E.ΔAC
    linarith only [E.ΔAC_pos]
  have hmax : max (max g 0) g = max g 0 := max_eq_left (le_max_left _ _)
  obtain ⟨hheld, hslack⟩ := publication_held_psync_at S rho hn hnet r hr hxt
    (not_isFGAtt_of_decodeForward hdecode)
    (a := max g 0) (by rw [hmax]; exact fun h => hyT (rho.faultyAt_mono hdlT h))
    (by rw [htime]; exact hbefore.le)
    (by rw [hmax]; exact hservice)
    (by
      rw [hmax]
      exact fun u hlo hhi => hawake (rho.key y) u hlo (hhi.trans hservice)
        (fun h => hyT (rho.faultyAt_mono (hhi.trans hdlT) h)))
  rw [hmax] at hheld hslack
  have hdeadline : max g 0 + (S.params (Model.pubOf E) hn).Δ ≤
      (simTraceAt S rho hn).time j := by
    change max g 0 + E.ΔAC ≤ _
    linarith only [E.ΔAC_pos, hstart]
  have hj₀ : ∀ k < j, (simTraceAt S rho hn).time k ≤ min T rho.horizon := by
    intro k hk
    have hkT : (simTraceAt S rho hn).time k < T := hfirst.2 k hk
    have hT : T ≤ rho.horizon + 1 := hfirst.1.trans hbound
    refine le_min hkT.le ?_
    exact Int.lt_add_one_iff.mp (hkT.trans_le hT)
  have hrel : rho.releases (rho.key x) r.object ((simTraceAt S rho hn).time i) := by
    rw [← horg, ← htime]
    exact ⟨r.event, (publisherExecution S rho).actual_event r hr,
      (publisherExecution S rho).actual_release r hr⟩
  obtain ⟨k, hkj, hk, hkt⟩ := held_forward_accepted_before_at S rho hn hv hnc hj₀ hyT
    (not_faulty_of_mem_honestKeysAt S rho hx le_rfl hih) hrel hheld
    (by simpa only [horg] using hdecode) hslack hdeadline hF
  refine ⟨k, lt_of_le_of_ne hkj ?_, hk⟩
  intro heq
  subst k
  exact (not_lt_of_ge hdeadline) hkt

end Consensus.Goldilocks.Obligations.Growing

end
