module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.DeclaredVoteTransfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the committee facts at a constant honest set

The static healing premises (`HSShared`, `ResetPremises`, `ResetPremisesUpTo`) carry the committee
facts of a slot dictionary `K` in the form the growing proofs use,
`Compose.Growing.CommitteeFacts tr (fun _ => H) K`, and CS2 for the slots after the slot of `ḡ`
(`twoK`). This module reads them at the constant honest set:

* `committeeP_of_facts`, `committeeT_of_facts`: P and T over the AC projection (T from P: a
  counted declared head vote is backed in the read point's pool);
* `mayVote_iff_of_facts`: an honest node may vote in exactly its committees' slots (the gate);
* `cs2_of_twoK`: CS2 against `committeeSize`;
* `faultBoundK_of_awake`: CS at a slot after the slot of `ḡ`, read at a time whose previous slot
  starts at or after `ḡ`, from CS2, awake honest nodes and no restart after `ḡ`. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- **P** over the AC projection, from the committee facts. -/
theorem committeeP_of_facts (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K)
    (hrun : GoldilocksRun proposer dg H tr ini) : AC.CommitteeP K tr.projAC H :=
  ⟨fun y hy i s v hv => hK.hP.1 (tr.time i) y hy i
      (fun _ hk => hrun.time_mono hk.le) s v hv,
    fun y hy i ℓ A hpt s v hv => hK.hP.2 y i ℓ A hy hpt s v hv⟩

/-- **T** over the AC projection, from P: every merged-view vote of an honest cast is backed in
the pool of its slot at the read point (the vote itself, or two votes of its validator), and the
read point's pool votes are in the node's pool after the cast (P). -/
theorem committeeT_of_facts (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K)
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr) :
    AC.CommitteeT K tr.projAC H := by
  intro y hy i ℓ e hc m v hv
  have hacr := Compose.goldilocks_ac_projection_from hrun hnc
  have hst : ∀ k, ∀ w ∈ e.readPoint.pool k,
      w ∈ (tr.projAC.state y (i + 1)).pool k ∧ w.slot = k := fun k w hw =>
    have hp := (AC.readPoint_poolU hacr.localRun.toU hy hc hw).1
    ⟨hp, AC.state_pool_slotU _ hacr.localRun.toU hacr.vstart hy (i + 1) _ w hp⟩
  have hP := (committeeP_of_facts hK hrun).1 y hy (i + 1) v.slot
  rcases AC.merged_declared_backing_at_vote_slot (fun k w hw => (hst k w hw).2) hv with
    hp | ⟨u, hu, -, -, -, hu', -⟩
  · exact hP v (hst _ v hp).1
  · rw [← hu']
    exact hP u (hst _ u hu).1

/-- **The gate**: an honest node may vote in slot `s`, at every cut, iff it is in the slot-`s`
committee. -/
private theorem mayVote_iff_of_facts (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K)
    (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n} (hy : y ∈ H) (i s : Nat) :
    (tr.state y i).ac.mayVote s = true ↔ y ∈ K.committee s :=
  hK.hGate (tr.time i) (hrun.time_nonneg i) y hy i (fun _ hk => hrun.time_mono hk.le) s

/-- **CS2** against `committeeSize`, at a slot after the slot of `ḡ`. -/
theorem cs2_of_twoK (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K) {g : Time}
    (htwo : ∀ s : Nat, sp.slot (gbar g) + 1 ≤ s →
      2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard)
    {s : Nat} (hs : sp.slot (gbar g) + 1 ≤ s) :
    2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize :=
  hK.hsize s ▸ htwo s hs

/-- **A cast is by a member of its slot's committee** (the gate at the cast). -/
theorem mem_committee_of_castAt (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K)
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ℓ e) : y ∈ K.committee e.msg.slot := by
  have h := AC.mayVote_of_castAt (Compose.goldilocks_ac_projection_from hrun hnc).localRun hy hc
  rw [Compose.projAC_state hrun.toLocalRun hy i] at h
  exact (mayVote_iff_of_facts hK hrun hy i _).1 h

/-- **A vote is by a member of its slot's committee**. -/
theorem mem_committee_of_voteAt (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K)
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {e : AC.Em sp (List (FG.Att sp.n))} (hv : AC.VoteAt tr.projAC y i e) :
    y ∈ K.committee e.msg.slot := by
  obtain ⟨ℓ, hc, he⟩ := hv
  exact mem_committee_of_castAt hK hrun hnc hy ⟨hc, he⟩

/-- Two members of a committee of at most one member are equal. -/
theorem eq_of_mem_committee (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K) {s : Nat}
    (h1 : sp.committeeSize ≤ 1) {u v : Fin sp.n} (hu : u ∈ K.committee s)
    (hv : v ∈ K.committee s) : u = v :=
  (Set.ncard_le_one (Set.toFinite _)).1 ((hK.hsize s).le.trans h1) u hu v hv

/-- A committee with a member is not empty, so `committeeSize` is positive. -/
theorem committeeSize_pos_of_mem (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K)
    {s : Nat} {u : Fin sp.n} (hu : u ∈ K.committee s) : 0 < sp.committeeSize :=
  hK.hsize s ▸ (Set.ncard_pos (Set.toFinite _)).2 ⟨u, hu⟩

/-- `committeeSize` is positive: CS2 at the slot after the slot of `ḡ` leaves a member. -/
private theorem committeeSize_pos_of_twoK (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K)
    {g : Time} (htwo : ∀ s : Nat, sp.slot (gbar g) + 1 ≤ s →
      2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard) : 0 < sp.committeeSize := by
  have := cs2_of_twoK hK htwo (le_refl (sp.slot (gbar g) + 1))
  omega

/-- A slot that starts at or after `c_z` is after the slot of `ḡ`. -/
theorem slot_gbar_lt_of_cutZ_le {g : Time} {j : Nat} (h : cutZ sp.toParams g ≤ sp.ts j) :
    sp.slot (gbar g) + 1 ≤ j := by
  rw [cutZ_eq sp g] at h
  have := (AC.ts_le_iff sp).1 h
  omega

/-! ### The first slot start after `ḡ`

The committee bounds hold for the slots after the slot of `ḡ`, so the AC base of the static
healing proofs is read from `g' = t_{slot(ḡ)+1}`, the first slot start strictly after `ḡ`: there
`gbar g' ≤ t_s` is exactly `slot(ḡ) + 1 ≤ s`. -/

/-- **Catch-up from a later time**: under `Sync` from `a` (acceptance relay), with every honest
restart at or before `a' ≥ a` within the horizon, a catch-up by `a + κ` (`κ > Δ`) of the acceptances
before `a` is a catch-up by `a' + κ` of the acceptances before `a'`: an acceptance in `[a, a')` is
relayed by `max(τ, a') + Δ < a' + κ`. -/
theorem _root_.Consensus.Goldilocks.CatchACWindowBefore.shift {P : Params} {FGP : Type}
    {A : ACInterface P FGP} {ac : ACTrace A} {H' : Set (Fin P.n)} {U : Set A.Blk}
    {a a' κ b : Time} (hc : CatchACWindowBefore ac H' U a κ b)
    (hs : SyncACWindowBefore H' U a b ac) (ha : a ≤ a')
    (hmono : ∀ {k c : Nat}, k ≤ c → ac.time k ≤ ac.time c)
    (hrest : ∀ y ∈ H', ∀ k, ac.RestartAt y k → ac.time k ≤ b → ac.time k ≤ a')
    (hκ : P.Δ < κ) : CatchACWindowBefore ac H' U a' κ b := by
  refine ⟨fun x hx i B hB hi y hy j ℓ hcj hj hjb hanc => ?_⟩
  by_cases hia : ac.time i < a
  · obtain ⟨k, hk, hak, hkt⟩ := hc.relay x hx i B hB hia y hy j ℓ hcj (by linarith) hjb hanc
    exact ⟨k, hk, hak, by linarith⟩
  · push Not at hia
    have hdl : ∀ c ≤ j, ac.deadline y c (ac.time i) ≤ a' + P.Δ := fun c hc =>
      (Compose.ac_deadline_le_of_restarts (fun k hk hrk =>
        hrest y hy k hrk ((hmono (hk.trans hc)).trans hjb)) _).trans
        (by rw [max_eq_right hi.le])
    obtain ⟨k, hk, hak, hkt⟩ := hs.relay x hx i B hB hia y hy j ℓ hcj
      ((hdl j le_rfl).trans (by linarith)) ((hdl j le_rfl).trans (by linarith)) hanc
    exact ⟨k, hk, hak, by linarith [hdl k hk]⟩

/-- **Sync from a later time**: `Sync` from `a` gives `Sync` from every `a' ≥ a`. -/
theorem _root_.Consensus.Goldilocks.SyncACWindowBefore.mono {P : Params} {FGP : Type}
    {A : ACInterface P FGP} {ac : ACTrace A} {H' : Set (Fin P.n)} {U : Set A.Blk}
    {a a' b : Time} (hs : SyncACWindowBefore H' U a b ac) (ha : a ≤ a') :
    SyncACWindowBefore H' U a' b ac :=
  ⟨fun x hx i m hm hi => hs.message x hx i m hm (ha.trans hi),
    fun x hx i B hB hi => hs.relay x hx i B hB (ha.trans hi)⟩

/-- **CS after the cut**, from awake honest validators: at a time `t ≥ c_z` at which every honest
validator is awake, with its restarts by `t` at or before `t_{slot(ḡ)+1} < t_{slot(t) − 1}` (so
joined), for a slot after the slot of `ḡ` the faulty committee members, fewer than half of it
(CS2), are fewer than its honest, awake and joined members. -/
theorem faultBoundK_of_awake (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K)
    (hrun : GoldilocksRun proposer dg H tr ini) {g : Time}
    (htwo : ∀ s : Nat, sp.slot (gbar g) + 1 ≤ s →
      2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard)
    {s : Nat} (hs : sp.slot (gbar g) + 1 ≤ s) {t : Time} (ht : cutZ sp.toParams g ≤ t)
    (hawake : ∀ y ∈ H, tr.awake y t)
    (hrest : ∀ y ∈ H, ∀ k, tr.RestartAt y k → tr.time k ≤ t →
      tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat)) :
    AC.FaultBoundK K s tr.projAC H t := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ t := by have := lt_cutZ sp g; linarith
  have ht0 : 0 ≤ t := (AC.gbar_nonneg g).trans hgt
  have hst : sp.slot (gbar g) + 3 ≤ sp.slot t := by
    have h := (AC.ts_le_iff_le_slot sp ht0 ((sp.slot (gbar g) + 3 : Nat) : Int)).mp
      ((cutZ_eq sp g) ▸ ht)
    exact_mod_cast h
  have hsub : K.committee s ∩ H ⊆
      K.committee s ∩ {y | y ∈ H ∧ tr.projAC.awake y t ∧ AC.JoinedAt tr.projAC y t} := by
    rintro y ⟨hyK, hy⟩
    refine ⟨hyK, hy, hawake y hy, (Compose.joined_projection_from hrun hy t).1.1
      fun k hk hkt => ?_⟩
    change 0 < sp.slot t ∧ tr.time k ≤ sp.toParams.slotTime (sp.slot t - 1)
    have he : sp.toParams.slotTime (sp.slot t - 1) = sp.ts ((sp.slot t - 1 : Nat) : Int) :=
      sp.slotTime_eq _
    refine ⟨by omega, (hrest y hy k hk hkt).trans ?_⟩
    rw [he]
    exact (AC.ts_le_iff sp).mpr (by omega)
  have hle := Set.ncard_le_ncard hsub
  have hsplit : (K.committee s ∩ H).ncard + (K.committee s ∩ Hᶜ).ncard = sp.committeeSize := by
    rw [← hK.hsize s]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hf := cs2_of_twoK hK htwo hs
  unfold AC.FaultBoundK
  omega

namespace ResetPremisesUpTo

variable {g ΔF a b : Time} (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
include hp

/-- P over the AC projection. -/
theorem hP : AC.CommitteeP K tr.projAC H := committeeP_of_facts hp.committee hp.run

/-- T over the AC projection. -/
theorem hT : AC.CommitteeT K tr.projAC H := committeeT_of_facts hp.committee hp.run hp.noColl

/-- Every slot committee has `committeeSize` members. -/
theorem hsize (s : Nat) : (K.committee s).ncard = sp.committeeSize := hp.committee.hsize s

/-- CS2 against `committeeSize`, at a slot after the slot of `ḡ`. -/
theorem cs2 {s : Nat} (hs : sp.slot (gbar g) + 1 ≤ s) :
    2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize := cs2_of_twoK hp.committee hp.twoK hs

/-- The gate. -/
theorem mayVote_iff {y : Fin sp.n} (hy : y ∈ H) (i s : Nat) :
    (tr.state y i).ac.mayVote s = true ↔ y ∈ K.committee s :=
  mayVote_iff_of_facts hp.committee hp.run hy i s

/-- `committeeSize` is positive. -/
theorem committee_pos : 0 < sp.committeeSize := committeeSize_pos_of_twoK hp.committee hp.twoK

/-- **CS after the cut**: at a time `t ∈ [c_z, b]` every honest validator is awake and joined
(its restarts are at or before `t_{slot(ḡ)+1} < t_{slot(t) − 1}`, `restart_le_before`), so for a
slot after the slot of `ḡ` the faulty committee members, fewer than half of it (CS2), are fewer
than its honest, awake and joined members. -/
theorem faultBoundK_late {s : Nat} (hs : sp.slot (gbar g) + 1 ≤ s) {t : Time}
    (ht : cutZ sp.toParams g ≤ t) (htb : t ≤ b) : AC.FaultBoundK K s tr.projAC H t := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ t := by have := lt_cutZ sp g; linarith
  exact faultBoundK_of_awake hp.committee hp.run hp.twoK hs ht
    (fun y hy => hp.awake y hy t hgt htb)
    fun _ hy _ hk hkt => restart_le_before hp hy hk (hkt.trans htb)

end ResetPremisesUpTo

namespace ResetPremises

variable {g ΔF a : Time} (hp : ResetPremises tr H K proposer dg g ΔF a)
include hp

/-- P over the AC projection. -/
theorem hP : AC.CommitteeP K tr.projAC H := committeeP_of_facts hp.committee hp.run

/-- T over the AC projection. -/
theorem hT : AC.CommitteeT K tr.projAC H := committeeT_of_facts hp.committee hp.run hp.noColl

/-- Every slot committee has `committeeSize` members. -/
theorem hsize (s : Nat) : (K.committee s).ncard = sp.committeeSize := hp.committee.hsize s

/-- CS2 against `committeeSize`, at a slot after the slot of `ḡ`. -/
theorem cs2 {s : Nat} (hs : sp.slot (gbar g) + 1 ≤ s) :
    2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize := cs2_of_twoK hp.committee hp.twoK hs

/-- The gate. -/
theorem mayVote_iff {y : Fin sp.n} (hy : y ∈ H) (i s : Nat) :
    (tr.state y i).ac.mayVote s = true ↔ y ∈ K.committee s :=
  mayVote_iff_of_facts hp.committee hp.run hy i s

/-- `committeeSize` is positive. -/
theorem committee_pos : 0 < sp.committeeSize := committeeSize_pos_of_twoK hp.committee hp.twoK

/-- **CS after the cut**, whole-run form of `ResetPremisesUpTo.faultBoundK_late`. -/
theorem faultBoundK_late {s : Nat} (hs : sp.slot (gbar g) + 1 ≤ s) {t : Time}
    (ht : cutZ sp.toParams g ≤ t) : AC.FaultBoundK K s tr.projAC H t :=
  (hp.toUpTo tr H (le_max_left a t)).faultBoundK_late hs ht (le_max_right _ _)

end ResetPremises

namespace HSShared

variable {g ΔF : Time} (hs : HSShared tr H K dg g ΔF)
include hs

/-- CS2 against `committeeSize`, at a slot after the slot of `ḡ`. -/
theorem cs2 {s : Nat} (hsl : sp.slot (gbar g) + 1 ≤ s) :
    2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize := cs2_of_twoK hs.committee hs.twoK hsl

/-- `committeeSize` is positive. -/
theorem committee_pos : 0 < sp.committeeSize := committeeSize_pos_of_twoK hs.committee hs.twoK

/-- Every slot committee has `committeeSize` members. -/
theorem hsize (s : Nat) : (K.committee s).ncard = sp.committeeSize := hs.committee.hsize s

/-- P over the AC projection of a run. -/
theorem hP (hrun : GoldilocksRun proposer dg H tr ini) : AC.CommitteeP K tr.projAC H :=
  committeeP_of_facts hs.committee hrun

/-- T over the AC projection of a run. -/
theorem hT (hrun : GoldilocksRun proposer dg H tr ini) : AC.CommitteeT K tr.projAC H :=
  committeeT_of_facts hs.committee hrun hs.noColl

/-- The gate. -/
theorem mayVote_iff (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n} (hy : y ∈ H)
    (i s : Nat) : (tr.state y i).ac.mayVote s = true ↔ y ∈ K.committee s :=
  mayVote_iff_of_facts hs.committee hrun hy i s

end HSShared

end Consensus.Goldilocks.Healing

end
