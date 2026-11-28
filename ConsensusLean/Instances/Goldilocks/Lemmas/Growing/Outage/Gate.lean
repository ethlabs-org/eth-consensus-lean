module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Confirmation
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageGateSlot

import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the reader's gate count and read majority (L1, L-gate, L3)

The outage gate count and read majority under growing faults, with the receiver service after GST
(`ReceiverServiceAfterAt`):

* `OutageReaderGate` and `outage_reader_gate_at` (E0–E4): the latest gate and update before
  an explicit strict read, with restart exclusion and the reader's latest view;
* `vote_held_before_early_at` (L1): a slot-`q` vote of a node honest at its cast and still honest
  at the receiver call, whose head extends the receiver's `Σ.F`, is pooled, its head framed and the
  vote resolved before `t_q + 2Δ`, at every call from `t_q + 2Δ` of a receiver honest then with no
  restart after `t_q` (D3 with the voter's head facts at its cast);
* `gate_result_extends_at` (L-gate): at an update of a label from GST by a node honest at it,
  joined, with its frame below `B` and an extending majority for `B` charged at the update's cut,
  the update returns a result, and every result extends `B`;
* `read_majority_of_extending_at` (L3): at a read by a node honest at the read time `d` (every
  earlier cut at a time `≤ d`), the latest view's voters are fewer than twice the supporters of
  `B` when the extending majority charged at `d` holds and every extending vote of a validator
  honest at `d` is delivered.

Every count classifies a validator at the cut that reads it: the update's cut, or the read time. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

/-- The latest restored gate before an explicit strict read. -/
structure OutageReaderGate (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))
    (b₁ : Time) (y : Fin sp.n) (j : Nat) (t : Time) where
  slot : Nat
  restored : b₁ ≤ sp.ts slot + sp.Δ
  gate_le : sp.ts slot + 6 * sp.Δ ≤ t
  lt_next : t < sp.ts slot + 10 * sp.Δ
  cut : Nat
  label : ACLabel (AC.goldilocksAC sp (List (FG.Att sp.n)))
  update : AC.UpdateAt tr.projAC y cut slot label
  cut_lt : cut < j
  restarts : ∀ k, tr.projAC.RestartAt y k → tr.time k ≤ t → tr.time k ≤ sp.ts slot
  read : Consensus.Goldilocks.Generic.ReadPointAt tr j t ∧ t < tr.time j
  view : (AC.latestView sp (tr.state y j).ac (Node.frame (tr.state y j)) t).2 =
    ((slot + 1 : Nat) : Int)

/-- Readiness over a joining window gives joining on the prefix through the read time. -/
private theorem joined_of_ready
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {t c : Time} (hy : y ∈ H t) (ht : 0 ≤ t)
    (hc : 8 * sp.Δ ≤ c + 1)
    (hawake : ∀ u, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) :
    tr.JoinedAt y t := by
  obtain ⟨-, hj⟩ := Compose.ready_implies_joined_of (hrun.upTo ht) hy ht hc
    fun u h1 h2 => ⟨hawake u h1 h2, h2⟩
  exact fun k hk hkt => hj k ((RunTrace.upTo_restartAt tr).2 ⟨hkt, hk⟩) hkt

/-- Joining bounds projected restarts on the prefix through the read time. -/
private theorem restarts_of_joined
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {t : Time} (hy : y ∈ H t) (ht : 0 ≤ t) (hJ : tr.JoinedAt y t) :
    ∀ k, tr.projAC.RestartAt y k → tr.time k ≤ t →
      tr.time k ≤ sp.ts ((sp.slot t : Int) - 1) := by
  have h := ((Compose.joined_projection_from (hrun.upTo ht) hy t).1).mp
    (joinedAt_upTo hJ)
  intro k hk hkt
  rw [RunTrace.upTo_projAC] at h
  exact h k ((ACTrace.upTo_restartAt (tr := tr.projAC)).2 ⟨hkt, hk⟩) hkt

/-- E0–E4 at an actual strict read, independently of the engine representation. -/
theorem outage_reader_gate_at
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {b₁ : Time}
    (hb₁ : 0 ≤ b₁) {b c t : Time} (hc : Regimes.catchUp sp ≤ c)
    (hrec : b₁ + 9 * sp.Δ ≤ t) {y : Fin sp.n} {j : Nat}
    (hR : Consensus.Goldilocks.Generic.ReadyReadPoint tr H b c y j t)
    (hstrict : t < tr.time j) : Nonempty (OutageReaderGate tr H b₁ y j t) := by
  have hΔ := sp.toParams.hΔ
  have ht0 : 0 ≤ t := hR.1.2.2.1
  have hy : y ∈ H t := hR.1.1
  have hcu : Regimes.catchUp sp = 18 * sp.Δ := rfl
  obtain ⟨s, hrestored, hgate, hnext⟩ := Obligations.outage_latest_gate sp hb₁ hrec
  obtain ⟨hslu, hle⟩ := Obligations.outage_gate_restarts sp hgate hnext
  set u := sp.ts s + 6 * sp.Δ with hu_def
  have hu : u = 4 * sp.Δ * s + 6 * sp.Δ := rfl
  have hu0 : 0 ≤ u := by linarith
  have hut : u ≤ t := by linarith
  have hyu : y ∈ H u := hrun.antitone hut hy
  have hpub : sp.toParams.IsPublic u := ⟨4 * s + 6, by rw [hu]; ring⟩
  have hwin : ∀ v, max 0 (u - (14 * sp.Δ - 1) - 1) ≤ v → v ≤ u → tr.awake y v := by
    intro v h₁ h₂
    exact hR.2 v (le_trans (max_le_max le_rfl (by rw [hcu] at hc; linarith)) h₁)
      (by linarith)
  have hyuw := hwin u (max_le hu0 (by linarith)) le_rfl
  obtain ⟨c₁, x, fgDue, hg⟩ := hrun.tick_of_awake y u hyu hu0 hpub hyuw
  obtain ⟨hc₁, ht₁⟩ := Healing.tick_first_cut hg
  have hJu := joined_of_ready hrun hyu hu0 (by linarith) hwin
  have hj₁ : AC.joined sp (tr.state y c₁).ac u := by
    have hst : (tr.upTo u).state y c₁ = tr.state y c₁ :=
      RunTrace.upTo_state_of_le hrun.time_mono ht₁.le
    have h := ((Compose.joined_projection_from (hrun.upTo hu0) hyu u).2.1 c₁
      ((RunTrace.upTo_isCall _).mpr ⟨ht₁.le, _, hc₁⟩)
      (fun hr => by
        obtain ⟨-, ℓ, hc', hr⟩ := (RunTrace.upTo_restartAt tr).1 hr
        have := Option.some.inj (hc₁.2.symm.trans hc'.2)
        simp only [Node.acCall, Cut.ac.injEq] at this
        rw [← this] at hr
        cases hr) ht₁).1 (joinedAt_upTo hJu)
    rwa [hst] at h
  obtain ⟨ℓ₁, hupd⟩ : ∃ ℓ₁, AC.UpdateAt tr.projAC y c₁ s ℓ₁ := by
    refine ⟨_, Compose.projAC_callAt.2 hc₁, rfl, ht₁.trans hu_def, ?_⟩
    change AC.joined sp (tr.projAC.state y c₁) (tr.time c₁)
    rw [projAC_state_at hrun (ht₁ ▸ hyu), ht₁]
    exact hj₁
  have hc₁j : c₁ < j := by
    by_contra hh
    have := hrun.time_mono (show j ≤ c₁ by omega)
    linarith
  have hJt := joined_of_ready hrun hy ht0 (by rw [hcu] at hc; linarith) hR.2
  have hJt' := restarts_of_joined hrun hy ht0 hJt
  have hJu' := restarts_of_joined hrun hyu hu0 hJu
  have hrestarts : ∀ k, tr.projAC.RestartAt y k → tr.time k ≤ t → tr.time k ≤ sp.ts s :=
    fun k hk hkt => (hJu' k hk ((hJt' k hk hkt).trans hle)).trans_eq hslu
  have hview :=
    Obligations.latestView_label_of_gate sp (tr.state y j).ac
      (Node.frame (tr.state y j)) hgate hnext
  exact ⟨⟨s, hrestored, hgate, hnext, c₁, ℓ₁, hupd, hc₁j, hrestarts,
    ⟨hR.1.2.1, hstrict⟩, hview⟩⟩

/-- A block between `Σ.F` and a block of a well-formed frame is in the frame. -/
private theorem mem_tree_between {n : Nat} {FGP : Type} {U : Set (AC.Blk n FGP)}
    (hU : Coherent U) {Φ : AC.Frm n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {B C : AC.Blk n FGP} (hFB : Anc U Φ.F B) (h : Anc U B C) : C ∈ Φ.tree → B ∈ Φ.tree := by
  induction h with
  | refl => exact id
  | @tail c d hBc e ih =>
    intro hd
    by_cases hdF : d = Φ.F
    · subst hdF
      obtain rfl := Anc.antisymm hU hFB (hBc.tail e)
      exact hΦ.rooted.1
    obtain rfl | ⟨p, -, hp⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hd)
    · exact absurd rfl hdF
    have hpc : p = c := hU.1 (hΦU hp.1) e.1 (Option.some_injective _ (hp.2.2.symm.trans e.2.2))
    subst hpc
    exact ih hp.1

/-- **L1** under growing faults: a slot-`q` vote of a node honest at its cast and at the receiver
call, whose head extends the receiver's `Σ.F`, is held, its head framed, and resolved strictly
before `t_q + 2Δ` at every receiver call from `t_q + 2Δ` with no restart after `t_q`. -/
theorem vote_held_before_early_at
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} {q c : Nat} (hy : y ∈ H (tr.time c))
    (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC)
    {ℓ : ACLabel (AC.goldilocksAC sp (List (FG.Att sp.n)))} (hc : tr.projAC.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts q)
    {x : Fin sp.n} {i : Nat} {e : AC.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x i e)
    (hx : x ∈ H (tr.time c)) (hes : e.msg.slot = q) {Hd : AC.Blk sp.n (List (FG.Att sp.n))}
    (hHd : Hd ∈ tr.HonestBlocksAt H) (hHdr : Hd.root = e.msg.head)
    (hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F Hd) :
    e.msg ∈ (tr.projAC.state y c).pool q ∧ Hd ∈ ℓ.frame.tree ∧
      AC.resolutionTime (tr.projAC.state y c) ℓ.frame e.msg <
        AC.ETime.of (sp.ts q + 2 * sp.Δ) := by
  obtain ⟨hxi, ℓv, hcv, hev⟩ := hVoteAt_iff.1 hv
  have hr := (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun
  obtain ⟨Hd₀, hHd₀, hHd₀r, hHd₀s⟩ :=
    AC.honest_head_frameU hr.toU hxi (ac_castAt_upTo.mpr ⟨le_rfl, hcv, hev⟩)
  obtain rfl : Hd₀ = Hd := (honestBlocksAt_coherent hrun hnc).1
    ((frameIn_at hrun hnc hxi hcv).2 hHd₀) hHd (hHd₀r.trans hHdr.symm)
  have htj : tr.time i ≤ sp.ts q + sp.Δ := by
    have h := (cast_head_fcRoot_at hrun hnc hxi ⟨hcv, hev⟩).2
    rw [hes] at h
    exact h
  have hacc : Hd₀.root = sp.genesisRoot ∨
      ∃ k, x ∈ H (tr.time k) ∧ tr.projAC.AcceptAt x k Hd₀ ∧ tr.time k ≤ sp.ts q + sp.Δ := by
    rcases frame_anc_accepted_at hrun hnc hxi hcv hHd₀ .refl with hgen | ⟨k, hk, hak⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨k, hrun.antitone (hrun.time_mono hk) hxi, hak,
        (hrun.time_mono hk).trans htj⟩
  exact vote_resolved_before_early_at hrun hnc hy hS hc hct hg hres hv hx hes hHd hHdr
    (by rw [← hes]; exact hHd₀s) hacc hF

/-- **L-gate** under growing faults: an update of a label from GST by a node honest at it, whose
frame is below `B`, returns a result, and every result of it extends `B`, when the extending
casters of the label outnumber its opponents in the label's committee, both charged at the
update's cut (the pools of honest nodes hold votes of members, `hP`). -/
theorem gate_result_extends_at
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : AC.CommitteeDict sp.n} (hP : AC.CommitteePAt K tr.projAC H)
    {g : Time} {y : Fin sp.n} {c s : Nat} (hy : y ∈ H (tr.time c))
    (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC)
    {ℓ : ACLabel (AC.goldilocksAC sp (List (FG.Att sp.n)))}
    (hu : AC.UpdateAt tr.projAC y c s ℓ)
    (hg : g ≤ sp.ts s + sp.Δ) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hmaj : ExtendingMajorityAt tr H K B s (tr.time c))
    (hFB : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    (∃ C CV, AC.ResultAt tr.projAC y c s C CV) ∧
      ∀ C CV, AC.ResultAt tr.projAC y c s C CV → Anc (tr.HonestBlocksAt H) B C := by
  have hm := hrun.time_mono
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hr := (acRun_upTo hrun hnc (hrun.time_nonneg c)).localRun
  have hres : ∀ k ≤ c, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s := fun k hk hrk =>
    Compose.update_restarts hr hy ((ac_updateAt_upTo hm).2 ⟨le_rfl, hu⟩) k hk
      ((ACTrace.upTo_restartAt (tr := tr.projAC)).2 ⟨hm hk, hrk⟩)
  have hct : sp.ts s + 2 * sp.Δ ≤ tr.time c := by
    have : tr.projAC.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
    change sp.ts s + 2 * sp.Δ ≤ tr.projAC.time c
    linarith
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hu.1
  set A := tr.projAC.state y c
  -- every extending caster still honest at the update is delivered
  have hdel : ∀ x k e, HVoteAt tr H x k e → x ∈ H (tr.time c) → e.msg.slot = s →
      ∀ Hd ∈ tr.HonestBlocksAt H, Hd.root = e.msg.head → Anc (tr.HonestBlocksAt H) B Hd →
      e.msg ∈ A.pool s ∧ Hd ∈ ℓ.frame.tree ∧
        AC.resolutionTime A ℓ.frame e.msg < AC.ETime.of (sp.ts s + 2 * sp.Δ) :=
    fun x k e hv hx hes Hd hHd hHdr hBHd =>
      vote_held_before_early_at hrun hnc hy hS hu.1 hct hg hres hv hx hes hHd hHdr
        (hFB.trans hBHd)
  -- `B` is in the frame: an extending caster exists, and its head is framed above `B`
  have hBt : B ∈ ℓ.frame.tree := by
    have hpos : 0 < (ExtendingCastersAt tr H B s (tr.time c)).ncard :=
      lt_of_le_of_lt (Nat.zero_le _) (extendingMajorityAt_iff.1 hmaj)
    obtain ⟨x, hxE⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    obtain ⟨hx, k, e, hv, hes, Hd, hHd, hHdr, hBHd⟩ := extendingCastersAt_iff.1 hxE
    exact mem_tree_between hU hΦ hΦU hFB hBHd (hdel x k e hv hx hes Hd hHd hHdr hBHd).2.1
  -- a validator honest at the update has its one slot-`s` vote in the update's pool
  have hone : ∀ x ∈ H (tr.time c), ∀ j e, HVoteAt tr H x j e → e.msg.slot = s →
      ∀ v ∈ A.pool s, v.val = x → v = e.msg := by
    intro x hx j e hv hs v hvp hvx
    obtain ⟨j', -, e', hv', rfl⟩ := pool_vote_at hrun hnc hy hvp (hvx ▸ hx)
    have hs' := state_pool_slot_at hrun hnc hy s _ hvp
    rw [hvx] at hv'
    exact congrArg (fun e : AC.Em sp (List (FG.Att sp.n)) => e.msg)
      (one_vote_per_slot_at hrun hnc hv' hv (hs'.trans hs.symm)).2
  set V : AC.View sp.n := ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
    AC.resolutionTime A ℓ.frame v < AC.ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  have hsupp : ExtendingCastersAt tr H B s (tr.time c) ⊆ AC.supporters ℓ.frame V s B := by
    intro x hxE
    obtain ⟨hx, k, e, hv, hes, Hd, hHd, hHdr, hBHd⟩ := extendingCastersAt_iff.1 hxE
    obtain ⟨hvp, hHdt, hrs⟩ := hdel x k e hv hx hes Hd hHd hHdr hBHd
    obtain ⟨hxk, ℓv, hcv, hev⟩ := hVoteAt_iff.1 hv
    refine ⟨?_, e.msg, ⟨hvp, hrs⟩, (castAt_spec_at hrun hnc hxk ⟨hcv, hev⟩).1,
      by exact_mod_cast hes, Hd, hHdt, hHdr, AC.anc_tree_of_anc_U hU hΦ hΦU hBt hBHd hHdt⟩
    rintro ⟨v, hv1, v', hv2, hne, hvx, hv'x⟩
    exact hne ((hone x hx k e hv hes v hv1 hvx).trans (hone x hx k e hv hes v' hv2 hv'x).symm)
  have hvot : AC.voters {v | v ∈ A.pool s} ⊆ ExtendingCastersAt tr H B s (tr.time c) ∪
      (K.committee s ∩ OpponentsAt tr H B s (tr.time c)) := by
    rintro w ⟨v, hv, rfl⟩
    have hvK : v.val ∈ K.committee s := hP.1 (tr.time c) y hy c (fun _ hk => hm hk.le) s v hv
    by_cases hw : v.val ∈ H (tr.time c)
    · obtain ⟨j, -, e, he, rfl⟩ := pool_vote_at hrun hnc hy hv hw
      have hs := state_pool_slot_at hrun hnc hy s _ hv
      by_cases hext : AC.VoteExtends (tr.HonestBlocksAt H) e.msg B
      · exact Or.inl (extendingCastersAt_iff.2 ⟨hw, j, e, he, hs, hext⟩)
      · exact Or.inr ⟨hvK, opponentsAt_iff.2 (Or.inr ⟨hw, j, e, he, hs, hext⟩)⟩
    · exact Or.inr ⟨hvK, opponentsAt_iff.2 (Or.inl hw)⟩
  have hmaj' : (AC.voters {v | v ∈ A.pool s}).ncard <
      2 * AC.confirmationScore sp A ℓ.frame s B :=
    confirmation_majority_of_cover hvot (extendingMajorityAt_iff.1 hmaj) hsupp
  obtain ⟨D, hD, hBD⟩ := getConfirmation_extends_of_majority hΦ hBt (hΦ.rooted.2 B hBt) hmaj'
  refine ⟨⟨D, _, ℓ, hu, hD, rfl⟩, ?_⟩
  rintro C CV ⟨ℓ', hu', hC, -⟩
  obtain rfl : ℓ' = ℓ := Option.some.inj (hu'.1.2.symm.trans hu.1.2)
  have hCD : C = D := Option.some.inj (hC.symm.trans hD)
  subst hCD
  exact hBD.mono hΦU

/-- **Lemma G at a read**: a vote of the pool of a node honest at a read time `d` (every cut
before `i` at a time `≤ d`) whose validator is honest at `d` was cast by it while honest. -/
private theorem pool_vote_read
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {w : Fin sp.n} {i : Nat} {d : Time} (hd : 0 ≤ d) (hw : w ∈ H d)
    (hi : ∀ k < i, tr.time k ≤ d) {σ : Nat} {v : Vote sp.n}
    (hv : v ∈ (tr.projAC.state w i).pool σ) (hvH : v.val ∈ H d) :
    v.slot = σ ∧ ∃ j < i, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v := by
  have hr := acRun_upTo hrun hnc hd
  have hst : (tr.projAC.upTo d).state w i = tr.projAC.state w i := Trace.upTo_state _ w hi
  have hv' : v ∈ ((tr.projAC.upTo d).state w i).pool σ := by rw [hst]; exact hv
  obtain ⟨j, hj, e, hve, hev⟩ := hr.honest.pool_vote w hw i σ v hv' hvH
  obtain ⟨hjd, hve⟩ := ac_voteAt_upTo.mp hve
  exact ⟨AC.state_pool_slotU sp hr.localRun.toU hr.vstart hw i σ v hv', j, hj, e,
    hVoteAt_iff.2 ⟨hrun.antitone hjd hvH, hve⟩, hev⟩

/-- **L3** under growing faults: at a read by a node honest at the read time `d` (every cut
before `i` at a time `≤ d`), when the extending casters of the latest view's label `s` outnumber
its opponents in the label's committee, both charged at `d`, and every extending vote of a
validator honest at `d` is delivered, the latest view's voters are fewer than twice the
supporters of `B`. -/
theorem read_majority_of_extending_at
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : AC.CommitteeDict sp.n} (hP : AC.CommitteePAt K tr.projAC H)
    {w : Fin sp.n} {i : Nat} {d : Time} (hd : 0 ≤ d) (hw : w ∈ H d)
    (hi : ∀ k < i, tr.time k ≤ d) {t : Time} {B : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hs : (AC.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).2 = s)
    (hmaj : ExtendingMajorityAt tr H K B s d) (hBt : B ∈ (Node.frame (tr.state w i)).tree)
    (hdeliv : ∀ x k e, HVoteAt tr H x k e → x ∈ H d → e.msg.slot = s →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg B →
      e.msg ∈ (tr.state w i).ac.pool s ∧
      ∃ Hd ∈ (Node.frame (tr.state w i)).tree, Hd.root = e.msg.head ∧
        (tr.state w i).ac.blockStamp Hd.root < ⊤) :
    (AC.voters (AC.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).1.votes).ncard <
      2 * (AC.supporters (Node.frame (tr.state w i))
        (AC.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).1
        (AC.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).2 B).ncard := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hstT : (tr.upTo d).state w i = tr.state w i := Trace.upTo_state tr w hi
  have hst : tr.projAC.state w i = (tr.state w i).ac := by
    have h := projAC_state (hrun.upTo hd).toLocalRun hw i
    rwa [RunTrace.upTo_projAC, hstT, Trace.upTo_state tr.projAC w hi] at h
  have hΦ : FrameOK (Node.frame (tr.state w i)) := frameOK_at hrun hd hw hi
  have hΦU : (Node.frame (tr.state w i)).tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => tree_held_at hd hw hi hX.1
  set A := (tr.state w i).ac
  set Φ := Node.frame (tr.state w i)
  set LV := AC.latestView sp A Φ t
  have hL : ((s : Nat) : Int) = LV.2 := hs.symm
  -- the latest view's votes are slot-`s` pool votes
  have hpool : ∀ u ∈ LV.1.votes, u ∈ (tr.projAC.state w i).pool s := by
    intro u hu
    rw [hst]
    exact ((latestView_mem hL u).1.1 hu).1
  have hsupp : ExtendingCastersAt tr H B s d ⊆ AC.supporters Φ LV.1 LV.2 B := by
    intro x hxE
    obtain ⟨hx, k, e, hv, hes, Hd, hHdU, hHdr, hBHd⟩ := extendingCastersAt_iff.1 hxE
    obtain ⟨hvp, Hd', hHd't, hHd'r, hbst⟩ := hdeliv x k e hv hx hes ⟨Hd, hHdU, hHdr, hBHd⟩
    obtain rfl : Hd' = Hd := hU.1 (hΦU hHd't) hHdU (hHd'r.trans hHdr.symm)
    obtain ⟨hxk, ℓv, hcv, hev⟩ := hVoteAt_iff.1 hv
    obtain ⟨Hd₂, hHd₂, hHd₂r, hHd₂s⟩ :=
      AC.honest_headU (acRun_upTo hrun hnc (hrun.time_nonneg k)).toU hxk
        (ac_voteAt_upTo.mpr ⟨le_rfl, ℓv, hcv, hev⟩)
    obtain rfl : Hd' = Hd₂ :=
      hU.1 hHdU (upTo_subset hrun (hrun.time_nonneg k) hHd₂) (hHdr.trans hHd₂r.symm)
    have hvotes : e.msg ∈ LV.1.votes := by
      have hvp' : e.msg ∈ ((tr.upTo d).projAC.state w i).pool s := by
        rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC w hi, hst]; exact hvp
      have h := mem_latest_votes (hrun.upTo hd) (hnc.upTo d) hw (by rw [hstT]; exact hL) hvp'
      rwa [hstT] at h
    have hvst : A.voteStamp e.msg < ⊤ := ((latestView_mem hL e.msg).1.1 hvotes).2
    have hres : AC.resolutionTime A Φ e.msg < ⊤ := by
      unfold AC.resolutionTime
      rw [← hHdr, AC.lookup_of_mem hΦ hHd't]
      dsimp only
      simp only [not_lt.2 hHd₂s, ↓reduceIte]
      exact max_lt hvst hbst
    have hval := (castAt_spec_at hrun hnc hxk ⟨hcv, hev⟩).1
    refine ⟨?_, e.msg, (latestView_mem hL e.msg).2.2 ⟨(latestView_mem hL e.msg).1.1 hvotes, hres⟩,
      hval, by rw [← hL, hes], Hd', hHd't, hHdr,
      AC.anc_tree_of_anc_U hU hΦ hΦU hBt hBHd hHd't⟩
    rintro ⟨a, ha, b, hb, hab, hav, hbv⟩
    obtain ⟨-, ja, -, ea, hea, hea'⟩ :=
      pool_vote_read hrun hnc hd hw hi (hpool a ha) (by rw [hav]; exact hx)
    obtain ⟨-, jb, -, eb, heb, heb'⟩ :=
      pool_vote_read hrun hnc hd hw hi (hpool b hb) (by rw [hbv]; exact hx)
    rw [hav] at hea
    rw [hbv] at heb
    obtain ⟨-, rfl⟩ := one_vote_per_slot_at hrun hnc hea heb
      (by rw [hea', heb', (pool_vote_read hrun hnc hd hw hi (hpool a ha) (by rw [hav]; exact hx)).1,
        (pool_vote_read hrun hnc hd hw hi (hpool b hb) (by rw [hbv]; exact hx)).1])
    exact hab (hea'.symm.trans heb')
  have hvot : AC.voters LV.1.votes ⊆
      ExtendingCastersAt tr H B s d ∪ (K.committee s ∩ OpponentsAt tr H B s d) := by
    rintro u ⟨v, hv, rfl⟩
    have hvK : v.val ∈ K.committee s := hP.1 d w hw i hi s v (hpool _ hv)
    by_cases hu : v.val ∈ H d
    · obtain ⟨hes, j, -, e, he, rfl⟩ := pool_vote_read hrun hnc hd hw hi (hpool _ hv) hu
      by_cases hext : AC.VoteExtends (tr.HonestBlocksAt H) e.msg B
      · exact Or.inl (extendingCastersAt_iff.2 ⟨hu, j, e, he, hes, hext⟩)
      · exact Or.inr ⟨hvK, opponentsAt_iff.2 (Or.inr ⟨hu, j, e, he, hes, hext⟩)⟩
    · exact Or.inr ⟨hvK, opponentsAt_iff.2 (Or.inl hu)⟩
  have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
  have h2 := Set.ncard_union_le (ExtendingCastersAt tr H B s d)
    (K.committee s ∩ OpponentsAt tr H B s d)
  have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
  have h4 := extendingMajorityAt_iff.1 hmaj
  omega

end Consensus.Goldilocks.Compose.Growing

end
