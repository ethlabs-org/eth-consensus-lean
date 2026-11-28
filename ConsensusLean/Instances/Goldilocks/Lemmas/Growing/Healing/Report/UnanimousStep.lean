module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Propagating an AC prefix through a slot

The caller supplies viability at the reading call, or shows the frame's finality already
extends the prefix. Cast induction is independent of the transfer rule: a unanimous batch,
an optimistic selection, or a regular result can supply the transfer above finality.
-/

namespace Consensus.Goldilocks.Healing.Growing.UnanimousStep

open AC (ACParams Payload gbar)
open Compose.Growing (acRun_upTo castAt_spec_at cast_head_fcRoot_at)

variable {sp : ACParams} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {ini : Fin sp.n → (goldilocksNode sp).State}
  {g ΔF b hold : Time} {m : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}

/-- All historically honest preceding-slot votes are carried to the next cast, provided they
extend `P` and `P` extends the receiver's frame finality. -/
theorem carry_votes_of_extending
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hext : ∀ x j e, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j e → tr.time j ≤ b →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hg : gbar g ≤ sp.ts m) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = m + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e m (Compose.Growing.honestVotes tr H m) := by
  have hΔ := sp.toParams.hΔ
  have hti : sp.ts (m + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2
      (by rw [← (castAt_spec_at hrun hnc hy hc).2.1, hs])
  have ht := AC.ts_succ (sp := sp) m
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  apply KernelProof.carry_of_service_senders hrun hnc hsvc hcatch hg hy hc hs
  rintro v ⟨x, j, e', hx, ⟨ell', hv⟩, rfl, hj⟩
  have hd := hrun.time_nonneg j
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hv' := AC.upTo_castAt.mpr ⟨le_rfl, hv⟩
  obtain ⟨⟨D, hD, hDr, -⟩, hhi⟩ := cast_head_fcRoot_at hrun hnc hx hv
  rw [hj] at hhi
  have hlo : sp.ts m ≤ tr.time j := (AC.ts_le_iff_le_slot sp hd _).2
    (by rw [← (castAt_spec_at hrun hnc hx hv).2.1, hj])
  have hDU := (Compose.Growing.frameIn_at hrun hnc hx hv.1).2 hD
  obtain ⟨D', hD', hD'r, hPD⟩ := hext x j e' hx ⟨ell', hv⟩ (by linarith) hj
  have he : D = D' := hU.1 hDU hD' (hDr.trans hD'r.symm)
  rw [← he] at hPD
  refine ⟨hj, ⟨x, j, hx, ⟨ell', hv.1, Or.inl ⟨e', hv.2, rfl⟩⟩, hlo, by linarith⟩,
    D, hDr, hFP.trans hPD, ?_⟩
  exact (Compose.frame_anc_acceptedU hr.toU hx j ell' hv'.1 D hD D .refl).imp_right
    fun ⟨k, hkj, ha⟩ =>
      ⟨x, k, hrun.antitone (hrun.time_mono hkj) hx, (ACTrace.upTo_acceptAt.mp ha).2,
        lt_of_le_of_lt (hrun.time_mono hkj) (by linarith)⟩

/-- Exact-head unanimity is the reflexive case of carry. -/
theorem carry_votes_of_unanimous
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ x j e, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j e → tr.time j ≤ b →
      e.msg.slot = m → e.msg.head = P.root)
    (hg : gbar g ≤ sp.ts m) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = m + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e m (Compose.Growing.honestVotes tr H m) :=
  carry_votes_of_extending hrun hnc hsvc hcatch
    (fun x j e hx hv hj hs' => ⟨P, hP, (hun x j e hx hv hj hs').symm, .refl⟩) hg hy hc hs hib hFP

/-- The batch transfer at a cast where the prefix is viable and above finality. Counting only
nodes still honest at this cut is sufficient; carry itself includes historically honest votes. -/
theorem next_vote_of_batch
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hext : ∀ x j e, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j e → tr.time j ≤ b →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hg : gbar g ≤ sp.ts m) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteePAt K tr.projAC H) (hTK : AC.CommitteeTAt K tr.projAC H)
    (hsize : ∀ s, (K.committee s).ncard = sp.committeeSize)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = m + 1)
    (hib : tr.time i ≤ b)
    (hvotes : ∀ x ∈ K.committee m ∩ H (tr.time i), ∃ q e',
      AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = m ∧ tr.time q ≤ sp.ts m + sp.Δ)
    (hf : AC.FaultBoundK K m tr.projAC (H (tr.time i)) (tr.time i))
    (hf1 : 2 * (K.committee (m + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P) (hV : AC.ViableAtVote ell e (m + 1) P)
    (ih : AC.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (m + 1) P) :
    AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  have ht := AC.ts_succ (sp := sp) m
  have hti : sp.ts (m + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2
      (by rw [← (castAt_spec_at hrun hnc hy hc).2.1, hs])
  have hhalf : sp.committeeSize ≤ 2 * {x | x ∈ H (tr.time i) ∧ ∃ q e', x ∈ H (tr.time q) ∧
      AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = m}.ncard := by
    have hsub : K.committee m ∩ H (tr.time i) ⊆ {x | x ∈ H (tr.time i) ∧ ∃ q e',
        x ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = m} := by
      intro x hx
      obtain ⟨q, e', hv, hvs, hq⟩ := hvotes x hx
      exact ⟨hx.2, q, e', hrun.antitone (by linarith) hx.2, hv, hvs⟩
    have hle := Set.ncard_le_ncard hsub
    have hready := Set.ncard_le_ncard (s := K.committee m ∩ {x | x ∈ H (tr.time i) ∧
        tr.projAC.awake x (tr.time i) ∧ AC.JoinedAt tr.projAC x (tr.time i)})
      (t := K.committee m ∩ H (tr.time i)) (fun _ hx => ⟨hx.1, hx.2.1⟩)
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee m) (H (tr.time i))
      (Set.toFinite _)
    rw [hsize m, Set.sdiff_eq_compl_inter, Set.inter_comm (H (tr.time i))ᶜ] at hsplit
    unfold AC.FaultBoundK at hf
    omega
  refine AC.Growing.next_transfer_from (Compose.Growing.goldilocks_ac_projection_from hrun hnc)
    K hPK hTK hsize hy hc hs ?_ hhalf
    (carry_votes_of_extending hrun hnc hsvc hcatch hext hg hy hc hs hib hFP) hf hf1 hV ih
  intro x q e' hx hv hvs
  obtain ⟨ell', hc'⟩ := hv
  have hq := (cast_head_fcRoot_at hrun hnc hx hc').2
  rw [hvs] at hq
  exact hext x q e' hx ⟨ell', hc'⟩ (by linarith) hvs

/-- Propagate through the next-slot casts by cut induction. A prefix already below finality
needs no transfer. Otherwise the caller supplies viable read-point geometry and selects the
transfer rule for its source of support. Both may use the earlier next-slot votes. -/
theorem next_votes_extend_of_viable
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hviable : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      e.msg.slot = m + 1 → tr.time i ≤ b →
      AC.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (m + 1) P →
      Anc (tr.HonestBlocksAt H) P ell.frame.F ∨
        (Anc (tr.HonestBlocksAt H) ell.frame.F P ∧ AC.ViableAtVote ell e (m + 1) P))
    (htransfer : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      e.msg.slot = m + 1 → tr.time i ≤ b → Anc (tr.HonestBlocksAt H) ell.frame.F P →
      AC.ViableAtVote ell e (m + 1) P →
      AC.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (m + 1) P →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → tr.time i ≤ b →
      e.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  suffices ∀ i, ∀ y e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → tr.time i ≤ b →
      e.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P from fun y i => this i y
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rintro y e hy ⟨ell, hc⟩ hib hs
    have hearlier : AC.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (m + 1) P :=
      fun x j hji hx e' hv hj => ih j hji x e' hx hv ((hrun.time_mono hji.le).trans hib) hj
    rcases hviable y i ell e hy hc hs hib hearlier with hPF | ⟨hFP, hV⟩
    · obtain ⟨D, hD, hDr, hroot⟩ := (cast_head_fcRoot_at hrun hnc hy hc).1
      obtain ⟨hΦ, hΦU⟩ := Compose.Growing.frameIn_at hrun hnc hy hc.1
      exact ⟨D, hΦU hD, hDr, hPF.trans (Anc.mono hΦU hroot)⟩
    · exact htransfer y i ell e hy hc hs hib hFP hV hearlier

/-- A base vote batch propagates through later slots; a proposal in the base slot itself is not
needed. The successor callbacks can use the previous slot's votes to establish viability. -/
theorem later_heads_of_step {s N : Nat}
    (hbase : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → tr.time i ≤ b →
      e.msg.slot = s → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hstep : ∀ m, s ≤ m → m + 1 ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → tr.time i ≤ b →
        e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P) →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → tr.time i ≤ b →
        e.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P) ∧
      (∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell → ell.call = .proposal →
        tr.time i = sp.ts (m + 1 : Nat) → tr.time i ≤ b → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) P d.head)) :
    ∀ r, s ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → tr.time i ≤ b →
        e.msg.slot = r → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P) ∧
      (s < r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell → ell.call = .proposal →
        tr.time i = sp.ts r → tr.time i ≤ b → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) P d.head) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hsr hrN
    by_cases h : r = s
    · subst r
      exact ⟨hbase, fun h => (lt_irrefl _ h).elim⟩
    · cases r with
      | zero => omega
      | succ m =>
        obtain ⟨hv, hp⟩ := hstep m (by omega) hrN (ih m (by omega) (by omega) (by omega)).1
        exact ⟨hv, fun _ => hp⟩

end Consensus.Goldilocks.Healing.Growing.UnanimousStep

end
