module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Groups
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RoleBinding
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Unforgeable
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Queue
import ConsensusLean.Lemmas.Model.Credentials
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields

public section

/-! # Committee membership of the votes of the canonical growing trace

For a dictionary `K` that binds the run's role selection (`K.BindsSel rho voteRole`), every vote
the canonical trace handles is of a member of its slot's committee:

* the gate (`simTraceAt_gate`): a node may vote in slot `s` iff it is in `K.committee s`;
* a cast (`simTraceAt_vote_member`), a received message (`simTraceAt_msgCall_member`) and the
  votes of an occurring block (`simTraceAt_occurs_member`), from the credentials of the engine;
* on a run record, the blocks held while honest (`simTraceAt_honestBlock_member`), the frames
  (`simTraceAt_tree_member`) and the pools (`simTraceAt_pool_member`).

None of these needs an honest-set premise beyond the record's, nor the population binding. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote)

/-- **The pool of an AC run keeps a vote predicate** that holds of the votes of the blocks of
`U`, of the node's received messages and of its own emissions. -/
theorem pool_mem_of_run {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    {H₀ : Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)} {trA : SA.SATrace sp FGP ro} {ini} {g : Nat}
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H₀ U trA ini) (hini : ∀ y, SA.VoteStart g (ini y))
    {y : Fin sp.n} (hy : y ∈ H₀)
    (P : Vote sp.n → Prop) (hU : ∀ B ∈ U, ∀ v ∈ SA.blockVotes B, P v)
    (hmsg : ∀ i ℓ v, trA.CallAt y i ℓ → ℓ.call = .message v → P v)
    (hem : ∀ i ℓ e, trA.CallAt y i ℓ → e ∈ ℓ.emits → P e.msg) :
    ∀ i σ, ∀ v ∈ (trA.state y i).pool σ, P v := by
  intro i
  induction i with
  | zero =>
    intro σ v hv
    change v ∈ (trA.init y).pool σ at hv
    rw [hr.init y hy, (hini y).pool σ] at hv
    exact False.elim (List.not_mem_nil hv)
  | succ i ih =>
    by_cases hc : ∃ ℓ, trA.CallAt y i ℓ
    · obtain ⟨ℓ, hc⟩ := hc
      rw [trA.state_succ_of_call hc]
      have he := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at he
      obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc
      have hB : ∀ B, ℓ.call = .block B → B ∈ ℓ.frame.tree := by
        intro B hcl
        have key : ∀ Φ, (SA.goldilocksSA sp FGP ro).CallOK U Φ (trA.time i) ℓ.call ℓ.frame →
            B ∈ ℓ.frame.tree := by
          intro Φ h
          rw [hcl] at h
          obtain ⟨-, hst, -, -⟩ := h
          rw [hst.tree_eq]
          exact ⟨Set.mem_insert _ _, hst.F'_anc_B⟩
        rcases hr.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨-, ℓ', -, -, -, h⟩ <;>
          exact key _ h
      have key := pool_step_inventory P ro y (trA.state y i) ℓ.frame (trA.time i) ℓ.call ih hΦ
        ?_ (by rw [he]; exact fun e he' => hem i ℓ e hc he')
      · rwa [he] at key
      · split
        · rename_i B hcl
          exact fun v hv => hU B (hΦU (hB B hcl)) v hv
        · rename_i v hcl
          exact hmsg i ℓ v hc hcl
        · exact fun B hB' v hv => hU B (hΦU hB') v hv
        · trivial
    · rw [trA.state_succ_of_not fun ℓ h => hc ⟨ℓ, h⟩]
      exact ih

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)
  {K : SA.CommitteeDict (Fintype.card V)}

/-- **The committee of an observed vote object**: its signer is selected for the vote role of
its slot. -/
theorem observed_vote_member (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole)
    {o : Wire (Fintype.card V) (binding := S.vote)} (ho : o ∈ rho.Observed)
    {m : Vote (Fintype.card V)} (hc : Model.Obj.Contains o (voteObj (binding := S.vote) m)) :
    m.val ∈ K.committee m.slot :=
  ((K.bindsSel_iff rho _).1 hK m.slot m.val).2 (rho.selected_of_observed hv ho hc rfl)

/-- **The votes of an occurring block are of committee members** (its object is observed). -/
theorem simTraceAt_occurs_member (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole)
    {C : Blk (S.params (pubOf E) hn)} (hC : (simTraceAt S rho hn).Occurs C) :
    ∀ v ∈ SA.blockVotes C, v.val ∈ K.committee v.slot := fun v hvC =>
  observed_vote_member S rho hv hK (occurs_blockObj_observed_at S rho hn hv hC).2
    (Model.Obj.Contains.step
      (List.mem_append_right _ (List.mem_map.mpr ⟨v, List.mem_append_left _ hvC, rfl⟩))
      (.refl _))

/-- **A received vote is of a committee member** (the credentials of its delivery). -/
theorem simTraceAt_msgCall_member (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole)
    {y : Fin (Fintype.card V)} {k : Nat} {m : Vote (Fintype.card V)}
    (hc : (simTraceAt S rho hn).MsgCallAt y k m) : m.val ∈ K.committee m.slot := by
  rw [simTraceAt_eq] at hc
  obtain ⟨i, v, o, t, he, ho, -, -⟩ := msgCall_delivered S rho hn hc
  exact ((K.bindsSel_iff rho _).1 hK m.slot m.val).2 (hv.credentials i v o t he _ ho m.val _ rfl)

/-- **The installed permission is the committee**: a node may vote in slot `s` iff it is in
`K.committee s` (B2.0, at every cut and for every node). -/
theorem simTraceAt_mayVote_iff (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole)
    (x : Fin (Fintype.card V)) (i s : Nat) :
    ((simTraceAt S rho hn).state x i).ac.mayVote s = true ↔ x ∈ K.committee s := by
  simp only [simTraceAt_mayVote S rho hn hv x i, decide_eq_true_eq]
  exact ((K.bindsSel_iff rho _).1 hK s x).symm

/-- **The gate** (`hGate`), stated for the nodes honest at time `0`. -/
theorem simTraceAt_gate (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole) :
    ∀ x, x ∈ honestKeysAt S rho 0 → ∀ i s,
      ((simTraceAt S rho hn).state x i).ac.mayVote s = true ↔ x ∈ K.committee s :=
  fun x _ => simTraceAt_mayVote_iff S rho hn hv hK x

/-- **A caster is a member of its vote's committee**: the emission gate at the cast, then the
installed permission. -/
theorem simTraceAt_vote_member (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole) :
    ∀ x i e, SA.VoteAt (simTraceAt S rho hn).projAC x i e → x ∈ K.committee e.msg.slot := by
  rintro x i e ⟨ℓ, hc, he⟩
  obtain ⟨-, hstep, -, -⟩ :=
    simTraceAt_cutLaw S rho hn hv x i (.ac ℓ) (Compose.projAC_callAt.1 hc)
  exact (simTraceAt_mayVote_iff S rho hn hv hK x i _).1
    (SA.emits_mayVote (S.ro _) x _ ℓ.frame _ ℓ.call e (by rw [hstep]; exact he))

/-! ### On a run record of the canonical trace -/

variable {rho hn} {ini}
  (hrun : Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho) (honestKeysAt S rho)
    (simTraceAt S rho hn) ini)
include hrun

/-- **The blocks held while honest by `d ≥ 0` carry votes of members**: genesis carries none,
and an accepted block occurs. -/
theorem simTraceAt_honestBlock_member (hv : rho.ExecutionValid)
    (hK : K.BindsSel rho S.vote.voteRole) {d : Time} (hd : 0 ≤ d) :
    ∀ C ∈ ((simTraceAt S rho hn).upTo d).HonestBlocks (honestKeysAt S rho d),
      ∀ v ∈ SA.blockVotes C, v.val ∈ K.committee v.slot := by
  rintro C ⟨y, hy, i, hC⟩
  rcases Compose.tree_cases (hrun.upTo hd).toLocalRun hy hC with rfl | ⟨k, -, hk⟩
  · intro v hv'
    simp [SA.blockVotes, Params.genesisBlock] at hv'
  · exact simTraceAt_occurs_member S rho hn hv hK ⟨y, k, true, ((Trace.upTo_callAt _).mp hk).2⟩

/-- **The frames of the nodes honest then carry votes of members** (`hT`). -/
theorem simTraceAt_tree_member (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole) :
    ∀ w c, w ∈ honestKeysAt S rho ((simTraceAt S rho hn).time c) →
      ∀ C ∈ (Node.frame ((simTraceAt S rho hn).state w c)).tree,
        ∀ v ∈ SA.blockVotes C, v.val ∈ K.committee v.slot := by
  intro w c hw C hC
  refine simTraceAt_honestBlock_member S hrun hv hK (hrun.time_nonneg c) C ⟨w, hw, c, ?_⟩
  rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl]
  exact hC.1

/-- The pools of the prefix through `d ≥ 0` of a node honest at `d` hold votes of members. -/
private theorem upTo_pool_member (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {d : Time} (hd : 0 ≤ d)
    {w : Fin (Fintype.card V)} (hw : w ∈ honestKeysAt S rho d) :
    ∀ i σ, ∀ v ∈ (((simTraceAt S rho hn).projAC.upTo d).state w i).pool σ,
      v.val ∈ K.committee v.slot := by
  have hacr := Compose.Growing.acRun_upTo hrun hnc hd
  have hr := hacr.localRun
  refine pool_mem_of_run hr hacr.vstart hw (fun v => v.val ∈ K.committee v.slot)
    (simTraceAt_honestBlock_member S hrun hv hK hd)
    (fun _ ℓ v hci hcl => simTraceAt_msgCall_member S rho hn hv hK
      ⟨ℓ, Compose.projAC_callAt.1 ((Trace.upTo_callAt _).mp hci).2, hcl⟩)
    (fun i ℓ e hci he => ?_)
  show e.msg.val ∈ K.committee e.msg.slot
  rw [(SA.castAt_spec hr hw ⟨hci, he⟩).1]
  exact simTraceAt_vote_member S rho hn hv hK w i e ⟨ℓ, ((Trace.upTo_callAt _).mp hci).2, he⟩

/-- **The pool after an honest call holds votes of members of its slot** (`hPool`). -/
theorem simTraceAt_pool_member (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole)
    (hc : ¬ rho.HashCollision) :
    ∀ w c m, w ∈ honestKeysAt S rho ((simTraceAt S rho hn).time c) →
      ∀ v ∈ ((simTraceAt S rho hn).projAC.state w (c + 1)).pool m, v.val ∈ K.committee m := by
  intro w c m hw v hvp
  have hnc := noCollRun_simTraceAt S rho hn hv hc
  have hd := hrun.time_nonneg c
  have hst : ((simTraceAt S rho hn).projAC.upTo ((simTraceAt S rho hn).time c)).state w (c + 1) =
      (simTraceAt S rho hn).projAC.state w (c + 1) :=
    Trace.upTo_state _ w fun k hk => hrun.time_mono (Nat.lt_succ_iff.mp hk)
  rw [← hst] at hvp
  have hm := upTo_pool_member S hrun hv hK hnc hd hw (c + 1) m v hvp
  have hacr := Compose.Growing.acRun_upTo hrun hnc hd
  rwa [SA.state_pool_slot_from _ hacr.localRun hacr.vstart hw (c + 1) m v hvp] at hm

end Consensus.Goldilocks.Simulation

end
