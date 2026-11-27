module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Groups
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RoleBinding
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Queue
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.BlockView
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeBlockView
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
* a cast (`simTraceAt_vote_member`) and a received message (`simTraceAt_msgCall_member`),
  from the installed permission and the receiver's verification, respectively;
* on a run record, the pools (`simTraceAt_pool_member`).

None of these needs an honest-set premise beyond the record's, nor the population binding. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)
open AC (ACParams Vote)

/-- **The pool of an AC run keeps a vote predicate** that holds of the node's received
messages and its own emissions. A block's declared references do not enter the pool. -/
theorem pool_mem_of_run {sp : ACParams} {FGP : Type}
    {H₀ : Set (Fin sp.n)} {U : Set (AC.Blk sp.n FGP)} {trA : AC.GTrace sp FGP} {ini} {g : Nat}
    (hr : ACLocalRun (AC.goldilocksAC sp FGP) H₀ U trA ini) (hini : ∀ y, AC.VoteStart g (ini y))
    {y : Fin sp.n} (hy : y ∈ H₀)
    (P : Vote sp.n → Prop)
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
      have key := pool_step_inventory P y (trA.state y i) ℓ.frame (trA.time i) ℓ.call ih
        ?_ (by rw [he]; exact fun e he' => hem i ℓ e hc he')
      · rwa [he] at key
      · split
        · rename_i v hcl
          exact hmsg i ℓ v hc hcl
        · trivial
    · rw [trA.state_succ_of_not fun ℓ h => hc ⟨ℓ, h⟩]
      exact ih

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
  {K : AC.CommitteeDict (Fintype.card V)}

/-- **A decoded vote is of a committee member** (the receiver's vote verification). -/
theorem simTraceAt_msgCall_member (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole)
    {y : Fin (Fintype.card V)} {k : Nat} {m : Vote (Fintype.card V)}
    (hc : (simTraceAt S rho hn).MsgCallAt y k m) : m.val ∈ K.committee m.slot := by
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1,
    ← NodeAsChainShape.CanonicalTrace.simTraceAt_eq] at hc
  apply ((K.bindsSel_iff rho _).1 hK m.slot m.val).2
  revert hc
  refine traceEncoding_induction S hn (fun e _ _ =>
    (NodeAsChainShape.CanonicalTrace.simTraceAt e rho).MsgCallAt y k m →
      m.val ∈ rho.sel (S.vote.voteRole m.slot)) ?_
  intro e _ hc
  obtain ⟨_, v, _, _, w, _, _, hd, _, _⟩ :=
    NodeAsChainShape.CanonicalTrace.simTraceAt_msgCall_delivered e rho hc
  rw [NodeAsChainShape.CanonicalTrace.receiverCodec_eq,
    NodeAsChainShape.CanonicalTrace.voteIOAt_eq] at hd
  have hd' : decodeVoteObj (S.params (pubOf E) hn) (binding := S.vote) (rho.voteIO v) w =
      some m := hd
  obtain ⟨data, token, _, hcheck⟩ := decodeVoteObj_verified
    (sp := S.params (pubOf E) hn) (binding := S.vote) (rho.voteIO v) hd'
  exact ((hv.credentials.1.2 m.val (S.vote.voteRole m.slot) data token).mp hcheck).2.1

/-- **The installed permission is the committee**: a node may vote in slot `s` iff it is in
`K.committee s`, at every cut and for every node. -/
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
    ∀ x i e, AC.VoteAt (simTraceAt S rho hn).projAC x i e → x ∈ K.committee e.msg.slot := by
  rintro x i e ⟨ℓ, hc, he⟩
  obtain ⟨-, hstep, -, -⟩ :=
    simTraceAt_cutLaw S rho hn hv x i (.ac ℓ) (Compose.projAC_callAt.1 hc)
  exact (simTraceAt_mayVote_iff S rho hn hv hK x i _).1
    (AC.emits_mayVote x _ ℓ.frame _ ℓ.call e (by rw [hstep]; exact he))

/-! ### On a run record of the canonical trace -/

variable {rho hn} {ini}
  (hrun : Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho) (honestKeysAt S rho)
    (simTraceAt S rho hn) ini)
include hrun

/-- The pools of the prefix through `d ≥ 0` of a node honest at `d` hold votes of members. -/
private theorem upTo_pool_member (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {d : Time} (hd : 0 ≤ d)
    {w : Fin (Fintype.card V)} (hw : w ∈ honestKeysAt S rho d) :
    ∀ i σ, ∀ v ∈ (((simTraceAt S rho hn).projAC.upTo d).state w i).pool σ,
      v.val ∈ K.committee v.slot := by
  have hacr := Compose.goldilocks_ac_projection_from (hrun.upTo hd) (hnc.upTo d)
  rw [RunTrace.upTo_projAC] at hacr
  have hr := hacr.localRun
  refine pool_mem_of_run hr hacr.vstart hw (fun v => v.val ∈ K.committee v.slot)
    (fun _ ℓ v hci hcl => simTraceAt_msgCall_member S rho hn hv hK
      ⟨ℓ, Compose.projAC_callAt.1 ((Trace.upTo_callAt _).mp hci).2, hcl⟩)
    (fun i ℓ e hci he => ?_)
  show e.msg.val ∈ K.committee e.msg.slot
  rw [(AC.castAt_specU hr.toU hw ⟨hci, he⟩).1]
  exact simTraceAt_vote_member S rho hn hv hK w i e ⟨ℓ, ((Trace.upTo_callAt _).mp hci).2, he⟩

/-- **The pool after an honest call holds votes of members of its slot** (`hPool`). -/
theorem simTraceAt_pool_member (hv : rho.ExecutionValid) (hK : K.BindsSel rho S.vote.voteRole)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) :
    ∀ w c m, w ∈ honestKeysAt S rho ((simTraceAt S rho hn).time c) →
      ∀ v ∈ ((simTraceAt S rho hn).projAC.state w (c + 1)).pool m, v.val ∈ K.committee m := by
  intro w c m hw v hvp
  have hd := hrun.time_nonneg c
  have hst : ((simTraceAt S rho hn).projAC.upTo ((simTraceAt S rho hn).time c)).state w (c + 1) =
      (simTraceAt S rho hn).projAC.state w (c + 1) :=
    Trace.upTo_state _ w fun k hk => hrun.time_mono (Nat.lt_succ_iff.mp hk)
  rw [← hst] at hvp
  have hm := upTo_pool_member S hrun hv hK hnc hd hw (c + 1) m v hvp
  have hacr := Compose.goldilocks_ac_projection_from (hrun.upTo hd) (hnc.upTo _)
  rw [RunTrace.upTo_projAC] at hacr
  rwa [AC.state_pool_slotU _ hacr.localRun.toU hacr.vstart hw (c + 1) m v hvp] at hm

end Consensus.Goldilocks.Simulation

end
