module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing

public section

/-! # The constant honest set is the static model

At `H := fun _ => H₀` every growing-fault run definition and premise is its static counterpart,
exactly: the run model (`Growing.LocalRun`, `Growing.GoldilocksRun`), the blocks held while honest,
the premises (`SyncOnAt`, `FaultBoundAt` at every consumption horizon, `SleepyRunAt` at every
look-ahead, `HealthyRunAt`), and the component contracts (`Growing.ACLocalRun`, `SyncACAt`,
`SA.Growing.ACRun`, `SA.FaultBoundAt`, `Growing.FGLocalRun`). These are the bridges by which each
growing-fault statement implies its static version. -/

namespace Consensus.Goldilocks

/-- Every finite prefix of a time sequence has a bound `≥ 0`. -/
private theorem exists_bound (f : Nat → Time) : ∀ i : Nat, ∃ t, 0 ≤ t ∧ ∀ k < i, f k ≤ t
  | 0 => ⟨0, le_rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | i + 1 => by
    obtain ⟨t, h0, ht⟩ := exists_bound f i
    refine ⟨max t (f i), h0.trans (le_max_left _ _), fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact (ht k hk).trans (le_max_left _ _)
    · exact le_max_right _ _

variable {P : Params}

namespace Growing

variable {A : NodeAC P} {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- The run model with a constant honest set is `Node.LocalRun`. -/
theorem LocalRun.const_iff :
    Growing.LocalRun proposer dg (fun _ => H) sg tr ↔ Node.LocalRun proposer dg H sg tr := by
  constructor
  · intro h
    exact
      { init := h.init
        grouped := fun y hy i c hc => h.grouped y i c hc hy
        cutLaw := fun y hy i c hc => h.cutLaw y i c hc hy
        wire := fun y hy j t e he => h.wire y j t e hy he
        proposerCredential := fun y hy j t B hB => h.proposerCredential y j t B hy hB
        time_nonneg := h.time_nonneg
        time_mono := h.time_mono
        finite := h.finite
        phase_order := fun y hy y' hy' j j' t e e' => h.phase_order y y' j j' t e e' hy hy'
        tick_public := fun y hy j t => h.tick_public y j t hy
        tick_unique := fun y hy j j' t => h.tick_unique y j j' t hy
        tick_of_awake := fun y hy t => h.tick_of_awake y t hy
        awake_in_horizon := fun y hy t => h.awake_in_horizon y t hy
        awake_of_call := fun y hy i => h.awake_of_call y i hy
        restart_of_sleep := fun y hy i u => h.restart_of_sleep y i u hy
        restart_at_wake := fun y hy u v => h.restart_at_wake y u v hy
        sleep_of_restart := fun y hy i => h.sleep_of_restart y i hy
        block_unforgeable := fun y hy i B hB hp => h.block_unforgeable y i B hy hB hp
        att_unforgeable := fun y hy i a ha hv => h.att_unforgeable y i a hy ha hv
        msg_unforgeable := fun y hy i m hm hs => h.msg_unforgeable y i m hy hm hs }
  · intro h
    exact
      { antitone := fun _ _ _ => le_rfl
        init := h.init
        grouped := fun y i c hc hy => h.grouped y hy i c hc
        cutLaw := fun y i c hc hy => h.cutLaw y hy i c hc
        wire := fun y j t e hy he => h.wire y hy j t e he
        proposerCredential := fun y j t B hy hB => h.proposerCredential y hy j t B hB
        time_nonneg := h.time_nonneg
        time_mono := h.time_mono
        finite := h.finite
        phase_order := fun y y' j j' t e e' hy hy' => h.phase_order y hy y' hy' j j' t e e'
        tick_public := fun y j t hy => h.tick_public y hy j t
        tick_unique := fun y j j' t hy => h.tick_unique y hy j j' t
        tick_of_awake := fun y t hy => h.tick_of_awake y hy t
        awake_in_horizon := fun y t hy => h.awake_in_horizon y hy t
        awake_of_call := fun y i hy => h.awake_of_call y hy i
        restart_of_sleep := fun y i u hy => h.restart_of_sleep y hy i u
        restart_at_wake := fun y u v hy => h.restart_at_wake y hy u v
        sleep_of_restart := fun y i hy => h.sleep_of_restart y hy i
        block_unforgeable := fun y i B hy hB hp => h.block_unforgeable y hy i B hB hp
        att_unforgeable := fun y i a hy ha hv => h.att_unforgeable y hy i a ha hv
        msg_unforgeable := fun y i m hy hm hs => h.msg_unforgeable y hy i m hm hs }

end Growing

namespace Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro}

/-- A Goldilocks run with a constant honest set is `GoldilocksRun`. -/
theorem GoldilocksRun.const_iff :
    Growing.GoldilocksRun proposer dg (fun _ => H) tr ↔
      Consensus.Goldilocks.GoldilocksRun proposer dg H tr := by
  constructor
  · intro h
    exact
      { toLocalRun := LocalRun.const_iff.mp h.toLocalRun
        stock := h.stock
        genesis_root_ok := h.genesis_root_ok
        carried_vote_unforgeable := fun y hy i B hB v hv hvH =>
          h.carried_vote_unforgeable y i B hy hB v hv hvH }
  · intro h
    exact
      { toLocalRun := LocalRun.const_iff.mpr h.toLocalRun
        stock := h.stock
        genesis_root_ok := h.genesis_root_ok
        carried_vote_unforgeable := fun y i B hy hB v hv hvH =>
          h.carried_vote_unforgeable y hy i B hB v hv hvH }

end Growing

namespace RunTrace

variable {A : NodeAC P} {H : Set (Fin P.n)} (tr : RunTrace A)

/-- With a constant honest set, the blocks held while honest are the honest blocks. -/
theorem honestBlocksAt_const : tr.HonestBlocksAt (fun _ => H) = tr.HonestBlocks H := by
  ext B
  constructor
  · rintro ⟨y, i, _, _, _, hy, hB⟩
    exact ⟨y, hy, i, hB⟩
  · rintro ⟨y, hy, i, hB⟩
    obtain ⟨t, h0, ht⟩ := exists_bound tr.time i
    exact ⟨y, i, t, h0, ht, hy, hB⟩

/-- With a constant honest set, the count charged at any horizon is `FaultBound`. -/
theorem faultBoundAt_const (t d : Time) : tr.FaultBoundAt (fun _ => H) t d ↔ tr.FaultBound H t :=
  Iff.rfl

/-- With a constant honest set, `SyncOnAt` is `SyncOn`. -/
theorem syncOnAt_const {ΔF : Time} {W Wr : Time → Prop} {eff : Time → Time} :
    tr.SyncOnAt (fun _ => H) ΔF W Wr eff ↔ tr.SyncOn H ΔF W Wr eff := by
  constructor
  · intro h
    refine ⟨h.deltaF, h.delta_le, fun x hx i m hs hw y hy j hc hd => ?_,
      fun x hx i B hs hw y hy j hc hd => ?_, fun x hx i B hs hw y hy j hc hd hanc => ?_,
      fun x hx i a hs hw y hy j hc hd => ?_⟩
    · exact h.message x i m hx hs hw y j hy hc hd
    · exact h.block x i B hx hs hw y j hy hc hd
    · exact h.relay x i B hx hs hw y j hy hc hd (by rwa [honestBlocksAt_const])
    · exact h.attestation x i a hx hs hw y j hy hc hd
  · intro h
    refine ⟨h.deltaF, h.delta_le, fun x i m hx hs hw y j hy hc hd => ?_,
      fun x i B hx hs hw y j hy hc hd => ?_, fun x i B hx hs hw y j hy hc hd hanc => ?_,
      fun x i a hx hs hw y j hy hc hd => ?_⟩
    · exact h.message x hx i m hs hw y hy j hc hd
    · exact h.block x hx i B hs hw y hy j hc hd
    · exact h.relay x hx i B hs hw y hy j hc hd (by rwa [honestBlocksAt_const] at hanc)
    · exact h.attestation x hx i a hs hw y hy j hc hd

/-- With a constant honest set, `SyncRunAt` is `SyncRun`. -/
theorem syncRunAt_const {ΔF a b : Time} :
    tr.SyncRunAt (fun _ => H) ΔF a b ↔ tr.SyncRun H ΔF a b :=
  syncOnAt_const tr

/-- With a constant honest set, `GSTRunAt` is `GSTRun`. -/
theorem gstRunAt_const {ΔF g : Time} : tr.GSTRunAt (fun _ => H) ΔF g ↔ tr.GSTRun H ΔF g :=
  syncOnAt_const tr

/-- With a constant honest set, `SleepyRunAt` is `SleepyRun`, at every look-ahead. -/
theorem sleepyRunAt_const {ΔF : Time} (W : Time) :
    tr.SleepyRunAt (fun _ => H) ΔF W ↔ tr.SleepyRun H ΔF := by
  unfold SleepyRunAt SleepyRun
  rw [syncOnAt_const]
  refine and_congr_right fun _ => forall_congr' fun s => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    faultBoundAt_const, add_zero]

/-- With a constant honest set, `HealthyRunAt` is `HealthyRun`. -/
theorem healthyRunAt_const {ΔF g : Time} :
    tr.HealthyRunAt (fun _ => H) ΔF g ↔ tr.HealthyRun H ΔF g := by
  unfold HealthyRunAt HealthyRun
  rw [gstRunAt_const]
  refine and_congr_right fun _ => ⟨fun h => ⟨fun y hy t ht => h.1 y t ht hy, h.2 0⟩,
    fun h => ⟨fun y t ht hy => h.1 y hy t ht, fun _ => h.2⟩⟩

end RunTrace

namespace Growing

variable {FGP : Type} {A : ACInterface P FGP} {H : Set (Fin P.n)} {U : Set A.Blk}
  {tr : ACTrace A}

/-- The AC trace contract with a constant honest set is `ACLocalRun`. -/
theorem ACLocalRun.const_iff :
    Growing.ACLocalRun A (fun _ => H) U tr ↔ Consensus.Goldilocks.ACLocalRun A H U tr := by
  constructor
  · intro h
    exact
      { coherent := h.coherent
        init := h.init
        exec := fun i ℓ hl hy => h.exec i ℓ hl hy
        frameLaw := fun y hy i ℓ hc => h.frameLaw y i ℓ hy hc
        time_nonneg := h.time_nonneg
        time_mono := h.time_mono
        awake_of_call := fun y hy i ℓ hc => h.awake_of_call y i ℓ hy hc
        restart_of_sleep := fun y hy i ℓ u => h.restart_of_sleep y i ℓ u hy
        restart_at_wake := fun y hy u v => h.restart_at_wake y u v hy
        sleep_of_restart := fun y hy i ℓ => h.sleep_of_restart y i ℓ hy }
  · intro h
    exact
      { antitone := fun _ _ _ => le_rfl
        coherent := h.coherent
        init := h.init
        exec := fun i ℓ hl hy => h.exec i ℓ hl hy
        frameLaw := fun y i ℓ hy hc => h.frameLaw y hy i ℓ hc
        time_nonneg := h.time_nonneg
        time_mono := h.time_mono
        awake_of_call := fun y i ℓ hy hc => h.awake_of_call y hy i ℓ hc
        restart_of_sleep := fun y i ℓ u hy => h.restart_of_sleep y hy i ℓ u
        restart_at_wake := fun y u v hy => h.restart_at_wake y hy u v
        sleep_of_restart := fun y i ℓ hy => h.sleep_of_restart y hy i ℓ }

end Growing

/-- `Sync[a, b]` over an AC trace with a constant honest set is `SyncAC`. -/
theorem syncACAt_const {FGP : Type} {A : ACInterface P FGP} {H : Set (Fin P.n)} {U : Set A.Blk}
    {a b : Time} {tr : ACTrace A} : SyncACAt A (fun _ => H) U a b tr ↔ SyncAC A H U a b tr := by
  constructor
  · rintro ⟨hm, hb⟩
    exact ⟨fun x hx i m hs ha hb' y hy j ℓ hc hd => hm x i m hx hs ha hb' y j ℓ hy hc hd,
      fun x hx i B hs ha hb' y hy j ℓ hc hd hanc => hb x i B hx hs ha hb' y j ℓ hy hc hd hanc⟩
  · rintro ⟨hm, hb⟩
    exact ⟨fun x i m hx hs ha hb' y j ℓ hy hc hd => hm x hx i m hs ha hb' y hy j ℓ hc hd,
      fun x i B hx hs ha hb' y j ℓ hy hc hd hanc => hb x hx i B hs ha hb' y hy j ℓ hc hd hanc⟩

namespace SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {selectedProposer : Nat → Fin sp.n} {tr : SATrace sp FGP ro}

/-- With a constant honest set, the SA count charged at any horizon is `FaultBound`. -/
theorem faultBoundAt_const (t d : Time) : FaultBoundAt tr (fun _ => H) t d ↔ FaultBound tr H t :=
  Iff.rfl

/-- With a constant honest set, the frame blocks read while honest are the honest frame blocks. -/
theorem honestFrameBlockAt_const (B : Blk sp.n FGP) :
    HonestFrameBlockAt tr (fun _ => H) B ↔ HonestFrameBlock tr H B :=
  ⟨fun ⟨y, i, ℓ, hy, hc, hB⟩ => ⟨y, hy, i, ℓ, hc, hB⟩,
    fun ⟨y, hy, i, ℓ, hc, hB⟩ => ⟨y, i, ℓ, hy, hc, hB⟩⟩

/-- With a constant honest set, the earlier votes read while honest are the honest earlier
votes. -/
theorem earlierVotesExtendAt_const (i σ : Nat) (B : Blk sp.n FGP) :
    EarlierVotesExtendAt tr (fun _ => H) U i σ B ↔ EarlierVotesExtend tr H U i σ B :=
  ⟨fun h x hx j hj e he hs => h x j hj hx e he hs,
    fun h x j hj hx e he hs => h x hx j hj e he hs⟩

/-- With a constant honest set, `Growing.Carry` is `Carry`. -/
theorem carry_const (s : Nat) (CV : Set (Vote sp.n)) :
    Growing.Carry tr (fun _ => H) U s CV ↔ Carry tr H U s CV :=
  ⟨fun h y hy i e he hs => h y i e hy he hs, fun h y i e hy he hs => h y hy i e he hs⟩

/-- With a constant honest set, the growing-fault honest objects are `HonestObjects`. -/
theorem honestObjects_const :
    Growing.HonestObjects selectedProposer tr (fun _ => H) ↔
      HonestObjects selectedProposer tr H := by
  constructor
  · intro h
    exact
      { pool_vote := fun y hy i σ v hv hvH => h.pool_vote y i σ hy v hv hvH
        message_vote := fun y hy i ℓ v hc hl hvH => h.message_vote y i ℓ v hy hc hl hvH
        carried_vote := fun y hy i ℓ hc B hB v hv hvH => h.carried_vote y i ℓ hy hc B hB v hv hvH
        proposer := fun B hB hg => h.proposer B ((honestFrameBlockAt_const B).mpr hB) hg
        one_block := fun B B' ⟨y, hy, i, ℓ, hc, hB⟩ ⟨y', hy', i', ℓ', hc', hB'⟩ hp =>
          h.one_block y i ℓ B y' i' ℓ' B' hy hc hB hy' hc' hB' hp }
  · intro h
    exact
      { pool_vote := fun y i σ hy v hv hvH => h.pool_vote y hy i σ v hv hvH
        message_vote := fun y i ℓ v hy hc hl hvH => h.message_vote y hy i ℓ v hc hl hvH
        carried_vote := fun y i ℓ hy hc B hB v hv hvH => h.carried_vote y hy i ℓ hc B hB v hv hvH
        proposer := fun B hB hg => h.proposer B ((honestFrameBlockAt_const B).mp hB) hg
        one_block := fun y i ℓ B y' i' ℓ' B' hy hc hB hy' hc' hB' hp =>
          h.one_block B B' ⟨y, hy, i, ℓ, hc, hB⟩ ⟨y', hy', i', ℓ', hc', hB'⟩ hp }

/-- With a constant honest set, `Growing.ACRun` is `ACRun`. -/
theorem acRun_const :
    Growing.ACRun selectedProposer tr (fun _ => H) U ↔ ACRun selectedProposer tr H U :=
  ⟨fun h => ⟨h.stock, Goldilocks.Growing.ACLocalRun.const_iff.mp h.localRun,
      honestObjects_const.mp h.honest⟩,
    fun h => ⟨h.stock, Goldilocks.Growing.ACLocalRun.const_iff.mpr h.localRun,
      honestObjects_const.mpr h.honest⟩⟩

end SA

namespace Growing

variable {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- The FG trace contract with a constant honest set is `FGLocalRun`. -/
theorem FGLocalRun.const_iff :
    Growing.FGLocalRun acp₀ (fun _ => H) U tr ↔ Consensus.Goldilocks.FGLocalRun acp₀ H U tr := by
  constructor
  · intro h
    exact
      { coherent := h.coherent
        init := h.init
        exec := fun i ℓ hl hy => h.exec i ℓ hl hy
        tree_subset := fun y hy i => by
          obtain ⟨t, h0, ht⟩ := exists_bound tr.time i
          exact h.tree_subset y i t h0 ht hy
        time_nonneg := h.time_nonneg
        time_mono := h.time_mono
        attest_public := fun y hy i src signed hc => h.attest_public y i src signed hy hc
        own_first := fun y hy i B hc hp hs => h.own_first y i B hy hc hp hs
        attest_order := fun y hy j src signed hc => h.attest_order y j src signed hy hc
        own_payload := fun y hy i B hc hp hs => h.own_payload y i B hy hc hp hs
        unforgeable := fun y hy i a ha hv => h.unforgeable y i a hy ha hv }
  · intro h
    exact
      { antitone := fun _ _ _ => le_rfl
        coherent := h.coherent
        init := h.init
        exec := fun i ℓ hl hy => h.exec i ℓ hl hy
        tree_subset := fun y i _ _ _ hy => h.tree_subset y hy i
        time_nonneg := h.time_nonneg
        time_mono := h.time_mono
        attest_public := fun y i src signed hy hc => h.attest_public y hy i src signed hc
        own_first := fun y i B hy hc hp hs => h.own_first y hy i B hc hp hs
        attest_order := fun y j src signed hy hc => h.attest_order y hy j src signed hc
        own_payload := fun y i B hy hc hp hs => h.own_payload y hy i B hc hp hs
        unforgeable := fun y i a hy ha hv => h.unforgeable y hy i a ha hv }

end Growing

end Consensus.Goldilocks

end
