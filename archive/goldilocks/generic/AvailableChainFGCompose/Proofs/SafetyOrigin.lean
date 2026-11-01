module
public import AvailableChainFGCompose.Statements.SafetyOrigin
public import AvailableChainFGCompose.Statements.SafetyClaims
public import AvailableChainFGCompose.Proofs.SafetyStore
public import AvailableChainFGCompose.Proofs.SafetyAccountable
public import AvailableChainFGCompose.Proofs.SafetyClient

public section

/-! The safety consumers under the origin laws. A delivery can admit the delivered body
and bodies that were pending. Each stored non-genesis block still has a delivery to the
same node with its erasure and rows, so the conclusions of the consumers do not change. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {Ef : Electorate (Fin n)} {H : FGHeightView (Fin n)} {f : FGFinalityView (Fin n)}
variable {cfg : FGConfig}
variable [DecidableEq V] {E : Generic.Env V} {rho : V2.D.Run V P}
variable {Good : P.State → Prop} {pending : P.State → P.Object → Prop} {Q : Block → Prop}

/-- The frozen record implies the origin record, with no pending object: the one new block
of a delivery has the delivered object as its origin. With this empty pending reader the
converse also holds. With a nonempty pending reader the origin record is strictly weaker. -/
theorem safetyStoreOriginLaws_of_storeLaws (L : FGSafetyStoreLaws R S H f Good) :
    FGSafetyStoreOriginLaws R S H f Good (fun _ _ => False) where
  initial_good := L.initial_good
  clock_good := L.clock_good
  process_good := L.process_good
  own_good := L.own_good
  restart_good := L.restart_good
  invariant := L.invariant
  initial_tf := L.initial_tf
  restart_tf := L.restart_tf
  process_origin := fun nd o B hg hB hold =>
    ⟨o, Or.inl rfl, L.process_new nd o B hg hB hold⟩
  pending_origin := ⟨fun _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h.elim,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

/-- The shared origin lemma under the origin record: every prefix state is `Good`, each
stored block is genesis or was delivered to the same node, and each pending object was
delivered to the same node. -/
theorem safety_origin_stateBefore (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) :
    Good (V2.D.Run.stateBefore E rho i x) ∧
      (∀ B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF, B = .genesis ∨
        ∃ o t, V2.Event.deliver x o t ∈ rho.events ∧
          S.proposalErase o = some (R.erase B) ∧
          B.rows = (S.proposalRows o).filterMap S.decode) ∧
      ∀ q, pending (V2.D.Run.stateBefore E rho i x) q →
        ∃ t, V2.Event.deliver x q t ∈ rho.events := by
  obtain ⟨pInit, pClock, pProcess, pOwn, pRestart⟩ := L.pending_origin
  let M : P.State → Prop := fun st => Good st ∧
    (∀ B ∈ (R.core st).fg.TF, B = .genesis ∨
      ∃ o t, V2.Event.deliver x o t ∈ rho.events ∧
        S.proposalErase o = some (R.erase B) ∧
        B.rows = (S.proposalRows o).filterMap S.decode) ∧
    ∀ q, pending st q → ∃ t, V2.Event.deliver x q t ∈ rho.events
  refine V2.D.Engine.stateBefore_step_induction E rho M (Nat.zero_le i) x ?_
    ⟨L.initial_good, fun B hB => Or.inl (L.initial_tf B hB), fun q hq => (pInit q hq).elim⟩
  intro k e _ _ he hv hk
  obtain ⟨hg, htf, hpend⟩ := hk
  cases e with
  | restart u t =>
    change u = x at hv
    subst u
    have hM : M (P.restore (P.durable (V2.D.Run.stateBefore E rho k x)) t) :=
      ⟨L.restart_good _ t hg, fun B hB => htf B (L.restart_tf _ t B hg hB),
        fun q hq => hpend q (pRestart _ t q hg hq)⟩
    change M (Function.update (V2.D.Run.stateBefore E rho k) x _ x)
    rw [Function.update_self]
    exact hM
  | tick u t =>
    change u = x at hv
    subst u
    have hown : ∀ st o, M st → M (P.recordOwn st o) := by
      intro st o hst
      refine ⟨L.own_good st o hst.1, ?_, fun q hq => hst.2.2 q (pOwn st o q hst.1 hq)⟩
      rw [C.own_core]
      exact hst.2.1
    have hclock : M (P.clock (V2.D.Run.stateBefore E rho k x) t) := by
      refine ⟨L.clock_good _ t hg, ?_, fun q hq => hpend q (pClock _ t q hg hq)⟩
      rw [C.clock_fg]
      exact htf
    change M (Function.update (V2.D.Run.stateBefore E rho k) x _ x)
    rw [Function.update_self]
    exact V2.D.Engine.tick_preserve E rho M hown hclock
  | deliver u o t =>
    change u = x at hv
    subst u
    have hM : M (P.process (V2.D.Run.stateBefore E rho k x) o) := by
      refine ⟨L.process_good _ o hg, fun B hB => ?_, fun q hq => ?_⟩
      · by_cases hold : B ∈ (R.core (V2.D.Run.stateBefore E rho k x)).fg.TF
        · exact htf B hold
        · obtain ⟨origin, hsource, hp, hrows⟩ := L.process_origin _ o B hg hB hold
          rcases hsource with rfl | hwaiting
          · exact Or.inr ⟨origin, t, List.mem_of_getElem? he, hp, hrows⟩
          · obtain ⟨t', hd⟩ := hpend origin hwaiting
            exact Or.inr ⟨origin, t', hd, hp, hrows⟩
      · rcases pProcess _ o q hg hq with hold | rfl
        · exact hpend q hold
        · exact ⟨t, List.mem_of_getElem? he⟩
    change M (Function.update (V2.D.Run.stateBefore E rho k) x _ x)
    rw [Function.update_self]
    exact hM

private theorem safety_origin_good_readAt (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) (x : V) :
    Good (V2.D.Run.readAt E rho t x) := by
  obtain ⟨rho', -, h⟩ := safety_readAt_replay E rho t
  rw [h]
  exact (safety_origin_stateBefore C L E rho' _ x).1

private theorem safety_origin_read_delivery (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF) (hne : B ≠ .genesis) :
    ∃ o t', V2.Event.deliver x o t' ∈ rho.events ∧
      S.proposalErase o = some (R.erase B) ∧
      B.rows = (S.proposalRows o).filterMap S.decode := by
  obtain ⟨rho', hsub, h⟩ := safety_readAt_replay E rho t
  rw [h] at hB
  obtain ⟨o, t', hd, hp, hrows⟩ :=
    ((safety_origin_stateBefore C L E rho' _ x).2.1 B hB).resolve_left hne
  exact ⟨o, t', hsub _ hd, hp, hrows⟩

private theorem safety_origin_preceq_refl (b : Block) : Block.Preceq b b := by
  cases b <;> simp [Block.Preceq, Block.preceq]

/-- `safety_stored_runBlock` under the origin record. -/
theorem safety_stored_runBlock_origin (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF) (hne : B ≠ .genesis) :
    safetyRunBlock R S E rho B := by
  obtain ⟨o, t, hd, hp, -⟩ :=
    ((safety_origin_stateBefore C L E rho i x).2.1 B hB).resolve_left hne
  exact ⟨o, R.erase B, hp, Or.inr ⟨x, t, hd⟩, safety_origin_preceq_refl _⟩

private theorem safety_origin_read_runBlock (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF) (hne : B ≠ .genesis) :
    safetyRunBlock R S E rho B := by
  obtain ⟨o, t', hd, hp, -⟩ := safety_origin_read_delivery C L E rho t x B hB hne
  exact ⟨o, R.erase B, hp, Or.inr ⟨x, t', hd⟩, safety_origin_preceq_refl _⟩

private theorem safety_origin_stored_scope (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (N : FGSafetyScopeLaws R S E rho Q) (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (B : FGBlock (Fin n)) (hB : B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF) :
    Q (R.erase B) := by
  by_cases hne : B = .genesis
  · subst B
    exact N.genesis_scope x hx
  obtain ⟨o, t, hd, hp, -⟩ :=
    ((safety_origin_stateBefore C L E rho i x).2.1 B hB).resolve_left hne
  exact N.delivered_scope x o t _ hd hp

/-- `safety_read_scope` under the origin record. -/
theorem safety_read_scope_origin (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (N : FGSafetyScopeLaws R S E rho Q) (t : Time) (x : V) (hx : x ∈ rho.honest)
    (B : FGBlock (Fin n)) (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF) :
    Q (R.erase B) := by
  by_cases hne : B = .genesis
  · subst B
    exact N.genesis_scope x hx
  obtain ⟨o, t', hd, hp, -⟩ := safety_origin_read_delivery C L E rho t x B hB hne
  exact N.delivered_scope x o t' _ hd hp

variable (R S Ef H f E rho Good pending Q) in
/-- `safety_run_accountable` under the origin record. -/
theorem safety_run_accountable_origin
    (C : FGCoreLaws R) (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (K : FGCertificateLaws Ef H f) (N : FGSafetyScopeLaws R S E rho Q)
    (hr : safetyScopedRoots R Q) : SafetyWholeAccountable R S Ef f E rho := by
  refine ⟨fun A B T T' _ _ hA hB hfA hfB => ?_, fun x hx y hy i j => ?_,
    fun x hx y hy t t' => ?_⟩
  · exact (safety_runBlock_accountable K N hr hA hB).imp id (fun hc => hfA.1 ▸ hfB.1 ▸ hc)
  · exact safety_store_accountable K hr
      (L.invariant _ (safety_origin_stateBefore C L E rho i x).1)
      (L.invariant _ (safety_origin_stateBefore C L E rho j y).1)
      (fun B hB => safety_origin_stored_scope C L N i x hx B hB)
      (fun B hB => safety_origin_stored_scope C L N j y hy B hB)
  · exact safety_store_accountable K hr
      (L.invariant _ (safety_origin_good_readAt C L E rho t x))
      (L.invariant _ (safety_origin_good_readAt C L E rho t' y))
      (fun B hB => safety_read_scope_origin C L N t x hx B hB)
      (fun B hB => safety_read_scope_origin C L N t' y hy B hB)

variable (R S Ef H f E rho Good pending Q) in
/-- `safety_run_agreement` under the origin record. -/
theorem safety_run_agreement_origin
    (C : FGCoreLaws R) (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (K : FGCertificateLaws Ef H f) (N : FGSafetyScopeLaws R S E rho Q)
    (hr : safetyScopedRoots R Q) (hb : safetyBound R S Ef E rho) :
    SafetyWholeAgreement R S f E rho := by
  refine ⟨fun A B T T' _ _ hA hB hfA hfB => ?_, fun x _ y _ t t' => ?_⟩
  · exact hfA.1 ▸ hfB.1 ▸
      (safety_runBlock_accountable K N hr hA hB).resolve_left (hb A B hA hB)
  · exact safety_store_agreement K N hr hb
      (L.invariant _ (safety_origin_good_readAt C L E rho t x))
      (L.invariant _ (safety_origin_good_readAt C L E rho t' y))
      (fun B hB hne => safety_origin_read_runBlock C L E rho t x B hB hne)
      (fun B hB hne => safety_origin_read_runBlock C L E rho t' y B hB hne)

variable (R S Ef H f E rho Good pending Q) in
/-- `safety_event_agreement` under the origin record. -/
theorem safety_event_agreement_origin
    (C : FGCoreLaws R) (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (K : FGCertificateLaws Ef H f) (N : FGSafetyScopeLaws R S E rho Q)
    (hr : safetyScopedRoots R Q) (hb : safetyBound R S Ef E rho)
    (i j : Nat) (x y : V) :
    FGBlock.compatible (R.core (V2.D.Run.stateBefore E rho i x)).fg.F
      (R.core (V2.D.Run.stateBefore E rho j y)).fg.F = true :=
  safety_store_agreement K N hr hb
    (L.invariant _ (safety_origin_stateBefore C L E rho i x).1)
    (L.invariant _ (safety_origin_stateBefore C L E rho j y).1)
    (fun B hB hne => safety_stored_runBlock_origin C L E rho i x B hB hne)
    (fun B hB hne => safety_stored_runBlock_origin C L E rho j y B hB hne)

private theorem safety_origin_read_row (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (t : Time) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF)
    (u : Row (Fin n)) (hu : u ∈ chainRows B) :
    ∃ a o t', V2.Event.deliver x o t' ∈ rho.events ∧ a ∈ S.proposalRows o ∧
      S.decode a = some u := by
  induction B with
  | genesis => exact (Finset.notMem_empty u hu).elim
  | node Q s root body rows ih =>
    change u ∈ rows.toFinset ∪ chainRows Q at hu
    rcases (Finset.mem_union.mp hu).symm with hu | hu
    · exact ih ((L.invariant _ (safety_origin_good_readAt C L E rho t x)).closed _ hB) hu
    · obtain ⟨o, t', hd, -, hrows⟩ :=
        safety_origin_read_delivery C L E rho t x _ hB (by intro h; cases h)
      change rows = (S.proposalRows o).filterMap S.decode at hrows
      have hur : u ∈ rows := List.mem_toFinset.mp hu
      rw [hrows] at hur
      obtain ⟨a, ha, hau⟩ := List.mem_filterMap.mp hur
      exact ⟨a, o, t', hd, ha, hau⟩

/-- `safety_read_carriage` under the origin record. -/
theorem safety_read_carriage_origin (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (W : FGSafetyWireLaws S) (hu : V2.D.UnforgeableSignatures E rho)
    (t : Time) (x : V) :
    safetyCarriage S E rho (safetyRows R (V2.D.Run.readAt E rho t x)) := by
  rw [safetyCarriage_def]
  intro u hmem
  rw [safetyRows_def] at hmem
  obtain ⟨B, hB, hrow⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨a, o, t', hd, ha, hdec⟩ := safety_origin_read_row C L t x B hB u hrow
  refine ⟨a, hdec, fun hh => ?_⟩
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hd
  have hholder :
      V2.D.Run.holder rho (S.encode a).auth = some (safetyHolder S rho u.signer) := by
    rw [W.decode_auth a u hdec, safetyHolder_def]
    rfl
  obtain ⟨t'', -, i, hi, hem⟩ :=
    hu.carried x o t' ⟨k, hk⟩ (S.encode a) (W.carried o a ha) _ hh hholder
  rw [safetyEmits_def]
  exact ⟨i, t'', hi, hem⟩

variable (R S Ef H f cfg E rho Good pending) in
/-- `safety_honest_never_slashed` under the origin record. `Linked` is unchanged. -/
theorem safety_honest_never_slashed_origin
    (C : FGCoreLaws R) (W : FGSafetyWireLaws S)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (J : FGSafetyClientLaws S Ef cfg)
    (linked : P.Label → Prop) (hfg : linked S.fgLabel)
    (I : Gen.V2.Duty.SlashingInterface (V := V) P)
    (hi : safetySlashesRead R S E rho I)
    (hu : V2.D.UnforgeableSignatures E rho) (hl : V2.D.Linked linked rho) :
    Gen.V2.Duty.HonestNeverSlashed I rho := by
  rw [Gen.V2.Duty.HonestNeverSlashed_def]
  intro v hv hs
  rw [safetySlashesRead_def] at hi
  obtain ⟨x, y, t, t', i, ⟨a, ha, b, hb, hai, hbi, hab⟩, rfl⟩ := (hi v).mp hs
  have hca := safety_read_carriage_origin C L W hu t x
  have hcb := safety_read_carriage_origin C L W hu t' y
  rw [safetyCarriage_def] at hca hcb
  obtain ⟨wa, hwa, hea⟩ := hca a ha
  obtain ⟨wb, hwb, heb⟩ := hcb b hb
  rw [hai] at hea
  rw [hbi] at heb
  have hn := safety_emitted_noSlash S Ef cfg E rho W J linked hfg hl (safetyHolder S rho i)
  rw [safetyNoSlash_def] at hn
  exact hn wa wb (hea hv) (heb hv) a b hwa hwb hab

end AvailableChain.FGCompose
end
