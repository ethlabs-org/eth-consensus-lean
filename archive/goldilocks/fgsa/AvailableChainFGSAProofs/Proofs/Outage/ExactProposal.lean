module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSAClaims.Statements.Channels
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- A durable block has a network acceptance before the index. A restart
restamps the block but does not create its original acceptance. -/
theorem inclusion_acceptance_before_index
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (k : Nat) (x : V)
    (b : Block) (hne : b ≠ .genesis)
    (hm : b ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) :
    ∃ i < k, ∃ t o, blockOf? p o = some b ∧ V2.D.Run.acceptsAt E rho i x o t := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [← (metaInv_stateBefore E rho k x).stampKeys] at hm
    obtain ⟨⟨b', stamp⟩, hm, he⟩ := List.mem_map.mp hm
    dsimp only at he
    subst b'
    rcases fgsa_block_stamp_source_or_restart E rho k x b stamp hm with
      hg | ⟨i, hi, t, o, ho, ha, _⟩ | ⟨j, hj, _, _, _, hb, _⟩
    · exact (hne hg.1).elim
    · exact ⟨i, hi, t, o, ho, ha⟩
    · obtain ⟨i, hi, t, o, ho, ha⟩ := ih j hj hb
      exact ⟨i, hi.trans hj, t, o, ho, ha⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X1 (acceptance step).
Class (iii). DC: INTENTIONAL; a non-genesis block in the strict read has an
earlier acceptance. The original acceptance survives every restart. -/
theorem inclusion_acceptance_of_stored
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (b : Block) (u : Time) (x : V)
    (hne : b ≠ .genesis)
    (hm : b ∈ (V2.D.Run.stateBeforeTime E rho u x).st.base.blocks) :
    ∃ o i t, (fgsaInterface p c).block o.payload = some b ∧ t < u ∧
      V2.D.Run.acceptsAt E rho i x o t := by
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho u hs] at hm
  obtain ⟨i, hi, t, o, ho, ha⟩ := inclusion_acceptance_before_index E rho _ x b hne hm
  obtain ⟨parent, hd, _⟩ := ha.1
  refine ⟨o, i, t, ?_, (Gen.V2.Duty.index_lt_idxBefore_iff hs hd u).mp hi, ha⟩
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> cases ho
  | seat l j =>
    cases l with
    | base l => cases l <;> cases payload <;> cases ho
    | prop s =>
        cases payload with
        | head => cases ho
        | row => cases ho
        | proposal => exact ho

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X1 (receipt step).
Class (iii). DC: INTENTIONAL; non-row traffic uses Delta independently of
the row delay. This is the receipt consumer; Clean compatibility must be
produced with receiver service before it can discharge X1. Readers are joined. -/
theorem inclusion_receipt_of_compatible [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (s : Slot) (N : NamedProposal p.n)
    (hne : N.erase ≠ .genesis)
    (hService : ∀ x, headReader p E rho x s (SA.voteTime p.toParams s) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.voteTime p.toParams s) x)) :
    ∀ x, headReader p E rho x s (SA.voteTime p.toParams s) →
      ∃ o i t, (fgsaInterface p c).block o.payload = some N.erase ∧
        t < SA.voteTime p.toParams s ∧ V2.D.Run.acceptsAt E rho i x o t := by
  intro x hx
  obtain ⟨h⟩ := hService x hx
  obtain ⟨Y, hY, heY⟩ := h.proposal hset.pre.base.valid.toScheduleWellFormed hx.1
    hset.pre.base.receiptIdealization
  have hm := ((storeBundle_stateBeforeTime E rho (SA.voteTime p.toParams s) x).cstore.baseTree
    N.erase).mpr ⟨Y, hY, heY⟩
  exact inclusion_acceptance_of_stored E rho hset.pre.base.valid.toScheduleWellFormed
    N.erase (SA.voteTime p.toParams s) x hne hm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X1 (honest input).
Class (iii). DC: INTENTIONAL; the supplied honest proposal produces the
non-genesis fact. The Clean joint induction must supply receiver service
with checked dependencies, finality compatibility, and the current epoch. -/
theorem inclusion_proposal_receipt [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF) (pt : PtSP)
    (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hService : ∀ N, V2.D.Run.emits E rho (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
      (ofWire p ⟨.proposer pt.s, .proposal N⟩) (SA.proposalTime p.toParams pt.s) →
      ∀ x, headReader p E rho x pt.s (SA.voteTime p.toParams pt.s) →
        Nonempty (ReceiverService E rho (ofWire p ⟨.proposer pt.s, .proposal N⟩)
          (SA.proposalTime p.toParams pt.s) (SA.voteTime p.toParams pt.s) x)) :
    ∀ x, headReader p E rho x pt.s (SA.voteTime p.toParams pt.s) →
      ∃ o i t, (fgsaInterface p c).block o.payload = some pt.P ∧
        t < SA.voteTime p.toParams pt.s ∧ V2.D.Run.acceptsAt E rho i x o t := by
  obtain ⟨hslot, o, ⟨ip, hip, hem⟩, hb⟩ := hprop
  have hx : V2.D.proposerOf rho (fgsaInterface p c) pt.s ∈ rho.honest := hslot.2
  have haw : E.awake (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
      (SA.proposalTime p.toParams pt.s) = true := by
    cases he : E.awake (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
        (SA.proposalTime p.toParams pt.s) with
    | true => rfl
    | false =>
      rw [(V2.D.Run.step_tick_eq E rho hip).2,
        (fgsa_tick_asleep E rho (V2.D.Run.stateBefore E rho ip
          (V2.D.proposerOf rho (fgsaInterface p c) pt.s))
          (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
          (V2.D.proposalTime (fgsaInterface p c) pt.s) he).1] at hem
      exact (List.not_mem_nil hem).elim
  have hw := honest_emit_wellFormed E rho hset.pre.base.valid.toDeliveryWellFormed
    hset.pre.base.valid.toScheduleWellFormed ip _ _ hip hx haw o hem
  rcases o with ⟨auth, payload⟩
  cases payload with
  | head b => cases hb
  | row body => cases hb
  | proposal N =>
    have hbp : N.erase = pt.P := Option.some.inj hb
    cases auth with
    | none => cases hw
    | seat l j =>
      cases l with
      | base l => cases l <;> cases hw
      | prop s =>
        have hj : j = ⟨0, Nat.one_pos⟩ := Subsingleton.elim (α := Fin 1) _ _
        subst j
        have hm := hem
        rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
        have hp := (fgsa_emits_proposal E rho _ _ _ s _).mp hm
        have htime := hp.2.1
        change (4 * p.Δ) * (s : Int) = (4 * p.Δ) * (pt.s : Int) at htime
        have hs : s = pt.s := Int.natCast_inj.mp
          (mul_left_cancel₀ (ne_of_gt (mul_pos (by decide) p.deltaPos)) htime)
        subst s
        have hne : N.erase ≠ .genesis := by
          intro hg
          have hn := (named_erase_eq_genesis N).mp hg
          subst N
          change false = true at hw
          cases hw
        have hresult := inclusion_receipt_of_compatible E rho ΔF hset pt.s N hne
          (hService N ⟨ip, hip, hem⟩)
        simpa only [hbp] using hresult

/-- A joined HEAD read excludes only a local restart at this vote time.
Earlier restarts and other nodes' same-time restarts are allowed. -/
theorem inclusion_preTick_eq_timeRead_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {t : Time}
    (hi : rho.events[i]? = some (.tick x t))
    (hRestart : V2.Event.restart x t ∉ rho.events) :
    V2.D.Run.stateBefore E rho i x =
      V2.D.Run.stateBeforeTime E rho t x := by
  let q := fun e : V2.Event V (fgsa p c).Object => decide (e.time < t)
  have hdown : ∀ e f : V2.Event V (fgsa p c).Object, e.key ≤ f.key → q f = true → q e = true := by
    intro e f hk hf
    exact decide_eq_true ((V2.D.Engine.time_le_of_key_le e f hk).trans_lt
      (of_decide_eq_true hf))
  have hf := V2.D.Engine.filter_eq_take hs q hdown
  have hni : (rho.events.filter q).length ≤ i := by
    by_contra hn
    have hlt := Nat.lt_of_not_ge hn
    have hm : V2.Event.tick x t ∈ rho.events.filter q := by
      rw [hf]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    exact lt_irrefl t (of_decide_eq_true (List.mem_filter.mp hm).2)
  change _ = ((rho.events.filter q).foldl (V2.D.World.step E rho) V2.D.World.init) x
  rw [hf]
  apply V2.D.Engine.stateBefore_other_node E rho hni
  intro j e hj hji hget hnode
  have hl : t ≤ e.time := by
    have hh := V2.D.Engine.filter_false_of_index_ge hs q hdown hj hget
    simpa [q] using hh
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk : e.key ≤ (V2.Event.tick x t : V2.Event V (fgsa p c).Object).key := by
    simpa [hje, hie] using (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  have ht : e.time = t := le_antisymm (V2.D.Engine.time_le_of_key_le _ _ hk) hl
  have he : e = .tick x t := by
    cases e with
    | restart u w =>
        change u = x at hnode
        subst u
        change w = t at ht
        subst w
        exact (hRestart (List.mem_of_getElem? hget)).elim
    | tick u w =>
        change u = x at hnode
        change w = t at ht
        rw [hnode, ht]
    | deliver u o w =>
        change w = t at ht
        subst w
        change toLex (t, (2 : Nat)) ≤ toLex (t, (1 : Nat)) at hk
        simp [Prod.Lex.toLex_le_toLex] at hk
  have hjiEq : j = i :=
    (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, he])
  omega


/-- A joined vote reader excludes its own restart at the vote cut. -/
theorem inclusion_preTick_eq_timeRead_joined
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hJ : joinedAt p E rho x s (SA.voteTime p.toParams s)) :
    V2.D.Run.stateBefore E rho i x =
      V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams s) x := by
  apply inclusion_preTick_eq_timeRead_on E rho hs hi
  intro hR
  have hb := hJ.2.2 _ (hs.in_horizon _ hR).1 le_rfl hR
  change 4 * p.Δ * (s : Time) + p.Δ ≤ 4 * p.Δ * ((s : Time) - 1) at hb
  nlinarith [p.deltaPos]

/-- An enabled gate excludes its own restart at that gate cut. -/
theorem inclusion_preTick_eq_timeRead_enabled
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hG : enabledGateAt p c E rho i x s) :
    V2.D.Run.stateBefore E rho i x =
      V2.D.Run.stateBeforeTime E rho (SA.gateTime p.toParams s) x := by
  apply inclusion_preTick_eq_timeRead_on E rho hs hG.1
  intro hR
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hR
  have hji := V2.D.Engine.restart_index_lt_event hs hj hG.1 le_rfl
    (by change (0 : Nat) < 1; decide)
  obtain ⟨w, hw, hsw⟩ := fgsa_restartTime_ge E rho hs hj hji
  have hb := hG.2
  change (storeAt p c E rho i x).restartTime = some w at hw
  rw [hw] at hb
  have hle := hsw.trans hb
  change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ 4 * p.Δ * (s : Time) at hle
  nlinarith [p.deltaPos]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X2 (read step).
Class (iii). DC: INTENTIONAL; the strict-before clocked read equals the
scheduled deterministic HEAD for a joined reader. The retained-walk proof
supplies the HEAD value. Earlier restarts are allowed. -/
theorem inclusion_head_read
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (x : V) (s : Slot) (b : Block)
    (hJ : joinedAt p E rho x s (SA.voteTime p.toParams s))
    (hh : headAtLabel p c E rho x s = some b) :
    FGSA.headVote p ((fgsa p c).clock
      (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams s) x)
      (SA.voteTime p.toParams s)).st s = b := by
  change (postClock E rho x (SA.voteTime p.toParams s)).map _ = some b at hh
  rw [postClock_def, preTick_def] at hh
  cases hi : V2.D.Run.tickIdx? rho x (SA.voteTime p.toParams s) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hh
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hh
    rw [inclusion_preTick_eq_timeRead_joined E rho hs (V2.D.Run.tickIdx?_spec hi) hJ] at hh
    exact hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X3.
Class (iii). DC: INTENTIONAL; sleep suppresses every emitted object while
the deterministic clock and read remain defined. No Clean or tick premise
is needed. -/
theorem inclusion_sleep_silence
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (s : Slot) :
    ∀ x ∈ rho.honest, E.awake x (SA.voteTime p.toParams s) = false →
      ∀ o, ¬ V2.D.Run.emits E rho x o (SA.voteTime p.toParams s) := by
  intro x _ hx o ⟨i, hi, hem⟩
  rw [(V2.D.Run.step_tick_eq E rho hi).2,
    (fgsa_tick_asleep E rho (V2.D.Run.stateBefore E rho i x) x _ hx).1] at hem
  exact List.not_mem_nil hem

end AvailableChain.FGSA.Run
end
