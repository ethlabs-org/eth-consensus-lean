module
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSARun.Proofs.Emission

public import AvailableChainFGSAProofs.Proofs.Shared.Roots

public section

/-! W3 (blueprint 21:526–546), B19. The read index is arbitrary.
Assembly supplies the INLINE Cap, held-chain delivery, RQCOrigin,
and honest finality HEAD facts.
No healing reset is used. A receipt before a tick gives strict time order;
strict order on the action grid gives a full period. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem timing_row_wire {a : RowWire p.n} {u : Row (Fin p.n)}
    (hd : a.toRow? = some u) :
    a = ⟨.seat .fg u.signer, .vote ⟨u.height_pair, u.finality_pair⟩⟩ := by
  rcases a with ⟨auth, body⟩
  cases auth with
  | none => cases hd
  | proposer s => cases hd
  | seat label seat =>
    cases label with
    | head s => cases hd
    | fg =>
      have he : (⟨seat, body.height_pair, body.finality_pair⟩ : Row (Fin p.n)) = u :=
        Option.some.inj hd
      cases he
      cases body with
      | vote body => cases body; rfl

private theorem timing_row_signer {j r : Nat} {z : V} {a : RowWire p.n}
    {u : Row (Fin p.n)} (ha : HonestRowAt p c E rho j z r a)
    (hd : a.toRow? = some u) : RowSigner p c rho a z := by
  rw [timing_row_wire p hd] at ha ⊢
  obtain ⟨_, hseat, _, _, _⟩ := (fgsa_emitsAt_row E rho j z _ ha.2.1
    u.signer (.vote ⟨u.height_pair, u.finality_pair⟩)).mp ha.2.2
  exact ⟨u.signer, rfl, hseat⟩

/-- Route 2: keep the receipt and bind its round to the actual source row.
Assembly supplies the INLINE held-chain delivery fact. -/
theorem healing_row_delivery (hv : V2.D.ExecutionValid E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    {i : Nat} {x z : V} {r : Nat} {a : RowWire p.n}
    {W : FGBlock (Fin p.n)} {u : Row (Fin p.n)}
    (hW : HeldAt p c E rho i x W) (hu : u ∈ chainRows W)
    (hb : HonestRowBefore p c E rho i z r a) (hd : a.toRow? = some u) :
    ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧ p.actionTime r ≤ t := by
  obtain ⟨j, hji, hj⟩ := hb
  have hsign := timing_row_signer p c E rho hj hd
  obtain ⟨b, r', hbd, _, k, o, t, hki, hk, hem⟩ := heldRows i x W hW u hu
  have heq : b = a := (timing_row_wire p hbd).trans
    (timing_row_wire p hd).symm
  subst b
  obtain ⟨⟨j', _, hj'⟩, ht⟩ := hem z hsign hj.1
  obtain ⟨seat, har, hseat⟩ := hsign
  rcases a with ⟨auth, body⟩
  change auth = _ at har
  subst auth
  have he : j = j' := fgsa_emitOnceUnder E rho hv seat (hseat ▸ hj.1) (.row body)
    j j' (p.actionTime r) (p.actionTime r')
    (hseat ▸ hj.2.1) (hseat ▸ hj'.2.1) hj.2.2 hj'.2.2
  have hticks := hj.2.1.symm.trans (he ▸ hj'.2.1)
  have htime : p.actionTime r = p.actionTime r' :=
    congrArg V2.Event.time (Option.some.inj hticks)
  exact ⟨k, o, t, hki, hk, htime ▸ ht⟩

omit [DecidableEq V] in
/-- Route 4: all ticks at a time precede its deliveries. Event order alone
between ticks of different nodes does not give strict time order. -/
theorem healing_receipt_before_tick (hs : V2.D.ScheduleWellFormed E rho)
    {k i : Nat} {x z : V} {o : Obj p} {t a : Time}
    (hki : k < i) (hk : rho.events[k]? = some (.deliver x o t))
    (hi : rho.events[i]? = some (.tick z a)) : t < a := by
  by_contra hn
  have hik := V2.D.Engine.tick_index_lt_delivery E rho hs hi hk (le_of_not_gt hn)
  omega

/-- Route 5: strict action-time order on a_r = rP + 6Δ gives one period. -/
theorem healing_action_period {r r' : Nat}
    (ht : p.actionTime r < p.actionTime r') :
    p.actionTime r + P p ≤ p.actionTime r' := by
  have hp : 0 < P p := by
    change 0 < 4 * (p.R : Int) * p.Δ
    have hr : 0 < (p.R : Int) := by exact_mod_cast (show 0 < p.R by have := p.RLarge; omega)
    exact mul_pos (mul_pos (by decide) hr) p.deltaPos
  have he (n : Nat) : p.actionTime n = (n : Int) * P p + 6 * p.Δ := by
    change 4 * p.Δ * ((n * p.R : Nat) : Int) + 6 * p.Δ = _
    unfold P
    push_cast
    ring
  rw [he r, he r'] at ht ⊢
  have hlt : (r : Int) < r' := by
    by_contra hn
    have hn' : (r' : Int) ≤ r := le_of_not_gt hn
    nlinarith
  have hstep : (r : Int) + 1 ≤ r' := by omega
  nlinarith

/-- Route 6: the saved delivery gives the stored local clock bound.
This includes sleeping readers and reads after the event list ends. -/
theorem healing_delivery_clock (hv : V2.D.ExecutionValid E rho)
    (hnr : V2.D.NoRestart rho) {i k j r : Nat} {x z : V} {o : Obj p} {t : Time}
    (hki : k < i) (hk : rho.events[k]? = some (.deliver x o t))
    (hj : rho.events[j]? = some (.tick z (p.actionTime r)))
    (ht : p.actionTime r ≤ t) :
    p.actionTime r ≤ (storeAt p c E rho i x).base.now := by
  have hs := hv.toScheduleWellFormed
  have hpub := hs.tick_public z _ (List.mem_of_getElem? hj)
  have hzero : 0 ≤ p.actionTime r := by
    change 0 ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    have := p.deltaPos
    positivity
  have hclock := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho hv
    hk hpub hzero ht
  have hmono := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c)
    E rho hs hnr (Nat.le_of_lt hki) x
  exact (hclock.trans hmono).trans_eq
    (fgsa_clock_now p c (V2.D.Run.stateBefore E rho i x))

/-- Kept-state restart uses the exact wake clock and preserves this bound. -/
theorem healing_delivery_clock_on (hv : V2.D.ExecutionValid E rho)
    {i k j r : Nat} {x z : V} {o : Obj p} {t : Time}
    (hki : k < i) (hk : rho.events[k]? = some (.deliver x o t))
    (hj : rho.events[j]? = some (.tick z (p.actionTime r)))
    (ht : p.actionTime r ≤ t) :
    p.actionTime r ≤ (storeAt p c E rho i x).base.now := by
  have hs := hv.toScheduleWellFormed
  have hpub := hs.tick_public z _ (List.mem_of_getElem? hj)
  have hzero : 0 ≤ p.actionTime r := by
    change 0 ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    have := p.deltaPos
    positivity
  have hclock := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho hv
    hk hpub hzero ht
  have hmono := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho hs (Nat.le_of_lt hki) x
  exact (hclock.trans hmono).trans_eq
    (fgsa_clock_now p c (V2.D.Run.stateBefore E rho i x))

private theorem timing_choose_rows {Q : Finset (Fin p.n)}
    {P : Fin p.n → FGBlock (Fin p.n) → Row (Fin p.n) → Prop}
    (h : ∀ k ∈ Q, ∃ W a, P k W a) :
    ∃ rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n),
      ∀ k ∈ Q, P k (rows k).1 (rows k).2 := by
  classical
  refine ⟨fun k => if hk : k ∈ Q then
      (Classical.choose (h k hk), Classical.choose (Classical.choose_spec (h k hk)))
    else (.genesis, ⟨k, .empty, none⟩), ?_⟩
  intro k hk
  simp only [hk, ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec (h k hk))

/-- ROOT-DIGEST W2b. Route 4: apply INLINE RQCOrigin at this pre-action store and retain
its target row's real receiver delivery. Assembly supplies the INLINE
origin and held-chain delivery facts. -/
theorem healing_justification_timed (hroots : NamedRootCollisionFree p c E rho) (hv :
    V2.D.ExecutionValid E rho)
    (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    {i : Nat} {x : V} {W : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hnz : (heightView p W).h_j ≠ 0)
    (hqc : KitFG.TargetQCAt p.E W (heightView p W).h_j (heightView p W).J) :
    ∃ K r j z a, j < i ∧ HonestRowAt p c E rho j z r a ∧
      actionSourceFG p c E rho z r = some (some K) ∧
      (heightView p K).h = (heightView p W).h_j ∧
      (heightView p K).T_h = (heightView p W).J ∧
      ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧ p.actionTime r ≤ t := by
  obtain ⟨Q, hQ, hrows⟩ := hqc
  obtain ⟨rows, hr⟩ := timing_choose_rows p hrows
  obtain ⟨_, h2, _⟩ := origin i x W hx hW
  obtain ⟨k, hk, z, r, a, hb, hd, _, K, G, hK, hn, _⟩ := h2 Q rows hnz hQ hr
  obtain ⟨hc, hu, _, hpair⟩ := hr k hk
  have hdel := healing_row_delivery p c E rho hv heldRows ⟨hx, hW⟩
    (KitFG.mem_chainRows_of_carrier hc hu) hb hd
  rw [hpair] at hn
  obtain ⟨hh, hroot⟩ := Prod.mk.inj (Option.some.inj hn)
  obtain ⟨j, hji, hj⟩ := hb
  exact ⟨K, r, j, z, a, hji, hj, hK, hh.symm,
    rootScope_eq hroots (rootScope_entry (rootScope_source hj.1 hK))
      (rootScope_justified (rootScope_store hx hW)) hroot.symm, hdel⟩

/-- ROOT-DIGEST W2b. T1, routes 1–6. INLINE Cap supplies the honest finality row at the
selected carrier's certificate height. It is not the height of F. -/
theorem healing_finality_source_clock (hroots : NamedRootCollisionFree p c E rho) (hv :
    V2.D.ExecutionValid E rho)
    (hnr : V2.D.NoRestart rho) (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    (cap : ∀ (y i : Nat), 0 < y → ∀ x W, HeldAt p c E rho i x W →
      y ≤ (finalityView p W).h_F →
      ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
        RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
        u.finality_pair = some ⟨(finalityView p W).h_F, (finalityView p W).F.root⟩)
    (hhead : ∀ {j r : Nat} {z : V} {a : RowWire p.n} {u : Row (Fin p.n)},
      HonestRowAt p c E rho j z r a → RowSigner p c rho a z →
      a.toRow? = some u → ∀ fp, u.finality_pair = some fp →
      ∃ H, HeldAt p c E rho j z H ∧ fp.height = (heightView p H).h_j ∧
        fp.target = (heightView p H).J.root ∧
        KitFG.TargetQCAt p.E H fp.height (heightView p H).J)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hF : (storeAt p c E rho i x).fg.F ≠ .genesis) :
    ∃ D ∈ (storeAt p c E rho i x).fg.TF,
      (finalityView p D).F = (storeAt p c E rho i x).fg.F ∧
      ∃ K s, SourceBefore p c E rho i K s ∧
        (heightView p K).h = (finalityView p D).h_F ∧
        (heightView p K).T_h = (storeAt p c E rho i x).fg.F ∧
        SA.gateTime p.toParams s + P p ≤ (storeAt p c E rho i x).base.now := by
  obtain ⟨D, hD, hDF⟩ := (cstoreInv_stateBefore E rho i x).fg.Fcar
  have hpos : 0 < (finalityView p D).h_F := by
    have hnz : (finalityView p D).h_F ≠ 0 := fun hz =>
      hF (hDF.symm.trans ((fgCertificateLaws p).finalized_zero D hz))
    exact Nat.pos_of_ne_zero hnz
  obtain ⟨z, rf, a, u, hb, hsign, hd, hu, hf⟩ :=
    cap _ i hpos x D ⟨hx, hD⟩ le_rfl
  obtain ⟨kf, objf, tf, hkfi, hkf, hft⟩ :=
    healing_row_delivery p c E rho hv heldRows ⟨hx, hD⟩ hu hb hd
  obtain ⟨jf, hjfi, hjf⟩ := hb
  obtain ⟨H, hH, hh, hroot, hqc⟩ := hhead hjf hsign hd _ hf
  change (finalityView p D).h_F = (heightView p H).h_j at hh
  change (finalityView p D).F.root = (heightView p H).J.root at hroot
  have hqc' : KitFG.TargetQCAt p.E H (heightView p H).h_j (heightView p H).J := by
    rwa [hh] at hqc
  obtain ⟨K, rt, jt, zt, atr, hjtjf, hjt, hK, hKh, hKT, kt, ot, tt, hktjf, hkt, htt⟩ :=
    healing_justification_timed (hroots := hroots) p c E rho hv origin heldRows hH.1 hH.2
      (by rw [← hh]; exact Nat.ne_of_gt hpos) hqc'
  have hlt := healing_receipt_before_tick p c E rho hv.toScheduleWellFormed hktjf hkt hjf.2.1
  have hperiod := healing_action_period p (htt.trans_lt hlt)
  have hclock := healing_delivery_clock p c E rho hv hnr
    hkfi hkf hjf.2.1 hft
  have htime : SA.gateTime p.toParams (rt * p.R) + P p ≤
      (storeAt p c E rho i x).base.now := by
    change p.actionTime rt + P p ≤ _
    exact hperiod.trans hclock
  refine ⟨D, hD, hDF, K, rt * p.R,
    ⟨jt, zt, rt, atr, Nat.lt_trans hjtjf hjfi, hjt, hK, rfl⟩,
    hKh.trans hh.symm, ?_, htime⟩
  apply rootScope_eq hroots (rootScope_entry (rootScope_source hjt.1 hK))
    (rootScope_store hx (cstoreInv_stateBefore E rho i x).fg.Fmem)
  rw [hKT, ← hroot]
  exact congrArg FGBlock.root hDF

/-- Kept-state restart uses the exact wake clock and preserves this bound. -/
theorem healing_finality_source_clock_on (hroots : NamedRootCollisionFree p c E rho) (hv :
    V2.D.ExecutionValid E rho)
    (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    (cap : ∀ (y i : Nat), 0 < y → ∀ x W, HeldAt p c E rho i x W →
      y ≤ (finalityView p W).h_F →
      ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
        RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
        u.finality_pair = some ⟨(finalityView p W).h_F, (finalityView p W).F.root⟩)
    (hhead : ∀ {j r : Nat} {z : V} {a : RowWire p.n} {u : Row (Fin p.n)},
      HonestRowAt p c E rho j z r a → RowSigner p c rho a z →
      a.toRow? = some u → ∀ fp, u.finality_pair = some fp →
      ∃ H, HeldAt p c E rho j z H ∧ fp.height = (heightView p H).h_j ∧
        fp.target = (heightView p H).J.root ∧
        KitFG.TargetQCAt p.E H fp.height (heightView p H).J)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hF : (storeAt p c E rho i x).fg.F ≠ .genesis) :
    ∃ D ∈ (storeAt p c E rho i x).fg.TF,
      (finalityView p D).F = (storeAt p c E rho i x).fg.F ∧
      ∃ K s, SourceBefore p c E rho i K s ∧
        (heightView p K).h = (finalityView p D).h_F ∧
        (heightView p K).T_h = (storeAt p c E rho i x).fg.F ∧
        SA.gateTime p.toParams s + P p ≤ (storeAt p c E rho i x).base.now := by
  obtain ⟨D, hD, hDF⟩ := (cstoreInv_stateBefore E rho i x).fg.Fcar
  have hpos : 0 < (finalityView p D).h_F := by
    have hnz : (finalityView p D).h_F ≠ 0 := fun hz =>
      hF (hDF.symm.trans ((fgCertificateLaws p).finalized_zero D hz))
    exact Nat.pos_of_ne_zero hnz
  obtain ⟨z, rf, a, u, hb, hsign, hd, hu, hf⟩ :=
    cap _ i hpos x D ⟨hx, hD⟩ le_rfl
  obtain ⟨kf, objf, tf, hkfi, hkf, hft⟩ :=
    healing_row_delivery p c E rho hv heldRows ⟨hx, hD⟩ hu hb hd
  obtain ⟨jf, hjfi, hjf⟩ := hb
  obtain ⟨H, hH, hh, hroot, hqc⟩ := hhead hjf hsign hd _ hf
  change (finalityView p D).h_F = (heightView p H).h_j at hh
  change (finalityView p D).F.root = (heightView p H).J.root at hroot
  have hqc' : KitFG.TargetQCAt p.E H (heightView p H).h_j (heightView p H).J := by
    rwa [hh] at hqc
  obtain ⟨K, rt, jt, zt, atr, hjtjf, hjt, hK, hKh, hKT, kt, ot, tt, hktjf, hkt, htt⟩ :=
    healing_justification_timed (hroots := hroots) p c E rho hv origin heldRows hH.1 hH.2
      (by rw [← hh]; exact Nat.ne_of_gt hpos) hqc'
  have hlt := healing_receipt_before_tick p c E rho hv.toScheduleWellFormed hktjf hkt hjf.2.1
  have hperiod := healing_action_period p (htt.trans_lt hlt)
  have hclock := healing_delivery_clock_on p c E rho hv
    hkfi hkf hjf.2.1 hft
  have htime : SA.gateTime p.toParams (rt * p.R) + P p ≤
      (storeAt p c E rho i x).base.now := by
    change p.actionTime rt + P p ≤ _
    exact hperiod.trans hclock
  refine ⟨D, hD, hDF, K, rt * p.R,
    ⟨jt, zt, rt, atr, Nat.lt_trans hjtjf hjfi, hjt, hK, rfl⟩,
    hKh.trans hh.symm, ?_, htime⟩
  apply rootScope_eq hroots (rootScope_entry (rootScope_source hjt.1 hK))
    (rootScope_store hx (cstoreInv_stateBefore E rho i x).fg.Fmem)
  rw [hKT, ← hroot]
  exact congrArg FGBlock.root hDF

/-- ROOT-DIGEST W2b. T2: the analogous J source needs only the one-action clock bound.
No reset, future event, or equality with a next event time is used. -/
theorem healing_justified_source_clock (hv : V2.D.ExecutionValid E rho)
    (hnr : V2.D.NoRestart rho) (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hj : (storeAt p c E rho i x).fg.h_j ≠ 0)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∃ K s, SourceBefore p c E rho i K s ∧
      (heightView p K).h = (storeAt p c E rho i x).fg.h_j ∧
      (heightView p K).T_h = (storeAt p c E rho i x).fg.J ∧
      SA.gateTime p.toParams s ≤ (storeAt p c E rho i x).base.now := by
  obtain ⟨W, hW, _, hjW, hJW⟩ := (cstoreInv_stateBefore E rho i x).fg.pair.1
  have hnz : (heightView p W).h_j ≠ 0 := by rwa [← hjW]
  have hqc := (fgCertificateLaws p).height.justification_certificate W hnz
  obtain ⟨K, r, j, z, a, hji, ha, hK, hh, hT, k, o, t, hki, hk, ht⟩ :=
    healing_justification_timed (hroots := hroots) p c E rho hv origin heldRows hx hW hnz hqc
  exact ⟨K, r * p.R, ⟨j, z, r, a, hji, ha, hK, rfl⟩, hh.trans hjW.symm,
    hT.trans hJW.symm, healing_delivery_clock p c E rho hv hnr
      hki hk ha.2.1 ht⟩

/-- Kept-state restart uses the exact wake clock and preserves this bound. -/
theorem healing_justified_source_clock_on (hv : V2.D.ExecutionValid E rho)
    (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hj : (storeAt p c E rho i x).fg.h_j ≠ 0)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∃ K s, SourceBefore p c E rho i K s ∧
      (heightView p K).h = (storeAt p c E rho i x).fg.h_j ∧
      (heightView p K).T_h = (storeAt p c E rho i x).fg.J ∧
      SA.gateTime p.toParams s ≤ (storeAt p c E rho i x).base.now := by
  obtain ⟨W, hW, _, hjW, hJW⟩ := (cstoreInv_stateBefore E rho i x).fg.pair.1
  have hnz : (heightView p W).h_j ≠ 0 := by rwa [← hjW]
  have hqc := (fgCertificateLaws p).height.justification_certificate W hnz
  obtain ⟨K, r, j, z, a, hji, ha, hK, hh, hT, k, o, t, hki, hk, ht⟩ :=
    healing_justification_timed (hroots := hroots) p c E rho hv origin heldRows hx hW hnz hqc
  exact ⟨K, r * p.R, ⟨j, z, r, a, hji, ha, hK, rfl⟩, hh.trans hjW.symm,
    hT.trans hJW.symm, healing_delivery_clock_on p c E rho hv
      hki hk ha.2.1 ht⟩

end AvailableChain.FGSA.Run
end
