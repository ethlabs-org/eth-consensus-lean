module
public import AvailableChainFGCompose.Statements.FinalityRecords
public import AvailableChainFGCompose.Statements.Population.Seats
public import AvailableChainFGCompose.Proofs.HolderClient
public import AvailableChainFGCompose.Proofs.OrdinaryHolderClient
public import AvailableChainFGCompose.Proofs.Population.HolderBaseHighTarget

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {O : FGObservationReads R} {T : FGTiming}
variable {E : Generic.Env V} {rho : V2.D.Run V P}
variable {D : FGHistoryWireReads S} {Ef : Electorate (Fin n)} {cfg : FGConfig}
variable {pt : FGServicePoint}

/-- The actual holder trace supplies durable row history without enumerating the nodes. -/
private theorem d7r_history_holder
    (trace : FGHolderClientTrace S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho)) (seat : Fin n) (hx : safetyHolder S rho seat ∈ rho.honest)
    (i : Nat) :
    FGRowRecordHistory (S.record (V2.D.Run.stateBefore E rho i (safetyHolder S rho seat))) := by
  rw [((ordinary_FGHolderClientTrace_iff S Ef cfg E rho _).mp trace seat hx i).1]
  let inputs := (List.range i).filterMap (safetyInputAt S E rho (safetyHolder S rho seat))
  have hc := clientRunOnce_covers Ef cfg seat inputs RecordOnce.initial recordInv_initial
  refine ⟨hc.1, ?_⟩
  intro h U timeout fp hm
  rw [clientRecordOnce_sent] at hm
  change (.vote h U timeout, fp) ∈
    ((clientRunOnce Ef cfg seat RecordOnce.initial inputs).map Row.onceKey).reverse ++ [] at hm
  simp only [List.append_nil, List.mem_reverse, List.mem_map] at hm
  obtain ⟨a, ha, hk⟩ := hm
  have hh := congrArg Prod.fst hk
  change a.height_pair = .vote h U timeout at hh
  exact ⟨fun ht => (hc.2.2 a ha).1 h U (ht ▸ hh),
    fun ht => (hc.2.2 a ha).2.1 h U (ht ▸ hh)⟩

-- P9 supplies the entry, durable invariant, HEAD alignment and exact prior origins.
-- These remain all-node leaves; this package produces rows only at honest FG holders.
variable (entry : Nat → BlockId)
variable (hentry : ∀ x r C, x ∈ rho.honest →
  actionSourceFG R E rho T x r = some (some C) → high R O pt.reset C →
  entry (O.height C).h = (O.height C).T_h.root)
variable (records : ∀ j x, x ∈ rho.honest →
  HighRecordInvariant pt.reset.M entry (S.record (V2.D.Run.stateBefore E rho j x)))
variable (finality : ∀ j x t Λ fp, x ∈ rho.honest →
  finality_pair Λ (S.inputs (P.clock (V2.D.Run.stateBefore E rho j x) t)).2 = some fp →
  pt.reset.M + 1 ≤ fp.height → fp.target = entry fp.height)
variable (prior : ∀ j x, x ∈ rho.honest →
  ∀ b ∈ (S.record (V2.D.Run.stateBefore E rho j x)).sent,
  ∃ k rSent a, k < j ∧ HonestRowAt S E rho T k x rSent a ∧
    namedEntry (D.heightPair a) = namedEntry b.1)
variable (hsrc : ∀ nd, (S.inputs nd).1 = R.source nd)
variable (hheight : ∀ C, ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root) =
  ((O.height C).h, (O.height C).T_h.root))
variable (J : FGSafetyClientLaws S Ef cfg)
variable (client : FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho)
  (safetyHolder S rho))
variable (trace : FGHolderClientTrace S Ef cfg E rho (ordinaryFGExecutionObs E rho)
  (safetyHolder S rho))
variable (emission : HighRecordEmission S T E rho Ef cfg)
variable {valid : Wire → Bool}
variable (complete : ∀ j x r a, HonestRowAt S E rho T j x r a →
  ∃ u, S.decode a = some u ∧ RowComplete S rho D.signer valid x a)
variable (wireLaws : FGRowPermissionWireLaws S (fun a => namedEntry (D.heightPair a)))
variable (hT : FGTimingLaws T) (hs : V2.D.ScheduleWellFormed E rho)
variable (enabled : ∀ r, S.enabled (T.action r) = true)

include hentry records finality prior hsrc hheight J client trace emission complete
  wireLaws hT hs enabled in
/-- The current/prior target split at an honest holder retains the original send index. -/
theorem high_target_row_covered_holder (seat : Fin n)
    (hx : safetyHolder S rho seat ∈ rho.honest) (r : Nat) (C : FGBlock (Fin n))
    (hsource : actionSourceFG R E rho T (safetyHolder S rho seat) r = some (some C))
    (hhigh : high R O pt.reset C)
    (hawake : E.awake (safetyHolder S rho seat) (T.action r) = true) :
    ∃ j rSent a, rSent ≤ r ∧ HonestRowAt S E rho T j (safetyHolder S rho seat) rSent a ∧
      RowComplete S rho D.signer valid (safetyHolder S rho seat) a ∧
      D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false := by
  let x := safetyHolder S rho seat
  obtain ⟨nd, hnd, hC⟩ := Option.map_eq_some_iff.mp hsource
  obtain ⟨i, htick, hclock⟩ := postClock_tick E rho hnd
  have hrec : S.record nd = S.record (V2.D.Run.stateBefore E rho i x) := by
    rw [← hclock, J.clock_record]
  have he := hentry x r C hx hsource hhigh
  obtain ⟨_, _, hl, _⟩ := records i x hx (O.height C).h hhigh
  have hol : own_lock (S.record nd).toRecord (O.height C).h
      (finality_pair (S.record nd).toRecord (S.inputs nd).2) = none ∨
      own_lock (S.record nd).toRecord (O.height C).h
        (finality_pair (S.record nd).toRecord (S.inputs nd).2) = some (O.height C).T_h.root := by
    cases hp : finality_pair (S.record nd).toRecord (S.inputs nd).2 with
    | none => simpa only [own_lock, hrec, he] using hl
    | some fp =>
      by_cases hy : fp.height = (O.height C).h
      · have hf := finality i x (T.action r) (S.record nd).toRecord fp hx
          (by rw [hclock]; exact hp) (hy ▸ hhigh)
        have hf' : fp.target = (O.height C).T_h.root := by simpa only [hy, he] using hf
        exact Or.inr (by simp only [own_lock, hy, ite_true, hf'])
      · simpa only [own_lock, hy, ite_false, hrec, he] using hl
  have hist : FGRowRecordHistory (S.record nd) := by
    rw [hrec]; exact d7r_history_holder trace seat hx i
  have hduty := ordinary_obsDutyState_tick E rho htick
  have coverage := rowPermission_covered_obs S Ef cfg E rho _
    (ordinaryFGExecutionObs_laws E rho) client O.height T hT
    (fun a => namedEntry (D.heightPair a)) wireLaws hs hheight i r seat hx htick C
    (by rw [hduty, hclock]; exact ⟨(hsrc nd).trans hC, hol⟩)
    (by rw [hduty, hclock]; exact hist)
    (by
      intro b hb
      obtain ⟨k, q, a, hk, ha, hn⟩ := prior i x hx b hb
      exact ⟨k, q, a, hk, (ordinary_obsHonestRowAt_iff S E rho T k x q a).2 ha, hn⟩)
    hawake (enabled r)
  obtain ⟨j, q, a, hqr, ha, hn⟩ := ordinary_rowPermission_covered S E rho T
    (fun a => namedEntry (D.heightPair a)) x i r _ coverage
  obtain ⟨u, hd, hc⟩ := complete j x q a ha
  have hn' : namedEntry u.height_pair = some ((O.height C).h, (O.height C).T_h.root) := by
    rwa [D.decode_height a u hd] at hn
  have hp : u.height_pair = .vote (O.height C).h (O.height C).T_h.root false := by
    cases hu : u.height_pair with
    | empty => rw [hu] at hn'; cases hn'
    | vote y U timeout =>
      rw [hu] at hn'
      have heq : (y, U) = ((O.height C).h, (O.height C).T_h.root) := Option.some.inj hn'
      cases heq
      let Λ := S.record (V2.D.Run.stateBefore E rho j x)
      let duty := P.clock (V2.D.Run.stateBefore E rho j x) (T.action q)
      obtain ⟨g, B, tm, hpair, hrow, _, _, _⟩ :=
        createRowOnce_released Ef cfg Λ u.signer (S.inputs duty).1 (S.inputs duty).2
          (emission j x q a u ha hd)
      have hhp := congrArg Row.height_pair hrow
      rw [hu] at hhp
      cases hhp
      rw [height_pair_vote_fields hpair] at hpair
      obtain ⟨ht, hn, hl, _⟩ := records j x hx (O.height C).h hhigh
      have choice := high_record_target_choice_core Λ.toRecord (O.height C).h
        (O.height C).T_h.root (finality_pair Λ.toRecord (S.inputs duty).2)
        (by simpa only [he] using ht) hn (by simpa only [he] using hl)
        (by
          intro fp hf hfy
          have hfroot := finality j x (T.action q) Λ.toRecord fp hx hf (hfy ▸ hhigh)
          simpa only [hfy, he] using hfroot)
      rw [choice] at hpair
      cases hpair
      rfl
  exact ⟨j, q, a, hqr, ha, hc, (D.decode_height a u hd).trans hp⟩

include hentry records finality prior hsrc hheight J client trace emission complete
  wireLaws hT hs enabled in
/-- At the first high action, the strict old-row cap rules out a prior target. -/
theorem high_target_first_row_holder (seat : Fin n)
    (hx : safetyHolder S rho seat ∈ rho.honest) (r : Nat) (C : FGBlock (Fin n))
    (hsource : actionSourceFG R E rho T (safetyHolder S rho seat) r = some (some C))
    (hhigh : high R O pt.reset C)
    (hawake : E.awake (safetyHolder S rho seat) (T.action r) = true)
    (hbefore : ∀ j q a h, q < r → HonestRowAt S E rho T j (safetyHolder S rho seat) q a →
      historyRowHeight S D a = some h → h < (O.height C).h) :
    ∃ j a, HonestRowAt S E rho T j (safetyHolder S rho seat) r a ∧
      RowComplete S rho D.signer valid (safetyHolder S rho seat) a ∧
      D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false := by
  obtain ⟨j, q, a, hqr, ha, hc, hp⟩ := high_target_row_covered_holder entry hentry records
    finality prior hsrc hheight J client trace emission complete wireLaws hT hs enabled
    seat hx r C hsource hhigh hawake
  have hq : q = r := by
    by_contra hne
    have hheight : historyRowHeight S D a = some (O.height C).h :=
      congrArg (fun pair : NamedHeightPair =>
        match pair with | .empty => none | .vote h _ _ => some h) hp
    have hlt := hbefore j q a _ (lt_of_le_of_ne hqr hne) ha hheight
    exact (Nat.lt_irrefl _ hlt).elim
  subst q
  exact ⟨j, a, ha, hc, hp⟩

include hentry records finality prior hsrc hheight J client trace emission complete
  wireLaws hT hs enabled in
/-- A nonempty honest seat quorum supplies total rows and receipts at every honest node. -/
theorem high_target_quorum_covered_holder
    (Q : Finset (Fin n)) (hQH : Q ⊆ FGHonestSeats S rho)
    (hne : Q.Nonempty) (hQ : Ef.IsQuorum Q)
    (blockWireRows : P.State → List Wire) (deltaF : Time) (hdeltaF : 0 ≤ deltaF)
    (receipt : TRowsReceipt R S E rho T blockWireRows deltaF)
    (awake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake x t = true)
    (r : Nat) (C : FGBlock (Fin n)) (hhigh : high R O pt.reset C)
    (hsource : ∀ i ∈ Q, actionSourceFG R E rho T (safetyHolder S rho i) r = some (some C))
    (hGST : E.t_GST ≤ T.action r) (hhor : T.action r + deltaF ≤ rho.horizon) :
    Ef.IsQuorum Q ∧ ∃ rows : Fin n → Wire, ∀ i ∈ Q, ∃ j rSent,
      rSent ≤ r ∧ HonestRowAt S E rho T j (safetyHolder S rho i) rSent (rows i) ∧
      RowComplete S rho D.signer valid (safetyHolder S rho i) (rows i) ∧
      D.signer (rows i) = some i ∧
      D.heightPair (rows i) = .vote (O.height C).h (O.height C).T_h.root false ∧
      ∀ x ∈ rho.honest, HeldBefore R E rho blockWireRows x (rows i)
        (max (T.action rSent) E.t_GST + deltaF) := by
  classical
  refine ⟨hQ, ?_⟩
  have haction : T.action r ≤ rho.horizon := by linarith
  have forSeat : ∀ i ∈ Q, ∃ a, ∃ j rSent,
      rSent ≤ r ∧ HonestRowAt S E rho T j (safetyHolder S rho i) rSent a ∧
      RowComplete S rho D.signer valid (safetyHolder S rho i) a ∧ D.signer a = some i ∧
      D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false ∧
      ∀ x ∈ rho.honest, HeldBefore R E rho blockWireRows x a
        (max (T.action rSent) E.t_GST + deltaF) := by
    intro i hi
    have hx : safetyHolder S rho i ∈ rho.honest := by
      simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and]
        using hQH hi
    obtain ⟨j, q, a, hr, ha, hc, hp⟩ := high_target_row_covered_holder entry hentry records
      finality prior hsrc hheight J client trace emission complete wireLaws hT hs enabled
      i hx r C (hsource i hi) hhigh (awake _ hx _ hGST haction)
    have hauth : D.signer a = some i := by
      obtain ⟨k, hk, hki⟩ := hc.2
      exact hk.trans (congrArg some (client.holder_inj hki))
    have hmono : T.action q ≤ T.action r := by
      have hmul : ((q * T.roundSlots : Nat) : Time) ≤
          ((r * T.roundSlots : Nat) : Time) := by
        exact_mod_cast Nat.mul_le_mul_right T.roundSlots hr
      rw [hT.action_eq, hT.action_eq, hT.gate_eq, hT.gate_eq,
        hT.proposal_eq, hT.proposal_eq]
      have := hT.delta_pos
      nlinarith
    have hdeadline : max (T.action q) E.t_GST + deltaF ≤ rho.horizon := by
      have := max_le hmono hGST
      linarith
    exact ⟨a, j, q, hr, ha, hc, hauth, hp, receipt j _ q a ha hdeadline⟩
  obtain ⟨k, hk⟩ := hne
  obtain ⟨fallback, _⟩ := forSeat k hk
  have total : ∀ i : Fin n, ∃ a, i ∈ Q → ∃ j rSent,
      rSent ≤ r ∧ HonestRowAt S E rho T j (safetyHolder S rho i) rSent a ∧
      RowComplete S rho D.signer valid (safetyHolder S rho i) a ∧ D.signer a = some i ∧
      D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false ∧
      ∀ x ∈ rho.honest, HeldBefore R E rho blockWireRows x a
        (max (T.action rSent) E.t_GST + deltaF) := by
    intro i
    by_cases hi : i ∈ Q
    · obtain ⟨a, ha⟩ := forSeat i hi
      exact ⟨a, fun _ => ha⟩
    · exact ⟨fallback, fun h => (hi h).elim⟩
  choose rows hrows using total
  exact ⟨rows, hrows⟩

end AvailableChain.FGCompose
end
