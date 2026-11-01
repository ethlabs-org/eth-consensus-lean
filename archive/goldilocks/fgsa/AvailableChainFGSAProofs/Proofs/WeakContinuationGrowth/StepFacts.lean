module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Epoch
public import AvailableChainFGSAProofs.Proofs.Shared.Roots
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.ReceiptOrigins

namespace AvailableChain.FGSA
open AvailableChain.SimplexFG
/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private def wcg_step_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem wcg_step_admitBlock_eq : @admitBlock = @wcg_step_admitBlock := rfl

end AvailableChain.FGSA

public section

/-! WC plan §6.5; DC original saved-result and certificate events persist in each finite read. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

private theorem wcg_step_storeAt (i : Nat) (x : V) :
    storeAt p c E rho i x = (rho.stateBefore E i x).st := rfl

/-- WC plan §6.5; DC receipt replay: retain the original trigger and acceptance index. -/
private theorem wcg_step_receiptOrigins (i : Nat) (x : V) :
    WCReceiptOrigins p c E rho i x (storeAt p c E rho i x) :=
  wcg_receiptOrigins E rho i x

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private def wcg_step_savedPairs (st : State p.n) : List (Slot × Block) :=
  st.base.genuine.filterMap (fun row => row.2.map (fun B => (row.1, B)))

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem wcg_step_savedPairs_mem (st : State p.n) (s : Slot) (B : Block) :
    (s, B) ∈ wcg_step_savedPairs st ↔ (s, some B) ∈ st.base.genuine := by
  constructor
  · intro h
    obtain ⟨row, hr, hb⟩ := List.mem_filterMap.mp h
    obtain ⟨C, hc, he⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hrow : row = (row.1, some C) := Prod.ext rfl hc
    rwa [hrow] at hr
  · intro h
    exact List.mem_filterMap.mpr ⟨(s, some B), h, rfl⟩

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem wcg_step_savedPairs_reconcile (st : State p.n) :
    wcg_step_savedPairs (reconcile st) ⊆ wcg_step_savedPairs st := by
  rintro ⟨s, B⟩ hm
  rw [wcg_step_savedPairs_mem, reconcile_genuine] at hm
  obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
  have hk := congrArg Prod.fst he
  have hb := (Option.filter_eq_some_iff.mp (congrArg Prod.snd he)).1
  rw [wcg_step_savedPairs_mem]
  have hrow : row = (s, some B) := Prod.ext hk hb
  rwa [hrow] at hr

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem wcg_step_savedPairs_admitRows (rows : List (RowWire p.n)) (st : State p.n) :
    wcg_step_savedPairs (rows.foldl (admitRow p) st) = wcg_step_savedPairs st := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    rw [List.foldl_cons, ih]
    rcases admitRow_eq p st a with h | h
    · rw [h]
    · rw [h]
      rfl

-- WC plan §6.5; DC handler order. The upstream Schedule helper is private.
/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem wcg_step_proposal_genuine (q : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block)
    (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q st o b raw).genuine = st.genuine := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> unfold GridCO.admitProposal <;> dsimp only <;> split
  all_goals first | rfl | exact (foldVotes_fields q raw _).2.2.2.2.1

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem wcg_step_savedPairs_process (st : State p.n) (o : Wire p.n) :
    wcg_step_savedPairs (process p st o) ⊆ wcg_step_savedPairs st := by
  change wcg_step_savedPairs (match o.decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s N) => admitBlock p st s N
    | none => st) ⊆ wcg_step_savedPairs st
  cases o.decode with
  | none => exact List.Subset.refl _
  | some a =>
    cases a <;> dsimp only
    case vote s i b =>
      unfold wcg_step_savedPairs
      rw [admitHead_genuine]
    case row i body =>
      rcases admitRow_eq p st ⟨o.auth, body⟩ with h | h <;> rw [h]
      exact List.Subset.refl _
    case block s N =>
      cases hn : namedParentHeld st N with
      | false => rw [admitBlock_refused p st s N (Or.inl hn)]
      | true =>
        cases hp : parentFG st N.erase with
        | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]
        | some P =>
          cases ha : blockAccepted p st s N P with
          | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
          | true =>
            rw [wcg_step_admitBlock_eq]
            unfold wcg_step_admitBlock
            simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
            rw [hp]
            dsimp only
            rw [ha, ite_eq_left rfl, wcg_step_savedPairs_admitRows]
            split
            · unfold wcg_step_savedPairs
              dsimp only
              rw [wcg_step_proposal_genuine]
            · apply List.Subset.trans (wcg_step_savedPairs_reconcile _)
              unfold wcg_step_savedPairs
              dsimp only
              rw [wcg_step_proposal_genuine]

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem wcg_step_savedPairs_clock (st : State p.n) (t : Time) (pair : Slot × Block)
    (hm : pair ∈ wcg_step_savedPairs (clock p st t)) :
    pair ∈ wcg_step_savedPairs st ∨
      (t = SA.gateTime p.toParams pair.1 ∧
       joinedNow p (clockPre p st t) = true ∧
       SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p st t).fg.F)
         (actView (clockPre p st t)) pair.1 = some pair.2) := by
  change pair ∈ wcg_step_savedPairs (if isGateTime p t then
    gateStep p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    else clockPre p st t) at hm
  have hpre : wcg_step_savedPairs (clockPre p st t) = wcg_step_savedPairs st := by
    unfold wcg_step_savedPairs
    rw [clockPre_genuine]
  split at hm
  · rename_i ht
    let s := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    let pre := clockPre p st t
    have htime : t = SA.gateTime p.toParams s :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).2
    cases hs : GridCO.savedGenuine pre.base s with
    | some saved =>
      rw [gateStep_saved p pre s (by rw [hs]; rfl)] at hm
      unfold wcg_step_savedPairs at hm
      rw [normalizeS_fields] at hm
      exact Or.inl (hpre ▸ hm)
    | none =>
      by_cases hJ : joinedNow p pre = true
      · have hg : (gateStep p pre s).base.genuine = pre.base.genuine ++
            [(s, SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s)] := by
          unfold gateStep
          rw [normalizeS_fields]
          simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false, hJ,
            Bool.not_true]
          exact saGate_genuine p.toParams (eraseFG pre.fg.F) (actView pre) s hs
        rcases pair with ⟨v, B⟩
        rw [wcg_step_savedPairs_mem, hg, List.mem_append] at hm
        rcases hm with hm | hm
        · exact Or.inl (hpre ▸ (wcg_step_savedPairs_mem pre v B).mpr hm)
        · obtain ⟨rfl, hC⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
          exact Or.inr ⟨htime, hJ, hC.symm⟩
      · have hg : (gateStep p pre s).base.genuine = pre.base.genuine ++ [(s, none)] := by
          unfold gateStep
          rw [normalizeS_fields]
          simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false,
            hJ]
          rfl
        rcases pair with ⟨v, B⟩
        rw [wcg_step_savedPairs_mem, hg, List.mem_append] at hm
        rcases hm with hm | hm
        · exact Or.inl (hpre ▸ (wcg_step_savedPairs_mem pre v B).mpr hm)
        · have he := congrArg Prod.snd (List.mem_singleton.mp hm)
          cases he
  · exact Or.inl (hpre ▸ hm)

/-- WC plan §6.5; DC actual saved origin: a retained value still has its original gate result. -/
private theorem wcg_step_savedOrigin (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) (s : Slot) (B : Block)
    (hb : GridCO.savedGenuine (storeAt p c E rho i x).base s = some (some B)) :
    ∃ j < i, V2.D.restartFree rho x j i ∧ enabledGateAt p c E rho j x s ∧
      gateResultAt p c E rho j = some (some B) := by
  have origin : ∀ n, (s, B) ∈ wcg_step_savedPairs (storeAt p c E rho n x) →
      ∃ j < n, V2.D.restartFree rho x j n ∧ IsGateTick p c rho j x s ∧
        joinedNow p (clockPre p (storeAt p c E rho j x)
          (SA.gateTime p.toParams s)) = true ∧
        SA.Root.confirmationFrom p.toParams
          (eraseFG (clockPre p (storeAt p c E rho j x)
            (SA.gateTime p.toParams s)).fg.F)
          (actView (clockPre p (storeAt p c E rho j x)
            (SA.gateTime p.toParams s))) s = some B := by
    intro n hm
    induction n with
    | zero => exact (List.not_mem_nil hm).elim
    | succ n ih =>
      have carry (hn : ∀ t, rho.events[n]? ≠ some (.restart x t))
          (hm : (s, B) ∈ wcg_step_savedPairs (storeAt p c E rho n x)) :
          ∃ j < n + 1, V2.D.restartFree rho x j (n + 1) ∧ IsGateTick p c rho j x s ∧
            joinedNow p (clockPre p (storeAt p c E rho j x)
              (SA.gateTime p.toParams s)) = true ∧
            SA.Root.confirmationFrom p.toParams
              (eraseFG (clockPre p (storeAt p c E rho j x)
                (SA.gateTime p.toParams s)).fg.F)
              (actView (clockPre p (storeAt p c E rho j x)
                (SA.gateTime p.toParams s))) s = some B := by
        obtain ⟨j, hj, hRF, ht, hJ, hC⟩ := ih hm
        refine ⟨j, Nat.lt_succ_of_lt hj, ?_, ht, hJ, hC⟩
        intro k t hjk hkn
        rcases (Nat.le_of_lt_succ hkn).lt_or_eq with hk | rfl
        · exact hRF k t hjk hk
        · exact hn t
      cases he : rho.events[n]? with
      | none =>
        apply carry (by intro t; rw [he]; simp)
        simpa [wcg_step_storeAt, V2.D.Run.stateBefore, List.take_add_one, he] using hm
      | some e =>
        have hp := V2.D.Run.stateBefore_succ E rho he
        unfold storeAt at hm
        rw [hp] at hm
        by_cases hx : e.node = x
        · cases e with
          | restart v t =>
            change v = x at hx
            subst v
            simp only [V2.D.World.step, Function.update_self] at hm
            change (s, B) ∈ wcg_step_savedPairs (acRestart p (storeAt p c E rho n x) t) at hm
            unfold wcg_step_savedPairs at hm
            rw [acRestart_genuine] at hm
            simp only [List.filterMap_nil] at hm
            exact (List.not_mem_nil hm).elim
          | deliver v o t =>
            change v = x at hx
            subst v
            apply carry (by intro u; rw [he]; simp)
            simp only [V2.D.World.step, Function.update_self] at hm
            exact wcg_step_savedPairs_process _ (toWire p o) hm
          | tick v t =>
            change v = x at hx
            subst v
            simp only [V2.D.World.step, Function.update_self] at hm
            rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho n x) x t] at hm
            rcases wcg_step_savedPairs_clock _ t (s, B) hm with hm | ⟨ht, hJ, hC⟩
            · exact carry (by intro u; rw [he]; simp) hm
            · subst t
              refine ⟨n, Nat.lt_succ_self n, ?_, he, hJ, hC⟩
              intro k t hnk hkn heq
              have hk : k = n := by omega
              subst k
              rw [he] at heq
              cases heq
        · apply carry (by
            intro t ht
            exact hx (congrArg V2.Event.node (Option.some.inj (he.symm.trans ht))))
          rwa [V2.D.World.step_apply_of_node_ne E rho _ hx] at hm
  obtain ⟨row, hr, he⟩ := Option.map_eq_some_iff.mp hb
  have hk : row.1 = s := by simpa using List.find?_some hr
  have hm : (s, B) ∈ wcg_step_savedPairs (storeAt p c E rho i x) := by
    rw [wcg_step_savedPairs_mem]
    simpa only [← hk, ← he] using List.mem_of_find?_eq_some hr
  obtain ⟨j, hj, hRF, ht, hJ, hC⟩ := origin i hm
  have hraw : gateResultAt p c E rho j = some (some B) := by
    rw [gateResultAt_eq_gateResult p c E rho hs ht,
      gateResult_eq_saved p c E rho hs ht]
    have hG := fgsa_gate_saved_result E rho hs ht (by rwa [clockPre_joined] at hJ)
    rw [clockPre_fg] at hC
    exact hG.trans (congrArg some hC)
  exact ⟨j, hj, hRF, wcg_gate_enabled_of_result hs ht hraw, hraw⟩


/-- Finite seed facts follow from continuation producers at any index.
No seed, suffix invariant, one-third cap, or FaultX premise is needed. -/
theorem wcg_finiteFacts :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hroots : NamedReceiptRootCollisionFree p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → enabledGateAt p c E rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, V2.D.restartFree rho x j i ∧
        enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline),
  ∀ n, WCFiniteFacts p c E rho n := by
  intro hvalid hroots hstrat hnoslash hemitted hlease hfast hdeadlines n
  refine ⟨fun x _ => cstoreInv_stateBefore E rho n x,
    fun x _ => nestOK_stateBefore E rho n x,
    fun x _ => metaInv_stateBefore E rho n x,
    fun x _ => wcg_step_receiptOrigins n x,
    fun x _ row hr => by
      obtain ⟨j, hj, s, B, ht, hp, hB, hrest⟩ := hlease n x row hr
      exact ⟨j, hj, s, B, wcg_gate_enabled_of_result hvalid.toScheduleWellFormed ht hB,
        hp, hB, hrest⟩,
    fun x _ => hdeadlines n x,
    fun x _ => hfast n x,
    fun x _ s C hc => wcg_step_savedOrigin hvalid.toScheduleWellFormed n x s C hc,
      ?_, ?_⟩
  · intro x hx W hW X hX hne
    obtain ⟨y, r, wire, ⟨j, hj, hrow⟩, hname⟩ := hstrat n x W hx hW X hX hne
    obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ := hemitted j y r wire _ hrow hname
    have hXK : X = (derive p.E p.cfg K).T_h := rootScope_eq (hroots.toNamedRootCollisionFree E rho)
      (rootScope_ancestor (rootScope_store hx hW) (certified_preceq hX))
      (rootScope_ancestor (rootScope_source hrow.1 hK) hentry) (congrArg Prod.snd hpair)
    exact ⟨j, y, r, wire, K, B, hj, hrow, hname, hK, hXK ▸ hentry, hB, hKB⟩
  · intro j k x r r' a b u v _ _ ha hb hu hv
    exact hnoslash x ha.1 a b ⟨j, p.actionTime r, ha.2⟩ ⟨k, p.actionTime r', hb.2⟩ u v hu hv


variable [Fintype V]

/-- WC plan §6.5; DC each event's finite facts retain actual origins and deadlines. -/
theorem wcg_finiteStep (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.RestartsAtWakes E rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedReceiptRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
  (_hmono : RMonoAll p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNextEpoch p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → enabledGateAt p c E rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, V2.D.restartFree rho x j i ∧
        enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → ∀ e, rho.events[i]? = some e →
      WCFiniteFacts p c E rho (i + 1) := by
  intro hvalid _hlinked _hcstar _hnr _hdelta hroots _hsync _hdeltaF _hfaultQ
    _haccountable _hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel _hqc hstrat hnoslash hemitted _htargets hlease hfast hdeadlines
    _hheldRows _hscopeRows _hfinalHead _hs i _hi _hilen _inv _e _he
  let n := i + 1
  refine ⟨fun x _ => cstoreInv_stateBefore E rho n x,
    fun x _ => nestOK_stateBefore E rho n x,
    fun x _ => metaInv_stateBefore E rho n x,
    fun x _ => wcg_step_receiptOrigins n x,
    fun x _ row hr => by
      obtain ⟨j, hj, s, B, ht, hp, hB, hrest⟩ := hlease n x row hr
      exact ⟨j, hj, s, B, wcg_gate_enabled_of_result hvalid.toScheduleWellFormed ht hB,
        hp, hB, hrest⟩,
    fun x _ => hdeadlines n x,
    fun x _ => hfast n x,
    fun x _ s C hc => wcg_step_savedOrigin hvalid.toScheduleWellFormed n x s C hc, ?_, ?_⟩
  · intro x hx W hW X hX hne
    obtain ⟨y, r, wire, ⟨j, hj, hrow⟩, hname⟩ := hstrat n x W hx hW X hX hne
    obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ := hemitted j y r wire _ hrow hname
    have hXK : X = (derive p.E p.cfg K).T_h := rootScope_eq (hroots.toNamedRootCollisionFree E rho)
      (rootScope_ancestor (rootScope_store hx hW) (certified_preceq hX))
      (rootScope_ancestor (rootScope_source hrow.1 hK) hentry) (congrArg Prod.snd hpair)
    exact ⟨j, y, r, wire, K, B, hj, hrow, hname, hK, hXK ▸ hentry, hB, hKB⟩
  · intro j k x r r' a b u v _ _ ha hb hu hv
    exact hnoslash x ha.1 a b ⟨j, p.actionTime r, ha.2⟩ ⟨k, p.actionTime r', hb.2⟩ u v hu hv

end AvailableChain.FGSA.Run
end
