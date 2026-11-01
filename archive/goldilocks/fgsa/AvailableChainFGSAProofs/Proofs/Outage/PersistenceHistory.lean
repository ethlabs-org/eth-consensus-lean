module
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceDefs
public import AvailableChainFGSAProofs.Proofs.Shared.Roots

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Blueprint 03 §8.3; O-INDUCT plan §6 step 2. Class (iii).
DC: INTENTIONAL; a row before the successor of a delivery was emitted
strictly before that delivery, including rows at the same time. -/
theorem outage_row_before_delivery {i : Nat} {x y : V} {o : Obj p} {t : Time}
    (hdel : rho.events[i]? = some (.deliver x o t)) {r : Nat} {a : RowWire p.n}
    (ha : HonestRowBefore p c E rho (i + 1) y r a) :
    HonestRowBefore p c E rho i y r a := by
  obtain ⟨k, hk, hrow⟩ := ha
  refine ⟨k, ?_, hrow⟩
  have hne : k ≠ i := by
    rintro rfl
    have ht := hrow.2.1
    rw [hdel] at ht
    cases ht
  omega

/-- ROOT-DIGEST W2b. Blueprint 03 §8.3; O-INDUCT plan §6 step 3. Class (iii).
DC: INTENTIONAL; the exact name identifies the source entry by its root.
The source history is the induction hypothesis, not a certificate premise. -/
theorem outage_named_of_source_history (hroots : NamedRootCollisionFree p c E rho) {B : Block} {β
    : FGBlock (Fin p.n)} {i : Nat}
    (hβ : eraseFG β = B) (hist : OutageSourceHistory p c E rho B i)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C)) :
    OutageNamedHistory p c E rho β i := by
  constructor
  intro y r a e ⟨k, hk, ha⟩ he heScope
  obtain ⟨C, G, hC, hname, hTC, _, _, _⟩ := hnamed k y r a _ ha he
  have heC : e = (heightView p C).T_h :=
    rootScope_eq hroots heScope (rootScope_entry (rootScope_source ha.1 hC))
      (congrArg Prod.snd hname)
  have hsource : actionSource p c E rho y r = some (some (eraseFG C)) := by
    change (actionSourceFG p c E rho y r).map (Option.map eraseFG) = _
    rw [hC]
    rfl
  have hCB := hist.history k y r _ hk ha.1 ha.2.1 hsource
  have heB := block_compatible_of_preceq_compatible (eraseFG_preceq (heC ▸ hTC)) hCB
  rcases Bool.or_eq_true_iff.mp heB with h | h
  · exact Or.inl (eraseFG_preceq_iff.mp (hβ ▸ h))
  · exact Or.inr (eraseFG_preceq_iff.mp (hβ ▸ h))

/-- ROOT-DIGEST W2b. Blueprint 03 §8.3; O-INDUCT plan §6 steps 2–3. Class (iii).
DC: INTENTIONAL; a newly disclosed honest QC row uses the old source
history. This lemma does not assume successor persistence. -/
theorem outage_disclosed_name_compatible (hroots : NamedRootCollisionFree p c E rho) {i : Nat} {x
    y : V} {o : Obj p} {t : Time}
    (hdel : rho.events[i]? = some (.deliver x o t))
    {B : Block} {β C e : FGBlock (Fin p.n)} {r : Nat} {wire : RowWire p.n}
    {a : Row (Fin p.n)} {h : Nat} (hβ : eraseFG β = B)
    (hist : OutageSourceHistory p c E rho B i)
    (ha : HonestRowBefore p c E rho (i + 1) y r wire)
    (_hdecode : wire.toRow? = some a)
    (hC : actionSourceFG p c E rho y r = some (some C))
    (hname : namedEntry a.height_pair = some ((heightView p C).h, (heightView p C).T_h.root))
    (hTC : FGBlock.Preceq (heightView p C).T_h C)
    (he : namedEntry a.height_pair = some (h, e.root))
    (heScope : RootBlockInRun p c E rho (eraseFG e)) :
    HonestRowBefore p c E rho i y r wire ∧
      (FGBlock.Preceq e β ∨ FGBlock.Preceq β e) := by
  have hbefore := outage_row_before_delivery hdel ha
  obtain ⟨k, hk, hrow⟩ := hbefore
  have heC : e = (heightView p C).T_h := rootScope_eq hroots heScope
    (rootScope_entry (rootScope_source hrow.1 hC))
    (congrArg Prod.snd (Option.some.inj (he.symm.trans hname)))
  have hsource : actionSource p c E rho y r = some (some (eraseFG C)) := by
    change (actionSourceFG p c E rho y r).map (Option.map eraseFG) = _
    rw [hC]
    rfl
  have hcompat := block_compatible_of_preceq_compatible (eraseFG_preceq (heC ▸ hTC))
    (hist.history k y r _ hk hrow.1 hrow.2.1 hsource)
  refine ⟨⟨k, hk, hrow⟩, ?_⟩
  rcases Bool.or_eq_true_iff.mp hcompat with h | h
  · exact Or.inl (eraseFG_preceq_iff.mp (hβ ▸ h))
  · exact Or.inr (eraseFG_preceq_iff.mp (hβ ▸ h))

private theorem named_of_matches {pair : NamedHeightPair} {h : Nat} {root : BlockId}
    (hm : pair.matchesEntry h root = true) : namedEntry pair = some (h, root) := by
  cases pair with
  | empty => cases hm
  | vote h' root' tm =>
    obtain ⟨rfl, rfl⟩ := of_decide_eq_true hm
    rfl

/-- ROOT-DIGEST W2b. Blueprint 03 §8.3; O-INDUCT plan §6 steps 2–4. Class (iii).
DC: INTENTIONAL; the selected crossing QC identifies its crossed entry,
not the terminal carrier. INLINE hqc: sourceDiscipline_qcOrigin. -/
theorem outage_disclosed_crossing (hqc : RQCOrigin p c E rho)
    {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hdel : rho.events[i]? = some (.deliver x o t)) (hx : x ∈ rho.honest)
    {B : Block} {β W X : FGBlock (Fin p.n)} (hβ : eraseFG β = B)
    (hist : OutageSourceHistory p c E rho B i)
    (hW : W ∈ (storeAt p c E rho (i + 1) x).fg.TF)
    {m : Nat} (hm : 1 ≤ m) (hlt : m < (heightView p W).h)
    (hX : FGBlock.Preceq X W) (hheight : (heightView p X).h = m)
    {Q : Finset (Fin p.n)} {rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)}
    (hQ : p.E.IsQuorum Q)
    (hr : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
      (rows k).2.signer = k ∧ (rows k).2.height_pair.matchesEntry m X.root = true)
    (hroots : NamedRootCollisionFree p c E rho) :
    (∃ k ∈ Q, ∃ y r, ∃ wire : RowWire p.n,
      HonestRowBefore p c E rho i y r wire ∧ wire.toRow? = some (rows k).2) ∧
      (FGBlock.Preceq X β ∨ FGBlock.Preceq β X) := by
  obtain ⟨k, hk, y, r, wire, ha, hd, _, C, G, hC, hn, hTC, _, _, _⟩ :=
    (hqc (i + 1) x W hx hW).1 m X Q rows hm hlt hX hheight hQ hr
  have he : namedEntry (rows k).2.height_pair = some ((heightView p X).h, X.root) := by
    rw [hheight]
    exact named_of_matches (hr k hk).2.2.2
  obtain ⟨hb, hc⟩ := outage_disclosed_name_compatible (hroots := hroots) hdel hβ hist ha hd hC hn
    hTC he
    (rootScope_ancestor (rootScope_store hx hW) hX)
  exact ⟨⟨k, hk, y, r, wire, hb, hd⟩, hc⟩

/-- ROOT-DIGEST W2b. Blueprint 03 §8.3; O-INDUCT plan §6 steps 2–3. Class (iii).
DC: INTENTIONAL; a newly disclosed target QC uses an old honest action
source. INLINE hqc: sourceDiscipline_qcOrigin. -/
theorem outage_disclosed_justification (hqc : RQCOrigin p c E rho)
    {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hdel : rho.events[i]? = some (.deliver x o t)) (hx : x ∈ rho.honest)
    {B : Block} {β W : FGBlock (Fin p.n)} (hβ : eraseFG β = B)
    (hist : OutageSourceHistory p c E rho B i)
    (hW : W ∈ (storeAt p c E rho (i + 1) x).fg.TF)
    (hnz : (heightView p W).h_j ≠ 0)
    {Q : Finset (Fin p.n)} {rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)}
    (hQ : p.E.IsQuorum Q)
    (hr : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
      (rows k).2.signer = k ∧
      (rows k).2.height_pair = .vote (heightView p W).h_j (heightView p W).J.root false)
    (hroots : NamedRootCollisionFree p c E rho) :
    (FGBlock.Preceq (heightView p W).J β ∨ FGBlock.Preceq β (heightView p W).J) := by
  obtain ⟨k, hk, y, r, wire, ha, hd, _, C, G, hC, hn, hTC, _, _, _⟩ :=
    (hqc (i + 1) x W hx hW).2.1 Q rows hnz hQ hr
  have he : namedEntry (rows k).2.height_pair =
      some ((heightView p W).h_j, (heightView p W).J.root) := by
    rw [(hr k hk).2.2.2]
    rfl
  exact (outage_disclosed_name_compatible (hroots := hroots) hdel hβ hist ha hd hC hn hTC he
    (rootScope_justified (rootScope_store hx hW))).2

/-- ROOT-DIGEST W2b. Blueprint 03 §8.3; O-INDUCT plan §6 step 5. Class (iii).
DC: INTENTIONAL; a retained finalization uses the target QC of its prior
justification. The current J may be different. INLINE hqc:
sourceDiscipline_qcOrigin, with window_final_birth in its producer. -/
theorem outage_disclosed_finalization (hqc : RQCOrigin p c E rho)
    {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hdel : rho.events[i]? = some (.deliver x o t)) (hx : x ∈ rho.honest)
    {B : Block} {β W : FGBlock (Fin p.n)} (hβ : eraseFG β = B)
    (hist : OutageSourceHistory p c E rho B i)
    (hW : W ∈ (storeAt p c E rho (i + 1) x).fg.TF)
    (hne : (finalityView p W).F ≠ .genesis)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∃ carrier, FGBlock.Preceq carrier W ∧
      (heightView p carrier).J = (finalityView p W).F ∧
      (heightView p carrier).h_j = (finalityView p W).h_F ∧
      (FGBlock.Preceq (finalityView p W).F β ∨ FGBlock.Preceq β (finalityView p W).F) := by
  obtain ⟨carrier, hp, hJ, hh, Q, rows, _, hr, k, hk,
    y, r, wire, ha, hd, _, C, G, hC, hn, hTC, _, _, _⟩ :=
    (hqc (i + 1) x W hx hW).2.2 hne
  have he : namedEntry (rows k).2.height_pair =
      some ((heightView p carrier).h_j, (heightView p carrier).J.root) := by
    rw [(hr k hk).2.2.2]
    rfl
  have hc := (outage_disclosed_name_compatible (hroots := hroots) hdel hβ hist ha hd hC hn hTC he
    (rootScope_justified (rootScope_ancestor (rootScope_store hx hW) hp))).2
  rw [hJ] at hc
  exact ⟨carrier, hp, hJ, hh, hc⟩

omit [DecidableEq V] in
/-- O-INDUCT plan §2, §3.1. Class (iii). DC: INTENTIONAL;
every tick after the all-ticks cut has a strictly later time. -/
theorem outage_tick_after_cut (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V}
    {d t : Time} (hi : rho.events[i]? = some (.tick x t))
    (hI : afterTicksIdx rho d ≤ i) : d < t := by
  by_contra hn
  have htd : t ≤ d := le_of_not_gt hn
  have hdown : ∀ e f : V2.Event V (Obj p), e.key ≤ f.key →
      cutPred (P := fgsa p c) d f = true → cutPred (P := fgsa p c) d e = true := by
    intro e f hef hf
    exact decide_eq_true (hef.trans (of_decide_eq_true hf))
  have hf := V2.D.Engine.filter_false_of_index_ge hs (cutPred (P := fgsa p c) d) hdown hI hi
  have ht : cutPred (P := fgsa p c) d (.tick x t : V2.Event V (Obj p)) = true := by
    apply decide_eq_true
    exact Prod.Lex.toLex_le_toLex.mpr
      (htd.lt_or_eq.imp id (fun h => ⟨h, le_rfl⟩))
  have htf : true = false := ht.symm.trans hf
  cases htf

/-- O-INDUCT plan §2, §6. Class (iii). DC: INTENTIONAL;
a delivery does not add an action source to the event history. -/
theorem outage_source_history_delivery {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hi : rho.events[i]? = some (.deliver x o t)) {B : Block}
    (hist : OutageSourceHistory p c E rho B i) : OutageSourceHistory p c E rho B (i + 1) := by
  constructor
  intro k y r C hk hy htick hsource
  have hne : k ≠ i := by
    rintro rfl
    rw [hi] at htick
    cases htick
  exact hist.history k y r C (by omega) hy htick hsource

end AvailableChain.FGSA.Run
end
