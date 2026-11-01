module
public import AvailableChainFGSAProofs.Proofs.Finality.TailFrame
public import AvailableChainFGSAProofs.Proofs.Finality.TailRows
public import AvailableChainFGSAProofs.Proofs.Finality.TailRetention

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-! ### Pure split of a covering key -/

variable (p : Params)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1993–1996, plan §6. A finality certificate at the latest justified height
is that justification: both are entries of one height on one chain.
DC: SAME entry geometry; INTENTIONAL: W certificate heights. -/
theorem ktail_F_eq_J_of_heights (B : FGBlock (Fin p.n))
    (h : (finalityView p B).h_F = (heightView p B).h_j) :
    (finalityView p B).F = (heightView p B).J := by
  have cl := fgCertificateLaws p
  have jl := fgJustificationLaws p
  have hFJ := cl.finalized_preceq_justified B
  by_cases hz : (heightView p B).h_j = 0
  · have hJ := cl.justified_zero B hz
    rw [hJ] at hFJ ⊢
    exact preceq_genesis.mp hFJ
  · have hFz : (finalityView p B).h_F ≠ 0 := by rw [h]; exact hz
    obtain ⟨C, -, hCJ, hCj⟩ := KitFG.provenance_finality_of_certificate p.E
      (heightView p) (finalityView p) cl B hFz
    have hCz : (heightView p C).h_j ≠ 0 := by rw [hCj]; exact hFz
    have hFh := jl.J_height C hCz
    have hFe := jl.J_entry C
    rw [hCJ, hCj] at hFh
    rw [hCJ] at hFe
    have hJh := jl.J_height B hz
    have hJe := jl.J_entry B
    have hplat := cl.height.entry_plateau hFJ (hFh.trans (h.trans hJh.symm))
    rw [hFe, hJe] at hplat
    exact hplat

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1993–1996 (FT-Tail-W: "a common pending (h_K, K), K ⪰ U and h_K ≤ e, or an
already-finalized covering entry"), plan §1 step 3. The cover of the witness splits into
the finalized arm and the pending arm. In the pending arm the latest key is above
finality, is not at height zero, and is at least as high as U.
DC: INTENTIONAL: W keeps the pending key; no equality K = U or h_K = e. -/
theorem ktail_witness_split (Q U : FGBlock (Fin p.n))
    (hcover : FGBlock.Preceq U (heightView p Q).J ∨ FGBlock.Preceq U (finalityView p Q).F) :
    FGBlock.Preceq U (finalityView p Q).F ∨
      (FGBlock.Preceq U (heightView p Q).J ∧ ¬ FGBlock.Preceq U (finalityView p Q).F ∧
        (finalityView p Q).h_F < (heightView p Q).h_j ∧
        (heightView p U).h ≤ (heightView p Q).h_j) := by
  by_cases hF : FGBlock.Preceq U (finalityView p Q).F
  · exact Or.inl hF
  · have hJ := hcover.resolve_right hF
    have hle := (fgCertificateLaws p).heights_ordered Q
    have hlt : (finalityView p Q).h_F < (heightView p Q).h_j := by
      rcases Nat.lt_or_ge (finalityView p Q).h_F (heightView p Q).h_j with h | h
      · exact h
      · exfalso
        have heq := ktail_F_eq_J_of_heights p Q (le_antisymm hle h)
        exact hF (heq ▸ hJ)
    have hz : (heightView p Q).h_j ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hlt)
    have hUh := (fgCertificateLaws p).height.h_mono hJ
    rw [(fgJustificationLaws p).J_height Q hz] at hUh
    exact Or.inr ⟨hJ, hF, hlt, hUh⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:2007–2009 (FT-Tail-W: "in the already-finalized case the chain retains and
exposes the covering finalization"). The finalized arm propagates to every descendant.
DC: SAME finality monotonicity. -/
theorem ktail_finalized_propagates (Q X U : FGBlock (Fin p.n)) (hQX : FGBlock.Preceq Q X)
    (hU : FGBlock.Preceq U (finalityView p Q).F) :
    FGBlock.Preceq U (finalityView p X).F :=
  preceq_trans hU ((fgCertificateLaws p).finalized_mono hQX).2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1993–1996 and 1739–1754 (action head on the plateau), plan §1 step 4 and
§6 "mixed receiver states". A head on Q's height plateau keeps Q's latest key. Its own
finality is either below that key (it names the key) or exactly at it, and then it has
finalized the key itself. The two arms can differ between honest heads.
DC: INTENTIONAL: W finality pair; DC carries the same pending pair. -/
theorem ktail_head_dichotomy (Q H : FGBlock (Fin p.n)) (hQH : FGBlock.Preceq Q H)
    (hh : (heightView p H).h = (heightView p Q).h) :
    (heightView p H).J = (heightView p Q).J ∧ (heightView p H).h_j = (heightView p Q).h_j ∧
      ((finalityView p H).h_F < (heightView p Q).h_j ∨
        ((finalityView p H).h_F = (heightView p Q).h_j ∧
          (finalityView p H).F = (heightView p Q).J)) := by
  have hplat := KitFG.justification_eq_on_plateau_of_bridge p.E p.cfg (heightView p)
    (heightView_bridge p) hQH hh.symm
  refine ⟨hplat.1, hplat.2, ?_⟩
  have hle := (fgCertificateLaws p).heights_ordered H
  rw [hplat.2] at hle
  rcases Nat.lt_or_ge (finalityView p H).h_F (heightView p Q).h_j with h | h
  · exact Or.inl h
  · have heq : (finalityView p H).h_F = (heightView p Q).h_j := le_antisymm hle h
    refine Or.inr ⟨heq, ?_⟩
    rw [ktail_F_eq_J_of_heights p H (heq.trans hplat.2.symm), hplat.1]

/-! ### The Tail instances -/

variable {p} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1997–2000, plan §2 "hrecord". At every honest action read of round r+1:
the FF2 guards at the witness key (h_j(Q), J(Q)) and freshness at e+1.
DC: INTENTIONAL: H1 and QC origin; Assembly supplies RQCOrigin and the source names. -/
theorem ktail_tail_record {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hhigh : pt.w.M + 1 ≤ (heightView p ow.Q).h_j) {x : V} (hx : x ∈ rho.honest) :
    ∀ nd, postClock E rho x (p.actionTime (pt.r + 1)) = some nd →
      (nd.record.target (heightView p ow.Q).h_j = none ∨
        nd.record.target (heightView p ow.Q).h_j = some (heightView p ow.Q).J.root) ∧
      nd.record.timeout (heightView p ow.Q).h_j = false ∧
      (nd.record.lock (heightView p ow.Q).h_j = none ∨
        nd.record.lock (heightView p ow.Q).h_j = some (heightView p ow.Q).J.root) ∧
      nd.record.target (ow.e + 1) = none ∧ nd.record.timeout (ow.e + 1) = false ∧
      nd.record.lock (ow.e + 1) = none ∧
      ∀ b ∈ nd.record.sent, ∀ T timeout, b.1 ≠ .vote (ow.e + 1) T timeout := by
  have hs := hT.set.base.valid.toScheduleWellFormed
  have hW := ow.heldQFrom x hx (afterTicksIdx rho (SA.voteTime p.toParams pt.carrier))
    (SA.voteTime p.toParams pt.carrier) le_rfl le_rfl
  exact ktail_record_guards_at_action p c E rho pt.w hT.input.t.h1 hqc hnames hs _ x ow.Q
    hx hW hhigh (ow.e + 1) (pt.r + 1) x hx (fun j r a h hr ha hh =>
      Nat.lt_succ_of_le (ow.rowsThroughOpening j x r a h (Nat.le_of_lt_succ hr) ha hh))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1993–1996, plan §1 step 4 and §6 (mixed receiver states). The actual action
head of every honest node at round r+1 extends Q on its plateau and keeps Q's latest key.
Its finality is below that key, or it has finalized the key itself. When the key is
fresh (h_j(Q) = e) the second arm is impossible: held finality is below e.
The walk batch is an input (K-ROWS hbatch).
DC: INTENTIONAL: plateau head; W finality pair. -/
theorem ktail_action_head_split {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    {x : V} (hx : x ∈ rho.honest) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime (pt.r + 1)) = some nd)
    (raw support : List (GridCO.Wire p.n .root)) (seats : Finset (Fin p.n)) (m : Nat)
    (hhead : FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support)
    (hcount : Gen.Pure.Batch seats.card m)
    (hbatch : WalkBatch p c rho nd.st ((pt.r + 1) * p.R + 1)
      raw support (eraseFG ow.Q) seats m) :
    ∃ H : FGBlock (Fin p.n),
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
      H ∈ nd.st.fg.TF ∧ FGBlock.Preceq ow.Q H ∧
      (heightView p H).h = ow.e + 1 ∧
      (heightView p H).T_h = (heightView p ow.Q).T_h ∧
      (heightView p H).J = (heightView p ow.Q).J ∧
      (heightView p H).h_j = (heightView p ow.Q).h_j ∧
      (finalityView p H).h_F < ow.e ∧
      ((finalityView p H).h_F < (heightView p ow.Q).h_j ∨
        ((finalityView p H).h_F = (heightView p ow.Q).h_j ∧
          (finalityView p H).F = (heightView p ow.Q).J)) := by
  obtain ⟨k, hk, hread, -, -, -, -, hfull, hcompat, hcap⟩ := ktail_action_frame hT ow hx nd hnd
  obtain ⟨-, -, hcut1⟩ := ktail_action_suffix hT hk
  obtain ⟨H, hdec, hH, hQH, hHh, -, -, hT_h⟩ := ktail_plateau_action_head p c E rho (k + 1) x
    (pt.r + 1) (ow.e + 1) ow.Q nd raw support seats m hx hnd hread (fgsa_tWalk E rho) hhead
    hcount hfull hcompat hbatch ow.heightQ hcap
  obtain ⟨hJ, hj, harm⟩ := ktail_head_dichotomy p ow.Q H hQH (hHh.trans ow.heightQ.symm)
  have hfin : (finalityView p H).h_F < ow.e :=
    ow.finalityThroughAction (k + 1) x H hcut1 ⟨hx, by rw [hread]; exact hH⟩
  exact ⟨H, hdec, hH, hQH, hHh, hT_h, hJ, hj, hfin, harm⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1997–2000, plan §2 "hfields". In the pending arm of the actual action head,
the client head fields are the witness key with finality below it.
DC: INTENTIONAL: the window head fields of the decoded head. -/
theorem ktail_head_fields (st : State p.n) (H Q : FGBlock (Fin p.n))
    (hdec : FGSA.fgBlockOf st (FGSA.fgHead p st) = some H)
    (hJ : (heightView p H).J = (heightView p Q).J)
    (hj : (heightView p H).h_j = (heightView p Q).h_j)
    (hlt : (finalityView p H).h_F < (heightView p Q).h_j) :
    (FGSA.fgInputs p st).2.h_j = (heightView p Q).h_j ∧
      (FGSA.fgInputs p st).2.J = (heightView p Q).J.root ∧
      (FGSA.fgInputs p st).2.h_F < (heightView p Q).h_j := by
  rw [FGSA.fgInputs_headFields p st H hdec, certificateHeadFields_def]
  exact ⟨hj, by rw [hJ], hlt⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1993–2000 (FT-Tail-W: "each honest identity sends the exact finality pair in
its new higher-height row"), plan §1 steps 4–5 and §6. In the pending arm of the witness,
either some honest action head of round r+1 has already finalized the witness key, or
every honest seat releases a complete fresh row at height e+1 with Q's entry and the
finality pair (h_j(Q), J(Q)). The walk batches are an input (K-ROWS hbatch).
DC: INTENTIONAL: W finality pair; the already-finalized arm is kept explicit. -/
theorem ktail_pending_rows {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hnotF : ¬ FGBlock.Preceq pt.U (finalityView p ow.Q).F)
    (hbatch : ∀ x ∈ rho.honest, ∀ nd,
      postClock E rho x (p.actionTime (pt.r + 1)) = some nd →
      ∃ raw support seats m,
        FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support ∧
        Gen.Pure.Batch (Finset.card seats) m ∧
        WalkBatch p c rho nd.st ((pt.r + 1) * p.R + 1) raw support (eraseFG ow.Q) seats m) :
    (∃ x ∈ rho.honest, ∃ nd H,
      postClock E rho x (p.actionTime (pt.r + 1)) = some nd ∧
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
      FGBlock.Preceq ow.Q H ∧ (heightView p ow.Q).h_j < ow.e ∧
      (finalityView p H).h_F = (heightView p ow.Q).h_j ∧
      (finalityView p H).F = (heightView p ow.Q).J) ∨
    ∃ rows : Fin p.n → RowWire p.n, ∀ i ∈ honestSeats p c rho, ∃ j C,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) (pt.r + 1) (rows i) ∧
      RowComplete p c rho (rho.seatOf (.base .fg) i) (rows i) ∧
      (rows i).auth = .seat .fg i ∧
      rowHeight (rows i) = some (ow.e + 1) ∧
      FinalityNames p (rows i) (heightView p ow.Q).h_j (heightView p ow.Q).J ∧
      actionSourceFG p c E rho (rho.seatOf (.base .fg) i) (pt.r + 1) = some (some C) ∧
      (heightView p C).h = ow.e + 1 ∧
      (rows i).payload.height_pair =
        NamedHeightPair.vote (ow.e + 1) (heightView p ow.Q).T_h.root false ∧
      (∀ j' r a h, r < pt.r + 1 →
        HonestRowAt p c E rho j' (rho.seatOf (.base .fg) i) r a →
        rowHeight a = some h → h < ow.e + 1) := by
  classical
  have hsplit := ktail_witness_split p ow.Q pt.U ow.coverQ
  obtain ⟨-, -, -, hUh⟩ := hsplit.resolve_left hnotF
  have hhigh : pt.w.M + 1 ≤ (heightView p ow.Q).h_j := hT.high.trans hUh
  have hseat : ∀ i ∈ honestSeats p c rho, rho.seatOf (.base .fg) i ∈ rho.honest := by
    intro i hi
    have hdef : honestSeats p c rho =
        @Finset.filter (Fin p.n) (fun i => rho.seatOf (.base .fg) i ∈ rho.honest)
          (fun i => Classical.propDecidable (rho.seatOf (.base .fg) i ∈ rho.honest))
          Finset.univ := rfl
    rw [hdef] at hi
    exact (Finset.mem_filter.mp hi).2
  have hGSTq : E.t_GST ≤ p.actionTime (pt.r + 1) :=
    (ktail_slot_gst hT (s := pt.r * p.R) le_rfl).trans
      ((kmid_proposal_le_action p le_rfl).trans
        (le_of_lt (kmid_action_strictMono p (Nat.lt_succ_self pt.r))))
  by_cases hmix : ∃ x ∈ rho.honest, ∃ nd H,
      postClock E rho x (p.actionTime (pt.r + 1)) = some nd ∧
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
      FGBlock.Preceq ow.Q H ∧ (heightView p ow.Q).h_j < ow.e ∧
      (finalityView p H).h_F = (heightView p ow.Q).h_j ∧
      (finalityView p H).F = (heightView p ow.Q).J
  · exact Or.inl hmix
  · right
    refine ktail_fresh_rows p c E rho (pt.r + 1) (ow.e + 1) (heightView p ow.Q).h_j
      (Nat.lt_succ_of_le ow.justifiedBelowQ) ow.Q (heightView p ow.Q).J
      (honestSeats p c rho) subset_rfl ow.heightQ ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨nd, C, hnd, hsrc, hQC, hCh, -⟩ := ktail_action_source hT ow _ (hseat i hi)
      exact ⟨nd, C, hnd, hT.set.awake _ (hseat i hi) _ hGSTq ow.actionInRun, hsrc, hQC, hCh⟩
    · intro i hi nd hnd
      obtain ⟨raw, support, seats, m, hhead, hcount, hwb⟩ := hbatch _ (hseat i hi) nd hnd
      obtain ⟨H, hdec, -, hQH, -, -, hJ, hj, hfin, harm⟩ :=
        ktail_action_head_split hT ow (hseat i hi) nd hnd raw support seats m hhead hcount hwb
      rcases harm with hlt | ⟨heq, hFJ⟩
      · exact ktail_head_fields nd.st H ow.Q hdec hJ hj hlt
      · exfalso
        exact hmix ⟨_, hseat i hi, nd, H, hnd, hdec, hQH, heq ▸ hfin, heq, hFJ⟩
    · intro i hi
      exact ktail_tail_record hT ow hqc hnames hhigh (hseat i hi)
    · intro i _ j r a h hr ha hh
      exact Nat.lt_succ_of_le
        (ow.rowsThroughOpening j _ r a h (Nat.le_of_lt_succ hr) ha hh)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:2001–2005 (FT-Tail-W: "before the terminal z+κ carrier there is at most one
newer justification, at e+1 … K remains in two entries or is already covered"), plan §3.
For an honest proposal X at the terminal slot, in the pending arm of the witness: Q is
below X's parent, the parent height is e+1 or e+2, and the witness key is retained in the
parent's window or covered by its finality. In the covered case U is below its finality.
DC: INTENTIONAL: W retention with K_W ≥ 2; Assembly supplies the raw origin and names. -/
theorem ktail_terminal_key {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hnotF : ¬ FGBlock.Preceq pt.U (finalityView p ow.Q).F)
    (X : FGBlock (Fin p.n))
    (hX : HonestProposal E rho (fgsaInterface p c)
      ((pt.r + 1) * p.R + kappaF p ΔF) (eraseFG X)) :
    FGBlock.Preceq ow.Q X.parent ∧ ow.e + 1 ≤ (heightView p X.parent).h ∧
      (heightView p X.parent).h ≤ ow.e + 2 ∧
      FGBlock.Preceq pt.U (heightView p ow.Q).J ∧
      (Window.RetainedW p X.parent (heightView p ow.Q).h_j (heightView p ow.Q).J ∨
        Window.CoveredW p X.parent (heightView p ow.Q).h_j (heightView p ow.Q).J) ∧
      (FGBlock.Preceq pt.U (finalityView p X.parent).F ∨
        Window.RetainedW p X.parent (heightView p ow.Q).h_j (heightView p ow.Q).J) := by
  have hs := hT.set.base.valid.toScheduleWellFormed
  have laws := (fgCertificateLaws p).height
  obtain ⟨-, hκ2, hκR, -, -, -, -⟩ := ktail_bounds hT
  obtain ⟨hUJ, -, hpend, -⟩ := (ktail_witness_split p ow.Q pt.U ow.coverQ).resolve_left hnotF
  -- The carrier parent is held by the honest proposer at its proposal read.
  obtain ⟨Xb, heX, -, -, -, st, hst, -, hparTF⟩ := kmid_opening_carrier p c E rho hs hX
  rw [kmid_eraseFG_inj p heX] at hparTF
  have hprop : V2.D.proposerOf rho (fgsaInterface p c) ((pt.r + 1) * p.R + kappaF p ΔF) ∈
      rho.honest := hX.1.2
  change (postClock E rho _ (V2.D.proposalTime (fgsaInterface p c) _)).map (·.st) = some st
    at hst
  rw [postClock_def, preTick_def] at hst
  cases hj : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c)
      ((pt.r + 1) * p.R + kappaF p ΔF))
      (V2.D.proposalTime (fgsaInterface p c) ((pt.r + 1) * p.R + kappaF p ΔF)) with
  | none => rw [hj] at hst; cases hst
  | some j =>
    rw [hj] at hst
    have hjev := V2.D.Run.tickIdx?_spec hj
    have hst' : ((fgsa p c).clock (V2.D.Run.stateBefore E rho j
        (V2.D.proposerOf rho (fgsaInterface p c) ((pt.r + 1) * p.R + kappaF p ΔF)))
        (V2.D.proposalTime (fgsaInterface p c) ((pt.r + 1) * p.R + kappaF p ΔF))).st = st :=
      Option.some.inj hst
    have hheld : HeldAt p c E rho j (V2.D.proposerOf rho (fgsaInterface p c)
        ((pt.r + 1) * p.R + kappaF p ΔF)) X.parent := by
      refine ⟨hprop, ?_⟩
      rw [← hst'] at hparTF
      change X.parent ∈ (FGSA.clock p _ _).fg.TF at hparTF
      rw [FGSA.clock_fg] at hparTF
      exact hparTF
    -- Q is below the carrier parent (TCarrier from a fresh source of round r+1).
    have hwin := hT.window
    rw [Gen.Pure.Tail_W_def] at hwin
    have hx₀ := hwin.1.2
    obtain ⟨nd, C, hnd, hsrc, hQC, hCh, -⟩ := ktail_action_source hT ow _ hx₀
    have hsrc' : actionSourceFG p c E rho (V2.D.proposerOf rho (fgsaInterface p c)
        (pt.r * p.R)) (pt.r + 1) = some (some C) := by
      rw [actionSourceFG_def, hnd]
      change some (FGSA.fgSource p nd.st) = some (some C)
      rw [hsrc]
    have hhighC : high p pt.w C := by
      change pt.w.M + 1 ≤ (heightView p C).h
      rw [hCh]
      exact Nat.le_succ_of_le ow.highA
    have hCX := hT.input.t.h2 _ (pt.r + 1) C _ (eraseFG X) hx₀ hsrc' hhighC hX
      (Nat.add_le_add_left hκ2 _)
    rw [eraseFG_parent] at hCX
    have hQP : FGBlock.Preceq ow.Q X.parent := preceq_trans hQC (kmid_lift_preceq p hCX)
    have hlow : ow.e + 1 ≤ (heightView p X.parent).h := ow.heightQ ▸ laws.h_mono hQP
    -- Rows through round r+1 are at most e+1 high: the cap at the action of round r+2.
    have rows1 : ∀ j z r a h, r ≤ pt.r + 1 → HonestRowAt p c E rho j z r a →
        rowHeight a = some h → h ≤ ow.e + 1 := by
      intro j z r a h hr ha hh
      rcases Nat.lt_or_ge r (pt.r + 1) with hlt | hge
      · exact (ow.rowsThroughOpening j z r a h (Nat.le_of_lt_succ hlt) ha hh).trans
          (Nat.le_succ _)
      · obtain rfl : r = pt.r + 1 := le_antisymm hr hge
        obtain ⟨C', hC', rfl⟩ := kmid_row_source_height p c E rho hnames ha hh
        obtain ⟨nd', C'', hnd', hsrc'', -, hC''h, -⟩ :=
          ktail_action_source hT ow z ((HonestRowAt_def p c E rho _ _ _ _).mp ha).1
        rw [actionSourceFG_def, hnd'] at hC'
        change some (FGSA.fgSource p nd'.st) = some (some C') at hC'
        rw [hsrc''] at hC'
        cases Option.some.inj (Option.some.inj hC')
        exact hC''h.le
    obtain ⟨-, rowsBefore⟩ := kmid_rows_cut p c E rho (ow.e + 1) (pt.r + 1) rows1
    have hprop2 : V2.D.proposalTime (fgsaInterface p c) ((pt.r + 1) * p.R + kappaF p ΔF) ≤
        p.actionTime (pt.r + 1 + 1) := by
      have hle : (pt.r + 1) * p.R + kappaF p ΔF ≤ (pt.r + 1 + 1) * p.R := by
        rw [Nat.succ_mul (pt.r + 1)]
        exact Nat.add_le_add_left hκR _
      exact kmid_proposal_le_action p hle
    have hcut := (kmid_tick_lt_afterTicks p c E rho hs hjev hprop2).le
    have hhigh : (heightView p X.parent).h ≤ ow.e + 2 :=
      kmid_held_cap_afterTicks p c E rho hOrigin hT.set.base hT.set.faultQ _ _ rowsBefore
        j _ X.parent hcut hheld
    have hrc := ktail_retained_or_covered p ow.Q X.parent (ow.e + 1) hQP
      (ow.heightQ ▸ le_rfl) hhigh hpend
    refine ⟨hQP, hlow, hhigh, hUJ, hrc, ?_⟩
    rcases hrc with hr | hc
    · exact Or.inr hr
    · left
      rw [Window.CoveredW_def] at hc
      have hF : FGBlock.Preceq (heightView p ow.Q).J (finalityView p X.parent).F := by
        have h2 := hc.2
        rw [finalityView_def, Window.certificateFinality_def]
        dsimp only
        rw [Window.projectFinality_def]
        exact h2
      exact preceq_trans hUJ hF

end AvailableChain.FGSA.Run
end
