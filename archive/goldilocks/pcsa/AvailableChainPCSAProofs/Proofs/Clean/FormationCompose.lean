module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCollection
public import AvailableChainPCSAProofs.Proofs.Clean.FormationTerminal

public section

/-! Formation parts 1–4 through the freeze. The remaining run inputs have
names here. The gate conclusion uses its longer window in Assembly. -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

/-- The retained inputs for the actual proposer and voter reads. -/
structure FormationRetainedHeadInputs (p : Params) (src dst : Node p)
    (s : Slot) (N : NamedProposal p.n) : Prop where
  hRawKeep : proposerVotes src.st s ⊆ headVotes p dst.st s
  hRawBack : ∀ o ∈ headVotes p dst.st s, ∀ i, GridCO.headSeat? o = some i →
    o ∈ proposerVotes src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true
  hSupportKeep : proposerSupport src.st s ⊆ headSupport p dst.st s
  hSupportBack : ∀ o ∈ headSupport p dst.st s, ∀ i, GridCO.headSeat? o = some i →
    o ∈ proposerSupport src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true
  hResolution : ∀ o ∈ proposerSupport src.st s, ∀ B,
    Gen.AC.Root.voteSupports src.st.base.blocks B o =
      Gen.AC.Root.voteSupports dst.st.base.blocks B o
  hKeep : Gen.Pure.SuffixPersists (walkBase p src.st (proposerPC p src.st)) N.erase.parent
    (erasedList src.st (fullTree p src.st))
    (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
      (voterBlocks p dst.st s)))
    (GridCO.goldfishScore src.st.base.blocks (proposerVotes src.st s) (proposerSupport src.st s))
    (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
    (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s))
  hReflect : Gen.Pure.SuffixReflects (walkBase p src.st (proposerPC p src.st)) N.erase.parent
    (erasedList src.st (fullTree p src.st))
    (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
      (voterBlocks p dst.st s)))
    (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
    (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s))
  hChild : N.erase ∈ erasedList dst.st
    (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s))
  hUnique : ∀ B ∈ erasedList dst.st
    (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s)),
    B.parent? = some N.erase.parent →
    eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s) B = true →
    B = N.erase


/-- The exact remaining run inputs for Formation parts 1–4. -/
structure FormationPreFreezeInputs (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) : Prop where
  hRetained : ∀ src dst y,
    pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
    y ∈ rho.honest → E.awake y (SA.voteTime p.toParams s) = true →
    pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst →
    FormationRetainedHeadInputs p src dst s N
  hTimelyHeads : ∀ y ∈ rho.honest, ∀ nd,
    pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd →
    ∀ i : Fin p.n, rho.seatOf (.base (.head s)) i ∈ awakeHonestLabel p c E rho s →
      ∃ o ∈ timelyHeads p (actView nd.st) s,
        GridCO.headSeat? o = some i ∧ GridCO.resolvedHead? (actView nd.st) o = some N.erase
  hFrozenPCReceipt : ∀ y ∈ rho.honest, ∀ nd,
    pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd →
    ∀ src, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
    ∀ C ∈ pcSnapshotAt nd.st (s - 1), frameActive p nd.st C = true →
      ∃ A ∈ src.st.pcs.filter (frameActive p src.st), A.slot = C.slot ∧ A.target = C.target
  hCarriedPresence : ∀ y ∈ rho.honest, ∀ nd,
    pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd →
    ∀ D, N.pc = some D →
      D ∈ (pcSnapshotAt nd.st (s - 1) ++ carriedPCs nd.st s).filter (frameActive p nd.st)
  hAckAdmit : ∀ y ∈ rho.honest, ∀ (i : Fin p.n) j t,
    rho.seatOf (.base (.ack s)) i ∈ rho.honest →
    SA.earlyTime p.toParams s ≤ t → t < SA.freezeTime p.toParams s →
    V2.D.Run.handlesAt E rho j y (ackObj p s i N.erase.root) t →
    (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈
      (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool

/-- Every honest node has its scheduled early read inside the freeze window. -/
theorem pcsa_formation_early_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (hy : y ∈ rho.honest) :
    ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd := by
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = ((4 * s + 2 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.earlyTime p.toParams s := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    positivity
  have hcut : SA.earlyTime p.toParams s ≤ SA.freezeTime p.toParams s := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    nlinarith
  have hm := h.base.valid.tick_total y hy _ hpub hz (le_trans hcut h.horizon)
  have hsome : (V2.D.Run.tickIdx? rho y (SA.earlyTime p.toParams s)).isSome = true := by
    delta V2.D.Run.tickIdx?
    rw [List.findIdx?_isSome, List.any_eq_true]
    exact ⟨_, hm, decide_eq_true ⟨rfl, rfl⟩⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨(pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k y) (SA.earlyTime p.toParams s), ?_⟩
  rw [pcsa_postClock_def, pcsa_preTick_def, hk]
  rfl

/-- The counted awake HEAD seats supply the required N count. -/
theorem pcsa_formation_n_counts_of_timely_heads (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hTimelyHeads : ∀ y ∈ rho.honest, ∀ nd,
      pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd →
      ∀ i : Fin p.n, rho.seatOf (.base (.head s)) i ∈ awakeHonestLabel p c E rho s →
        ∃ o ∈ timelyHeads p (actView nd.st) s,
          GridCO.headSeat? o = some i ∧ GridCO.resolvedHead? (actView nd.st) o = some N.erase) :
    ∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
      holdsN p (actView nd.st) s N.erase = true := by
  classical
  let H := awakeHonestLabel p c E rho s
  let holder : Fin p.n → V := rho.seatOf (.base (.head s))
  let Q := Finset.univ.filter (fun i => holder i ∈ H)
  have hbij : Function.Bijective holder := h.base.cstar (.base (.head s)) trivial
  have hcard : Q.card = H.card := by
    apply Finset.card_bij (fun i _ => holder i)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ he
      exact hbij.injective he
    · intro y hy
      obtain ⟨i, hi⟩ := hbij.surjective y
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi ▸ hy⟩, hi⟩
  intro y hy
  obtain ⟨nd, hr⟩ := pcsa_formation_early_read E rho s N ΔF h y hy
  refine ⟨nd, hr, pcsa_formation_holdsN p (actView nd.st) s N.erase Q
    (hcard.symm ▸ h.participation) ?_⟩
  intro i hi
  exact hTimelyHeads y hy nd hr i (Finset.mem_filter.mp hi).2

/-- The retained HEAD inputs alone make every honest HEAD of slot `s` exact.
The proof uses no early HEAD receipt, so early receipt can use it. -/
theorem pcsa_formation_head_exact_of_retained (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hRetained : ∀ src dst y,
      pcsa_postClock E rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      y ∈ rho.honest → E.awake y (SA.voteTime p.toParams s) = true →
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst →
      FormationRetainedHeadInputs p src dst s N) :
    ∀ y H, HonestHeadAt p c E rho y s H → H = N.erase := by
  intro y H hh
  rw [pcsa_HonestHeadAt_def] at hh
  rw [pcsa_voteHeadAt_def] at hh
  obtain ⟨dst, hr, he⟩ := Option.map_eq_some_iff.mp hh.2.2
  obtain ⟨src, hs, _⟩ := pcsa_formation_base_below_parent E rho s N ΔF h
  have hi := hRetained src dst y hs hh.1 hh.2.1 hr
  exact he.symm.trans (pcsa_formation_head_exact_of_run_terminal E rho s N ΔF h src dst y
    hs hh.1 hh.2.1 hr hi.hRawKeep hi.hRawBack hi.hSupportKeep hi.hSupportBack hi.hResolution
    hi.hKeep hi.hReflect hi.hChild hi.hUnique)

/-- Formation parts 1–4 use only the window through z_s and the named run inputs. -/
theorem pcsa_formation_preFreeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hInputs : FormationPreFreezeInputs E rho s N) :
    (∀ y H, HonestHeadAt p c E rho y s H → H = N.erase) ∧
    (∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
      holdsN p (actView nd.st) s N.erase = true) ∧
    (∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
      HonestAckAt p c E rho y s N.erase) ∧
    (∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase) := by
  have hN := pcsa_formation_n_counts_of_timely_heads E rho s N ΔF h hInputs.hTimelyHeads
  have hAck : ∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
      HonestAckAt p c E rho y s N.erase := by
    intro y hy haw
    obtain ⟨nd, hr, hn⟩ := hN y hy
    exact pcsa_formation_early_ack_of_receipt E rho s N ΔF h y nd hy haw hr hn
      (hInputs.hFrozenPCReceipt y hy nd hr) (hInputs.hCarriedPresence y hy nd hr)
  exact ⟨pcsa_formation_head_exact_of_retained E rho s N ΔF h hInputs.hRetained, hN, hAck,
    pcsa_formation_pc_of_n_counts E rho s N ΔF h hAck hInputs.hAckAdmit hN⟩

end AvailableChain.PCSA.Run
end
