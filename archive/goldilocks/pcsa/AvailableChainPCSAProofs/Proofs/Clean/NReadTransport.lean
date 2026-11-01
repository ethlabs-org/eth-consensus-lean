module
public import AvailableChainPCSAProofs.Proofs.Clean.NWalkCounts
public import AvailableChainPCSAProofs.Proofs.Clean.ForwardReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.BodyPaths

public section

/-! C6 NReadTransport: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- A positive N count supplies an early resolved HEAD and the target slot bound. -/
theorem pcsa_N_head_witness (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (B : Block) (hN : holdsN p v s B = true) :
    ∃ i, (⟨.seat s i, .head B.root⟩ : GridCO.Wire p.n .root) ∈
      GridCO.earlyVotes p.toParams.engine v s ∧
      GridCO.resolvedHead? v ⟨.seat s i, .head B.root⟩ = some B ∧ B.slot ≤ s := by
  have hn : 0 < nQuorum p.n := by
    have hp := p.nPos
    have hq := Gen.Pure.qA_add_le_two_mul_qN p.n
    change pcQuorum p.n + p.n ≤ 2 * nQuorum p.n at hq
    omega
  have hc : nQuorum p.n ≤ nCount p v s B := of_decide_eq_true hN
  rw [pcsa_nCount_card] at hc
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (hn.trans_le hc)
  obtain ⟨o, ho, hoi⟩ := (Gen.AC.Root.vote_pool_mem_seats _ i).mp hi
  have hr : GridCO.resolvedHead? v o = some B := beq_iff_eq.mp (List.mem_filter.mp ho).2
  have hearly : o ∈ GridCO.earlyVotes p.toParams.engine v s :=
    (List.mem_filter.mp (List.mem_filter.mp ho).1).1
  have hl : GridCO.headLabel? o = some s :=
    beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hearly).1).2
  obtain ⟨r, rfl⟩ := Run.pcsa_count_head_shape (p := p) o s i hl hoi
  have he := FGSA.Run.resolvedHead_root _ _ hr
  change some r = some B.root at he
  have heq := Option.some.inj he
  subst r
  have ht : GridCO.resolvedBefore v ⟨.seat s i, .head B.root⟩
      (SA.earlyTime p.toParams s) = true := (List.mem_filter.mp hearly).2
  delta GridCO.resolvedBefore at ht
  rw [hr] at ht
  exact ⟨i, hearly, hr,
    of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).1).1⟩
private theorem N_score_seat {n : Nat} (tree : List Block)
    (raw sup : List (GridCO.Wire n .root)) (s : Slot) (i : Fin n) (B : Block)
    (hsub : sup ⊆ raw)
    (h : ((⟨.seat s i, .head B.root⟩ : GridCO.Wire n .root) ∈ sup ∧
      Gen.AC.Root.voteSupports tree B ⟨.seat s i, .head B.root⟩ = true) ∨
      GridCO.equivocates raw i = true) :
    i ∈ (GridCO.seats n raw).toFinset.filter
      (fun j => (GridCO.equivocates raw j || Gen.AC.Root.poolSupports tree sup j B) = true) := by
  rcases h with ⟨hm, hs⟩ | hc
  · exact Finset.mem_filter.mpr
      ⟨(Gen.AC.Root.vote_pool_mem_seats raw i).mpr ⟨_, hsub hm, rfl⟩,
        Bool.or_eq_true_iff.mpr (Or.inr
          ((Gen.AC.Root.vote_pool_support_witness tree sup i B).mpr ⟨_, hm, rfl, hs⟩))⟩
  · exact Finset.mem_filter.mpr
      ⟨Gen.AC.Root.vote_pool_equivocates_participant raw i hc,
        Bool.or_eq_true_iff.mpr (Or.inl hc)⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- In the delivery window: An actual N quorum reaches both next-label scores and both retained
path domains. -/
theorem pcsa_N_read_transport_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (v u : Time) (s : Slot) (B : Block)
    (hT : T₀ ≤ SA.earlyTime p.toParams s) (hc : SA.freezeTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k)
    (hN : holdsN p (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s B = true) :
    let dst := clock p (V2.D.Run.stateBefore E rho k y).st u
    nQuorum p.n ≤ GridCO.goldfishScore dst.base.blocks
      (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) B ∧
    nQuorum p.n ≤ GridCO.goldfishScore dst.base.blocks
      (proposerVotes dst (s + 1)) (proposerSupport dst (s + 1)) B ∧
    ∀ C, Block.Preceq C B → C ∈ erasedList dst (fullTree p dst) ∧
      C ∈ erasedList dst (KitFG.storeFrameView (FGSA.heightView p) dst.fg (voterBlocks p dst (s +
        1))) := by
  intro dst
  let src := clock p (V2.D.Run.stateBefore E rho a x).st v
  let Nvotes := (timelyHeads p (actView src) s).filter
    (fun o => GridCO.resolvedHead? (actView src) o == some B)
  let N := (GridCO.seats p.n Nvotes).toFinset
  have hNcard : nQuorum p.n ≤ N.card := by
    have hh : nQuorum p.n ≤ nCount p (actView src) s B := of_decide_eq_true hN
    rw [pcsa_nCount_card] at hh
    exact hh
  obtain ⟨i0, hearly0, hr0, hslot⟩ := pcsa_N_head_witness p (actView src) s B hN
  have hsV : headSupport p dst (s + 1) ⊆ headVotes p dst (s + 1) :=
    pcsa_headSupport_subset_at_read E rho h.valid.toDeliveryWellFormed k y u (s + 1)
  have hsP : proposerSupport dst (s + 1) ⊆ proposerVotes dst (s + 1) :=
    fun _ ho => (List.mem_filter.mp ho).1
  have hforward (i : Fin p.n) (hi : i ∈ N) :
      i ∈ (GridCO.seats p.n (headVotes p dst (s + 1))).toFinset.filter
        (fun j => (GridCO.equivocates (headVotes p dst (s + 1)) j ||
          Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) j B) = true) ∧
      i ∈ (GridCO.seats p.n (proposerVotes dst (s + 1))).toFinset.filter
        (fun j => (GridCO.equivocates (proposerVotes dst (s + 1)) j ||
          Gen.AC.Root.poolSupports dst.base.blocks (proposerSupport dst (s + 1)) j B) = true) := by
    obtain ⟨o, ho, hoi⟩ := (Gen.AC.Root.vote_pool_mem_seats Nvotes i).mp hi
    have hr : GridCO.resolvedHead? (actView src) o = some B :=
      beq_iff_eq.mp (List.mem_filter.mp ho).2
    have hearly : o ∈ GridCO.earlyVotes p.toParams.engine (actView src) s :=
      (List.mem_filter.mp (List.mem_filter.mp ho).1).1
    have hl : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hearly).1).2
    obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hoi
    have he := FGSA.Run.resolvedHead_root _ _ hr
    change some r = some B.root at he
    have heq := Option.some.inj he
    subst r
    rcases pcsa_early_input_relay_support_win E rho h hF hD (hT := hT) a k x y hx hy s i B v u hc hk
      hearly hr with hh | he
    · have hsup : Gen.AC.Root.voteSupports dst.base.blocks B ⟨.seat s i, .head B.root⟩ = true := by
        apply (Gen.AC.Root.vote_support_body dst.base.blocks B _).mpr
        refine ⟨B, ?_, ?_, hslot, Gen.Pure.block_preceq_refl B⟩
        · have hl := FGSA.Run.resolvedHead_target _ _ hh.2.2
          have hd : GridCO.resolutionTree (actView dst) = dst.base.blocks := by
            change (clock p _ u).base.headDomain.getD _ = _
            rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
            rfl
          rwa [hd] at hl
        · exact (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hh.2.2)).1
      exact ⟨N_score_seat dst.base.blocks _ _ s i B hsV (Or.inl ⟨hh.1, hsup⟩),
        N_score_seat dst.base.blocks _ _ s i B hsP (Or.inl ⟨hh.2.1, hsup⟩)⟩
    · exact ⟨N_score_seat dst.base.blocks _ _ s i B hsV (Or.inr he.1),
        N_score_seat dst.base.blocks _ _ s i B hsP (Or.inr he.2)⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Gen.AC.Root.vote_pool_score_card]
    exact hNcard.trans (Finset.card_le_card (fun i hi => (hforward i hi).1))
  · rw [Gen.AC.Root.vote_pool_score_card]
    exact hNcard.trans (Finset.card_le_card (fun i hi => (hforward i hi).2))
  · have hm := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hr0)).1
    have ht : GridCO.resolvedBefore (actView src) ⟨.seat s i0, .head B.root⟩
        (SA.earlyTime p.toParams s) = true := (List.mem_filter.mp hearly0).2
    delta GridCO.resolvedBefore at ht
    rw [hr0] at ht
    have hstamp : GridCO.stampBlock src.base B < SA.earlyTime p.toParams s :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp ht).2
    have hrelay := pcsa_early_body_relay_frozen_win E rho h hF hD (hT := hT) a
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) x y hx hy s B v u hc (le_refl _) hm
        hstamp
    have hb := hrelay.1
    rw [pcsa_clock_blocks] at hb
    have hb' := pcsa_body_stateBefore_mono E rho h.noRestart y hk hb
    have hclock : B ∈ dst.base.blocks := by
      change B ∈ (clock p _ u).base.blocks
      rw [pcsa_clock_blocks]
      exact hb'
    intro C hCB
    exact ⟨pcsa_full_read_prefix_mem E rho hF k y hy u B C hclock hCB,
      pcsa_frozen_read_prefix_mem E rho h hF _ k y hy s u B C (le_refl _) hk hb hCB⟩
/-- An actual N quorum reaches both next-label scores and both retained path domains. -/
theorem pcsa_N_read_transport (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (v u : Time) (s : Slot) (B : Block)
    (hc : SA.freezeTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k)
    (hN : holdsN p (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s B = true) :
    let dst := clock p (V2.D.Run.stateBefore E rho k y).st u
    nQuorum p.n ≤ GridCO.goldfishScore dst.base.blocks
      (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) B ∧
    nQuorum p.n ≤ GridCO.goldfishScore dst.base.blocks
      (proposerVotes dst (s + 1)) (proposerSupport dst (s + 1)) B ∧
    ∀ C, Block.Preceq C B → C ∈ erasedList dst (fullTree p dst) ∧
      C ∈ erasedList dst (KitFG.storeFrameView (FGSA.heightView p) dst.fg (voterBlocks p dst (s +
        1))) :=
  pcsa_N_read_transport_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx hy v u s
    B (pcsa_floor_early (pcsa_zero_le_proposal s)) hc hk hN
end AvailableChain.PCSA.Run

end
