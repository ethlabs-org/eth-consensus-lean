module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockFollow
public import AvailableChainPCSAProofs.Proofs.Recovery.Suffix
public import AvailableChainPCSAProofs.Proofs.Shared.Proposal

public section

namespace AvailableChain.PCSA

/-- Proposer support retains the resolved body's label bound. -/
theorem recovery_proposer_support_slot (p : Params) (st : State p.n)
    (hF : st.fg.F = .genesis) (hd : st.base.headDomain = none)
    (s : Slot) (o : GridCO.Wire p.n .root) (H : Block)
    (ho : o ∈ proposerSupport st s) (hr : GridCO.resolvedHead? st.base o = some H) :
    H.slot ≤ (GridCO.headLabel? o).getD 0 := by
  obtain ⟨hm, ht⟩ := List.mem_filter.mp ho
  have hl : GridCO.headLabel? o = some (s - 1) := beq_iff_eq.mp (List.mem_filter.mp hm).2
  rw [recovery_active_resolution st hF hd o, hr] at ht
  rw [hl]
  exact of_decide_eq_true ht

open Gen.Pure

/-- A majority target with lower conflicting scores is below the PC-SA head. -/
theorem recovery_base_walk_covers
    (p : Params) (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n .root)) (A B : Block)
    (hanchor : Block.Compatible A B)
    (hpath : ∀ C, Block.Prec A C → Block.Preceq C B → C ∈ tree)
    (hmajority : GridCO.voterCount raw <
      2 * GridCO.goldfishScore st.base.blocks raw support B)
    (hdominance : ∀ D, Block.compatible B D = false →
      GridCO.goldfishScore st.base.blocks raw support D <
        GridCO.goldfishScore st.base.blocks raw support B) :
    Block.Preceq B (GridCO.ghost A tree (GridCO.goldfishScore st.base.blocks raw support)
      (eligible p st raw support)) := by
  apply Gen.Pure.walk_covers_of_dominated_suffix A B tree
    (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support) hanchor
  intro C hac hcb
  have hm := Gen.AC.Root.goldfishScore_antitone st.base.blocks raw support C B hcb
  refine ⟨hpath C hac hcb, ?_, ?_⟩
  · unfold eligible
    have hmaj : GridCO.voterCount raw <
        2 * GridCO.goldfishScore st.base.blocks raw support C := by omega
    simp only [hmaj, decide_true, Bool.or_true, Bool.true_or]
  · intro D _ hp _ hne
    have he : D.depth = C.depth := by
      cases D with
      | genesis => cases C with
        | genesis => rfl
        | node P s r x => cases hp
      | node P s r x => cases C with
        | genesis => cases hp
        | node Q t u y =>
          have heq : P = Q := Option.some.inj hp
          subst Q
          rfl
    have hn : ¬ Block.Compatible D C := by
      intro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hne (prefix_eq_of_depth D C h (Nat.le_of_eq he.symm))
      · exact hne (prefix_eq_of_depth C D h (Nat.le_of_eq he)).symm
    have hd : Block.compatible B D = false := by
      rw [block_compatible_comm]
      exact Bool.eq_false_iff.mpr (block_incompatible_of_preceq hn hcb)
    exact lt_of_lt_of_le (hdominance D hd) hm

end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- The actual preceding honest HEAD batch supplies the next proposer path and counts. -/
theorem recovery_proposer_batch_path [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g r : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hg : g ≤ r) (hgst : E.t_GST ≤ SA.voteTime p.toParams r)
    (horizon : SA.voteTime p.toParams r ≤ rho.horizon)
    (B : Block) (hheads : ∀ x H, HonestHeadAt p c E rho x r H → Block.Preceq B H)
    (y : V) (hy : y ∈ rho.honest) (dst : Node p)
    (hn : pcsa_postClock E rho y (SA.proposalTime p.toParams (r + 1)) = some dst) :
    (∀ C, Block.Preceq C B → C ∈ erasedList dst.st
      (fullTree p dst.st)) ∧
    GridCO.voterCount (proposerVotes dst.st (r + 1)) <
      2 * GridCO.goldfishScore dst.st.base.blocks
        (proposerVotes dst.st (r + 1)) (proposerSupport dst.st (r + 1)) B ∧
    ∀ D, Block.compatible B D = false →
      GridCO.goldfishScore dst.st.base.blocks
        (proposerVotes dst.st (r + 1)) (proposerSupport dst.st (r + 1)) D <
      GridCO.goldfishScore dst.st.base.blocks
        (proposerVotes dst.st (r + 1)) (proposerSupport dst.st (r + 1)) B := by
  obtain ⟨Hon, hHon, hcard⟩ := recovery_honest_seats E rho h r
  obtain ⟨hf, hd⟩ := recovery_read_count_domain E rho hF y hy _ dst hn
  have batch (i : Fin p.n) (hi : i ∈ Hon) :
      ∃ H, HonestHeadAt p c E rho (rho.seatOf (.base (.head r)) i) r H ∧
        (⟨.seat r i, .head H.root⟩ : GridCO.Wire p.n .root) ∈ proposerSupport dst.st (r + 1) ∧
        GridCO.equivocates (proposerVotes dst.st (r + 1)) i = false ∧
        Gen.AC.Root.voteSupports dst.st.base.blocks B ⟨.seat r i, .head H.root⟩ = true ∧
        (∀ C, Block.Preceq C B → C ∈ erasedList dst.st
          (fullTree p dst.st)) := by
    have hx := (hHon i).mp hi
    obtain ⟨H, hH⟩ := recovery_honest_head_exists E rho h.base _ hx r
      (h.awake _ hx _ hgst horizon) horizon
    have hh := transport.honestProposerInputs r hg _ H hH i rfl y hy dst hn
    refine ⟨H, hH, hh.1, hh.2.2.1, ?_, ?_⟩
    · exact recovery_resolved_support dst.st hd _ H B hh.2.2.2.1
        (recovery_proposer_support_slot p dst.st hf hd _ _ H hh.1 hh.2.2.2.1) (hheads _ H hH)
    · intro C hCB
      exact hh.2.2.2.2 C (Gen.Pure.block_preceq_trans hCB (hheads _ H hH))
  have hpos : 0 < Hon.card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨_, _, _, _, _, hpath⟩ := batch i hi
  refine ⟨hpath, recovery_batch_scores p dst.st _ _ B Hon
    (fun _ ho => (List.mem_filter.mp ho).1) hcard ?_ ?_⟩
  · intro i hi
    obtain ⟨_, _, _, hc, _⟩ := batch i hi
    exact hc
  · intro i hi
    obtain ⟨H, _, hm, _, hs, _⟩ := batch i hi
    exact (Gen.AC.Root.vote_pool_support_witness _ _ i B).mpr ⟨_, hm, rfl, hs⟩

/-- The long mix is after label g and excludes slot zero. -/
theorem recovery_long_slot_bounds (p : Params) (g s : Slot)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ SA.proposalTime p.toParams s) :
    0 < s ∧ g ≤ s - 1 := by
  try delta Slot Time at *
  have hd := p.deltaPos
  have hk := p.kLarge
  have hmi : (g : Int) ≤ ((g + 2 * p.k - 1 : Nat) : Int) := by omega
  have hgs : g < s := by
    by_contra hn
    have hsg : (s : Int) ≤ (g : Int) := by omega
    change 4 * p.Δ * ((g + 2 * p.k - 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) at hmix
    nlinarith
  omega

omit [DecidableEq V] in
/-- The preceding label is synchronous and lies inside the chosen slot's horizon. -/
theorem recovery_preceding_vote_bounds (E : Generic.Env V) (g s : Slot)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g) (hpos : 0 < s) (hgs : g ≤ s - 1) :
    E.t_GST ≤ SA.voteTime p.toParams (s - 1) ∧
      SA.voteTime p.toParams (s - 1) ≤ SA.gateTime p.toParams s := by
  have hd := p.deltaPos
  have hgi : (g : Int) ≤ ((s - 1 : Nat) : Int) := by exact_mod_cast hgs
  have hsi : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
    try delta Slot at *
    omega
  constructor
  · apply hgst.trans
    change 4 * p.Δ * (g : Int) + p.Δ ≤ 4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ
    nlinarith
  · change 4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    nlinarith

/-- The long-slot proposer root is reached by the walk from its selected PC base. -/
theorem recovery_long_proposer_root [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g s : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ SA.proposalTime p.toParams s)
    (hp : V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s ∈ rho.honest)
    (horizon : SA.gateTime p.toParams s ≤ rho.horizon) :
  ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd →
    let st := nd.st
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    Block.Preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks (proposerVotes st s) (proposerSupport st s))
        (eligible p st (proposerVotes st s) (proposerSupport st s))) := by
  obtain ⟨hpos, hgs⟩ := recovery_long_slot_bounds p g s hmix
  obtain ⟨hvg, hvh⟩ := recovery_preceding_vote_bounds E g s hgst hpos hgs
  have hs : s - 1 + 1 = s := Nat.sub_add_cancel hpos
  intro nd hn
  dsimp only
  rw [← recovery_proposer_base]
  rcases pcsa_liveRoot_origin p nd.st (proposerPC p nd.st) with he | hm
  · rw [he]
    exact @GridCO.ghost_extends GridCO.slowLeasePolicy _ _ _ _
  · obtain ⟨row, hr, he, ht, _⟩ := (pcsa_walkLocks_mem p nd.st _ _).mp hm
    have hB : LiveLease nd.st (liveRoot p nd.st (proposerPC p nd.st)) := ⟨row, hr, he, ht⟩
    have hheads := recovery_live_lock_preceding_heads E rho h hF g s transport hgst
      _ hp _ (Or.inl rfl) hmix nd hn _ hB
    have hh := recovery_proposer_batch_path E rho h hF g (s - 1) transport hgs hvg
      (hvh.trans horizon) _ hheads _ hp nd (by rw [hs]; exact hn)
    rw [hs] at hh
    apply recovery_base_walk_covers p nd.st _ _ _ _ _ ?_
      (fun C _ hCB => hh.1 C hCB) hh.2.1 hh.2.2
    exact Gen.Pure.block_compatible_of_common (pcsa_liveRoot_extends_base p nd.st _)
      (Gen.Pure.block_preceq_refl _)

/-- Both reads' live targets are covered by the same preceding honest batch.
Compatibility with the common base therefore suffices for the voter F4 clause. -/
theorem recovery_long_voter_leases [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g s : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ SA.proposalTime p.toParams s)
    (horizon : SA.gateTime p.toParams s ≤ rho.horizon)
    (N : NamedProposal p.n) (hN : HonestNamedProposal p c E rho s N) :
    ∀ y ∈ rho.honest, ∀ nd, pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd →
      ∀ B, LiveLease nd.st B →
        Block.Compatible B ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z)) →
        Block.Preceq B N.erase.parent := by
  obtain ⟨hpos, hgs⟩ := recovery_long_slot_bounds p g s hmix
  obtain ⟨hvg, hvh⟩ := recovery_preceding_vote_bounds E g s hgst hpos hgs
  have hs : s - 1 + 1 = s := Nat.sub_add_cancel hpos
  obtain ⟨src, hn, _, hparent, hpc⟩ := pcsa_honest_proposal_state E rho h.base s N hN
  have hp := hN.1
  obtain ⟨H, hH⟩ := recovery_honest_head_exists E rho h.base _ hp (s - 1)
    (h.awake _ hp _ hvg (hvh.trans horizon)) (hvh.trans horizon)
  intro y hy nd hnd B hB hcompat
  have hΔ := p.deltaPos
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith
  have hheads := recovery_live_lock_preceding_heads E rho h hF g s transport hgst
    y hy _ (Or.inr rfl) (hmix.trans htv) nd hnd B hB
  have hroot : Block.Compatible (liveRoot p src.st (proposerPC p src.st)) B := by
    apply pcsa_liveRoot_compatible
    · obtain ⟨a, _, ha⟩ := recovery_postClock_index E rho _ _ src hn
      obtain ⟨b, _, hb⟩ := recovery_postClock_index E rho y _ nd hnd
      have hZa := (hF _ hp (a + 1)).2.1
      have hZb := (hF y hy (b + 1)).2.1
      rw [← ha] at hZa
      rw [← hb] at hZb
      rw [recovery_proposer_base, ← hpc, hZa]
      rw [hZb] at hcompat
      change Block.compatible _ B = true
      rw [Gen.Pure.block_compatible_comm]
      exact hcompat
    · intro row hr ht
      have hc := recovery_live_lock_preceding_heads E rho h hF g s transport hgst
        _ hp _ (Or.inl rfl) hmix src hn row.1 ⟨row, hr, rfl, ht⟩
      exact Gen.Pure.block_compatible_of_common (hc _ H hH) (hheads _ H hH)
  have hh := recovery_proposer_batch_path E rho h hF g (s - 1) transport hgs hvg
    (hvh.trans horizon) B hheads _ hp src (by rw [hs]; exact hn)
  rw [hs] at hh
  rw [hparent]
  exact pcsa_headInTree_covers_of_transfer p src.st _ _ _ _ B hroot
    (fun C _ hCB => hh.1 C hCB) hh.2.1 hh.2.2

end AvailableChain.PCSA.Run
end
