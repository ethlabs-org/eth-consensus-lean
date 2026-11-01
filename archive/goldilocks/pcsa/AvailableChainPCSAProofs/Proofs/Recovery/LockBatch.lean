module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockCounts
public import AvailableChainPCSAProofs.Proofs.Recovery.FirstHonestSlot

public section

namespace AvailableChain.PCSA

/-- With no pinned domain and a stage-one frame, active resolution is ordinary resolution. -/
theorem recovery_active_resolution {p : Params} (st : State p.n) (hF : st.fg.F = .genesis)
    (hd : st.base.headDomain = none) (o : GridCO.Wire p.n .root) :
    GridCO.resolvedHead? (actView st) o = GridCO.resolvedHead? st.base o := by
  delta GridCO.resolvedHead?
  rw [pcsa_actView_blocks_of_genesis st hF]
  have he : GridCO.resolutionTree (actView st) = GridCO.resolutionTree st.base := by
    change (some (st.base.headDomain.getD st.base.blocks)).getD (actView st).blocks =
      st.base.headDomain.getD st.base.blocks
    simp only [hd, Option.getD_none, Option.getD_some]
  rw [he]

/-- Every resolved support input passes the label bound in the actual voter merge. -/
theorem recovery_voter_support_slot (p : Params) (st : State p.n)
    (hF : st.fg.F = .genesis) (hd : st.base.headDomain = none)
    (s : Slot) (o : GridCO.Wire p.n .root) (H : Block)
    (ho : o ∈ headSupport p st s) (hr : GridCO.resolvedHead? st.base o = some H) :
    H.slot ≤ (GridCO.headLabel? o).getD 0 := by
  delta headSupport at ho
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with hf | hc
  · have hh := (List.mem_filter.mp hf).2
    unfold GridCO.resolvedBefore at hh
    rw [recovery_active_resolution st hF hd o, hr] at hh
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hh).1).1
  · have hh := (List.mem_filter.mp hc).2
    obtain ⟨hl, ht⟩ := Bool.and_eq_true_iff.mp hh
    rw [hr] at ht
    rw [beq_iff_eq.mp hl]
    exact of_decide_eq_true ht

/-- A strict seat majority in actual raw/support pools gives every prefix a dominant path. -/
theorem recovery_batch_scores (p : Params) (st : State p.n)
    (raw sup : List (GridCO.Wire p.n .root)) (B : Block) (Hon : Finset (Fin p.n))
    (hsub : sup ⊆ raw) (hcard : p.n < 2 * Hon.card)
    (hclean : ∀ i ∈ Hon, GridCO.equivocates raw i = false)
    (hbatch : ∀ i ∈ Hon, Gen.AC.Root.poolSupports st.base.blocks sup i B = true) :
    GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw sup B ∧
    ∀ D, Block.compatible B D = false →
      GridCO.goldfishScore st.base.blocks raw sup D <
        GridCO.goldfishScore st.base.blocks raw sup B := by
  have hle : Hon.card ≤ p.n := by simpa only [Fintype.card_fin] using Finset.card_le_univ Hon
  have hother : ((GridCO.seats p.n raw).toFinset \ Hon).card ≤ p.n - Hon.card := by
    calc
      _ ≤ (Finset.univ \ Hon).card := Finset.card_le_card (Finset.sdiff_subset_sdiff_left Hon
        (Finset.subset_univ _))
      _ = p.n - Hon.card := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin]
  have hh := Gen.AC.Root.batch_counts st.base.blocks raw raw sup Hon Hon.card
    (p.n - Hon.card) B (List.Subset.refl _) hsub rfl hclean hbatch hother ⟨by omega⟩
  have hb := hh.2.2.1 B (Gen.Pure.block_preceq_refl B)
  exact ⟨hb.2, fun D hD => lt_of_le_of_lt (hh.2.2.2.1 D hD) (by omega)⟩

end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- An awake honest node has its scheduled HEAD read. -/
theorem recovery_honest_head_exists (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (x : V) (hx : x ∈ rho.honest) (s : Slot)
    (hw : E.awake x (SA.voteTime p.toParams s) = true)
    (ht : SA.voteTime p.toParams s ≤ rho.horizon) :
    ∃ H, HonestHeadAt p c E rho x s H := by
  have hp : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.voteTime p.toParams s := by
    have hd := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    positivity
  have hm := h.valid.tick_total x hx _ hp hz ht
  have hs : (V2.D.Run.tickIdx? rho x (SA.voteTime p.toParams s)).isSome = true := by
    delta V2.D.Run.tickIdx?
    rw [List.findIdx?_isSome]
    apply List.any_eq_true.mpr
    exact ⟨.tick x (SA.voteTime p.toParams s), hm, decide_eq_true ⟨rfl, rfl⟩⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨headVote p (clock p (V2.D.Run.stateBefore E rho k x).st
    (SA.voteTime p.toParams s)) s, hx, hw, ?_⟩
  rw [pcsa_voteHeadAt_def, pcsa_postClock_def, pcsa_preTick_def, hk]
  rfl

/-- The quarter cap gives a strict majority of honest seats at every label. -/
theorem recovery_honest_seats [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (s : Slot) :
    ∃ Hon : Finset (Fin p.n),
      (∀ i, i ∈ Hon ↔ rho.seatOf (.base (.head s)) i ∈ rho.honest) ∧
      p.n < 2 * Hon.card := by
  classical
  let e : Fin p.n ≃ V := Equiv.ofBijective _ (h.base.cstar (.base (.head s)) trivial)
  refine ⟨rho.honest.image e.symm, ?_, ?_⟩
  · intro i
    change i ∈ rho.honest.image e.symm ↔ e i ∈ rho.honest
    simp only [Finset.mem_image, e.symm_apply_eq]
    exact ⟨fun ⟨_, hy, he⟩ => he ▸ hy, fun hi => ⟨e i, hi, rfl⟩⟩
  · rw [Finset.card_image_of_injective _ e.symm.injective]
    have hn : p.n = Fintype.card V := h.base.cstar.seats_eq (ℓ := .base (.head s)) trivial
    have hcap : 4 * (Gen.V2.Duty.faulty rho).card ≤ p.n := h.quarterCap
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, ← hn] at hcap
    have hh : rho.honest.card ≤ p.n := by rw [hn]; exact Finset.card_le_univ _
    have hp := p.nPos
    omega

/-- The actual preceding honest HEAD batch supplies the next voter path and counts. -/
theorem recovery_voter_batch_path [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g r : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hg : g ≤ r) (hgst : E.t_GST ≤ SA.voteTime p.toParams r)
    (horizon : SA.voteTime p.toParams r ≤ rho.horizon)
    (B : Block) (hheads : ∀ x H, HonestHeadAt p c E rho x r H → Block.Preceq B H)
    (y : V) (hy : y ∈ rho.honest) (dst : Node p)
    (hn : pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst) :
    (∀ C, Block.Preceq C B → C ∈ erasedList dst.st
      (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1)))) ∧
    GridCO.voterCount (headVotes p dst.st (r + 1)) <
      2 * GridCO.goldfishScore dst.st.base.blocks
        (headVotes p dst.st (r + 1)) (headSupport p dst.st (r + 1)) B ∧
    ∀ D, Block.compatible B D = false →
      GridCO.goldfishScore dst.st.base.blocks
        (headVotes p dst.st (r + 1)) (headSupport p dst.st (r + 1)) D <
      GridCO.goldfishScore dst.st.base.blocks
        (headVotes p dst.st (r + 1)) (headSupport p dst.st (r + 1)) B := by
  obtain ⟨Hon, hHon, hcard⟩ := recovery_honest_seats E rho h r
  obtain ⟨hf, hd⟩ := recovery_read_count_domain E rho hF y hy _ dst hn
  have batch (i : Fin p.n) (hi : i ∈ Hon) :
      ∃ H, HonestHeadAt p c E rho (rho.seatOf (.base (.head r)) i) r H ∧
        (⟨.seat r i, .head H.root⟩ : GridCO.Wire p.n .root) ∈ headSupport p dst.st (r + 1) ∧
        GridCO.equivocates (headVotes p dst.st (r + 1)) i = false ∧
        Gen.AC.Root.voteSupports dst.st.base.blocks B ⟨.seat r i, .head H.root⟩ = true ∧
        (∀ C, Block.Preceq C B → C ∈ erasedList dst.st
          (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1)))) := by
    have hx := (hHon i).mp hi
    obtain ⟨H, hH⟩ := recovery_honest_head_exists E rho h.base _ hx r
      (h.awake _ hx _ hgst horizon) horizon
    have hh := transport.honestVoterInputs r hg _ H hH i rfl y hy dst hn
    refine ⟨H, hH, hh.1, hh.2.2.1, ?_, ?_⟩
    · exact recovery_resolved_support dst.st hd _ H B hh.2.2.2.1
        (recovery_voter_support_slot p dst.st hf hd _ _ H hh.1 hh.2.2.2.1) (hheads _ H hH)
    · intro C hCB
      exact hh.2.2.2.2 C (Gen.Pure.block_preceq_trans hCB (hheads _ H hH))
  have hpos : 0 < Hon.card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨_, _, _, _, _, hpath⟩ := batch i hi
  refine ⟨hpath, recovery_batch_scores p dst.st _ _ B Hon
    (recovery_headSupport_subset E rho h.base y _ dst hn _) hcard ?_ ?_⟩
  · intro i hi
    obtain ⟨_, _, _, hc, _⟩ := batch i hi
    exact hc
  · intro i hi
    obtain ⟨H, _, hm, _, hs, _⟩ := batch i hi
    exact (Gen.AC.Root.vote_pool_support_witness _ _ i B).mpr ⟨_, hm, rfl, hs⟩

end AvailableChain.PCSA.Run
end
