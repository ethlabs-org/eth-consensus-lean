module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingPending
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingCover

public section

/-! Plan O-ARM §4 field 9, §6.2 step 8, §6.3. The pre-gate input of every
actual pending gate tick: no saved result yet, a raw result above `D`, leases
below `D`, B active, and the fast count or the slow saved window. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan O-ARM §4 field 9, §6.2 step 8, §6.3. Class (iii). DC: INTENTIONAL;
the stored batch at the pending gate tick gives strict majorities at the F
anchor and at `D` (`fgsa_gate_batch_premises`), so the raw result covers `D`
(`fgsa_confirmationFrom_covers_majority`). In fast mode the batch counts at
least τ seats for every prefix of `D`. The slow clause is an input. -/
theorem arming_pending_input [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    {l : Slot} {B D : Block} {Dh : FGBlock (Fin p.n)} (hBD : Block.Preceq B D)
    (hpartv : Gen.Pure.Batch
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (l + 1))).card
      (Gen.V2.Duty.faulty rho).card)
    (hprefix : ArmingPrefixState p c E rho l D Dh)
    (hbatchF : ArmingBatchState p c E rho l D) (fast : Bool)
    (hfast : fast = true → SA.releaseThreshold p.toParams ≤
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (l + 1))).card)
    (hslow : fast = false → ∀ i y, IsGateTick p c rho i y (l + 1) → y ∈ rho.honest →
      p.k ≤ l + 2 ∧ ∀ a < p.k - 1, ∃ Ca,
        GridCO.savedGenuine (FGSA.clockPre p (storeAt p c E rho i y)
          (SA.gateTime p.toParams (l + 1))).base (l + 1 - (a + 1)) = some (some Ca) ∧
        Block.Preceq B Ca) :
    ∀ i y, IsGateTick p c rho i y (l + 1) → y ∈ rho.honest →
      let P := FGSA.clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams (l + 1))
      GridCO.savedGenuine P.base (l + 1) = none ∧
      (∃ Cj, SA.Root.confirmationFrom p.toParams (eraseFG P.fg.F) (FGSA.actView P) (l + 1) =
        some Cj ∧ Block.Preceq D Cj) ∧
      (∀ row ∈ (FGSA.actView P).obligations, Block.Preceq row.1 D) ∧
      B ∈ (FGSA.actView P).blocks ∧ Block.Compatible (F_at p c E rho i y) B ∧
      (fast = true → SA.releaseThreshold p.toParams ≤
        SA.Root.prefixSupport p.toParams (FGSA.actView P) (l + 1) B) ∧
      (fast = false → p.k ≤ l + 2 ∧ ∀ a < p.k - 1, ∃ Ca,
        GridCO.savedGenuine P.base (l + 1 - (a + 1)) = some (some Ca) ∧
        Block.Preceq B Ca) := by
  intro i y hi hy P
  have hs := hE.toScheduleWellFormed
  have hiE : rho.events[i]? = some (.tick y (SA.gateTime p.toParams (l + 1))) := hi
  have hst := arming_tick_store hs hN hiE
  obtain ⟨hFD, -, -, -, -, hobl⟩ :=
    hprefix _ y le_rfl (arming_idxBefore_le_length rho _) hy
  have hFi : Block.Preceq (F_at p c E rho i y) D := by
    change Block.Preceq (eraseFG (storeAt p c E rho i y).fg.F) D
    rw [hst]
    exact hFD
  have hPF : eraseFG P.fg.F = F_at p c E rho i y := by
    change eraseFG (clockPre p (storeAt p c E rho i y) _).fg.F =
      eraseFG (storeAt p c E rho i y).fg.F
    rw [clockPre_fg]
  have hinvP : CStoreInv p P :=
    cstoreInv_clockPre p _ (storeBundle_stateBefore E rho i y).cstore _
  obtain ⟨H, hH, hcard⟩ := arming_head_seats (E := E) hC (l + 1)
  have hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card := hcard ▸ hpartv
  have hgt : SA.earlyTime p.toParams (l + 1) < SA.gateTime p.toParams (l + 1) :=
    (arming_early_next p l).trans_lt ((arming_gate_lt_iff p l (l + 1)).mpr (Nat.lt_succ_self l))
  have hheads : ∀ k ∈ H, ∃ K t,
      rho.seatOf (.base (.head (l + 1))) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) k)
        (ofHead p ⟨.seat (.head (l + 1)) k, K.root⟩) t ∧
      baseVote (⟨.seat (.head (l + 1)) k, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i y).base.votes ∧
      K ∈ (actView P).blocks ∧ K.slot ≤ l + 1 ∧
      GridCO.stampVote (actView P) (baseVote (⟨.seat (.head (l + 1)) k, K.root⟩ : HeadWire p.n)) <
        GridCO.earlyTime p.toParams.engine (l + 1) ∧
      GridCO.stampBlock (actView P) K < GridCO.earlyTime p.toParams.engine (l + 1) ∧
      Block.Preceq (eraseFG P.fg.F) K ∧ Block.Preceq D K := by
    intro w hw
    obtain ⟨hyw, haw⟩ := (hH w).mp hw
    obtain ⟨K, _, _, _, hem, hDK, hslot, _, hv, hKb, hvs, hbs⟩ :=
      arming_batch_at hs hN hbatchF hy hiE hgt w hyw haw
    have hFK : Block.Preceq (eraseFG P.fg.F) K := hPF ▸ block_preceq_trans hFi hDK
    refine ⟨K, _, hyw, hem, hv, ?_, hslot, ?_, ?_, hFK, hDK⟩
    · apply (actView_blocks P K).mpr
      refine ⟨?_, block_compatible_of_common (block_preceq_refl K) hFK⟩
      change K ∈ (clockPre p (storeAt p c E rho i y) _).base.blocks
      rw [(clockPre_fields p _ _).2.1]
      exact hKb
    · change GridCO.stampVote (clockPre p (storeAt p c E rho i y) _).base _ < _
      have hkey : baseVote (⟨.seat (.head (l + 1)) w, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i y).base.voteStamp.map Prod.fst := by
        change _ ∈ (V2.D.Run.stateBefore E rho i y).st.base.voteStamp.map Prod.fst
        rw [fgsa_vote_stamp_keys E rho i y]
        exact hv
      rw [inclusion_stampVote_of_prefix (by rw [(clockPre_stamps p _ _).2]) hkey]
      exact hvs
    · change GridCO.stampBlock (clockPre p (storeAt p c E rho i y) _).base K < _
      have hkey : K ∈ (storeAt p c E rho i y).base.blockStamp.map Prod.fst := by
        change K ∈ (V2.D.Run.stateBefore E rho i y).st.base.blockStamp.map Prod.fst
        rw [(storeBundle_stateBefore E rho i y).«meta».stampKeys]
        exact hKb
      rw [inclusion_stampBlock_of_prefix (by rw [(clockPre_stamps p _ _).1]) hkey]
      exact hbs
  have hcover := fgsa_gate_batch_premises E rho hE hC i y (l + 1) D H hbatch
    (fun q hq haw => (hH q).mpr ⟨hq, haw⟩) hheads
  obtain ⟨Cj, hCj, hDCj⟩ := fgsa_confirmationFrom_covers_majority p (actView P)
    (eraseFG P.fg.F) D (l + 1) D.root (block_compatible_of_common (hPF ▸ hFi) (block_preceq_refl D))
    hcover.1 hcover.2.1 hcover.2.2
  obtain ⟨w0, hw0⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbatch.lt)
  obtain ⟨K0, _, _, _, _, hK0, _, _, _, _, hDK0⟩ := hheads w0 hw0
  refine ⟨?_, ⟨Cj, hCj, hDCj⟩, ?_,
    actView_ancestor_closed p P hinvP hK0 (block_preceq_trans hBD hDK0),
    block_compatible_of_common hFi hBD, ?_, fun hf => hslow hf i y hi hy⟩
  · change GridCO.savedGenuine (clockPre p (storeAt p c E rho i y) _).base (l + 1) = none
    rw [savedGenuine_congr (clockPre_genuine p _ _)]
    exact fgsa_gate_fresh E rho hs hiE
  · intro row hrow
    have hm : row ∈ (storeAt p c E rho i y).base.obligations :=
      (clockPre_obligations_sublist p _ _).subset hrow
    rw [hst] at hm
    exact hobl row hm
  · intro hf
    have hsupp : ∀ k ∈ H, Gen.AC.Root.poolSupports (actView P).blocks
        (GridCO.cleanSupport p.toParams.engine (actView P) (l + 1)) k B = true := by
      intro k hk
      obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, _, hDK⟩ := hheads k hk
      exact fgsa_active_support_of_receipt E rho hE i y (l + 1) k K B t hh he hv hK hslot hvs
        hbs (block_preceq_trans hBD hDK)
    have hc := Gen.AC.Root.batch_counts (actView P).blocks
      (GridCO.lateVotes p.toParams.engine (actView P) (l + 1))
      (GridCO.cleanSupport p.toParams.engine (actView P) (l + 1))
      (GridCO.cleanSupport p.toParams.engine (actView P) (l + 1))
      H H.card (Gen.V2.Duty.faulty rho).card B
      (fun _ ho => fgsa_early_subset_late p _ _ (List.mem_filter.mp ho).1)
      (fun _ ho => ho) rfl (fun q _ => fgsa_cleanSupport_no_equivocation p _ _ q)
      hsupp (fgsa_late_rest_bound E rho hC hE i y (l + 1) H
        (fun q hq haw => (hH q).mpr ⟨hq, haw⟩)) hbatch
    change _ ≤ GridCO.goldfishScoreOn (GridCO.resolutionTree (actView P)) (actView P).blocks
      (GridCO.cleanSupport p.toParams.engine (actView P) (l + 1))
      (GridCO.cleanSupport p.toParams.engine (actView P) (l + 1)) B
    rw [actView_score p P hinvP
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i y))]
    exact (hcard ▸ hfast hf).trans (hc.2.2.1 B (block_preceq_refl B)).1

end AvailableChain.FGSA.Run
end
