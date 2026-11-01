module
public import AvailableChainFGSAProofs.Proofs.Healing.Frame

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F1.
DC: SAME accepted non-genesis blocks have positive slots. -/
private theorem frame_zero_process (st : State p.n) (hi : CStoreInv p st)
    (o : Wire p.n) (hz : ∀ B ∈ st.base.blocks, B.slot = 0 → B = .genesis) :
    ∀ B ∈ (process p st o).base.blocks, B.slot = 0 → B = .genesis := by
  unfold process
  cases hd : o.decode with
  | none => exact hz
  | some m =>
    cases m with
    | vote s i b => rw [admitHead_base_blocks]; exact hz
    | row i body =>
      dsimp only
      rcases admitRow_eq p st ⟨o.auth, body⟩ with he | he <;> rw [he] <;> exact hz
    | block s N =>
      dsimp only
      cases hn : namedParentHeld st N with
      | false =>
        rw [admitBlock_refused p st s N (Or.inl hn)]
        exact hz
      | true =>
        cases hp : parentFG st N.erase with
        | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]; exact hz
        | some P =>
          cases ha : blockAccepted p st s N P with
          | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
            exact hz
          | true =>
            have hbase := (base_admitProposal_accepts p st hi.toInv0 s N P hp ha).1
            have hpos := (blockAccepted_slot_pos ha).1
            obtain ⟨pool, he, _⟩ := admitBlock_accepted_eq p st s N P hn hp ha
            rw [he]
            dsimp only
            have hnext : ∀ B ∈ st.base.blocks ++ [N.erase], B.slot = 0 → B = .genesis := by
              intro B hB hzero
              rcases List.mem_append.mp hB with hB | hB
              · exact hz B hB hzero
              · have hBb := List.mem_singleton.mp hB
                subst B
                exact (Nat.ne_of_gt hpos hzero).elim
            split
            · rw [hbase]; exact hnext
            · rw [reconcile_eq]
              dsimp only
              rw [hbase]
              exact hnext

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F1.
DC: SAME local steps cannot store a non-genesis block at slot zero. -/
private theorem frame_zero_reachable (st : State p.n) (hr : Reachable p st) :
    ∀ B ∈ st.base.blocks, B.slot = 0 → B = .genesis := by
  induction hr with
  | init => intro B hB _; exact List.mem_singleton.mp hB
  | restart t _ ih => exact ih
  | tick t _ ih => rw [clock_base_blocks]; exact ih
  | deliver o hr ih =>
    exact frame_zero_process p _ (storeBundle_of_reachable p _ hr).cstore o ih

variable {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F1.
DC: INTENTIONAL the zero-label HEAD is the actual scheduled genesis read.
Positive labels use the full-domain witness theorem; frontier one is included.
The witness floor is not asserted for an arbitrary reachable zero-label store. -/
theorem healing_full_witness_all (hs : V2.D.ScheduleWellFormed E rho)
    (crossing : RXing p c E rho) {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s))) :
    let st := ((fgsa p c).clock (rho.stateBefore E i x) (SA.voteTime p.toParams s)).st
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st s ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq K W ∧ (controls p st).lo ≤ (heightView p W).h := by
  by_cases hzero : s = 0
  · subst s
    let old := storeAt p c E rho i x
    let st := clock p old (SA.voteTime p.toParams 0)
    have hr := reachable_stateBefore E rho i x
    have hinv : CStoreInv p st :=
      (storeBundle_postClock E rho i x (SA.voteTime p.toParams 0)).cstore
    have ht := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c)
      E rho hs hi x
    rw [fgsa_clock_now p c (rho.stateBefore E i x)] at ht
    have hslot : old.slot p ≤ 0 := by
      have hh := Internal.slotOf_mono (p := p) ht
      have he : p.slotOf (SA.voteTime p.toParams 0) = 0 := by
        exact slotOf_offset p 0 p.Δ p.deltaPos.le (by linarith [p.deltaPos])
      exact hh.trans_eq he
    have hall : ∀ B ∈ st.fg.TF, B = .genesis := by
      intro B hB
      have hBold : B ∈ old.fg.TF := by simpa only [st, clock_fg] using hB
      have hb := (storeBundle_stateBefore E rho i x).cstore.baseTree _ |>.mpr ⟨B, hBold, rfl⟩
      have hbslot := ((fgsa_stateBefore_bounds E rho hs i x).1 _ hb).trans hslot
      have hgen := frame_zero_reachable p old hr _ hb (Nat.eq_zero_of_le_zero hbslot)
      exact eraseFG_eq_genesis.mp hgen
    have hF : st.fg.F = .genesis := hall _ hinv.fg.Fmem
    have hZ : (controls p st).Z = .genesis := hall _ (Z_mem p st hinv)
    have hH : (controls p st).H ≤ (heightView p (.genesis : FGBlock (Fin p.n))).h := by
      change st.fg.h_max ≤ _
      rw [hinv.fg.hmax]
      apply max_le ?_ ((fgCertificateLaws p).height.one_le_h _)
      apply Finset.sup_le
      intro B hB
      rw [hall B hB]
    have hlo := (KitFG.Controls.lo_le_H (controls p st)).trans hH
    have hK : (.genesis : FGBlock (Fin p.n)) ∈ fullTree p st :=
      (KitFG.mem_filteredFromView _ _ _ _).mpr ⟨hinv.fg.gen, hF ▸ KitFG.preceq_refl _,
        hZ ▸ KitFG.preceq_refl _, .genesis, hinv.fg.gen, KitFG.preceq_refl _, hlo⟩
    exact ⟨.genesis, hK, rfl,
      .genesis, hinv.fg.gen, KitFG.preceq_refl _, hlo⟩
  · exact healing_full_witness p c E rho crossing hx hi (Nat.pos_of_ne_zero hzero)

end AvailableChain.FGSA.Run
end
