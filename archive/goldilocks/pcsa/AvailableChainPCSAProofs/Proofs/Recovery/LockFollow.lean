module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockBatch

public section

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Compatible selected PCs and live locks give a compatible voter root. -/
theorem recovery_voter_root_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hF : StageOneFrame p c E rho)
    (y : V) (hy : y ∈ rho.honest) (r : Slot) (nd : Node p)
    (hn : pcsa_postClock E rho y (SA.voteTime p.toParams r) = some nd) (B : Block)
    (hpcs : ∀ C, voterPC p nd.st r = some C → Block.Compatible C.target B)
    (hlocks : ∀ C, LiveLease nd.st C → Block.Compatible B C) :
    Block.Compatible (liveRoot p nd.st (voterPC p nd.st r)) B := by
  obtain ⟨i, _, he⟩ := recovery_postClock_index E rho y _ nd hn
  have hf := hF y hy (i + 1)
  rw [← he] at hf
  apply pcsa_liveRoot_compatible
  · cases hc : voterPC p nd.st r with
    | none =>
      change Block.Compatible (eraseFG (controls p nd.st).Z) B
      rw [hf.2.1]
      exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_genesis_preceq B)
        (Gen.Pure.block_preceq_refl B)
    | some C =>
      change Block.Compatible (if frameActive p nd.st C then C.target else _) B
      split
      · exact hpcs C hc
      · rw [hf.2.1]
        exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_genesis_preceq B)
          (Gen.Pure.block_preceq_refl B)
  · intro row hr ht
    change Block.compatible row.1 B = true
    rw [Gen.Pure.block_compatible_comm]
    exact hlocks row.1 ⟨row, hr, rfl, ht⟩

/-- F′: each honest HEAD after a selected write covers its target while the exact
row and rank survive through the later read. Receipt at e_r must precede that read. -/
theorem recovery_lock_follow [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g s S : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g)
    (i k : Nat) (x : V) (hx : x ∈ rho.honest) (row : Block × Nat × Time)
    (t : Time) (hi : rho.events[i]? = some (.tick x t))
    (hstart : SA.proposalTime p.toParams S ≤ t)
    (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)))
    (hlive : t < SA.gateTime p.toParams s + pcsaL p)
    (hsurv : ∀ a, k < a → a ≤ i + 1 →
      row ∈ (V2.D.Run.stateBefore E rho a x).st.base.obligations ∧
      leaseRank (V2.D.Run.stateBefore E rho a x).st row.1 =
        leaseRank (V2.D.Run.stateBefore E rho (i + 1) x).st row.1)
    (hrank : leaseRank (V2.D.Run.stateBefore E rho (i + 1) x).st row.1 =
      gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
        (SA.gateTime p.toParams s)) s)
    (hwrite : leaseWriteOK
      (clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams s)).pcs
      (gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
        (SA.gateTime p.toParams s)) s) row.1 = true)
    (hwindow : ∀ q, s + 1 - p.k ≤ q → q ≤ s → ∃ D,
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho (k + 1) x).st.base q = some (some D) ∧
      Block.Preceq row.1 D)
    (hfloor : g ≤ s + 1 - p.k) :
    ∀ r, s < r → r < S → ∀ y H, HonestHeadAt p c E rho y r H → Block.Preceq row.1 H := by
  try delta Slot Time at *
  have hsched := h.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hwin : s + 1 - p.k ≤ s := by have hh := p.kLarge; omega
  have hgs : g ≤ s := hfloor.trans hwin
  have hgi : (g : Int) ≤ (s : Int) := by exact_mod_cast hgs
  have hge : E.t_GST ≤ SA.earlyTime p.toParams s := by
    apply hgst.trans
    change 4 * p.Δ * (g : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    nlinarith
  have hth : t ≤ rho.horizon := (hsched.in_horizon _ (List.mem_of_getElem? hi)).2
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hsr hrS y H hH
    have hy := hH.1
    have hhead := hH.2.2
    rw [pcsa_voteHeadAt_def] at hhead
    obtain ⟨nd, hn, hhead⟩ := Option.map_eq_some_iff.mp hhead
    have hrs : (r : Int) + 1 ≤ (S : Int) := by exact_mod_cast hrS
    have hvr : SA.voteTime p.toParams r + p.Δ < t := by
      change 4 * p.Δ * (r : Int) + p.Δ + p.Δ < t
      change 4 * p.Δ * (S : Int) ≤ t at hstart
      nlinarith
    have hvg : E.t_GST ≤ SA.voteTime p.toParams r := by
      apply hgst.trans
      have hgr : (g : Int) ≤ (r : Int) := by exact_mod_cast (hgs.trans hsr.le)
      change 4 * p.Δ * (g : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + p.Δ
      nlinarith
    have hroot : Block.Compatible (liveRoot p nd.st (voterPC p nd.st r)) row.1 := by
      apply recovery_voter_root_compatible E rho hF y hy r nd hn row.1
      · intro C hC
        by_cases he : r = s + 1
        · subst r
          exact recovery_write_voter_compatible E rho h.base hF g s transport k x y hx hy
            hk hge row.1 hwrite nd hn C hC
        · have hsr' : (s : Int) + 2 ≤ (r : Int) := by omega
          have hlo : k < V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ) := by
            apply (Gen.V2.Duty.index_lt_idxBefore_iff hsched hk _).mpr
            change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (r : Int) + p.Δ + p.Δ
            nlinarith
          have hhi : V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ) ≤ i + 1 := by
            apply Nat.le_of_not_lt
            intro hlt
            have hh := (Gen.V2.Duty.index_lt_idxBefore_iff hsched hi
              (SA.voteTime p.toParams r + p.Δ)).mp (by omega)
            exact (not_lt_of_ge hvr.le) hh
          exact recovery_survivor_voter_compatible E rho h.base hF g s r hsr transport
            (i + 1) k x y hx hy row hsurv hrank hge (hvr.le.trans hth) hlo hhi nd hn C hC
      · intro C hC
        by_cases he : r = s + 1
        · subst r
          exact recovery_window_next_vote_locks_compatible E rho hsched g s transport
            x y hx hy (k + 1) row.1 hfloor hwindow nd hn C hC
        · have hsr' : (s : Int) + 2 ≤ (r : Int) := by omega
          apply recovery_window_later_locks_compatible E rho hsched g s transport
            x y hx hy (k + 1) row.1 hfloor hwindow _ ?_ ?_ nd hn C hC
          · change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (r : Int) + p.Δ
            nlinarith
          · exact lt_trans (by linarith : SA.voteTime p.toParams r < t) hlive
    rw [← hhead]
    by_cases he : r = s + 1
    · subst r
      obtain ⟨X, hX, hBX⟩ := hwindow s hwin le_rfl
      exact recovery_gate_prefix_next_head E rho h.base hF g s transport hgs
        (hsched.in_horizon _ (List.mem_of_getElem? hk)).2 x y hx hy X row.1
        (recovery_saved_gate_result E rho hsched x (k + 1) s X hX) hBX nd hn hroot
    · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      have hsq : s < q := by omega
      have hqg : E.t_GST ≤ SA.voteTime p.toParams q := by
        apply hgst.trans
        have hgr : (g : Int) ≤ (q : Int) := by exact_mod_cast (hgs.trans hsq.le)
        change 4 * p.Δ * (g : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + p.Δ
        nlinarith
      have hqh : SA.voteTime p.toParams q ≤ rho.horizon := by
        apply le_trans _ hth
        change 4 * p.Δ * (q : Int) + p.Δ ≤ t
        change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ + p.Δ < t at hvr
        push_cast at hvr
        linarith
      obtain ⟨hpath, hmaj, hdom⟩ := recovery_voter_batch_path E rho h hF g q transport
        (hgs.trans hsq.le) hqg hqh row.1 (ih q (Nat.lt_succ_self q) hsq (by omega))
        y hy nd hn
      change Block.Preceq row.1 (if q + 1 = 0 then .genesis else _)
      rw [ite_eq_right (Nat.succ_ne_zero q)]
      exact pcsa_headInTree_covers_of_transfer p nd.st _ _ _ _ row.1 hroot
        (fun C _ hCB => hpath C hCB) hmaj hdom

/-- A live lock after the mix is covered by the actual preceding honest HEAD batch.
The last write, full saved window, and survival interval are derived from the run. -/
theorem recovery_live_lock_preceding_heads [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g S : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g)
    (x : V) (hx : x ∈ rho.honest) (t : Time)
    (ht : t = SA.proposalTime p.toParams S ∨ t = SA.voteTime p.toParams S)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ t)
    (nd : Node p) (hn : pcsa_postClock E rho x t = some nd)
    (B : Block) (hB : LiveLease nd.st B) :
    ∀ y H, HonestHeadAt p c E rho y (S - 1) H → Block.Preceq B H := by
  try delta Slot Time at *
  have hsched := h.base.valid.toScheduleWellFormed
  obtain ⟨i, hi, row, hrow, hlive, k, hki, s, hk, hsurv, hd, _, _, C, _, _, hw, _, hr, hwindow⟩ :=
    recovery_live_lock_last_write E rho hsched x t nd hn B hB
  change Nat at s
  have hit := V2.D.Run.tickIdx?_spec hi
  have htime : SA.gateTime p.toParams s ≤ t := by
    rcases lt_or_eq_of_le (by omega : k ≤ i) with hlt | rfl
    · obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hit
      have ho := (List.pairwise_iff_getElem.mp hsched.sorted) k i hkl hil hlt
      rw [hke, hie] at ho
      exact V2.D.Engine.time_le_of_key_le _ _ ho
    · exact le_of_eq (congrArg V2.Event.time (Option.some.inj (hk.symm.trans hit)))
  rw [hd] at hlive
  have hfloor := recovery_postmix_write_window p g s t hmix hlive
  have horder := recovery_gate_before_read p S s t ht htime
  have hstart : SA.proposalTime p.toParams S ≤ t := by
    rcases ht with rfl | rfl
    · exact le_rfl
    · have hΔ := p.deltaPos
      change 4 * p.Δ * (S : Int) ≤ 4 * p.Δ * (S : Int) + p.Δ
      linarith
  have hlo : s < S - 1 := by
    change s + 2 ≤ S at horder
    omega
  have hhi : S - 1 < S := by
    change s + 2 ≤ S at horder
    omega
  simpa only [hrow] using recovery_lock_follow E rho h hF g s S transport hgst i k x hx
    row t hit hstart hk hlive hsurv hr hw hwindow hfloor (S - 1) hlo hhi

end AvailableChain.PCSA.Run
end
