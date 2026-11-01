module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockHistory
public import AvailableChainPCSAProofs.Proofs.Recovery.LockTransport
public import AvailableChainPCSAProofs.Proofs.Recovery.CleanSaved

public section

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

omit [DecidableEq V] in
/-- A deadline still live at the mix time has a wholly synchronous write window.
Equality at the mix time is safe because liveness is strict. -/
theorem recovery_postmix_write_window (p : Params) (g s : Slot) (t : Time)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ t)
    (hlive : t < SA.gateTime p.toParams s + pcsaL p) : g ≤ s + 1 - p.k := by
  try delta Slot Time at *
  by_contra h
  have hk := p.kLarge
  have hbound : s ≤ g + p.k - 2 := by omega
  have hi : (s : Int) ≤ (g : Int) + p.k - 2 := by omega
  have hc : ((g + 2 * p.k - 1 : Nat) : Int) = (g : Int) + 2 * p.k - 1 := by omega
  have hd := p.deltaPos
  rw [pcsaL_def] at hlive
  change 4 * p.Δ * ((g + 2 * p.k - 1 : Nat) : Int) + p.Δ ≤ t at hmix
  change t < 4 * p.Δ * (s : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ at hlive
  rw [hc] at hmix
  nlinarith

omit [DecidableEq V] in
/-- Two live write deadlines at one time force their k-windows to overlap. -/
theorem recovery_live_write_windows_overlap (p : Params) (s q : Slot) (t : Time)
    (hs : SA.gateTime p.toParams s ≤ t) (hq : SA.gateTime p.toParams q ≤ t)
    (hsl : t < SA.gateTime p.toParams s + pcsaL p)
    (hql : t < SA.gateTime p.toParams q + pcsaL p) :
    s + 1 - p.k ≤ min s q ∧ q + 1 - p.k ≤ min s q := by
  try delta Slot Time at *
  have hk := p.kLarge
  have hd := p.deltaPos
  rw [pcsaL_def] at hsl hql
  change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ t at hs
  change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ t at hq
  change t < 4 * p.Δ * (s : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ at hsl
  change t < 4 * p.Δ * (q : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ at hql
  have hsq : s < q + p.k := by
    by_contra hn
    have hi : (q : Int) + p.k ≤ (s : Int) := by omega
    nlinarith
  have hqs : q < s + p.k := by
    by_contra hn
    have hi : (s : Int) + p.k ≤ (q : Int) := by omega
    nlinarith
  omega

omit [DecidableEq V] in
/-- At v_(s+1), every live write label lies in the pending write's window. -/
theorem recovery_next_vote_write_in_window (p : Params) (s q : Slot)
    (hq : SA.gateTime p.toParams q ≤ SA.voteTime p.toParams (s + 1))
    (hlive : SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams q + pcsaL p) :
    s + 1 - p.k ≤ q ∧ q < s := by
  try delta Slot Time at *
  have hd := p.deltaPos
  have hc : ((s + 1 : Nat) : Int) = (s : Int) + 1 := by omega
  change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤
    4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at hq
  rw [pcsaL_def] at hlive
  change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
    4 * p.Δ * (q : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ at hlive
  rw [hc] at hq hlive
  constructor
  · by_contra hn
    have hi : (q : Int) + p.k ≤ (s : Int) := by omega
    nlinarith
  · by_contra hn
    have hi : (s : Int) ≤ (q : Int) := by omega
    nlinarith

/-- Saved results at one synchronous label exclude conflicting prefixes.
The reads can have different indices and different writers. -/
theorem recovery_saved_window_overlap_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (g r : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hr : g ≤ r) (horizon : SA.gateTime p.toParams r ≤ rho.horizon)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (a b : Nat) (B C X Y : Block)
    (hX : GridCO.savedGenuine (V2.D.Run.stateBefore E rho a x).st.base r = some (some X))
    (hY : GridCO.savedGenuine (V2.D.Run.stateBefore E rho b y).st.base r = some (some Y))
    (hBX : Block.Preceq B X) (hCY : Block.Preceq C Y) : Block.Compatible B C := by
  have hc := transport.sameLabel r hr horizon x hx y hy X Y
    (recovery_saved_gate_result E rho hs x a r X hX)
    (recovery_saved_gate_result E rho hs y b r Y hY)
  rcases Bool.or_eq_true_iff.mp hc with hc | hc
  · exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_trans hBX hc) hCY
  · exact Gen.Pure.block_compatible_of_common hBX (Gen.Pure.block_preceq_trans hCY hc)

private theorem recovery_overlap_write_at_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (x : V) (t : Time) (nd : Node p) (hn : pcsa_postClock E rho x t = some nd)
    (B : Block) (hB : LiveLease nd.st B) :
    ∃ a s, SA.gateTime p.toParams s ≤ t ∧
      SA.gateTime p.toParams s ≤ rho.horizon ∧
      t < SA.gateTime p.toParams s + pcsaL p ∧
      ∀ r, s + 1 - p.k ≤ r → r ≤ s → ∃ D,
        GridCO.savedGenuine (V2.D.Run.stateBefore E rho a x).st.base r = some (some D) ∧
        Block.Preceq B D := by
  obtain ⟨i, hi, row, hrow, ht, j, hj, s, he, _, hd, _, _, C, _, _, _, _, _, hw⟩ :=
    recovery_live_lock_last_write E rho hs x t nd hn B hB
  have hit := V2.D.Run.tickIdx?_spec hi
  have htime : SA.gateTime p.toParams s ≤ t := by
    have hji : j ≤ i := by omega
    rcases lt_or_eq_of_le hji with hji | rfl
    · obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hit
      have ho := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
      rw [hje, hie] at ho
      exact V2.D.Engine.time_le_of_key_le _ _ ho
    · have heq := congrArg V2.Event.time (Option.some.inj (he.symm.trans hit))
      exact le_of_eq heq
  refine ⟨j + 1, s, htime, (hs.in_horizon _ (List.mem_of_getElem? he)).2, ?_, ?_⟩
  · rwa [← hd]
  · simpa only [hrow] using hw

/-- Every actual live read after the mix has a wholly synchronous saved window.
The source is the derived last write, not a new run premise. -/
theorem recovery_postmix_lock_window (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (g : Slot) (x : V) (t : Time) (nd : Node p)
    (hn : pcsa_postClock E rho x t = some nd) (B : Block) (hB : LiveLease nd.st B)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ t) :
    ∃ a s, g ≤ s + 1 - p.k ∧ SA.gateTime p.toParams s ≤ t ∧
      t < SA.gateTime p.toParams s + pcsaL p ∧
      ∀ r, s + 1 - p.k ≤ r → r ≤ s → ∃ D,
        GridCO.savedGenuine (V2.D.Run.stateBefore E rho a x).st.base r = some (some D) ∧
        Block.Preceq B D := by
  obtain ⟨a, s, ht, _, hl, hw⟩ := recovery_overlap_write_at_read E rho hs x t nd hn B hB
  exact ⟨a, s, recovery_postmix_write_window p g s t hmix hl, ht, hl, hw⟩

/-- Coexisting post-mix locks at arbitrary honest nodes are compatible. -/
theorem recovery_postmix_live_locks_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (g : Slot) (transport : RecoveryLockTransport p c E rho g)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (t : Time) (nx ny : Node p)
    (hxn : pcsa_postClock E rho x t = some nx) (hyn : pcsa_postClock E rho y t = some ny)
    (B C : Block) (hB : LiveLease nx.st B) (hC : LiveLease ny.st C)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ t) : Block.Compatible B C := by
  obtain ⟨a, s, hst, hsh, hsl, hsw⟩ := recovery_overlap_write_at_read E rho hs x t nx hxn B hB
  obtain ⟨b, q, hqt, _, hql, hqw⟩ := recovery_overlap_write_at_read E rho hs y t ny hyn C hC
  have hg := recovery_postmix_write_window p g s t hmix hsl
  obtain ⟨hsr, hqr⟩ := recovery_live_write_windows_overlap p s q t hst hqt hsl hql
  obtain ⟨X, hX, hBX⟩ := hsw (min s q) hsr (min_le_left _ _)
  obtain ⟨Y, hY, hCY⟩ := hqw (min s q) hqr (min_le_right _ _)
  apply recovery_saved_window_overlap_compatible E rho hs g (min s q) transport
    (hg.trans hsr) ?_ x y hx hy a b B C X Y hX hY hBX hCY
  apply le_trans _ hsh
  have hd := p.deltaPos
  have hi : ((min s q : Nat) : Int) ≤ (s : Int) := by exact_mod_cast min_le_left s q
  change 4 * p.Δ * ((min s q : Nat) : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
  nlinarith

/-- At the first HEAD after a synchronous write window, no live lock conflicts
with its target, although the selected write gate has not run yet. -/
theorem recovery_window_next_vote_locks_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (g s : Slot) (transport : RecoveryLockTransport p c E rho g)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (a : Nat) (B : Block)
    (hg : g ≤ s + 1 - p.k)
    (hwindow : ∀ r, s + 1 - p.k ≤ r → r ≤ s → ∃ D,
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho a x).st.base r = some (some D) ∧
      Block.Preceq B D)
    (nd : Node p) (hn : pcsa_postClock E rho y (SA.voteTime p.toParams (s + 1)) = some nd)
    (C : Block) (hC : LiveLease nd.st C) : Block.Compatible B C := by
  obtain ⟨b, q, hqt, hqh, hql, hqw⟩ := recovery_overlap_write_at_read E rho hs y _ nd hn C hC
  obtain ⟨hlo, hhi⟩ := recovery_next_vote_write_in_window p s q hqt hql
  obtain ⟨X, hX, hBX⟩ := hwindow q hlo hhi.le
  have hself : q + 1 - p.k ≤ q := by
    have hk := p.kLarge
    exact Nat.sub_le_iff_le_add.mpr (Nat.add_le_add_left (by omega : 1 ≤ p.k) q)
  obtain ⟨Y, hY, hCY⟩ := hqw q hself le_rfl
  exact recovery_saved_window_overlap_compatible E rho hs g q transport
    (hg.trans hlo) hqh x y hx hy a b B C X Y hX hY hBX hCY

/-- While a synchronous write remains live, every later live lock is
compatible with its target. The read can be before the global mix time. -/
theorem recovery_window_later_locks_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (g s : Slot) (transport : RecoveryLockTransport p c E rho g)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (a : Nat) (B : Block)
    (hg : g ≤ s + 1 - p.k)
    (hwindow : ∀ r, s + 1 - p.k ≤ r → r ≤ s → ∃ D,
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho a x).st.base r = some (some D) ∧
      Block.Preceq B D)
    (t : Time) (ht : SA.gateTime p.toParams s ≤ t)
    (hlive : t < SA.gateTime p.toParams s + pcsaL p)
    (nd : Node p) (hn : pcsa_postClock E rho y t = some nd)
    (C : Block) (hC : LiveLease nd.st C) : Block.Compatible B C := by
  obtain ⟨b, q, hqt, hqh, hql, hqw⟩ := recovery_overlap_write_at_read E rho hs y t nd hn C hC
  obtain ⟨hsr, hqr⟩ := recovery_live_write_windows_overlap p s q t ht hqt hlive hql
  obtain ⟨X, hX, hBX⟩ := hwindow (min s q) hsr (min_le_left _ _)
  obtain ⟨Y, hY, hCY⟩ := hqw (min s q) hqr (min_le_right _ _)
  apply recovery_saved_window_overlap_compatible E rho hs g (min s q) transport
    (hg.trans hsr) ?_ x y hx hy a b B C X Y hX hY hBX hCY
  apply le_trans _ hqh
  have hd := p.deltaPos
  have hi : ((min s q : Nat) : Int) ≤ (q : Int) := by exact_mod_cast min_le_right s q
  change 4 * p.Δ * ((min s q : Nat) : Int) + 6 * p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
  nlinarith

/-- A received PC at or above the unchanged write rank cannot conflict with a
surviving exact row. This also covers a PC already held before the receipt. -/
theorem recovery_survivor_received_pc_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (i j q : Nat) (x : V)
    (row : Block × Nat × Time)
    (hsurv : ∀ a, j < a → a ≤ i →
      row ∈ (V2.D.Run.stateBefore E rho a x).st.base.obligations ∧
      leaseRank (V2.D.Run.stateBefore E rho a x).st row.1 =
        leaseRank (V2.D.Run.stateBefore E rho i x).st row.1)
    (hjq : j < q) (hqi : q ≤ i) (pc : PC p.n)
    (hpc : pc ∈ (V2.D.Run.stateBefore E rho q x).st.pcs)
    (hrank : rankAtLeast pc
      (leaseRank (V2.D.Run.stateBefore E rho i x).st row.1) = true) :
    Block.Compatible pc.target row.1 := by
  obtain ⟨hr, he⟩ := hsurv q hjq hqi
  exact recovery_stored_lock_rank_compatible p _ (pcsa_reachable_stateBefore E rho q x)
    row hr pc hpc (by rwa [he])

/-- Strict PC relay rules out a conflicting PC whenever the lock interval
contains its receipt deadline. The caller must establish the rank bound. -/
theorem recovery_survivor_relay_pc_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (g : Slot) (transport : RecoveryLockTransport p c E rho g)
    (i j : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (row : Block × Nat × Time)
    (hsurv : ∀ a, j < a → a ≤ i →
      row ∈ (V2.D.Run.stateBefore E rho a x).st.base.obligations ∧
      leaseRank (V2.D.Run.stateBefore E rho a x).st row.1 =
        leaseRank (V2.D.Run.stateBefore E rho i x).st row.1)
    (t : Time)
    (hcut : ∃ s, t = SA.earlyTime p.toParams s ∨ t = SA.voteTime p.toParams s)
    (ht : E.t_GST ≤ t) (horizon : t + p.Δ ≤ rho.horizon)
    (hlo : j < V2.D.Run.idxBefore rho (t + p.Δ))
    (hhi : V2.D.Run.idxBefore rho (t + p.Δ) ≤ i)
    (pc : PC p.n) (hpc : pc ∈ (V2.D.Run.stateBeforeTime E rho t y).st.pcs)
    (hrank : rankAtLeast pc
      (leaseRank (V2.D.Run.stateBefore E rho i x).st row.1) = true) :
    Block.Compatible pc.target row.1 := by
  have hk := transport.pcReceipt t hcut ht horizon y hy x hx pc hpc
  obtain ⟨D, hD, hslot, htarget⟩ := (KeyHeld_def _ _ _).mp hk
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hD
  have hge : rankAtLeast D
      (leaseRank (V2.D.Run.stateBefore E rho i x).st row.1) = true := by
    simpa only [rankAtLeast_def, hslot, htarget] using hrank
  rw [← htarget]
  exact recovery_survivor_received_pc_compatible E rho i j _ x row hsurv hlo hhi D hD hge

/-- A PC from the first later HEAD read reaches the writer before d_s.
A conflicting PC at the write rank would block the selected write. -/
theorem recovery_write_relay_pc_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (g s : Slot)
    (transport : RecoveryLockTransport p c E rho g)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (k : Nat) (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)))
    (hafter : E.t_GST ≤ SA.voteTime p.toParams (s + 1))
    (B : Block) (rank : Option PCRank)
    (hwrite : leaseWriteOK
      (clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams s)).pcs
      rank B = true)
    (pc : PC p.n)
    (hpc : pc ∈ (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams (s + 1)) y).st.pcs)
    (hrank : rankAtLeast pc rank = true) : Block.Compatible pc.target B := by
  have htime : SA.voteTime p.toParams (s + 1) + p.Δ = SA.gateTime p.toParams s := by
    change (4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ) + p.Δ =
      4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    ring
  have horizon : SA.voteTime p.toParams (s + 1) + p.Δ ≤ rho.horizon := by
    rw [htime]
    exact (hs.in_horizon _ (List.mem_of_getElem? hk)).2
  have held := transport.pcReceipt _ ⟨s + 1, Or.inr rfl⟩ hafter horizon y hy x hx pc hpc
  obtain ⟨D, hD, hslot, htarget⟩ := (KeyHeld_def _ _ _).mp held
  rw [htime, ← V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs hnr hk] at hD
  rw [clockPre_pcs] at hwrite
  have hc := (leaseWriteOK_iff _ _ _).mp hwrite D hD
    (by simpa only [rankAtLeast_def, hslot, htarget] using hrank)
  change Block.compatible pc.target B = true
  simpa only [htarget] using hc

end AvailableChain.PCSA.Run
end
