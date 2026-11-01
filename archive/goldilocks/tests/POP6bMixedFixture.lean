module
import all AvailableChainFGCompose.Tests.P0d5db
import AvailableChainFGCompose.Proofs.Population.FrontierSearchFull
import AvailableChainFGCompose.Proofs.Healing.Reset

noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6bMixed
open AvailableChain.SimplexFG AvailableChain.KitFG
open P0d5db

-- Generic event-fold control: one FG seat at 9, honest proposer and receiver 7.
private def entrySlot (s : Nat) : Nat := 4 * (s / 4)
private def heightAt (s : Nat) : Nat := 1 + s / 4
private def wireAt (r : Nat) : Row (Fin 1) :=
  ⟨0, .vote (heightAt (2 * r))
    (if entrySlot (2 * r) = 0 then genesisRoot else ⟨300 + entrySlot (2 * r)⟩) true, none⟩
private def chain : Nat → FGBlock (Fin 1)
  | 0 => .genesis
  | s + 1 => .node (chain s) (s + 1) ⟨300 + s + 1⟩ 0
      ((List.range ((s + 1) / 2)).map wireAt)
private abbrev allRows : List (Row (Fin 1)) := (List.range 32).map wireAt
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Time
  Duty := Time
  signLabel t := if t % 8 = 6 then 6 else t
  seats _ := 1
  Payload := Row (Fin 1) ⊕ FGBlock (Fin 1)
  Durable := Nat
  init := 0
  clock st _ := st
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act _ t _ := if t % 8 = 6 then some (.inl (wireAt (t.toNat / 8)))
    else if t % 4 = 0 ∧ 4 ≤ t ∧ t ≤ 256 then some (.inr (chain (t.toNat / 4)))
    else none
  gossip _ _ := []
  process st o := match o.payload with | .inr X => max st X.slot | .inl _ => st
  selfVisible _ := true
  recordOwn st _ := st
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False
private abbrev env : Generic.Env Nat := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
private abbrev delivery (s x : Nat) : V2.Event Nat protocol.Object :=
  .deliver x ⟨.none, .inr (chain s)⟩ (4 * (s : Time))
private def eventShape : List (Bool × Nat × Nat) :=
  (List.range 257).flatMap fun t =>
    [(true, 7, t), (true, 9, t)] ++
      (if 4 ≤ t ∧ t % 4 = 0 then [(false, 7, t), (false, 9, t)] else [])
private def eventOf (e : Bool × Nat × Nat) : V2.Event Nat protocol.Object :=
  if e.1 then .tick e.2.1 (e.2.2 : Time)
  else .deliver e.2.1 ⟨.none, .inr (chain (e.2.2 / 4))⟩ (e.2.2 : Time)
private def run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 256
  events := eventShape.map eventOf
  seatOf l _ := if l = 6 then 9 else 7
  input _ _ := ()
private abbrev reads : FGSafetyReads protocol 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.seat 6 0, .inl a⟩
  decode := some
  decodeObject o := match o.auth with
    | .seat l _ => if l = 6 then o.payload.getLeft? else none
    | .none => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (none, ⟨0, genesisRoot, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private abbrev stored (st : Nat) : Finset (FGBlock (Fin 1)) :=
  ((List.range (min st 64 + 1)).map chain).toFinset
private abbrev core : FGCoreReads protocol 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨stored st, .genesis, .genesis, 0, heightAt (min st 64)⟩, [], allRows⟩
  erase := v5erase
  source st := some (chain (min (st - 1) 64))
  headVote _ s := v5erase (chain s)
  finalityHead _ := some .genesis
  proposalFG _ _ := none
private abbrev obs : FGObservationReads core where
  height := v5H
  finality := v5F
  controls st := treeStoreControlsView v5H (core.core st).fg
  viable st X := treeStoreFrameView v5H (core.core st).fg X
private abbrev iface : V2.D.Interface protocol where
  confirmed _ := .genesis
  stable _ := v5erase (chain 64)
  block p := match p with | .inr X => some (v5erase X) | .inl _ => none
  opening _ := True
  propLabel s := 4 * (s : Time)
  propDuty s := 4 * (s : Time)
  propDuty_label s := by
    change (if 4 * (s : Int) % 8 = 6 then 6 else 4 * (s : Int)) = _
    rw [ite_eq_right (by omega)]
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * (a : Int) = 4 * (b : Int) at h
    exact Int.ofNat_inj.mp (by omega)
private abbrev wire : FGHistoryWireReads reads where
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  signer a := some a.signer
  decode_height _ _ h := by cases h; rfl
  decode_finality _ _ h := by cases h; rfl
  decode_signer _ _ h := by cases h; rfl
private abbrev decodeProposal (o : protocol.Object) : Option (Slot × FGBlock (Fin 1)) :=
  match o.payload with | .inr X => some (X.slot, X) | .inl _ => none
private abbrev parentFG (_ : Nat) (B : Block) : Option (FGBlock (Fin 1)) :=
  some (chain B.slot)
private abbrev fold (_ : Nat) (_ : Slot) (P : FGBlock (Fin 1)) := Window.derive v5E v5cfg 2 P
private abbrev parentHeight (st : Nat) (s : Slot) (P : FGBlock (Fin 1)) : Height × BlockId :=
  ((fold st s P).h, (fold st s P).T_h.root)
private abbrev validFor (st : Nat) (s : Slot) (P : FGBlock (Fin 1)) (a : Row (Fin 1)) :=
  Window.r6w (fold st s P) a

private theorem chain_slot (s : Nat) : (chain s).slot = s := by
  cases s <;> rfl

private theorem chain_facts_premises_sat : ∀ s : Fin 65,
    (v5H (chain s)).h = heightAt s ∧
    (v5H (chain s)).T_h = chain (entrySlot s) ∧
    (v5H (chain s)).h_j = 0 ∧ (v5H (chain s)).J = .genesis ∧
    (v5F (chain s)).F = .genesis := by
  decide +kernel

#print axioms chain_facts_premises_sat

private theorem geometry_premises_sat :
    FGCertificateLaws v5E obs.height obs.finality ∧ FGObservationLaws core obs ∧
    (∀ st, FGStoreInvariant obs.height obs.finality (core.core st).fg) := by
  refine ⟨v5cert, ⟨fun _ => rfl, fun _ _ => rfl⟩, ?_⟩
  intro st
  have mem (s : Nat) (hs : s ≤ min st 64) : chain s ∈ stored st :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨s, List.mem_range.mpr (by omega), rfl⟩)
  have extract (B : FGBlock (Fin 1)) (hB : B ∈ stored st) :
      ∃ s, s ≤ min st 64 ∧ B = chain s := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hB)
    exact ⟨s, Nat.le_of_lt_succ (List.mem_range.mp hs), rfl⟩
  have facts (s : Nat) (hs : s ≤ min st 64) :=
    chain_facts_premises_sat ⟨s, by omega⟩
  refine ⟨?_, mem 0 (by omega), mem 0 (by omega), ?_, ?_, rfl, ?_⟩
  · intro B hB
    obtain ⟨s, hs, rfl⟩ := extract B hB
    cases s with
    | zero => exact mem 0 (by omega)
    | succ s => exact mem s (Nat.le_of_succ_le hs)
  · change heightAt (min st 64) = (stored st).sup (fun B => (v5H B).h) ⊔ 1
    apply le_antisymm
    · have h := Finset.le_sup (f := fun B => (v5H B).h) (mem _ le_rfl)
      rw [(facts _ le_rfl).1] at h
      exact h.trans le_sup_left
    · apply sup_le
      · apply Finset.sup_le
        intro B hB
        obtain ⟨s, hs, rfl⟩ := extract B hB
        rw [(facts s hs).1]
        exact Nat.add_le_add_left (Nat.div_le_div_right hs) 1
      · dsimp only [heightAt]
        omega
  · refine ⟨⟨.genesis, mem 0 (by omega), ?_, rfl, rfl⟩, ?_⟩
    · exact genesis_preceq _
    · intro B hB _
      obtain ⟨s, hs, rfl⟩ := extract B hB
      change lexKey ((v5H (chain s)).h_j, (v5H (chain s)).J) ≤ lexKey (0, .genesis)
      rw [(facts s hs).2.2.1, (facts s hs).2.2.2.1]
  · exact ⟨.genesis, mem 0 (by omega), rfl⟩

#print axioms geometry_premises_sat

private abbrev output (x : Nat) (t : Time) : List protocol.Object :=
  if (if protocol.signLabel t = 6 then 9 else 7) = x then
    ((protocol.act 0 t ()).map (fun p => ⟨.seat (protocol.signLabel t) 0, p⟩)).toList else []

private theorem emissions_premises_sat (j x : Nat) (t : Time)
    (hj : run.events[j]? = some (.tick x t)) :
    V2.D.Run.emitsAt env run j = output x t := by
  have tick (st : Nat) : (V2.D.tick env run st x t).2 = output x t := by
    change ((([(0 : Fin 1)].filter
      (fun _ => decide ((if protocol.signLabel t = 6 then 9 else 7) = x))).filterMap
        (fun i => (protocol.act 0 t ()).map
          (fun p => (⟨.seat (protocol.signLabel t) i, p⟩ : protocol.Object)))) ++ []) ++ [] = _
    simp only [List.append_nil]
    by_cases h : (if protocol.signLabel t = 6 then 9 else 7) = x <;>
      simp only [output, h, ite_true, ite_false, decide_true, decide_false,
        List.filter_cons, List.filter_nil, List.filterMap_cons, List.filterMap_nil,
        Bool.false_eq_true]
    all_goals rfl
  simp only [V2.D.Run.emitsAt, hj]
  exact tick _

#print axioms emissions_premises_sat

end AvailableChain.FGCompose.Tests.POP6bMixed
end
