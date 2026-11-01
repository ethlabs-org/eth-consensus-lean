module
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGSAProofs.Proofs.Shared.RowAuth
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSARun.Proofs.Emission

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Erasure preserves identity and order on all FG blocks, hence on run blocks.
This uses the existing derived-root carrier lemmas. -/
theorem fgsa_carrier_geometry {n : Nat} (X Y : FGBlock (Fin n)) :
    (eraseFG X = eraseFG Y → X = Y) ∧
    (FGBlock.Preceq X Y ↔ Block.Preceq (eraseFG X) (eraseFG Y)) ∧
    eraseFG X.parent = (eraseFG X).parent ∧
    (eraseFG X).slot = X.slot ∧ (eraseFG X).root = X.root := by
  refine ⟨fun h => eraseFG_injective h, ⟨eraseFG_preceq, ?_⟩,
    (eraseFG_parent X).symm, eraseFG_slot X, eraseFG_root X⟩
  intro h
  exact eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
DC counterpart: none (shared stored-wire delivery step).
A stored non-genesis block at any node has a proposal delivered before the read. -/
theorem stored_block_wire_delivery (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (e : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (storeAt p c E rho e x).fg.TF) (hne : W ≠ .genesis) :
    ∃ slot N, N.erase = eraseFG W ∧ W.rows = N.rows.filterMap RowWire.toRow? ∧
      ∃ j o t, j < e ∧ rho.events[j]? = some (.deliver x o t) ∧
        o = ofWire p ⟨.proposer slot, .proposal N⟩ := by
  have hs := storeBundle_stateBefore E rho e x
  obtain ⟨slot, N, hw, heN, hr⟩ :=
    stored_wire_of_block p _ hs.cstore hs.«meta» hW hne
  obtain ⟨j, o, t, hje, hd, ho, _, _⟩ := stored_proposal_delivered E rho e x _ hw
  refine ⟨slot, N, heN, hr, j, o, t, hje, hd, ?_⟩
  apply toWire_injective
  rw [toWire_ofWire, ho]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. DC counterpart: none (stored-chain delivery refinement).
Every stored-chain row at any node has an authenticated wire from a delivered proposal.
T7.5 supplies the stored wire and its delivery; unforgeability supplies the
honest holder's emission. No schedule or execution-validity premise is needed. -/
theorem stored_chain_row_origin_delivery (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hU : V2.D.UnforgeableSignatures E rho)
    (e : Nat) (x : V) (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho e x).fg.TF) :
    ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
      RowWire.toRow? a = some u ∧ a.auth = .seat .fg u.signer ∧
      ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
        ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
          ∃ j, HonestRowAt p c E rho j z r a ∧ p.actionTime r ≤ t := by
  have hs := storeBundle_stateBefore E rho e x
  have held := hW
  clear hW
  induction W with
  | genesis => intro u hu; exact (Finset.notMem_empty u hu).elim
  | node P s root body rows ih =>
      intro u hu
      change u ∈ rows.toFinset ∪ chainRows P at hu
      rcases (Finset.mem_union.mp hu).symm with hu | hu
      · exact ih (hs.cstore.fg.closed _ held) u hu
      · obtain ⟨slot, N, _, hr, j, o, t, hje, hd, he⟩ :=
          stored_block_wire_delivery p c E rho e x _ held (by intro h; cases h)
        change rows = N.rows.filterMap RowWire.toRow? at hr
        have hur : u ∈ rows := List.mem_toFinset.mp hu
        rw [hr] at hur
        obtain ⟨a, ha, hau⟩ := List.mem_filterMap.mp hur
        have har := row_auth_of_toRow a u hau
        have hc : (fgsa p c).carries o (ofRow p a) := by
          rw [he]
          exact Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))
        let z := rho.seatOf (.base .fg) u.signer
        by_cases hz : z ∈ rho.honest
        · have hsign : RowSigner p c rho a z := ⟨u.signer, har, rfl⟩
          obtain ⟨t', htt, k, hk, hem⟩ := fgsa_carried_row E rho hU x z o t ⟨j, hd⟩ a hc hz
            ((rowSigner_iff_holder p c rho a z).mp hsign).2
          rcases a with ⟨auth, payload⟩
          dsimp only at har
          subst auth
          obtain ⟨_, _, r, hrt, _⟩ := (fgsa_emitsAt_row E rho k z t' hk u.signer payload).mp hem
          refine ⟨⟨.seat .fg u.signer, payload⟩, r, hau, rfl, j, o, t, hje, hd, ?_⟩
          intro z' hz' hzh
          have hez : z = z' := Option.some.inj
            ((rowSigner_iff_holder p c rho _ z').mp hz').2
          subst z'
          exact ⟨k, ⟨hz, hrt ▸ hk, hem⟩, hrt ▸ htt⟩
        · refine ⟨a, 0, hau, har, j, o, t, hje, hd, ?_⟩
          intro z' hz' hzh
          have hh := ((rowSigner_iff_holder p c rho a z').mp hz').2
          change V2.D.Run.holder rho (ofAuth p a.auth) = some z' at hh
          rw [har] at hh
          apply False.elim
          apply hz
          change rho.seatOf (.base .fg) u.signer ∈ rho.honest
          rw [Option.some.inj hh]
          exact hzh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every held-chain row has an authenticated wire from a delivered proposal.
T7.5 supplies the stored wire and its delivery; unforgeability supplies the
honest holder's emission. No schedule or execution-validity premise is needed.
The honest-node component of hW is retained by HeldAt and is not used.
DC counterpart: none (stored-chain delivery refinement). -/
theorem held_chain_row_origin_delivery (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hU : V2.D.UnforgeableSignatures E rho)
    (e : Nat) (x : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho e x W) :
    ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
      RowWire.toRow? a = some u ∧ a.auth = .seat .fg u.signer ∧
      ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
        ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
          ∃ j, HonestRowAt p c E rho j z r a ∧ p.actionTime r ≤ t :=
  stored_chain_row_origin_delivery p c E rho hU e x W hW.2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The scheduled origin keeps the delivery index and the earlier honest row.
The schedule is used only to turn emission time order into event index order. -/
theorem held_chain_row_origin_before (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hU : V2.D.UnforgeableSignatures E rho) (hs : V2.D.ScheduleWellFormed E rho)
    (e : Nat) (x : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho e x W)
    (u : Row (Fin p.n)) (hu : u ∈ chainRows W) :
    ∃ (a : RowWire p.n) (r : Nat),
      a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
      ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
        ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
          HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t := by
  obtain ⟨a, r, ha, har, k, o, t, hke, hk, he⟩ :=
    held_chain_row_origin_delivery p c E rho hU e x W hW u hu
  refine ⟨a, r, ha, har, k, o, t, hke, hk, ?_⟩
  intro z hz hzh
  obtain ⟨j, hj, ht⟩ := he z hz hzh
  exact ⟨⟨j, (V2.D.Engine.tick_index_lt_delivery E rho hs hj.2.1 hk ht).trans hke, hj⟩, ht⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The original schedule-free origin is a projection of the delivery producer. -/
theorem held_chain_row_origin (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hU : V2.D.UnforgeableSignatures E rho)
    (e : Nat) (x : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho e x W) :
    ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (_r : Nat),
      RowWire.toRow? a = some u ∧ a.auth = .seat .fg u.signer ∧
      ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a := by
  intro u hu
  obtain ⟨a, r, ha, har, _, _, _, _, _, he⟩ :=
    held_chain_row_origin_delivery p c E rho hU e x W hW u hu
  refine ⟨a, r, ha, har, ?_⟩
  intro z hz hzh
  obtain ⟨_, hj, hem⟩ := (he z hz hzh).choose_spec.1
  exact ⟨(he z hz hzh).choose, p.actionTime r, hj, hem⟩

end AvailableChain.FGSA.Run
end
