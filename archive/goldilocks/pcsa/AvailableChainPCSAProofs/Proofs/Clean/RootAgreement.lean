module
public import AvailableChainPCSAProofs.Proofs.Shared.Roots
public import AvailableChainPCSAProofs.Proofs.Clean.RootSources
public import AvailableChainPCSAProofs.Proofs.Clean.LockEvents

public section

/-! C6 RootAgreement: concrete receipt and count support. -/
namespace AvailableChain.PCSA
open Gen.Pure
/-- Equal selected PC targets give equal walk bases in stage one. -/
theorem pcsa_selected_walk_bases_eq (p : Params) (src dst : State p.n) (s : Slot)
    (hsrc : (controls p src).Z = .genesis) (hdst : (controls p dst).Z = .genesis)
    (hviews : (voterPC p dst s).map PC.target = (proposerPC p src).map PC.target) :
    walkBase p src (proposerPC p src) = walkBase p dst (voterPC p dst s) := by
  cases hs : proposerPC p src with
  | none =>
    cases hd : voterPC p dst s with
    | none =>
      change eraseFG (controls p src).Z = eraseFG (controls p dst).Z
      rw [hsrc, hdst]
    | some C => rw [hs, hd] at hviews; cases hviews
  | some C =>
    cases hd : voterPC p dst s with
    | none => rw [hs, hd] at hviews; cases hviews
    | some D =>
      have hCa := (List.mem_filter.mp (bestPC_mem _ C hs)).2
      have hDa := (List.mem_filter.mp (bestPC_mem _ D hd)).2
      have hCD : D.target = C.target := by
        rw [hs, hd] at hviews
        exact Option.some.inj hviews
      change (if frameActive p src C then C.target else eraseFG (controls p src).Z) =
        (if frameActive p dst D then D.target else eraseFG (controls p dst).Z)
      rw [ite_eq_left hCa, ite_eq_left hDa, hCD]
/-- Common bases and earlier-result lock bounds put both roots on the proposer path. -/
theorem pcsa_proposal_root_geometry (p : Params) (src dst : State p.n) (s : Slot)
    (parent result head : Block)
    (hbase : walkBase p src (proposerPC p src) = walkBase p dst (voterPC p dst s))
    (hsource : Block.Preceq (liveRoot p src (proposerPC p src)) parent)
    (hresultParent : Block.Preceq result parent) (hresultHead : Block.Preceq result head)
    (hsrcLocks : ∀ row ∈ src.base.obligations, Block.Preceq row.1 result)
    (hdstLocks : ∀ row ∈ dst.base.obligations, Block.Preceq row.1 result) :
    Block.Preceq (liveRoot p dst (voterPC p dst s)) parent ∧
      (Block.Preceq (liveRoot p src (proposerPC p src)) (liveRoot p dst (voterPC p dst s)) ∨
        Block.Preceq (liveRoot p src (proposerPC p src)) head) := by
  constructor
  · rcases pcsa_liveRoot_origin p dst (voterPC p dst s) with he | hm
    · rw [he, ← hbase]
      exact block_preceq_trans (pcsa_liveRoot_extends_base p src (proposerPC p src)) hsource
    · obtain ⟨row, hr, he, _, _⟩ := (pcsa_walkLocks_mem p dst _ _).mp hm
      exact block_preceq_trans (he ▸ hdstLocks row hr) hresultParent
  · rcases pcsa_liveRoot_origin p src (proposerPC p src) with he | hm
    · left
      rw [he, hbase]
      exact pcsa_liveRoot_extends_base p dst (voterPC p dst s)
    · right
      obtain ⟨row, hr, he, _, _⟩ := (pcsa_walkLocks_mem p src _ _).mp hm
      exact block_preceq_trans (he ▸ hsrcLocks row hr) hresultHead
end AvailableChain.PCSA

end
