module
public import AvailableChainFGSA.Proofs.Head.Walk
public import AvailableChainFGSAClaims.Statements.Channels

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4a:4838–4843, M6; S1a C1:1596–1607; bp02 §4.1.
Class (iii), batch/store composition. DC:
Adoption.goldfish_fork_choice_captures_supporter_majority:415.
INTENTIONAL: Batch h m supplies the majority and rival bounds for both
Clean and Recovery. FJ domain membership uses an explicit keep supplier
(P3 M6), and the anchor compatibility premise is the TWalk local premise
(P3 App. A.7:7814–7824). No run or lane premise is added. -/
theorem batch_head_covers
    (p : Params) (st : State p.n) (X : Finset (FGBlock (Fin p.n)))
    (raw support : List (GridCO.Wire p.n .root)) (Hon : Finset (Fin p.n))
    (h m : Nat) (B : Block)
    (hsupport : support ⊆ raw) (hcard : Hon.card = h)
    (hclean : ∀ i ∈ Hon, GridCO.equivocates raw i = false)
    (hbatch : ∀ i ∈ Hon, Gen.AC.Root.poolSupports st.base.blocks support i B = true)
    (hother : ((GridCO.seats p.n raw).toFinset \ Hon).card ≤ m)
    (hb : Gen.Pure.Batch h m)
    (hanchor : Block.Compatible (liveRoot p st) B)
    (hkeep : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      C ∈ erasedList st (domainR p st X)) :
    Block.Preceq B (headInTree p st (erasedList st (domainR p st X)) raw support) := by
  obtain ⟨_, _, hpath, hconflict, _⟩ := Gen.AC.Root.batch_counts st.base.blocks raw raw
    support Hon h m B (fun _ hi => hi) hsupport hcard hclean hbatch hother hb
  obtain ⟨hscore, hmajority⟩ := hpath B (Gen.Pure.block_preceq_refl B)
  apply fgsa_headInTree_covers_of_transfer p st _ raw support B hanchor hkeep hmajority
  intro D hd
  have := hconflict D hd
  have := hb.lt
  omega

end AvailableChain.FGSA.Run
