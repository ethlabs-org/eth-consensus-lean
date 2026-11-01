module
public import AvailableChainFGSA.Model.Store
public import AvailableChainGeneric.Proofs.AC.RootVotes

public section

namespace AvailableChain.FGSA
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.4a G25; bp02 §4.3:372–397. Class (iii), store instance.
DC: ProposalSnapshotBridge.CandidateScorePreservingViewExtension.goldfish_score_eq:210;
ProposalSnapshot.ScorePreservingViewExtension.voters_count_eq:257.
INTENTIONAL: support incidence is required only above the retained floor F;
full support inclusion can fail for heads incompatible with F (bp02:390–393).
The store pools remain parameters; F1b.4b supplies the run facts. -/
theorem fgsa_score_eq_on_retained_suffix
    (p : Params) (st st' : State p.n) (F : Block)
    (raw support raw' support' : List (GridCO.Wire p.n .root))
    (hraw : raw ⊆ raw')
    (hextra : ∀ o ∈ raw', ∀ i, GridCO.headSeat? o = some i →
      o ∉ raw → GridCO.equivocates raw i = true)
    (hinc : ∀ B, Block.Preceq F B → ∀ i, GridCO.equivocates raw i = false →
      Gen.AC.Root.poolSupports st.base.blocks support i B =
        Gen.AC.Root.poolSupports st'.base.blocks support' i B) :
    (GridCO.seats p.n raw).toFinset = (GridCO.seats p.n raw').toFinset ∧
    (∀ i, GridCO.equivocates raw i = GridCO.equivocates raw' i) ∧
    GridCO.voterCount raw = GridCO.voterCount raw' ∧
    (∀ B, Block.Preceq F B →
      GridCO.goldfishScore st.base.blocks raw support B =
        GridCO.goldfishScore st'.base.blocks raw' support' B) :=
  Gen.AC.Root.score_eq_on st.base.blocks st'.base.blocks raw raw' support support'
    {B | Block.Preceq F B} hraw hextra hinc

end AvailableChain.FGSA
