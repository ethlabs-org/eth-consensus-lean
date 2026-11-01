module
public import AvailableChainGeneric.Statements.Pure.Walk
public import AvailableChainFGSAProofs.Proofs.Shared.Channels -- shake: keep (domainR API through the permitted Shared path)
public import AvailableChainKitFG.FrameGeometry

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

namespace RetainedWalk

/-- Blueprint 21:798–814, 2847–2867; spec 1109–1114. Class (iii).
DC: INTENTIONAL; the ordinary source uses the full FG-SA frame. -/
abbrev S (p : Params) (src : State p.n) : List Block :=
  erasedList src (fullTree p src)

/-- Blueprint 21:798–814, 2847–2867; spec 1219–1226, 1276–1302.
Class (iii). DC: INTENTIONAL; the target uses the actual filtered duty view. -/
abbrev T (p : Params) (dst : State p.n) (s : Slot) : List Block :=
  erasedList dst (KitFG.treeStoreFrameView (heightView p) dst.fg (voterBlocks p dst s))

/-- Blueprint 03:293–331; spec 1240–1243. Class (iii).
DC: INTENTIONAL; the proposer score uses its own raw and support pools. -/
abbrev ss (src : State n) (s : Slot) : Block → Nat :=
  GridCO.goldfishScore src.base.blocks (proposerVotes src s) (proposerSupport src s)

/-- Blueprint 03:293–331; spec 1283–1294. Class (iii).
DC: INTENTIONAL; the reader score uses its own raw and support pools. -/
abbrev ts (p : Params) (dst : State p.n) (s : Slot) : Block → Nat :=
  GridCO.goldfishScore dst.base.blocks (headVotes p dst s) (headSupport p dst s)

/-- Blueprint 21:728–758; spec 1063–1072. Class (iii).
DC: INTENTIONAL; source eligibility includes the stored-parent band. -/
abbrev es (p : Params) (src : State p.n) (s : Slot) : Block → Bool :=
  eligible p src (proposerVotes src s) (proposerSupport src s)

/-- Blueprint 21:728–758; spec 1063–1072. Class (iii).
DC: INTENTIONAL; target eligibility includes the stored-parent band. -/
abbrev et (p : Params) (dst : State p.n) (s : Slot) : Block → Bool :=
  eligible p dst (headVotes p dst s) (headSupport p dst s)

/-- Blueprint 21:783–795, 2818–2825; spec 616–633. Class (iii).
DC: INTENTIONAL; the ordinary source starts at the FG-SA control root. -/
abbrev z (p : Params) (src : State p.n) : Block := eraseFG (controls p src).Z

/-- Blueprint 21:783–795, 2818–2825; spec 648–655, 1086–1098.
Class (iii). DC: INTENTIONAL; the actual proposer starts at its live root. -/
abbrev ap (p : Params) (src : State p.n) : Block := liveRoot p src

/-- Blueprint 21:787–806, 2822–2845; spec 648–655, 1086–1098.
Class (iii). DC: INTENTIONAL; the actual reader starts at its live root. -/
abbrev ay (p : Params) (dst : State p.n) : Block := liveRoot p dst

end RetainedWalk

open RetainedWalk

/-- Blueprint 21:783–814, 2818–2872; spec 1063–1114, 1276–1302.
Class (iii). DC: INTENTIONAL; ProposalWalkTransportCore.lean:162,259.
The ordinary source and actual target have separate starts and a retained splice.
The seven transport fields follow the landed atomic Generic API. -/
structure RetainedWalkRunGeometry (p : Params) (src dst : State p.n)
    (s : Slot) (D : FGBlock (Fin p.n)) (b Kc : Block) : Prop where
  pivot_parent : Block.Preceq (eraseFG D) b.parent
  ordinary_start : Block.Preceq (z p src) (ap p src)
  ordinary_prefix : BestAncestry (z p src) (ap p src) (S p src) (ss src s) (es p src s)
  target_parent : Block.Preceq (ay p dst) b.parent
  source_cut : Block.Preceq (z p src) Kc
  target_cut : Block.Preceq (ay p dst) Kc
  cut_parent : Block.Preceq Kc b.parent
  target_prefix : BestAncestry (ay p dst) Kc (T p dst s) (ts p dst s) (et p dst s)
  persists : SuffixPersists Kc b.parent (S p src) (T p dst s)
    (ss src s) (es p src s) (et p dst s)
  reflects : SuffixReflects Kc b.parent (S p src) (T p dst s) (es p src s) (et p dst s)
  scores : SuffixScoresAgree Kc b.parent (T p dst s) (ss src s) (ts p dst s) (et p dst s)

/-- Blueprint 21:812–814, 884–886, 2865–2872; spec 1276–1302.
Class (iii). DC: INTENTIONAL; ProposalWalkTransportCore.lean:229–246.
FG-SA adds a unique current proposal after the terminal source parent. -/
structure RetainedEndpointGeometry (p : Params) (src dst : State p.n)
    (s : Slot) (b : Block) : Prop where
  old_reflects : ∀ C ∈ T p dst s, C.parent? = some b.parent →
    C.slot < s → et p dst s C = true → C ∈ S p src ∧ es p src s C = true
  proposal_mem : b ∈ T p dst s
  proposal_parent : b.parent? = some b.parent
  proposal_slot : b.slot = s
  target_slot : dst.slot p = s
  current_unique : ∀ C ∈ T p dst s, C.slot = s → C = b
  no_future : ∀ C ∈ T p dst s, C.slot ≤ s
  child_slot : ∀ C ∈ T p dst s, C.parent? = some b → b.slot < C.slot

/-- Blueprint 21:728–740, 787–806, 2822–2845; spec 1063–1107.
Class (iii). DC: INTENTIONAL; ProposalWalkTransportCore.lean:259.
Every retained edge has membership and eligibility in the target view.
A unique domain child needs no score comparison. A supported edge has a
lower score bound h and rival upper bound a < h. Equal-score root choices
can instead use S0's BestAncestry directly in the geometry record. -/
theorem fgsa_retained_prefix_of_trunk_or_support
    (p : Params) (dst : State p.n) (s : Slot) (Kc : Block)
    (hpath : ∀ X, Block.Preceq (ay p dst) X → Block.Prec X Kc →
      ∃ C, C.parent? = some X ∧ Block.Preceq C Kc ∧
        C ∈ T p dst s ∧ et p dst s C = true ∧
        ((∀ B ∈ T p dst s, B.parent? = some X → B = C) ∨
          ∃ h a : Nat, a < h ∧ h ≤ ts p dst s C ∧
            ∀ B ∈ T p dst s, B.parent? = some X → et p dst s B = true →
              B ≠ C → ts p dst s B ≤ a)) :
    BestAncestry (ay p dst) Kc (T p dst s) (ts p dst s) (et p dst s) := by
  intro X hX hK
  obtain ⟨C, hp, hC, hm, he, horder⟩ := hpath X hX hK
  refine ⟨C, hp, hC, hm, he, ?_⟩
  intro B hB hpar hel
  rcases horder with hunique | ⟨h, a, hah, hh, hrival⟩
  · obtain rfl := hunique B hB hpar
    exact ⟨Nat.le_refl _, fun _ => le_refl _⟩
  · by_cases hBC : B = C
    · subst B
      exact ⟨Nat.le_refl _, fun _ => le_refl _⟩
    · have hlt := lt_of_le_of_lt (hrival B hB hpar hel hBC) (lt_of_lt_of_le hah hh)
      exact ⟨Nat.le_of_lt hlt, fun heq => (Nat.ne_of_lt hlt heq).elim⟩

/-- Blueprint 21:798–809, 2832–2845; spec 1025–1037, 1219–1226.
Class (iii). DC: INTENTIONAL; ProposalWalkTransportCore.lean:181–184
assumes membership; FG-SA requires a witness inside the duty view.
The base-list premise is only the erasure field of the store invariant. -/
theorem fgsa_walk_domain_of_witness (p : Params) (st : State p.n)
    (V : Finset (FGBlock (Fin p.n))) (C W : FGBlock (Fin p.n))
    (hbase : ∀ B ∈ st.fg.TF, eraseFG B ∈ st.base.blocks)
    (hV : V ⊆ st.fg.TF) (hC : C ∈ V) (hW : W ∈ V)
    (hF : FGBlock.Preceq st.fg.F C)
    (hZ : FGBlock.Preceq (controls p st).Z C)
    (hCW : FGBlock.Preceq C W) (hlo : (controls p st).lo ≤ (heightView p W).h) :
    eraseFG C ∈ erasedList st (domainR p st V) := by
  apply List.mem_filter.mpr
  refine ⟨hbase C (hV hC), ?_⟩
  apply decide_eq_true
  refine ⟨C, ?_, rfl⟩
  rw [domainR_def, frameR_def]
  exact (KitFG.mem_filteredFromView (heightView p) (controls p st) V C).2
    ⟨hC, hF, hZ, W, hW, hCW, hlo⟩

end AvailableChain.FGSA.Run
end
