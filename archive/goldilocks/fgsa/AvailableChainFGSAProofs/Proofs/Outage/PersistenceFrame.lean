module
public import AvailableChainFGSA.Proofs.Head
public import AvailableChainFGSAClaims.Statements.FrameNext
public import AvailableChainGeneric.Proofs.Pure.BlockOrder
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceHistory
public import AvailableChainFGSAProofs.Proofs.Shared.Channels

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

private def selectDeeper (a b : Block) : Block :=
  if a.depth < b.depth || (a.depth == b.depth && a.root < b.root) then b else a

private theorem selectDeeper_depth (a b : Block) :
    a.depth ≤ (selectDeeper a b).depth ∧ b.depth ≤ (selectDeeper a b).depth := by
  unfold selectDeeper
  split
  · next h =>
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact ⟨Nat.le_of_lt (of_decide_eq_true h), le_rfl⟩
    · exact ⟨(beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1).le, le_rfl⟩
  · next h =>
    have hn : ¬ a.depth < b.depth := by
      intro hab
      exact h (by simp only [hab, decide_true, Bool.true_or])
    exact ⟨le_rfl, Nat.le_of_not_gt hn⟩

private theorem foldDeeper_depth (xs : List Block) (init : Block) :
    init.depth ≤ (xs.foldl selectDeeper init).depth ∧
      ∀ b ∈ xs, b.depth ≤ (xs.foldl selectDeeper init).depth := by
  induction xs generalizing init with
  | nil => exact ⟨le_rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | cons x xs ih =>
    obtain ⟨hi, hb⟩ := ih (selectDeeper init x)
    refine ⟨(selectDeeper_depth init x).1.trans hi, ?_⟩
    intro b hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (selectDeeper_depth init b).2.trans hi
    · exact hb b hm

/-- Blueprint 03 §8.2; O-INDUCT plan §3.3. Class (iii).
DC: INTENTIONAL; the deepest selector covers a member when each possible
selection is compatible with it. No relation between different descendants
above that member is required. -/
theorem outage_fold_covers (xs : List Block) (init B : Block) (hB : B ∈ xs)
    (hinit : Block.Compatible init B)
    (hxs : ∀ b ∈ xs, Block.Compatible b B) :
    Block.Preceq B (xs.foldl (fun a b =>
      if a.depth < b.depth || (a.depth == b.depth && a.root < b.root) then b else a) init) := by
  change Block.Preceq B (xs.foldl selectDeeper init)
  have hdepth := (foldDeeper_depth xs init).2 B hB
  have hmem := foldl_select_mem (fun (a b : Block) =>
    a.depth < b.depth || (a.depth == b.depth && a.root < b.root)) xs init
  change xs.foldl selectDeeper init = init ∨ xs.foldl selectDeeper init ∈ xs at hmem
  have hcompat : Block.Compatible (xs.foldl selectDeeper init) B := by
    rcases hmem with he | hm
    · rw [he]; exact hinit
    · exact hxs _ hm
  rcases Bool.or_eq_true_iff.mp hcompat with h | h
  · have he := prefix_eq_of_depth _ _ h hdepth
    rw [he]
    exact block_preceq_refl _
  · exact h

/-- Blueprint 03 §8.2; O-INDUCT plan §3.3. Class (iii).
DC: INTENTIONAL; a live selected B lease in the full domain covers the live
root. Every other live target is below S, so it is compatible with B. -/
theorem outage_liveRoot_of_lease (p : Params) (st : State p.n) {B : Block}
    (hBS : Block.Preceq B st.base.stableRecord)
    (hbelow : LeaseBelowOutputStore p st) {dl : Time}
    (hlease : FGSA.leaseOf st B = some dl) (hlive : st.base.now < dl)
    (hdom : ∃ β ∈ FGSA.fullTree p st, eraseFG β = B) :
    Block.Preceq B (FGSA.liveRoot p st) := by
  obtain ⟨β, hβ, hβB⟩ := hdom
  have hZB : Block.Preceq (eraseFG (FGSA.controls p st).Z) B := by
    rw [← hβB]
    exact eraseFG_preceq
      ((KitFG.mem_filteredFromView (heightView p) _ _ β).mp hβ).2.2.1
  obtain ⟨row, hfind, hdl⟩ := Option.map_eq_some_iff.mp hlease
  have hrow := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  have hkey : row.1 = B := beq_iff_eq.mp hp
  let targets := st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && decide (∃ β ∈ FGSA.fullTree p st, eraseFG β = row.1)
    then some row.1 else none)
  have hBm : B ∈ targets := by
    apply List.mem_filterMap.mpr
    refine ⟨row, hrow, ?_⟩
    have htime : st.base.now < row.2.2 := hdl ▸ hlive
    have hdB : ∃ β ∈ FGSA.fullTree p st, eraseFG β = B := ⟨β, hβ, hβB⟩
    simp only [htime, decide_true, hkey, hdB, Bool.and_self, ite_true]
  change Block.Preceq B (targets.foldl selectDeeper (eraseFG (FGSA.controls p st).Z))
  apply outage_fold_covers targets _ B hBm
  · exact block_compatible_of_common hZB (block_preceq_refl B)
  · intro b hb
    obtain ⟨row, hr, he⟩ := List.mem_filterMap.mp hb
    split at he
    · next hc =>
      have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
      have hbe : row.1 = b := Option.some.inj he
      rw [← hbe]
      exact block_compatible_of_common (hbelow row hr hl) hBS
    · cases he

/-- Blueprint 03 §8.2; O-INDUCT plan §3.3. Class (iii).
DC: INTENTIONAL; the F branch, the frame-root branch, and the full-domain
lease branch all cover the live root. -/
theorem outage_liveRoot_covers (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    {B : Block} (hBS : Block.Preceq B st.base.stableRecord)
    (hbelow : LeaseBelowOutputStore p st)
    (hprotect : Block.Preceq B (eraseFG st.fg.F) ∨
      ∃ dl, FGSA.leaseOf st B = some dl ∧ st.base.now < dl ∧
        ((∃ β ∈ FGSA.fullTree p st, eraseFG β = B) ∨
          Block.Preceq B (eraseFG (FGSA.controls p st).Z))) :
    Block.Preceq B (FGSA.liveRoot p st) := by
  rcases hprotect with hF | ⟨dl, hlease, hlive, hdom | hZ⟩
  · exact block_preceq_trans hF (F_preceq_liveRoot p st hinv)
  · exact outage_liveRoot_of_lease p st hBS hbelow hlease hlive hdom
  · exact block_preceq_trans hZ (fgsa_Z_preceq_liveRoot p st)

/-- ROOT-DIGEST W2b. Blueprint 03 §7; O-INDUCT plan §6 step 6. Class (iii).
DC: INTENTIONAL; a delivery extends named history without a new emission,
then CPCompat proves the successor frame before any reconciliation argument.
INLINE hstore/hframe: fgsa_activeViewAt/fgsa_frameAt; hsrc:
fgsa_srcFrameAboveClaim; hnamed: sourceDiscipline_emittedName. -/
theorem outage_delivery_frame {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hdel : rho.events[i]? = some (.deliver x o t)) (hx : x ∈ rho.honest)
    {B : Block} {β : FGBlock (Fin p.n)} (hβ : eraseFG β = B)
    (hist : OutageSourceHistory p c E rho B i)
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    (∀ W ∈ (storeAt p c E rho (i + 1) x).fg.TF, ∀ e ∈ certified p W,
      FGBlock.Preceq e β ∨ FGBlock.Preceq β e) ∧
    (Block.Compatible B (F_at p c E rho (i + 1) x) ∧
      Block.Compatible B (J_at p c E rho (i + 1) x)) := by
  have _hcanonicalFrame := hframe
  have hnames : OutageNamedHistory p c E rho β (i + 1) := by
    constructor
    intro y r a e ha he heScope
    exact (outage_named_of_source_history (hroots := hroots) hβ hist hnamed).history y r a e
      (outage_row_before_delivery hdel ha) he heScope
  have hcp := fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat
  obtain ⟨hcert, hF, hJ, _, _⟩ := hcp (i + 1) x β hx hnames.history
  refine ⟨hcert, ?_, ?_⟩
  · rw [← hβ]
    rcases hF with h | h
    · exact block_compatible_of_common (block_preceq_refl _) (eraseFG_preceq h)
    · exact block_compatible_of_common (eraseFG_preceq h) (block_preceq_refl _)
  · rw [← hβ]
    rcases hJ with h | h
    · exact block_compatible_of_common (block_preceq_refl _) (eraseFG_preceq h)
    · exact block_compatible_of_common (eraseFG_preceq h) (block_preceq_refl _)

/-- ROOT-DIGEST W2b. Blueprint 03 §7; O-INDUCT plan §3.3. Class (iii).
DC: INTENTIONAL; named history gives F compatibility and the retained
full-domain or frame-root witness, including contested frames. INLINE
hstore/hframe: fgsa_activeViewAt/fgsa_frameAt; hsrc: fgsa_srcFrameAboveClaim. -/
theorem outage_frame_retains {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho)
    {i : Nat} {y : V} (hy : y ∈ rho.honest)
    {B : Block} {β : FGBlock (Fin p.n)} (hβ : eraseFG β = B)
    (hist : OutageNamedHistory p c E rho β i)
    (hBS : Block.Preceq B (S_at p c E rho i y))
    (hstrat : RStrat p c E rho) :
    Block.Compatible (F_at p c E rho i y) B ∧
      (Block.Preceq B (F_at p c E rho i y) ∨
        ((∃ X ∈ FGSA.fullTree p (storeAt p c E rho i y), eraseFG X = B) ∨
          Block.Preceq B (eraseFG (FGSA.controls p (storeAt p c E rho i y)).Z))) := by
  have _hcanonicalFrame := hframe
  let st := storeAt p c E rho i y
  have hinv := (hstore i y hy).1
  obtain ⟨S, hS, hSe⟩ := (hinv.baseTree _).mp hinv.Smem
  have hBS' : Block.Preceq B (eraseFG S) := by
    change Block.Preceq B (storeAt p c E rho i y).base.stableRecord at hBS
    rwa [hSe]
  obtain ⟨X, hX, hXe, _⟩ := eraseFG_ancestor_preceq hinv.fg.closed hS hBS'
  have hXβ : X = β := eraseFG_injective (hXe.trans hβ.symm)
  have hβmem : β ∈ st.fg.TF := hXβ ▸ hX
  have hcp := fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat
  obtain ⟨_, hF, _, hret, _⟩ := hcp i y β hy hist.history
  have hFB : Block.Compatible (F_at p c E rho i y) B := by
    rw [← hβ]
    rcases hF with h | h
    · exact block_compatible_of_common (eraseFG_preceq h) (block_preceq_refl _)
    · exact block_compatible_of_common (block_preceq_refl _) (eraseFG_preceq h)
  refine ⟨hFB, ?_⟩
  by_cases hBF : Block.Preceq B (F_at p c E rho i y)
  · exact Or.inl hBF
  right
  have hFβ : FGBlock.Preceq st.fg.F β := by
    rcases hF with h | h
    · exact h
    · exact (hBF (hβ ▸ eraseFG_preceq h)).elim
  rcases hret hβmem hFβ with hZ | hdom
  · exact Or.inr (hβ ▸ eraseFG_preceq hZ)
  · left
    refine ⟨β, ?_, hβ⟩
    rw [fgsa_fullTree_eq_filtered, ← fgsa_domainR_eq_filtered]
    exact hdom

end AvailableChain.FGSA.Run
end
