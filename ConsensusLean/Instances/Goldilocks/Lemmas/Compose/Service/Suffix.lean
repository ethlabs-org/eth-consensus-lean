module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the suffix of the proposal walk

On the proposal walk from the pivot `D` to `Q = P.parent`, at every block below
`Q` at or above a voter's anchor, the proposer's best child is the voter's best child. Its pieces:

* `winner_on_path` (proved): the proposer's best child `C` at a block `X ≠ Q` of the walk is on
  the walk, below `Q`;
* `winner_voter_tree_before` (proved): `C`, an ancestor of `P`, is in the voter's viable voter block
  tree (the voter holds `P`, a viable head there: the floor at the vote is at most the height of
  every block above the old origins, which are below `Q`);
* `competitor_reflect_before` (proved): for `X ≠ Q`, every child of `X` in the voter's viable voter
  block tree is in the proposer's viable tree (frozen before the vote freeze, so relayed to the
  proposer by `t_s`, or below `Q`; and viable there: heights do not decrease along ancestry and `X`
  is a proposer viable head); at `X = Q` it fails (`P` is not in the proposal's frame);
* `views_agree_before` (proved): the two views have the same equivocators and voters, and the same
  supporters for every block of both trees (`view_agree`, with the Sleepy relay), once the voter
  holds `P` (`voter_holds_before`: its anchor is below the block `X ⪯ Q`).

With `X` a proposer viable head (`hviab`) and `C` of a slot below `s`, the best child carries over
(`SA.isBest_transfer`, Lemmas/AC/BestChild): `C` is proposer-eligible only by a strict majority,
so voter-eligible by the same majority (`views_agree_before`), and a competitor the proposer does
not count has no majority, so its score is below `C`'s.

The proofs are those of `Compose/Service/SuffixWindow`, generic in the service start, which this
module imports privately: the whole-history forms here (`relay_mem_before`,
`suffix_agree_before`, `old_child_ineligible_before`, `proposal_at_voter_before`) are its forms
from `0`, with the voter's facts at `Q` from the old origins below `Q`. `proposal_accepted`,
`eq_of_slot` and `payload_eq` are in `Compose/Service/SuffixBase`, imported publicly. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

section Run

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **The acceptance relay into a frame** under the whole-history service
(`relay_mem_window_before` from `0`: no acceptance is before time `0`). -/
theorem relay_mem_before (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocks H) {jz : Nat}
    {ℓz : ACLabel (goldilocksNode sp ro)} (hcz : tr.projAC.CallAt z jz ℓz)
    (hb : tr.time jz ≤ b) {a : Time}
    (hrs : ∀ c ≤ jz, tr.projAC.RestartAt z c → tr.projAC.time c ≤ a)
    (hacc : B.root = sp.genesisRoot ∨ ∃ kx, tr.projAC.AcceptAt x kx B ∧
      max (tr.projAC.time kx) a + sp.Δ ≤ tr.projAC.time jz)
    (hF : Anc (tr.HonestBlocks H) ℓz.frame.F B) : B ∈ ℓz.frame.tree := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  exact relay_mem_window_before hrun hnc (κ := 0) hsync
    ⟨fun _ _ k _ _ hk => absurd hk (not_lt.2 (hr.time_nonneg k))⟩ hx hz hBU hcz hb
    (by rw [add_zero]; exact hr.time_nonneg jz) hrs hacc hF
/-- The whole-history service is the suffix service from `0`, for a slot `s > 0`: no acceptance
is before time `0`, and `0 ≤ t_{s−1}`. -/
private theorem suffixService_of_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {s : Nat} (hs0 : 0 < s) : SuffixService H tr 0 0 b s := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  refine ⟨hsync, ⟨fun _ _ k _ _ hk => absurd hk (not_lt.2 (hr.time_nonneg k))⟩, le_rfl, ?_⟩
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [add_zero, show ((s' + 1 : Nat) : Int) - 1 = (s' : Int) by push_cast; ring]
  simp only [SAParams.ts]
  exact mul_nonneg (by linarith [sp.toParams.hΔ]) (by exact_mod_cast Nat.zero_le s')

/-- **The voter's facts at `Q` from the old origins**: when every old origin of slot `s > 0` is
below `Q`, the head of the proposal at `t_s`, a slot-`s` voter's `fc_root` is below `Q` (genesis or
below an old origin, `vote_fcRoot_old_of`), and its head height floor is at most the height of
every block of its tree above `Q` (`vote_floor_le_of`). -/
private theorem voter_facts_of_old (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {p : Fin sp.n} (hp : p ∈ H) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    {s : Nat} (hs0 : 0 < s) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O d.head) :
    Anc (tr.HonestBlocks H) ℓy.frame.fcRoot d.head ∧
      ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocks H) d.head B →
        (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨hΦy, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hQt : d.head ∈ ℓp.frame.tree := (acProposal_start_anc_head hΦp hd).2 |> fun h =>
    mem_of_anc_left h (acProposal_start_anc_head hΦp hd).1
  refine ⟨?_, fun B hB hQB =>
    vote_floor_le_of hrun hnc hf hs0 hy hcy hes hB (fun O hO => (hold O hO).trans hQB)
      hrun.stock⟩
  rcases vote_fcRoot_old_of hrun hnc hf hs0 hy hcy hes hrun.stock with hg | ⟨O, hO, hfO⟩
  · exact honest_genesis_root_anc hrun hU (hΦyU hΦy.fcRoot_mem) hg (hΦpU hQt)
  · exact hfO.trans (hold O hO)
end Run

section Leaves

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
  (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
  {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
  (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
  {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
  {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
  (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
  (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
  {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
  (hDQ : ℓp.frame.Anc D d.head)
  (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
  {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
  {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
  (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)

include hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hsD hDQ hviab hy hcy hes

omit hsl hpj hsD in
/-- **No old child of `Q` is eligible at the voter** (the `X = Q` case of the
leaves): a child `B ≠ P` of `Q` (of a slot below `s`) in the voter's viable voter block tree is
stamped before the vote freeze (it is not an ancestor of the slot-`s` block `P`), so it is in the
proposer's tree, and a viable head there (its height is at least `Q`'s, a proposer viable head);
the proposal walk stopped at `Q`, so `B` has no strict majority in the proposal's view; the views
agree on `B` (`views_agree_before`), and `Q` is a viable head of the voter (`vote_floor_le_of`), so
`B` is ineligible at the voter too. The form from `0` of `old_child_ineligible_of`, with the
voter's facts at `Q` from the old origins below `Q` (`voter_facts_of_old`). -/
theorem old_child_ineligible_before {b : Time}
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) (hf : 2 * Hᶜ.ncard < sp.n)
    (hold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O d.head)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
    (hBQ : B.parent = some d.head.root) (hBs : B.slot < s) :
    ¬ SA.goldfishEligible sp ℓy.frame (tr.time j)
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B := by
  have hs0 : 0 < s := by omega
  obtain ⟨hfcQ, hflQ⟩ := voter_facts_of_old hrun hnc hf hp hc hd hs0 hy hcy hes hold
  exact old_child_ineligible_of hrun hnc hp hP hPs hc hcall hd hti hPQ hDQ hviab hy hcy hes
    (suffixService_of_before hrun hnc hsync hs0) hib hjb hfcQ hflQ hB hBQ hBs
end Leaves

/-- **The suffix** (over the leaves above): at every block `X` from the pivot `D`
to `Q` (in the proposer's tree) at or above the voter's anchor, the proposer's best child is the
voter's best child. Only the winner is compared: in reachable runs a
voter-eligible competitor need not be proposer-eligible (the frame moves between the proposal read
and the vote, e.g. `Σ.F` rises to `X` when the node accepts `P`, and every child of `X` becomes
eligible), and competitor scores differ between the views; below the voter's anchor the proposer's
best child can be outside the voter's viable tree. The model finds the voter's winner score strictly
above every competitor's in all of these cases. The form from `0` of `suffix_agree_of`, with the
voter's facts at `Q` from the old origins (`proposal_walk_passes_old_before`). -/
theorem suffix_agree_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (_hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
    (hDQ : ℓp.frame.Anc D d.head)
    (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head →
      Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X →
      X ≠ d.head →
      ∀ C, SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
          {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
            SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay)
              ((s : Int) - 1) B} C →
        SA.IsBest sp (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
            ((s : Int) - 1))
          {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
            B.parent = some X.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
              (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} C := by
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have hzero := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb0)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at hzero
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hs0 : 0 < s := by
    have := head_slot_lt hrun hnc hp hP hPs hc hd hPQ
    omega
  obtain ⟨hfcQ, hflQ⟩ := voter_facts_of_old hrun hnc hf hp hc hd hs0 hy hcy hes
    (proposal_walk_passes_old_before hrun hnc hb0 hsync hfb hinv hp hc hcall hd hti hib)
  exact suffix_agree_of hrun hnc (suffixService_of_before hrun hnc hsync.ac hs0) hp hP hPs hc hcall
    hd hti hPQ hsD hDQ hviab hy hcy hes hib hjb hflQ

/-- **`P` is in the voter's viable voter block tree** (`P` extends every
receiving `Σ.F`, so it is accepted by the joined voter before its vote, which waits for a ready
proposal or `t_s + Δ`; it is viable, as an allowed witness above both floors). The form from `0`
of `proposal_at_voter_of`, with the voter's facts at `Q` from the old origins. -/
theorem proposal_at_voter_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (_hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) :
    P ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) := by
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have hzero := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb0)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at hzero
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hs0 : 0 < s := by
    have := head_slot_lt hrun hnc hp hP hPs hc hd hPQ
    omega
  obtain ⟨hfcQ, hflQ⟩ := voter_facts_of_old hrun hnc hf hp hc hd hs0 hy hcy hes
    (proposal_walk_passes_old_before hrun hnc hb0 hsync hfb hinv hp hc hcall hd hti hib)
  exact proposal_at_voter_of hrun hnc (suffixService_of_before hrun hnc hsync.ac hs0) hp hP hPs hc
    hd hPQ hy hcy hes hjb hfcQ hflQ

end Consensus.Goldilocks.Compose

end
