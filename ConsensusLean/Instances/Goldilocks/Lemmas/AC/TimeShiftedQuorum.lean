module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.ForkChoice
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Time-shifted quorums on signed Goldilocks pool views

The reader bounds the proposer's scores using two snapshots. The lower score counts resolved
descendant votes and proven equivocations before the freeze. The upper bound for an incompatible
branch counts live participants other than ordinary resolved supporters. The transport laws take
exact-vote-or-pair relay as a hypothesis; these lemmas do not change the protocol handlers. -/

namespace Consensus.Goldilocks.SA.TSQ

variable {n : Nat} {FGP : Type} {A B : View n} {Φ Ψ : Frm n FGP}
variable {s : Int} {C Y : Blk n FGP}

/-- Transport of actual messages, allowing the ordinary two-entry cap. -/
def Relays (A B : View n) := ∀ v ∈ A.votes, v ∈ B.votes ∨ v.val ∈ equivocators B.votes

theorem relays_iff : Relays A B ↔ ∀ v ∈ A.votes, v ∈ B.votes ∨ v.val ∈ equivocators B.votes := by
  rfl

private theorem pair_relay (h : Relays A B) : equivocators A.votes ⊆ equivocators B.votes := by
  rintro i ⟨v,hv,w,hw,ne,rfl,hi⟩
  rcases h v hv with vB | ve
  · rcases h w hw with wB | we
    · exact ⟨v,vB,w,wB,ne,rfl,hi⟩
    · exact hi ▸ we
  · exact ve

private theorem voters_relay (h : Relays A B) : voters A.votes ⊆ voters B.votes := by
  rintro i ⟨v,hv,rfl⟩
  rcases h v hv with h | ⟨w,hw,_,_,_,eq,_⟩
  · exact ⟨v,h,rfl⟩
  · exact ⟨w,hw,eq⟩

def scoreSeats (Φ : Frm n FGP) (A : View n) (s : Int) (C : Blk n FGP) :=
  supporters Φ A s C ∪ equivocators A.votes

theorem scoreSeats_eq : scoreSeats Φ A s C = supporters Φ A s C ∪ equivocators A.votes := by rfl

private theorem score_relay (h : Relays A B) (ha : A.support ⊆ A.votes)
    (heads : ∀ v ∈ A.support, v ∈ B.votes → AncR Φ C v.head → v ∈ B.support ∧ AncR Ψ C v.head) :
    scoreSeats Φ A s C ⊆ scoreSeats Ψ B s C := by
  rintro i (⟨_,v,hv,rfl,hs,anc⟩ | eq)
  · by_cases e : v.val ∈ equivocators B.votes
    · exact Or.inr e
    · obtain ⟨hb,an⟩ := heads v hv ((h v (ha hv)).resolve_right e) anc
      exact Or.inl ⟨e,v,hb,rfl,hs,an⟩
  · exact Or.inr (pair_relay h eq)

private theorem rival_bound (h : Relays A B) (ha : A.support ⊆ A.votes) (hb : B.support ⊆ B.votes)
    (branches : ∀ r, AncR Φ Y r → ¬AncR Ψ C r) :
    (scoreSeats Φ A s Y).ncard ≤ (voters B.votes).ncard - (supporters Ψ B s C).ncard := by
  have sub : supporters Ψ B s C ⊆ voters B.votes := by
    rintro i ⟨_,v,hv,rfl,_⟩; exact ⟨v,hb hv,rfl⟩
  rw [← Set.ncard_sdiff sub]; refine Set.ncard_le_ncard ?_
  intro i hi
  rcases hi with ⟨_,v,hv,rfl,_,hy⟩ | he
  · refine ⟨voters_relay h ⟨v,ha hv,rfl⟩, ?_⟩
    rintro ⟨ne,w,hw,eq,_,hc⟩
    have vB := (h v (ha hv)).resolve_right ne
    by_cases same : v = w
    · exact branches _ hy (same ▸ hc)
    · exact ne ⟨v,vB,w,hb hw,same,rfl,eq⟩
  · have e := pair_relay h he
    obtain ⟨v,hv,_,_,_,eq,_⟩ := e
    exact ⟨⟨v,hv,eq⟩, fun hc => hc.1 (pair_relay h he)⟩

/-- The two frames can prune different blocks. Root uniqueness in their common universe
and global incompatibility suffice for the rival-score upper bound. -/
private theorem rival_across_frames {U : Set (Blk n FGP)} (coh : Coherent U)
    (left : Φ.tree ⊆ U) (right : Ψ.tree ⊆ U) (incomp : ¬Compatible U Y C)
    (h : Relays A B) (ha : A.support ⊆ A.votes) (hb : B.support ⊆ B.votes) :
    (scoreSeats Φ A s Y).ncard ≤ (voters B.votes).ncard - (supporters Ψ B s C).ncard := by
  apply rival_bound h ha hb
  rintro r ⟨v,hv,vr,yv⟩ ⟨w,hw,wr,cw⟩
  obtain rfl := coh.1 (left hv) (right hw) (vr.trans wr.symm)
  exact incomp (Anc.total coh (Anc.mono left yv) (Anc.mono right cw))

/-- In the SAME frame, signed support already resolved by freeze remains resolved in
the cast view. Neither a stable electorate nor an unchanged equivocation set is needed. -/
theorem freeze_to_cast {sp : SAParams} {a : SAState sp.n} {φ : Frm sp.n FGP}
    {c : Blk sp.n FGP} {slot : Int} {f : ETime} :
    scoreSeats φ (voteView a φ slot f) slot c ⊆ scoreSeats φ (voteView a φ slot ⊤) slot c := by
  let F := voteView a φ slot f
  let T := voteView a φ slot ⊤
  have votes : F.votes ⊆ T.votes := by
    intro v hv
    have ⟨pool,stamp⟩ := List.mem_filter.1 hv
    exact List.mem_filter.2 ⟨pool, by simpa using lt_of_lt_of_le (of_decide_eq_true stamp) le_top⟩
  apply score_relay (fun v hv => Or.inl (votes hv)) (fun v hv => (List.mem_filter.1 hv).1)
  intro v hv vT anc
  exact ⟨List.mem_filter.2 ⟨vT, by
    simpa using lt_of_lt_of_le (of_decide_eq_true (List.mem_filter.1 hv).2) le_top⟩, anc⟩

/-- An actual lower-view cover suffices at any cast. Only equivocating seats in the
current view need charging to the faulty committee, not all the seats in the certificate. -/
theorem forced_optimistic {sp : SAParams} {a : SAState sp.n} {φ : Frm sp.n FGP}
    {c : Blk sp.n FGP} {slot : Int} {f : ETime} (signers committee faulty : Set (Fin sp.n))
    (cover : signers ⊆ scoreSeats φ (voteView a φ slot f) slot c)
    (charge : equivocators (voteView a φ slot ⊤).votes ⊆ faulty)
    (eligible : voters (voteView a φ slot ⊤).votes ⊆ committee)
    (cert : 3 * committee.ncard ≤ 4 * signers.ncard) (fault : 2 * faulty.ncard < committee.ncard) :
    let l := (scoreSeats φ (voteView a φ slot f) slot c).ncard
    let t := voteView a φ slot ⊤
    (voters t.votes).ncard < 2 * l ∧
      (voters t.votes).ncard - (supporters φ t slot c).ncard < l := by
  let d := supporters φ (voteView a φ slot ⊤) slot c
  have split : signers ⊆ d ∪ faulty := by
    intro i hi
    rcases freeze_to_cast (cover hi) with hd | he
    · exact Or.inl hd
    · exact Or.inr (charge he)
  have h := (Set.ncard_le_ncard split).trans (Set.ncard_union_le d faulty)
  have hl := Set.ncard_le_ncard cover
  have hn := Set.ncard_le_ncard eligible
  change _ < 2 * _ ∧ _ - d.ncard < _
  omega

/-- A regular writer's ordinary signer cannot have become a proven equivocator at
the earlier cast if the cast votes have been relayed to the writer. -/
theorem forced_regular {sp : SAParams} {a : SAState sp.n} {φ ψ : Frm sp.n FGP}
    {c : Blk sp.n FGP} {slot : Int} {f : ETime} {W : View sp.n} {S : Set (Fin sp.n)}
    (ordinary : S ⊆ supporters ψ W slot c)
    (majority : (voters W.votes).ncard < 2 * S.ncard)
    (carry : S ⊆ scoreSeats φ (voteView a φ slot f) slot c)
    (toWriter : Relays (voteView a φ slot ⊤) W) :
    let l := (scoreSeats φ (voteView a φ slot f) slot c).ncard
    let t := voteView a φ slot ⊤
    (voters t.votes).ncard < 2 * l ∧
      (voters t.votes).ncard - (supporters φ t slot c).ncard < l := by
  have ord : S ⊆ supporters φ (voteView a φ slot ⊤) slot c := by
    intro i hi
    exact (freeze_to_cast (carry hi)).resolve_right
      (fun h => (ordinary hi).1 (pair_relay toWriter h))
  have h1 := Set.ncard_le_ncard ord
  have h2 := Set.ncard_le_ncard carry
  have h3 := Set.ncard_le_ncard (voters_relay toWriter)
  dsimp only; omega

/-- The two relay hypotheses give a strict majority and strict dominance over each incompatible
rival at the proposer. They do not establish delivery or proposal adoption. -/
theorem forced_at_proposer {F M T : View n} {φ ψ θ : Frm n FGP} {U : Set (Blk n FGP)}
    (hFM : Relays F M) (hMT : Relays M T) (fs : F.support ⊆ F.votes)
    (ms : M.support ⊆ M.votes) (ts : T.support ⊆ T.votes)
    (heads : ∀ v ∈ F.support, v ∈ M.votes → AncR φ C v.head → v ∈ M.support ∧ AncR ψ C v.head)
    (coh : Coherent U) (mU : ψ.tree ⊆ U) (tU : θ.tree ⊆ U) (incomp : ¬Compatible U Y C)
    (maj : (voters T.votes).ncard < 2 * (scoreSeats φ F s C).ncard)
    (dom : (voters T.votes).ncard - (supporters θ T s C).ncard < (scoreSeats φ F s C).ncard) :
    (voters M.votes).ncard < 2 * (scoreSeats ψ M s C).ncard ∧
      (scoreSeats ψ M s Y).ncard < (scoreSeats ψ M s C).ncard := by
  have lo := Set.ncard_le_ncard (score_relay (s := s) hFM fs heads)
  have hi := rival_across_frames (s := s) coh mU tU incomp hMT ms ts
  have part := Set.ncard_le_ncard (voters_relay hMT)
  omega

end Consensus.Goldilocks.SA.TSQ

end
