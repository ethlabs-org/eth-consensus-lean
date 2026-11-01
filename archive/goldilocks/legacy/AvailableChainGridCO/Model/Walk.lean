module
public import AvailableChainModel.Objects.Blocks

@[expose] public section

namespace AvailableChain.GridCO

/-- The source GHOST walk, with the greatest root winning a score tie.
Source: verified-consensus `ForkChoice/Goldfish.lean`, `ghost`. -/
def ghostStep (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block) : Option Block :=
  let children := tree.filter (fun b => b.parent? == some anchor && eligible b)
  let best := children.foldl (fun best b =>
    match best with
    | none => some b
    | some old =>
      if score old < score b || (score old == score b && old.root < b.root)
      then some b else best) none
  match best with
  | none => none
  | some b =>
      if children.any (fun c => c != b && score c == score b && c.root == b.root)
      then none else some b

def ghostWalk (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) : Nat → Block → Block
  | 0, b => b
  | fuel + 1, b =>
      match ghostStep tree score eligible b with
      | none => b
      | some c => ghostWalk tree score eligible fuel c

def ghost (anchor : Block) (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) : Block :=
  let tree := tree.eraseDups
  ghostWalk tree score eligible tree.length anchor

end AvailableChain.GridCO
end
