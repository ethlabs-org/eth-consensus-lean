module

@[expose] public section

namespace CheckFixtures.ReviewBad

def Stmt : Prop := 1 = 1

/-- Wrong type: not `Stmt`. -/
theorem stmt : True := trivial

theorem src : 1 = 1 := rfl

/-- A statement that is not the type of `src`. -/
def Stmt2 : Prop := 2 = 2

theorem stmt2 : Stmt2 := rfl

/-- A correct pair. -/
def GoodStmt : Prop := 1 = 1

theorem goodStmt : GoodStmt := src

end CheckFixtures.ReviewBad
