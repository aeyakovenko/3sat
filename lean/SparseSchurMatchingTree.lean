import Std

namespace SparseSchurMatchingTree

structure Row where
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq

def Row.sparse (x : Row) : Bool :=
  !(x.a && x.b || x.a && x.c || x.b && x.c)

def matching (u v w : Row) : Bool :=
  u.sparse && v.sparse && w.sparse &&
    (Row.mk u.a v.a w.a).sparse && (Row.mk u.b v.b w.b).sparse &&
    (Row.mk u.c v.c w.c).sparse

def det (u v w : Row) : Bool :=
  xor (u.a && xor (v.b && w.c) (v.c && w.b))
    (xor (u.b && xor (v.a && w.c) (v.c && w.a))
         (u.c && xor (v.a && w.b) (v.b && w.a)))

def plusI (u v w : Row) : Bool :=
  det ⟨!u.a,u.b,u.c⟩ ⟨v.a,!v.b,v.c⟩ ⟨w.a,w.b,!w.c⟩

def off (x : Row) : Row := ⟨xor x.b x.c, xor x.a x.c, xor x.a x.b⟩
def bump (x : Row) : Row := ⟨x.a,x.b,xor x.a x.c⟩

def answer (u v w : Row) : Bool :=
  if plusI (off u) (off v) (off w) then !(plusI (bump u) (bump v) (bump w))
  else det u v w

theorem two_queries : ∀ a b c d e f g h i : Bool,
    matching ⟨a,b,c⟩ ⟨d,e,f⟩ ⟨g,h,i⟩ = true →
    answer ⟨a,b,c⟩ ⟨d,e,f⟩ ⟨g,h,i⟩ = xor a (xor e i) := by decide +kernel

end SparseSchurMatchingTree
