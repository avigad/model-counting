import ProofChecker.Data.ICnf
import ProofChecker.CountModels

/-! A possible POG API. -/

abbrev Var := Nat

def Pog := Nat

def PogError := Nat

namespace Pog

def empty : Pog := (0 : Nat)

def addVar (x : Var) : Pog → Except PogError Pog := fun _ => .ok (0 : Nat)

def addDisj (x : Var) (l₁ l₂ : ILit) : Pog → Except PogError Pog := fun _ => .ok (0 : Nat)

def addConj (x : Var) (ls : Array ILit) : Pog → Except PogError Pog := fun _ => .ok (0 : Nat)

def count (x : Var) (nVars : Nat) : Pog → Nat := fun _ => 0

axiom toPropForm (l : ILit) : Pog → PropForm Var

axiom toPropForm_neg (x : Var) (p : Pog) :
    p.toPropForm (.mkNeg x) = .neg (p.toPropForm (.mkPos x))

axiom toPropForm_addVar (x : Var) (p p' : Pog) :
    p.addVar x = .ok p' →
    p'.toPropForm (.mkPos x) = .var x

axiom toPropForm_addVar_of_ne (x y : Var) (p p' : Pog) :
    p.addVar x = .ok p' → x ≠ y →
    p'.toPropForm (.mkPos y) = p.toPropForm (.mkPos y)

axiom toPropForm_addDisj (x : Var) (l₁ l₂ : ILit) (p p' : Pog) :
    p.addDisj x l₁ l₂ = .ok p' →
    p'.toPropForm (.mkPos x) = .disj (p.toPropForm l₁) (p.toPropForm l₂)

axiom toPropForm_addDisj_of_ne (x y : Var) (l₁ l₂ : ILit) (p p' : Pog) :
    p.addDisj x l₁ l₂ = .ok p' → x ≠ y →
    p'.toPropForm (.mkPos y) = p.toPropForm (.mkPos y)

axiom toPropForm_addConj (x : Var) (ls : Array ILit) (p p' : Pog) :
    p.addConj x ls = .ok p' →
    p'.toPropForm (.mkPos x) =
      -- NOTE: This could change, and the `.tr` part is awkward. Should we have one canonical way
      -- to structurally turn a cube into a PropForm?
      ls.foldl (init := .tr) (fun acc l => acc.conj (p.toPropForm l))

axiom toPropForm_addConj_of_ne (x y : Var) (ls : Array ILit) (p p' : Pog) :
    p.addConj x ls = .ok p' → x ≠ y →
    p'.toPropForm (.mkPos y) = p.toPropForm (.mkPos y)

axiom count_of_decomposable (x : Var) (φ : PropForm Var) (p : Pog) (nVars : Nat) :
    p.toPropForm (.mkPos x) = φ → φ.decomposable →
    p.count x nVars = φ.countModels nVars

end Pog