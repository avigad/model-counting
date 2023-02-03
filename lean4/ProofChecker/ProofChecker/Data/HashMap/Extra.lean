/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import ProofChecker.Data.HashMap.Lemmas

/-! Extra stuff about hashmaps. -/

namespace HashMap

variable [BEq α] [Hashable α]

def adjustWithKey (m : HashMap α β) (a : α) (f : α → β → β) : HashMap α β :=
  -- TODO: more efficient implementation
  match m.findEntry? a with
  | some (a', b) => m.insert a' (f a' b)
  | none => m

def adjust (m : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  m.adjustWithKey a (fun _ v => f v)

/-! `mapsTo` -/

/-- This relation characterizes the map stored in `m`. -/
def mapsTo (m : HashMap α β) (a : α) (b : β) : Prop :=
  m.find? a = some b

theorem mapsTo_of_find?_eq {m : HashMap α β} {a : α} {b : β} : m.find? a = some b → m.mapsTo a b :=
  id

theorem find?_ne_none_of_mapsTo {m : HashMap α β} {a : α} {b : β} : m.mapsTo a b → m.find? a ≠ none :=
  fun h₁ h₂ => by cases h₁ ▸ h₂

def contains_iff_mapsTo {m : HashMap α β} {a : α} : m.contains a ↔ ∃ b, m.mapsTo a b :=
  sorry

theorem find?_ne_none_of_contains {m : HashMap α β} {a : α} : m.contains a → m.find? a ≠ none :=
  fun h =>
    have ⟨_, h⟩ := (m.contains_iff_mapsTo).mp h
    m.find?_ne_none_of_mapsTo h

/-! Dependently-typed accessors -/

def find (m : HashMap α β) (a : α) (h : m.contains a) : β :=
  match hFind : m.find? a with
  | some n => n
  | none => False.elim (m.find?_ne_none_of_contains h hFind)

end HashMap
