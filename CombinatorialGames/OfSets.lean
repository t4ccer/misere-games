/-
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import CombinatorialGames.Player
import Mathlib.Logic.Small.Defs

universe u

/--
Type class for the `ofSets` operation.
Used to implement the `!{st}` and `!{s | t}` syntax.
-/
class OfSets (α : Type (u + 1)) (Valid : outParam ((Player → Set α) → Prop)) where
  /-- Construct a combinatorial game from its left and right sets. -/
  ofSets (st : Player → Set α) (h : Valid st) [Small.{u} (st .left)] [Small.{u} (st .right)] : α
export OfSets (ofSets)

@[inherit_doc OfSets.ofSets]
macro "!{" st:term "}'" h:term:max : term => `(OfSets.ofSets $st $h)

@[inherit_doc OfSets.ofSets]
macro "!{" s:term " | " t:term "}'" h:term:max : term => `(!{Player.cases $s $t}'$h)

macro "of_sets_tactic" : tactic =>
  `(tactic| first
    | done
    | trivial
    | assumption
    | aesop
    | fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
where `h` is a proof that sets are valid"
   )

@[inherit_doc OfSets.ofSets]
macro:max "!{" st:term "}" : term => `(!{$st}'(by of_sets_tactic))

@[inherit_doc OfSets.ofSets]
macro:max "!{" s:term " | " t:term "}" : term => `(!{$s | $t}'(by of_sets_tactic))

recommended_spelling "ofSets" for "!{st}'h" in [ofSets, «term!{_}'_»]
recommended_spelling "ofSets" for "!{s | t}'h" in [ofSets, «term!{_|_}'_»]
recommended_spelling "ofSets" for "!{st}" in [ofSets, «term!{_}»]
recommended_spelling "ofSets" for "!{s | t}" in [ofSets, «term!{_|_}»]

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab OfSets.ofSets]
def delabOfSets : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity' ``OfSets.ofSets 7
  withNaryArg 3 do
    let e ← getExpr
    if e.isAppOfArity' ``Player.cases 3 then
      let s ← withNaryArg 1 delab
      let t ← withNaryArg 2 delab
      `(!{$s | $t})
    else
      let st ← delab
      `(!{$st})

theorem ofSets_eq_ofSets_cases {α} {Valid : (Player → Set α) → Prop} [OfSets α Valid]
    (st : Player → Set α) (h : Valid st) [Small (st .left)] [Small (st .right)] :
    !{st} = !{st .left | st .right}'(by convert h; aesop) := by
  congr; ext1 p; cases p <;> rfl
