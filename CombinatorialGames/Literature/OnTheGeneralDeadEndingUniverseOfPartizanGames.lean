/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.SimplestForm
public import CombinatorialGames.Misere.Separation
public import CombinatorialGames.Tactic.DocAlias

/-!
# On the general dead-ending universe of partizan games

This module records the formalisation of
[Aaron Siegel. On the general dead-ending universe of partizan games][siegel:GeneralDeadendingUniverse:2025].
-/

open AugmentedForm
open Form
open Form.Misere

public section

/-!
TODO: Reconstruct theorem_5_5 for universes
-/

doc_alias definition_5_6 := adjoint

doc_alias proposition_5_7 := Adjoint.misereOutcome_add_adjoint_eq_P

doc_alias lemma_5_8 := Separating.pair_of_not_misereGE

doc_alias definition_5_9 := Downlinked

/-!
TODO: Reconstruct lemma_5_10 from pieces
-/

doc_alias definition_5_11_left_dominated := DominatedLeft
doc_alias definition_5_11_right_dominated := DominatedRight
doc_alias definition_5_11_left_reversible := ReversibleLeftThrough
doc_alias definition_5_11_right_reversible := ReversibleRightThrough

doc_alias lemma_5_12 := removeLeftOption_misereEQ

doc_alias lemma_5_13 := openBypassLeft_misereEQ

doc_alias lemma_5_14 := atomicReplaceLeft_misereEQ

doc_alias definition_5_15 := eraseLeftTomb

doc_alias lemma_5_16 := eraseLeftTomb_misereEQ

doc_alias definition_5_17 := NotErasable

doc_alias theorem_5_18 := simplestForm_unique

doc_alias definition_5_19 := SimplestForm
