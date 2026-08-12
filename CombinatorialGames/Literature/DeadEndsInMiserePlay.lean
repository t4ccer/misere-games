/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.LeftDeadEnd
public import CombinatorialGames.Tactic.DocAlias

open Form
open Form.DeadEnding
open GameForm
open GameForm.DeadEnding
open GameForm.LeftDeadEnd

/-!
# Dead Ends in Misère Play: the Misère Monoid of Canonical Numbers

This module records the formalisation of
[Rebecca Milley, Gabriel Renault. Dead Ends in Misère Play: The Misère Monoid of Canonical Numbers]
[milley:DeadEndsMisere:2013].
-/

public section

namespace DeadEndsInMiserePlay

/-! ## 2. Preliminary results -/

doc_alias definition_1_deadEnd := IsDeadEnd
doc_alias definition_1_deadEnding := IsDeadEnding

doc_alias lemma_1 := isDeadEnding_of_mem_moves

doc_alias lemma_2 := IsDeadEnding.add

doc_alias lemma_3_left := isDeadEnd_left_misereOutcome_L
doc_alias lemma_3_right := isDeadEnd_right_misereOutcome_R

/- TODO: Lemma 4 -/

/- TODO: Definition 2: left-length -/

@[inherit_doc race] noncomputable def definition_2_race := race

/-! ## 3. Integers and other dead ends -/

doc_alias lemma_5 := winsGoingFirst_left_neg_add

doc_alias theorem_6 := lde_add_neg_misereEQ

doc_alias corollary_7 := IntegerInvertible.int_add_neg_misereEQ
doc_alias corollary_7_inst := DeadEnding.instIntegerInvertibleShortDeadEnding

/-! TODO: Theorem 8 -/

/-! TODO: Theorem 9 -/

/-! TODO: Lemma 10 -/

/-! TODO: Theorem 11 -/

/-! ## 4. Numbers -/

/-! TODO: Proposition 12 -/

/-! TODO: Lemma 13 -/

/-! TODO: Lemma 14 -/

/-! TODO: Corollary 15 -/

/-! TODO: Theorem 16 -/

/-! TODO: Lemma 17 -/

/-! TODO: Theorem 18 -/

/-! TODO: Theorem 19 -/

/-! TODO: Corollary 20 -/

/-! TODO: Lemma 21 -/

/-! TODO: Lemma 22 -/

/-! TODO: Theorem 23 -/

/-! TODO: Corollary 24 -/

/-! TODO: Theorem 25 -/

/-! ## 5. Zeros in the dead-ending universe -/

/-! TODO: Lemma 26 -/

/-! TODO: Theorem 27 -/

end DeadEndsInMiserePlay
