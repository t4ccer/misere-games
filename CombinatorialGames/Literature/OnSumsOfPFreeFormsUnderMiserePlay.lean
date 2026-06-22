/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.Comparison
public import CombinatorialGames.Misere.PFreeBlocking
public import CombinatorialGames.Tactic.DocAlias

open Form
open OutcomeStable
open IntegerInvertible
open GameForm

/-!
# On Sums of P-Free Forms Under Misère Play

This module records the formalisation of [Alfie Davies, Sarah Miller, Rebecca
Milley. On Sums of P-Free Forms Under Misère Play][davies:SumsPFreeForms:2025].
-/

public section

/-!
## 2. Preliminaries
-/

doc_alias theorem_2_1 := Promain.of_downlinking_of_hereditary

doc_alias definition_2_2_pfree := IsPFree
doc_alias definition_2_2_set := PFreeSubset

/-!
TODO: Definition 2.3
-/

/-!
## 3. Tipping point basics
-/

doc_alias definition_3_1_N := NTippingPoint
doc_alias definition_3_1_R := RTippingPoint
doc_alias definition_3_1_L := LTippingPoint

/-!
Theorem 3.2 is implied by definition of tipping points in Lean.
-/

doc_alias lemma_3_3 := misereOutcome_add_int_ne_P

doc_alias definition_3_4 := OutcomeStable

/-!
Open problem 3.5
-/

/-!
TODO: Theorem 3.6
-/

doc_alias lemma_3_7 := NTippingPoint_le_RTippingPoint_of_mem_moves_left
doc_alias lemma_3_7_mirror :=NTippingPoint_le_LTippingPoint_of_mem_moves_right

doc_alias lemma_3_8 := RTippingPoint_eq_one_of_isEnd_left_N

doc_alias lemma_3_9 := isEnd_left_or_exists_NTippingPoint_eq_RTippingPoint_of_N
doc_alias lemma_3_9_mirror := isEnd_right_or_exists_NTippingPoint_eq_LTippingPoint_of_N

doc_alias lemma_3_10 := RTippingPoint_eq_NTippingPoint_add_one_of_isEnd_left
doc_alias lemma_3_10_mirror := LTippingPoint_eq_NTippingPoint_add_one_of_isEnd_right

doc_alias lemma_3_11_1 := exists_mem_moves_left_L_NTippingPoint_eq_RTippingPoint
doc_alias lemma_3_11_1_mirror := exists_mem_moves_right_R_NTippingPoint_eq_LTippingPoint

/-!
TODO: Theorem 3.11 (2) and (3)
-/

doc_alias definition_3_12 := IntegerInvertible

doc_alias lemma_3_13_1 := pf_misereOutcome_add_L_of_LTippingPoint_lt_NTippingPoint
doc_alias lemma_3_13_1_mirror := pf_misereOutcome_add_R_of_RTippingPoint_lt_NTippingPoint
doc_alias lemma_3_13_2 := pf_misereOutcome_add_N_of_RTippingPoint_lt_LTippingPoint
doc_alias lemma_3_13_2_mirror := pf_misereOutcome_add_N_of_LTippingPoint_lt_RTippingPoint

doc_alias lemma_3_14 := pf_misereOutcome_add_ge_N_of_NN
doc_alias lemma_3_14_mirror := pf_misereOutcome_add_le_N_of_NN


doc_alias lemma_3_15_1 := pf_misereOutcome_add_L_of_LTippingPoint_lt_NTippingPoint_LR
doc_alias lemma_3_15_1_mirror := pf_misereOutcome_add_R_of_RTippingPoint_lt_NTippingPoint_RL
doc_alias lemma_3_15_2 := pf_misereOutcome_add_ge_N_of_LR
doc_alias lemma_3_15_2_mirror := pf_misereOutcome_add_le_N_of_RL

/-!
TODO: Theorem 3.15 (3) and (4)
-/

doc_alias definition_3_16 := PropertyX

doc_alias lemma_3_17 := lemma_3_17

doc_alias lemma_3_18 := misereOutcome_ne_P_of_propertyX

doc_alias theorem_3_19 := isPFree_of_propertyX

/-!
TODO: Corollary 3.20
-/

doc_alias corollary_3_21 := isPFree_of_subset_propertyX

/-!
## 4. Blocking games: an application
-/

doc_alias lemma_4_1 := misereOutcome_L_add_isEnd_left
doc_alias lemma_4_1_mirror := misereOutcome_R_add_isEnd_right

doc_alias lemma_4_2 := instOutcomeStableShortBlocking

/-!
TODO: Theorem 4.3
-/

/-!
TODO: Lemma 4.4
-/

doc_alias lemma_4_5 := instIntegerInvertibleShortBlocking

/-!
TODO: Proposition 4.6
-/

doc_alias lemma_4_7 := miserePlayerOutcome_right_isEnd_left_NN

doc_alias lemma_4_8 := instPropertyXShortBlocking

doc_alias lemma_4_9 := instClosedUnderAddPFreeBlocking

/-!
TODO: Lemma 4.10
-/

/-!
TODO: Proposition 4.11
-/

/-!
TODO: Theorem 4.12
-/

/-!
TODO: Proposition 4.13
-/

/-!
TODO: Proposition 4.14
-/

/-!
TODO: Corollary 4.15
-/
