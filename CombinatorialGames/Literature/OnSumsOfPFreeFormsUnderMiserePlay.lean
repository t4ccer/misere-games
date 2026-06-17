/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.Comparison
public import CombinatorialGames.Misere.PFreeBlocking

open Form
open OutcomeStable
open IntegerInvertible
open GameForm

-- TODO: Figure out alias macro that does @[inherit_doc <name>] without mentioning the name twice

/-!
# On Sums of P-Free Forms Under Misère Play

This is formalization of [Alfie Davies, Sarah Miller, Rebecca Milley. On Sums of P-Free Forms Under Misère Play][davies:SumsPFreeForms:2025].
-/

public section

/-!
## 2. Preliminaries
-/

alias theorem_2_1 := ComparisonSet.misereGE_iff_maintenance_proviso

alias definition_2_2_pfree := IsPFree
alias definition_2_2_set := PFreeSubset

/-!
TODO: Definition 2.3
-/

/-!
## 3. Tipping point basics
-/

alias definition_3_1_N := NTippingPoint
alias definition_3_1_R := RTippingPoint
alias definition_3_1_L := LTippingPoint

/-!
Theorem 3.2 is implied by definition of tipping points in Lean.
-/

alias lemma_3_3 := misereOutcome_add_int_ne_P

alias definition_3_4 := OutcomeStable

/-!
Open problem 3.5
-/

/-!
TODO: Theorem 3.6
-/

alias lemma_3_7 := NTippingPoint_le_RTippingPoint_of_mem_moves_left
alias lemma_3_7_mirror :=NTippingPoint_le_LTippingPoint_of_mem_moves_right

alias lemma_3_8 := RTippingPoint_eq_one_of_isEnd_left_N

alias lemma_3_9 := isEnd_left_or_exists_NTippingPoint_eq_RTippingPoint_of_N
alias lemma_3_9_mirror := isEnd_right_or_exists_NTippingPoint_eq_LTippingPoint_of_N

alias lemma_3_10 := RTippingPoint_eq_NTippingPoint_add_one_of_isEnd_left
alias lemma_3_10_mirror := LTippingPoint_eq_NTippingPoint_add_one_of_isEnd_right

alias lemma_3_11_1 := exists_mem_moves_left_L_NTippingPoint_eq_RTippingPoint
alias lemma_3_11_1_mirror := exists_mem_moves_right_R_NTippingPoint_eq_LTippingPoint

/-!
TODO: Theorem 3.11 (2) and (3)
-/

alias definition_3_12 := IntegerInvertible

alias lemma_3_13_1 := pf_misereOutcome_add_L_of_LTippingPoint_lt_NTippingPoint
alias lemma_3_13_1_mirror := pf_misereOutcome_add_R_of_RTippingPoint_lt_NTippingPoint
alias lemma_3_13_2 := pf_misereOutcome_add_N_of_RTippingPoint_lt_LTippingPoint
alias lemma_3_13_2_mirror := pf_misereOutcome_add_N_of_LTippingPoint_lt_RTippingPoint

alias lemma_3_14 := pf_misereOutcome_add_ge_N_of_NN
alias lemma_3_14_mirror := pf_misereOutcome_add_le_N_of_NN


alias lemma_3_15_1 := pf_misereOutcome_add_L_of_LTippingPoint_lt_NTippingPoint_LR
alias lemma_3_15_1_mirror := pf_misereOutcome_add_R_of_RTippingPoint_lt_NTippingPoint_RL
alias lemma_3_15_2 := pf_misereOutcome_add_ge_N_of_LR
alias lemma_3_15_2_mirror := pf_misereOutcome_add_le_N_of_RL

/-!
TODO: Theorem 3.15 (3) and (4)
-/

alias definition_3_16 := PropertyX

alias lemma_3_17 := lemma_3_17

alias lemma_3_18 := misereOutcome_ne_P_of_propertyX

alias theorem_3_19 := isPFree_of_propertyX

/-!
TODO: Corollary 3.20
-/

alias corollary_3_21 := isPFree_of_subset_propertyX

/-!
## 4. Blocking games: an application
-/

alias lemma_4_1 := misereOutcome_L_add_isEnd_left
alias lemma_4_1_mirror := misereOutcome_R_add_isEnd_right

alias lemma_4_2 := instOutcomeStableShortBlocking

/-!
TODO: Theorem 4.3
-/

/-!
TODO: Lemma 4.4
-/

alias lemma_4_5 := instIntegerInvertibleShortBlocking

/-!
TODO: Proposition 4.6
-/

alias lemma_4_7 := miserePlayerOutcome_right_isEnd_left_NN

alias lemma_4_8 := instPropertyXShortBlocking

alias lemma_4_9 := instClosedUnderAddPFreeBlocking

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
