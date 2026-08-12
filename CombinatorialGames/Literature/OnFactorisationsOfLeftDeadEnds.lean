/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import CombinatorialGames.Misere.LeftDeadEnd

public import CombinatorialGames.Tactic.DocAlias

open GameForm
open GameForm.LeftDeadEnd

/-!
# On Factorisations of Left Dead Ends

This module records the formalisation of
[Alfie Davies. On factorisations of Left dead ends][davies:FactorisationsLeftDead:2024].
-/

public section

namespace OnFactorisationsOfLeftDeadEnds

/-! ## 2. Preliminaries -/

doc_alias definition_2_1 := ShortUniverse

doc_alias definition_2_2 := ShortUniverse.closure

/-! TODO: Proposition 2.3 -/

doc_alias theorem_2_4 := misereGE_lde_iff

/-! TODO: Corollary 2.5 (multiversality of comparison) -/

doc_alias definition_2_6 := IsMolecule

/-! ## 3. Properties of the monoid -/

doc_alias theorem_3_1 := lde_misereEQ_zero_iff

doc_alias corollary_3_2 := exists_run_dominated

doc_alias definition_3_3 := IsGoodOption

doc_alias corollary_3_4 := lde_good_option_dominates

doc_alias corollary_3_4_eq := lde_good_option_misereEQ

doc_alias lemma_3_5 := lde_ge_of_add_pocancellative
doc_alias lemma_3_6 := lde_misereEQ_of_add_cancellative

doc_alias theorem_3_7 := lde_pocancellative
doc_alias theorem_3_7_cancellative := lde_cancellative

doc_alias proposition_3_8 := lde_nsmul_cancel

/-! TODO: Corollary 3.9 (the group of differences of $\mathcal{L}$ is torsion-free) -/

/-! TODO: Open Problem 3.10 (the isomorphism type of the group of differences) -/

doc_alias definition_3_11 := IsTerminalRun

doc_alias definition_3_12 := terminalLengths
doc_alias definition_3_12_runs := mem_terminalLengths_iff_exists_terminalRun

doc_alias lemma_3_13 := terminalLengths_of_ne_zero

@[inherit_doc race] noncomputable def definition_3_14 := race
doc_alias definition_3_14_integer := IsInteger

doc_alias lemma_3_15 := isInteger_iff_terminalLengths_subsingleton

doc_alias lemma_3_16 := lde_zero_tfae
doc_alias lemma_3_16_race := lde_race_zero_iff

doc_alias theorem_3_17 := terminalLengths_subset_of_ge

doc_alias corollary_3_18_race := race_ge_of_ge
doc_alias corollary_3_18_birthday := birthday_le_of_ge
doc_alias corollary_3_18_birthday_eq := birthday_eq_sSup_terminalLengths

doc_alias corollary_3_19 := exists_run_terminalLengths_subset

doc_alias proposition_3_20 := terminalLengths_add
doc_alias proposition_3_20_race := race_add

doc_alias corollary_3_21 := ncard_terminalLengths_add_eq_max_iff
doc_alias corollary_3_21_ge := ncard_terminalLengths_add_ge

doc_alias lemma_3_22 := birthday_lt_of_add

doc_alias lemma_3_23 := lde_atomic

doc_alias lemma_3_24 := factorisation_length_le_race

doc_alias corollary_3_25 := lde_atom_of_race_one

doc_alias theorem_3_26 := lde_ff

/-! ## 4. In search of a prime -/

doc_alias lemma_4_1 := neg_one_add_option_ge

doc_alias proposition_4_2 := neg_one_add_eq_singleton

doc_alias proposition_4_3 := unique_good_option_iff

doc_alias theorem_4_4 := neg_one_prime

doc_alias open_problem_4_5 := LdeOtherPrimeProblem
doc_alias open_problem_4_5_non_prime_atom := LdeNonPrimeAtomProblem

/-! ## 5. Flexibility -/

@[inherit_doc flexibility] noncomputable def definition_5_1 := flexibility

doc_alias proposition_5_2 := ge_of_flexibility_le_one

doc_alias definition_5_3 := IsVersatileOption

doc_alias lemma_5_4 := flexibility_le_birthday

doc_alias lemma_5_4_eq := flexibility_eq_birthday_iff

doc_alias proposition_5_5 := flexibility_le_of_ge

doc_alias definition_5_6 := IsFlexibleRun

doc_alias definition_5_6_maximal := IsMaximalFlexibleRun

doc_alias lemma_5_7 := flexibility_eq_sSup_flexibleRun_length

doc_alias definition_5_8 := IsRacingOption

doc_alias definition_5_9 := IsStallingOption

doc_alias proposition_5_10_int := flexibility_add_neg_intCast

doc_alias proposition_5_10_add := flexibility_add

doc_alias proposition_5_11 := birthday_lt_flexibility_of_ge

doc_alias corollary_5_12 := birthday_lt_flexibility_of_multi_good

doc_alias corollary_5_13 := atom_of_birthday_gt

doc_alias proposition_5_14 := atom_of_flexibility_one

doc_alias proposition_5_14_two := atom_of_flexibility_two

doc_alias proposition_5_14_three := atom_of_flexibility_three

/-! ## 6. Lengths of factorisations -/

doc_alias lemma_6_1 := longestLen_le_good_option

doc_alias theorem_6_2 := longestLen_of_unique_good

doc_alias theorem_6_3 := longestLen_bound

/-! ## 7. Uniqueness of factorisations -/

doc_alias proposition_7_1 := isFactorisation_erase_of_longestLen_eq
doc_alias proposition_7_1_2 := exists_isLdeAtom_add_of_longestLen_eq
doc_alias proposition_7_1_racing := isRacingOption_and_exists_unique_isLdeAtom_add

doc_alias corollary_7_2 := uniquelyFactorisable_of_good_atom

doc_alias corollary_7_3 := isLdeAtom_or_isFactorisation_of_good_atoms
doc_alias corollary_7_3_race := isLdeAtom_of_good_atoms_of_race_ne_two

doc_alias corollary_7_4 := isLdeAtom_of_three_good_atoms

doc_alias lemma_7_5 := factor_eq_of_good_pf

doc_alias theorem_7_6 := uniquelyFactorisable_of_chain
doc_alias theorem_7_6_chain := IsGoodPfChain

doc_alias lemma_7_7 := isGoodOption_of_add_isGoodOption

doc_alias theorem_7_8 := uniquelyFactorisable_S_racing

doc_alias theorem_7_9 := uniquelyFactorisable_S_stalling

doc_alias proposition_7_10 := uniquelyFactorisable_of_good_pf

doc_alias proposition_7_11 := atom_or_succ_of_good_int

doc_alias question_7_12 := GoodPrimeFactorisableQuestion

doc_alias lemma_7_13 := isGoodOption_add_nsmul_iff

doc_alias lemma_7_14 := uniquelyFactorisable_add_of_isPrimeFactorisable

doc_alias lemma_7_15 := strongAtom_of_atom_good_pf

doc_alias theorem_7_16 := nsmul_uniquelyFactorisable_of_good_pf

/-! ## 8. Final remarks -/

doc_alias open_problem_8_1 := LdeUniquelyFactorisableConjecture

doc_alias open_problem_8_1_multi_good := counterexample_has_multi_good
doc_alias open_problem_8_1_molecular := counterexample_good_options_molecular
doc_alias open_problem_8_1_disjoint := counterexample_factorisations_disjoint
doc_alias open_problem_8_1_three_atoms := counterexample_has_three_atoms

doc_alias open_problem_8_2 := atomsBornBy
doc_alias open_problem_8_2_molecules := moleculesBornBy
doc_alias open_problem_8_2_atoms_T := atomsWithTerminalLengths
doc_alias open_problem_8_2_molecules_T := moleculesWithTerminalLengths

/-! ## A. Similarities with the impartial monoid -/

/-! TODO: Lemma A.1 -/

/-! ## E -/

doc_alias open_problem_E_1 := pocancellativeNotInvertible

end OnFactorisationsOfLeftDeadEnds
