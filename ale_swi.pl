% ==============================================================================
% ALE -- Attribute Logic Engine
% ==============================================================================
% Version 3.2.1 --- December, 2001
% Developed under: SICStus Prolog, Version 3.8.6
% Ported to: SWI Prolog, Version 4.0.11
% Updated for: SWI Prolog, Version 5.6.47

% Authors:

% Bob Carpenter                     
% ---------------------------
% SpeechWorks Research
% 55 Broad St.
% New York, NY 10004
% USA                              
% carp@colloquial.com
%
% Gerald Penn
% --------------------------------
% Department of Computer Science
% University of Toronto
% 10 King's College Rd.
% Toronto M5S 3G4
% Canada
% gpenn@cs.toronto.edu
%
% Copyright 1992-1995, Bob Carpenter and Gerald Penn
% Copyright 1998,1999,2001, Gerald Penn
% All Rights Reserved
% ALE is distributed on the GNU Lesser GPL: http://www.gnu.org/copyleft/lesser.html
%
% ALE Homepage: http://www.cs.toronto.edu/~gpenn/ale.html

% BUG FIX  12 JAN 1993 '|' changed to ',' in compile_body(!,.. -- Carpenter

% Extensional types added, using predicates from general constraint
%  resolver - extensionality checked in rules before every edge assertion
%  1/26/93 - G. Penn

% Added iso/2, plus code for compiling extensionality check.
%  2/2/93 - G. Penn

% Bug corrected:  extensionalise hung on cyclic feature structures.
%  2/15/93 - G. Penn

% Added inequations:  checked in rules before edge insertion and after every 
%  recognised daughter description.  Inequation checking partially compiled, in
%  the manner of iso/2.
%  2/24/93 - G. Penn

% Added prolog-style inequation checking to procedural attachments.
%  2/25/93 - G. Penn

% Bug corrected: extensionalise did not handle feature structures with
%  shared structures
%  2/26/93 - G. Penn

% Interpreter added
%  2/26/93 - G. Penn

% Inequation pruning added (at time of full dereferencing)
%  3/3/93 - G. Penn

% Bug corrected: daughters list for parse tree was reversed
%  3/4/93 - G. Penn

% Structure-sharing marked in mother, daughters, and inequations in
%  interpreted mode.  Break command uses prolog "break".
%  3/4/93 - G. Penn

% Bug corrected: reload did not load .extensional.pl
%  3/4/93 - G. Penn

% Bug corrected: interpreter did not assert edges with variable tags.
%  3/4/93 - G. Penn

% Bug corrected: edge/2 printed nothing in non-interpreted mode, and did not
%  print inequations in interpreted mode.
%  3/6/93 - G. Penn

% Edge indices removed, and "trace" information incorporated into edge.  In
%  non-interpreted mode, extra information is uninstantiated.  Edge/2 will not
%  provide interpreter information for edges created while interpreter was
%  inactive
%  3/6/93 - G. Penn

% Inequation data-structure converted from ineq(Tag1-SVs1,Tag2-SVs2,Rest) to
%  ineq(Tag1,SVs1,Tag2,SVs2,Rest).
%  3/6/93 - G. Penn

% Bug corrected: extensionalise_list did not unify eligible structures from
%  different FSs in the given list
%  3/6/93 - G. Penn

% Extensionalise and extensionalise_list now extensionalise a given list of
%  inequations also (they don't check their consistency, however).
%  3/6/93 - G. Penn

% Bug corrected: nth_elt hung with input N <= 0.
%  3/12/93 - G. Penn

% Edges now indexed by a unique number, and daughters now stored by edge index.
%  3/12/93 - G. Penn

% General constraints added to types
%  3/17/93 - G. Penn

% Bug corrected: current_predicate needed to test existence of cons first in
%  compile_cons
%  3/29/93 - G. Penn

% Bug corrected: ud did not unify IqsIn and Out when tags were identical
%  3/29/93 - G. Penn

% Bug corrected: inequations were threaded through negated predicates in
%  compile_body
%  3/29/93 - G. Penn

% Bug corrected: quiet_interpreter mode not reset after parse is finished
%  (now reset by build and by clear).
%  3/29/93 - G. Penn

% cats> category added.  WARNING: Daughter indices not properly recorded for
%  initial cats> elements.
%  4/5/93 - G. Penn

% =\= converted to unary operator with general descriptions.  =@ added to
%  dcs language.
%  4/7/93 - G. Penn

% Bug corrected: find_exts_list terminating condition had too many arguments
%  4/13/93 - G. Penn

% Bug corrected: duplicates_list was passed the wrong FS in add_to
%  4/14/93 - G. Penn

% Bug corrected: lexical items were fully dereferenced and pruned before
%  lexical rules applied.  Now, after.
%  4/17/93 - G. Penn

% Empty categories now undergo lexical rules.
%  4/17/93 - G. Penn

% Bug corrected: add_to(Type,... used cut to prevent false error messages, but
%  also prevented backtracking to satisfy disjunctive constraints on Type.
%  4/17/93 - G. Penn

% Bug corrected: noadd option on query_edge_act did not have enough anonymous
%  arguments
%  4/19/93 - G. Penn

% Bug corrected: compile_body included the code for =@ on the solve list
%  rather than the prolog goal list.
%  4/19/93 - G. Penn

% Bug corrected: daughters of edges were not being printed with re-entrancy
%  intact, since edges were recorded by index and recalled from memory as
%  needed (which broke tag sharing).  Daughters are now printed with accurate
%  re-entrancy, although structure sharing between a daughter and a parent is
%  not indicated still.  Also, daughters of daughters, etc. are now available
%  from any parent edge.
%  4/24/93 - G. Penn

% Bug corrected: in pp_vs(_unwritten), when no_write_feat_flag(F) was detected,
%  the difference list for visited nodes was unlinked
%  4/24/93 - G. Penn

% Bug corrected: =\= had an operator precedence value higher than that of :,
%  and both =\= and : had precedence values lower than ==.
%  5/2/93 - G. Penn

% Bug corrected: extensionalise hung on cyclic feature structures
%  7/20/93 - G. Penn

% general hooks to prolog added (of the form prolog(Goal)).
%  7/20/93 - G. Penn

% option added to suppress error messages from add_to - disjunctive type
%  constraints can yield to many incompatible type messages before the
%  appropriate disjunct is found.  A check is also now made that every
%  word with a lexical description has a lexical entry.
%  7/20/93 - G. Penn

% rec/1 flushes buffer after printing CATEGORY (to allow more accurate timing
%  of rec/4).
%  7/20/93 - G. Penn

% disposed of unnecessary interpreter control code in interp.pl and renamed
%  secret_interp to secret_verbose.
%  10/26/93 - G. Penn

% Suppressing adderrs now automatic for compile_lex.  It remains an option
%  for other top-level predicates which usse add_to.  "Secret" versions of
%  control predicates added.
%  10/26/93 - G. Penn

% Bug corrected: cons/2 and cons/3 were not declared as dynamic.  Thus, the 
%  user could not use certain top-level predicates such as show_type and 
%  show_cons in signatures where no constraints existed.
%  10/26/93 - G. Penn

% Suppressing adderrs now automatic for compile_empty also.
%  11/20/93 - G. Penn

% Bug corrected: suppress_adderrs checks were not accompanied by fail.
%  11/23/93 - G. Penn

% dynamic no_interpreter added.  Helps non-interpreted mode not to be
%  impeded by interpreter code.
%  12/15/93 - G. Penn

% error message now given if extensional type in signature is not maximal.
%  12/15/93 - G. Penn

% Cuts switched from before retracts to after retracts where only one retract 
%  should be done since retract can succeed on backtracking (just to be safe -
%  cuts in other predicates probably prevented any errors before).
%  1/4/94 - G. Penn

% =.. replaced by functor(... when only functor was needed.
%  3/19/94 - G. Penn

% Bug corrected: SVsOut = changed to SVsOut =.. in prune_deref
%  3/19/94 - G. Penn

% fully(TagOut) changed to fully(TagOut,SVsOut), so that prune_deref does
%  not have to redereference the SVs-structure for TagOut.
%  3/19/94 - G. Penn

% Bug corrected: suppress_adderrs was not dynamically declared.
%  3/22/94 - G. Penn

% Bug corrected: missing ! in cats_member check for cats> [].
%  8/1/94 - G. Penn

% Bug corrected: maximality check always failed because every type subsumes
%  itself.  And I'm also really bummed out at the baseball strike that
%  started today since it's the first time the Yankees have had a shot at the 
%  pennant in 13 years.
%  8/12/94 - G. Penn

% ----------------------------------------
% Ale 2.0.1 patches

% Hello message now says Version 2.0.1 instead of Beta.
% 12/22/94 - G. Penn

% match_list and match_list_rest error messages missing set of parentheses.
% 12/22/94 - G. Penn
 
% missing extensionalise_list definition added.
% 12/22/94 - G. Penn

% Compiler did not flush continuants before adding prolog hooks.
%  NOTE - TAIL-RECURSIVE solve PLUS HOOKS LEADS TO UNEXPECTED BEHAVIOUR IN
%  SOME CASES
% 12/23/94 - G. Penn

% Missing abolishes added to compiler code.
% 12/23/94 - G. Penn

% Empty appropriateness definition inserted when no features exist to
%  avert SICStus existence error.
% 12/23/94 - G. Penn

% Missing cut added to compile_dtrs_rest in the final cats> clause.
% 12/23/94 - G. Penn

% 1/8/95 - Bob Carpenter
% Made Quintus compatible by bracketing if_h/1 and renaming append/3

% =====================================================================
% Errors Corrected 2.0.2
% =====================================================================

% 1/23/95 - Bob Carpenter
% Reported by Adam Przepiorkowski
% problem is that featval can be non-deterministic with constraints
% removed faulty cuts in add_to/5 to allow backtracking due to constraints
%    also conditioned error message
% removed cut after featval/6 in 2nd clause of pathval/7
%   conditioned error message

% =====================================================================
% ALE 2.0.2z 
% =====================================================================

% atoms (# _) have been added as extensional types, subsumed by bottom,
%  subsuming nothing, with no appropriate features, and no constraints.
%  As a result, bottom must have no appropriate features or constraints.
% 11-17-95 - G. Penn

% check_sub_seq compiler modified to add fail predicate if there are no
%  non_atomic extensional types.  Before, it only added fail predicate if
%  there were no extensional types.  check_sub_seq is never used with
%  atoms; and the main if_h check_sub_seq compiler clause depends on this
%  fact.
% 12-26-95 - G. Penn

% atom functor changed from #/1 to a_/1.  Because #/2 was already defined,
%  there was a problem with getting prolog to recognize hashed predicates
%  such as unify_type_#(X,Y,Z) as 'unify_type_#'(X,Y,Z) and not #(unify_type_,
%  (X,Y,Z)).  As a result, there can be no type called 'a_'.
% 12-26-95 - G. Penn

% =====================================================================
% Patches integrated from ALE 2.0.3
% =====================================================================

% Added reload/1 in order to load grammar source too (which needs to be there).
% 3/1/97 - G. Penn

% Added a clause for prolog hooks to satisfy_dtrs_goal/6 and pp_goal/4 so that
%  top-level show clauses can display them.
% 3/1/97 - G. Penn

% Added deref_list/2 to deref before calls to extensionalise_list/2.
% Added deref calls before extensionalise calls in show_type/1, mgsat/1,
%  query/1, macro/1, lex_rule/1, show_clause/1 and rule/1
% 3/1/97 - G. Penn

% Added extensionalisation check to compile_body just before =@ calls.
% 3/1/97 - G. Penn

% Added extensionalise/2 predicate for people to use inside hooks.
% 3/5/97 - G. Penn

% =====================================================================
% ALE 3.0
% =====================================================================

% 4/1/96 - Octav Popescu
% Changed compile_body/6 to take an extra argument that's used to compute the
% Goals list as a difference list

% Missing comma added to abolish(add_to_typcons,6) predicate in compile_gram/1.
% 4/5/96 - G. Penn

% 5/1/96 - Octav Popescu
% Added generator based on semantic head-driven generation algorithm
% (Shieber et al, 1990)

% 5/1/96 - Octav Popescu
% Added a test to check_inequal/2 for the case the inequations list is
% uninstantiated

% 5/1/96 - Octav Popescu
% Added test to compile_lex_rules/0 to signal lack of 'morphs' specification
% in a lexical rule

% 5/15/96 - Octav Popescu
% Added indexing and index compilation of the lexicon for generation

% 5/15/96 - Octav Popescu
% Changed to display the new version and add the banner to the version/0 message

% 7/15/96 - Octav Popescu
% Removed some ":" and added some " " to message errors to make them uniform

% Bug corrected: changed call to duplicates_list/8 from Args to
%  ArgsOut in query/1 to take advantage of earlier dereferencing.
% 4/13/97 - G. Penn

% Added missing multiple_heads/1 and sem_head_member/1 definitions
% 5/5/97 - G. Penn

% Removed dynamic cons declarations (which are erased by abolish/2 anyway) and
%  inserted current_predicate/2 declarations to protect top-level show
%  predicates and compile-time error messages which call cons.
% 5/5/97 - G. Penn

% 5/5/97 - Octav Popescu
% Removed 'var' test from check_inequal/2 and prune/2 to allow for first
%  argument indexing

% 5/7/97 - Octav Popescu
% Modified chained/6 and collect_entries/1 to avoid infinite loops generated by
%  the lack of a 'var' test in check_inequal/2

% 6/2/97 - Octav Popescu
% Introduced sem_goal> tags

% 6/10/97 - Octav Popescu
% Added tests for wrongly placed sem_goal> tags

% Changed operator precedence of mgsat/1 to 1125 (from 1150).
% 6/14/97 - G. Penn

% maximal_defaults and bottom_defaults added:  now if type is mentioned
%  as subtype, or introduces features, but is not mentioned as super, assume 
%  sub [] (maximal_defaults); if type is mentioned as supertype, but not as 
%  subtype, assume bot sub (bottom_defaults).
%  6/15/97 - G. Penn

% intro is now autonomous.  Only one of _ intro _ or _ sub _ intro _ is
%  allowed per type.
%  6/15/97 - G. Penn

% subsumption testing added, with interpreter interface.  Commands subtest 
%  and nosubtest toggle testing (run-time option and predicate).
%  6/15/97 - G. Penn

% functional constraints added to description language.
%  6/15/97 - G. Penn

% =@ flagged in type constraints.  More compiler-time error messages added 
%  to compiler code.
%  6/15/97 - G. Penn

% Bug corrected: mgsat/1 tried to print description out after having added
%  it to bottom - big trouble if it involved variables and created a cyclic
%  feature structure.
%  6/15/97 - G. Penn

% Bug corrected: bottom_defaults should not add a default for atoms.
%  9/15/97 - G. Penn

% Added edge/1 to display edge by index.
%  9/16/97 - G. Penn

% Changed name of next option of query_edgeout/9 to continue, and of discard 
%  option of query_discard/10 to noadd.  Added abort options to levels of
%  interpreter that didn't have them. Changed query_proceed in edge/2 to fail.
%  9/17/97 - G. Penn

% setof's removed from maximal_defaults.
%  9/17/97 - G. Penn

% Bug corrected:  T subs Ts did not behave correctly for uninstantiated T
%  9/17/97 - G. Penn

% Bug corrected: a_ X clauses in add_to_typeact and uact didn't bind reference
%  tags correctly.
%  9/23/97 - G. Penn

% Bug corrected: homomorphism condition check modified to handle non-grounded
%  atomic value restrictions.
%  9/23/97 - G. Penn

% Bug corrected: missing set of paren's in map_new_feats_introduced and
%  map_new_feats_find resulting in an improper list for atoms.
%  9/23/97 - G. Penn

% Removed extra lex_rule abolish from compile_lex_rules.
%  9/24/97 - G. Penn

% Bug corrected: maximal_defaults wasn't looking in _ sub Ss intro _ for
%  maximal members of Ss.
%  9/24/97 - G. Penn

% Bug corrected: pp_fs wasn't grounding VisOut for atoms
%  9/24/97 - G. Penn

% Added dynamic declaration for num/1.
%  9/25/97 - G. Penn

% Added abolish_preds/0.
%  9/25/97 - G. Penn

% Reordered type/1 clauses, cleaned up add_to's functional desc. handling,
%  and removed several extraneous extensionality checks on atoms.
%  9/27/97 - G. Penn

% Bug corrected:  current_predicate check added for if/2 in compile_cons.
%  9/27/97 - G. Penn

% Bug corrected:  Ref added to visited list for atoms also.
%  9/27/97 - G. Penn

% Moved secret_noadderrs/0 call in compile_rules past multi-hashing of rule/6.
%  10/5/97 - G. Penn

% Added parse, generate, and parse_and_gen modes.  Still only relative to one 
%  grammar.  parse_and_gen is the default.  Wrote ale_gen.pl and ale_parse.pl
%  glue.
%  10/5/97 - G. Penn

% Bug corrected: parentheses misplaced when parsing/generating modes were
%  added.
%  11/4/97 - G. Penn

% Added warning for ground atoms in appropriateness declarations.
%  11/4/97 - G. Penn

% Bug corrected: add_to/4 and compile_desc/6 had bad cut in inequation
%  clause.  Replaced with ->.
%  12/5/97 - G. Penn

% Modified edge_assert/8 and edge/2 to use rule-name and dtr info regardless
%  of interpreter setting.
%  12/7/97 - G. Penn

% Stripped out version bannering - if you reload ALE, you get two banners.
% Also made parsing only the startup mode.
%  12/10/97 - G. Penn

% Rewrote match_list/11 so that initial cats> daughters are accessible through
%  Dtrs list to the interpreter.  Also involved adding an e_list check to
%  compile_dtrs and compile_dtrs_rest that now requires goal_list_to_seq
%  conversion.
% 12/10/97 - G. Penn

% Bug corrected:  multi_hash on fsolve/5 must be done regardless of whether
%  +++>/2 exists.
% 12/10/97 - G. Penn

% Bug corrected:  fsolve/5, fun/1 and +++>/2 added to abolish_preds
% 12/10/97 - G. Penn

% Removed unused substring/4.
% 12/11/97 - G. Penn

% ALE now turns character_escapes off.
% 12/11/97 - G. Penn

% compile_iso and compile_check now called from inside compile_extensional.
% 2/1/98 - G. Penn

% Bug corrected: rewrote fsolve/5 (now fsolve/4) to compile further and
%  avoid infinite loops in compile_fun/6.
% 2/1/98 - G. Penn

% Bug corrected: added fail-clause for solve/4 for when no if/2 statements are
%  defined.
% 2/1/98 - G. Penn

% Bug corrected: moved compile_fun/0 to just after compile_sig - constraints
%  must have access to fun/1.
% 2/1/98 - G. Penn

% Translated abolish/2 calls to abolish/1 ISO standard.
% 2/28/98 - G. Penn

% ======================================================================
% ALE 3.1
% ======================================================================

% Eliminated unused edge_dtrs/4 predicate
% 3/18/98 - G. Penn

% Switched order of edge index and left node for 1st-arg. indexing during
%  parsing
% 3/18/98 - G. Penn

% Translated !; to ->; and if/3 wherever possible.
% 3/20/98 - G. Penn

% Bug corrected:  misplaced cut in fun/1 clause of add_to/5
% 3/20/98 - G. Penn

% Bug corrected: misplaced cut in mh_arg/8
% 3/20/98 - G. Penn

% =.. replaced by functor/3 and arg/3 calls except where all args are needed.
% 3/20/98 - G. Penn

% Added missing compile_approp/1
% 3/21/98 - G. Penn

% Bug corrected: misplaced paren in compile_lex/0
% 3/21/98 - G. Penn

% Replaced intermediate files with term-expansion-based compiler.
% 3/21/98 - G. Penn

% Bug corrected: misplaced paren in compile_sub_type/2
% 3/21/98 - G. Penn

% Bug corrected: missing existential quantifier in setof/3 call of compile_fun
% 3/22/98 - G. Penn

% Bug corrected: removed redundant "lexical desc. for W is unsatisfiable" error
% 3/22/98 - G. Penn

% Rewrote lex/4 to use if/3.
% 3/24/98 - G. Penn

% Rearranged compiler code dependencies and abolish/1 calls, so that alec_throw
%  compilation and abolish/1 of compiled predicates is performed as locally
%  as possible.  Also added '.alec_throw' compilation for incremental 
%  compilation predicates, and touch/1 to ensure its existence.
% 3/28/98 - G. Penn

% Added "multiple constraint declaration error" to compile_cons_act/0.
%  Added current_predicate check to compile_cons for when cons is not
%  defined.
% 3/30/98 - G. Penn

% Converted ucons/7 and add_to_typecons/6 to compile-time predicates.  Added
%  ct/7 compilation in place of carrying around large list of TypeConsPairs.
% 3/30/98 - G. Penn

% Added 5-place and 6-place versions of ud/4 to build less structure on heap
% 4/5/98 - G. Penn

% Added 7-place version of compile_desc/6 to build less structure on heap.
%  Also added 7-place version of compile_fun/6 and 8-place version of
%  compile_pathval/7.
% 4/5/98 - G. Penn

% Changed fsolve/4 to fsolve/5 - split Ref and SVs to build less structure on
%  heap
% 4/5/98 - G. Penn

% Eliminated :- true in compiled code, and first-arg indexed goal_list_to_seq
% 4/5/98 -  G. Penn

% Replaced conc/3 with built-in append/3
% 4/9/98 - G. Penn

% Replaced make_seq/2 with goal_list_to_seq/2.
% 4/9/98 - G. Penn

% Disposed of unused make_list/2.
% 4/9/98 - G. Penn

% Replaced member/2, select/3, memberchk/2, reverse/2 with
%  built-in definitions.
% 4/9/98 - G. Penn

% Replaced ord_union/3 with built-in merge/3
% 4/9/98 - G. Penn

% Added new clause to add_to/5 and compile_desc/6,7 for fast unification of
% unbound variables
% 4/13/98 - G. Penn

% Added MGSat compilation for map_new_feats_find and map_new_feats_introduced,
%  and for add_to_type and u when adding/unifying on one/two FSs with atomic
%  types.
% 4/12/98 - G. Penn

% Changed add_to_typeact so that Type2 is first argument, in case we need
%  to trap special cases of SVs.
% 4/13/98 - G. Penn

% Changed lexicon/empty_cat compilation from compiling to dynamic consulting.
% 4/17/98 - G. Penn

% Added lex_assert/0 and lex_compile/0 directives.  Also added dynamic
%  declaration in asserted case.  Extended option's control to empty
%  categories.
% 4/17/98 - G. Penn

% Added multifile declaration to asserted case for lex/4 and empty_cat/3
%  compilation.
% 4/20/98 - G. Penn

% Created lex_act/6 predicate for lex/4 to call from term_expansion/2 hook for
%  update_lex/1.  Added update_lex/1 and retract_lex/1.
% 4/20/98 - G. Penn

% Bug corrected: generation code for cats> was calling subtype/2 instead of
%  sub_type/2
% 6/15/98 - G. Penn

% Bug corrected: clause added to ct/7 for when cons/2 is not defined.
% 6/16/98 - G. Penn

% Switched order of number_display/2 clauses and added cut to handle variable
%  first arguments (for interpreted generator) 
% 6/18/98 - G. Penn

% Added export_words/2
% 6/23/98 - G. Penn

% Added rec/5 and rec/2 to enforce description on solution FS
% 6/23/98 - G. Penn

% Added rec_best/2, which produces all of the parses for the first list in a
%  a list of lists of words that has any solutions that match an input Desc,
%  rec_list/2, which produces all of the parses for every list in a 
%  list of lists of words, and rec_list/3, which is like rec_list/2 but
%  collects solutions as fs(FS,Iqs) pairs in a list of lists.
% 6/23/98 - G. Penn

% ALE now turns character escapes on.  Code generation modified to print
%  '\+' and '=\=' correctly.
% 6/23/98 - G. Penn

% Moved approps(Type3,FRs3) call in uact/10 to just before map_feats_unif
%   call - otherwise not needed.
% 6/24/98 - G. Penn

% Added default maximal type specs for value restrictions and ext/1 types.
% 6/25/98 - G. Penn

% Removed extra space from "Compiling sub-types..." message
% 6/29/98 - G. Penn

% Bug corrected: rec_best/2's recursive call was to rec_list/2.
% 6/30/98 - G. Penn

% Added lex and gen prefix operators to match rec, query etc.
% 6/30/98 - G. Penn

% Added domain exception to edge/2 to enforce M=<N.
% 6/30/98 - G. Penn

% Moved mode-specific compilation messages inside parsing/generating checks.
% 6/30/98 - G. Penn

% Rewrote generator.
% 7/1/98 - G. Penn

% Changed name of lex(icon)_assert to lex(icon)_consult.
% SWI PORT: not available - replaced with 'not available' messages
% 7/2/98 - G. Penn

% Bug corrected:  macro calls could not backtrack in add_to because -> was
%  used instead of if/3
% 7/7/98 - G. Penn

% Bug corrected: value restrictions from autonomous intro/2 declarations 
%  were not generating default maximal type specs.  Line break also added
%  at end of 'assuming' messages.
% 7/7/98 - G. Penn

% SWI PORT: Bug corrected: split_dtrs did not strip sem_goal> designations
%  off semantic goals.
% 7/15/98 - G. Penn

% Bug corrected: a_ subtype/feature spec error did not check for autonomous
%  intros.  bot feature spec error did not check for autonomous intros.
% 7/16/98 - G. Penn

% SWI PORT: Bug corrected:  maximal_defaults was still not generating default
%  specs for ext/1 types.
% 7/16/98 - G. Penn

% Bug corrected: maximal_defaults was not filtering out a_/1 value restrictions
%  or extensional types.
% 7/16/98 - G. Penn

% Bug corrected: turned off adderrs for enforcement of description argument of 
% rec/2,5.
% 7/13/98 - G. Penn

% Bug corrected: missing clauses for =@ in pp_goal/4.
% 7/19/98 - G. Penn

% Bug corrected: missing clause for prolog hooks in mg_sat_goal/4
% 7/19/98 - G. Penn

% Bug corrected: several top-level predicates assumed atomic attached goals
%  when collecting FS's to dereference.  Now they use satisfy_dtrs_goal/6
%  instead of mg_sat_goal/4.
% 7/19/98 - G. Penn

% Changed non_chain_rule/8, chained/7 and chain_rule/12 to if_b to keep unification
% cases as first clauses after multi-hashing
% 7/19/98 - G. Penn

% Changed edge access to clause/2 calls - bypasses call stack.
% 7/20/98 - G. Penn

% Changed maximal_defaults so that 'assuming' message prints types w/o carriage
% returns.  Modified bottom_defaults message to something parallel.  
% 7/31/98 - G. Penn

% Changed carriage returns on if_warning messages.
% 7/31/98 - G. Penn

% Bug corrected: (3.1.1) maximal_defaults added a sub_def entry for bot
%  if it was used as an appropriate value restriction or as an extensional
%  type.
% 11/22/98 - G. Penn

% ======================================================================
% ALE 3.2
% ======================================================================

% Renamed alec_catch_act/2 to alec_catch_hook/2.
% 9/7/98 - G. Penn

% Added multifile declaration for term_expansion/2 and alec_catch_hook/2.
% 9/7/98 - G. Penn

% Bug corrected:  sub_type(Type,Type) clause was matching a_ atoms.  Now use
%  subs/2 directly, rather than type/2.
% 10/24/98 - G. Penn

% Added compile-time analysis of variable binding to eliminate var/1 shallow
%  cuts in generated code where possible.
% 11/19/98 - G. Penn

% Added compile-time analysis of descriptions to eliminate fresh variable 
%  allocation in procedural calls where possible.
% 11/20/98 - G. Penn

% Removed solve/4 meta-interpreter.  Clauses are now compiled into Prolog
%  clauses with their names preceded by 'fs_'.  Also added query_goal/4,
%  query_goal/6 and pp_query_goal/4 for query/1 and gen_lex_close/9 to call, 
%  since there is no longer a close correspondence between preparing a goal 
%  for printing and preparing a goal for calling (actually, there never
%  was - the printing prep. code did not work in some cases for calling 
%  prep.).
% 11/22/98 - G. Penn

% Bug corrected: (3.1.1) maximal_defaults added a sub_def entry for bot
%  if it was used as an appropriate value restriction or as an extensional
%  type.
% 11/22/98 - G. Penn

% Quiet interpreter mode removed.  edge/8 always records daughters.
% 1/24/99 - G. Penn

% Cleaned up edge_assert/8 and pulled no_subsumption check out to add_edge.
% 1/24/99 - G. Penn

% Added upward closure error message.
% 2/5/99 - G. Penn

% Added non-negative error message for edge/2
% 2/6/99 - G. Penn

% Bug corrected: node was unhooked in empty category indices - can be bound 
%  from Left arg. of rule/6.
% 3/6/99 - G. Penn

% Bug corrected: compile_desc/11 was binding its FS variable with Tag-SVs and
%  inequational descriptions, which led to wasted structure on the heap.
% 3/6/99 - G. Penn

% Bug corrected: current_predicate check in empty_cat/7 needed to assert
%  alec_closed_rules for rule compiler.
% 3/7/99 - G. Penn

% Implemented EFD-Closure parsing algorithm.  Repairs ALE's problem with
%  empty category combination, as well as with non-ISO compliance of SICStus 
%  (and probably SWI) with respect to asserted predicates.  Tabulate FSs at
%  compile-time to avoid Tag-SVs copying in compiled code.  Cleaned up fresh
%  argument binding and compile_desc/11's FS binding.
% 3/10/99 - G. Penn

% Implemented on-heap parsing to minimise edge copying.
% 3/10/99 - G. Penn

% Added FS palettes to avoid having to compile large FS's in compiled code.
% 3/11/99 - G. Penn

% Changed sub_type/2 and unify_type/3 compilation to consulting.  Doing the
%  same for approp/3 had net effect of slowing compilation down.  System is
%  slightly slower at run-time, presumably because of match_list list checks.
% 3/11/99 - G. Penn

% Modified on-heap chart to use custom edge/8 structures.
% 4/8/99 - G. Penn

% Removed unused member_ref_eq/2.
% 4/9/99 - G. Penn

% Bug corrected: FS palettes need to save inequation tags.
% 4/9/99 - G. Penn

% Rewrote extensionalisation code.
% 4/14/99 - G. Penn

% Bug corrected: query_goal/7 left Dtrs unbound on disjunctions.
% 4/20/99 - G. Penn

% Bug corrected: mg_sat_goal/5 left Iqs unbound on disjunctions.
% 4/20/99 - G. Penn

% Bug corrected: incorrect spacing for =@ in pp_goal/5.
% 4/20/99 - G. Penn

% Added shallow cuts.
% 4/21/99 - G. Penn

% Bug corrected: match_cat_to_next_cat/9 lost empty cat inequations with cats>
% 5/7/99 - G. Penn

% Bug corrected: non_chain_rule/8 code was being consulted.
% 5/8/99 - G. Penn

% Bug corrected: multi_hash/4 reversed order of clauses with same first-arg
%  index by using accumulator in mh_arg/9.  Changed to mh_arg/10 with diff.
%  list to preserve order
% 5/9/99 - G. Penn

% Rewrote subsumption checking code.
% 5/20/99 - G. Penn

% Bug corrected: mh_arg was not capturing variable arguments before decomposing
%  to match hashed argument position.  Added nonvar/1 check.
% 5/21/99 - G. Penn

% Added two-place shallow cuts.
% 5/22/99 - G. Penn

% Bug corrected: cats> Dtrs were bound to rule Dtrs.
% 5/22/99 - G. Penn

% Bug corrected: changed order of all clauses matching shallow cut args so that
%  they are matched before disjunctions.
% 5/22/99 - G. Penn

% Bug corrected: changed edge/2 to check for M<N, since it doesnt display
%  empty cats.  Also added no_interpreter check.
% 5/22/99 - G. Penn

% Bug corrected: empty/0 didnt print nl after '# of dtrs:' line, and dtr-#
%  option didnt handle continue option properly.
% 5/22/99 - G. Penn

% Changed 't's to empty_assoc/1 calls.
% 5/23/99 - G. Penn

% Bug corrected: match_list_rest was not defined with a Chart argument.
% 5/23/99 - G. Penn

% Bug corrected: placed to_rebuild/1 lookup inside clause call
% 5/23/99 - G. Penn

% Changed compile_subsume to check first for parsing flag.
% 5/23/99 - G. Penn

% Bug corrected: show_type failed if there were constraints, but not on the
%  type shown.
% 5/23/99 - G. Penn

% Added type/1 call to show_type so that it can iterate through types if
%  uninstantiated.
% 5/23/99 - G. Penn

% Bug corrected (SWI port): fun/1 and fsolve/5 compilation must be split
%  into separate phases since compile_desc/13 needs fun/1.
% 6/26/99 - G. Penn

% SWI PORT: (ALE 3.2.1) Allow for user-defined discontiguity now that
%  SICStus can handle it.  Specific compiled predicates, if_h/1, if_h/2
%  and if_b/2 are declared discontiguous.  Also take advantage of
%  quintus compatibility library to define subsumes_chk/2 and compile/1.
% 12/11/01 - G. Penn

% Bug corrected (SWI port): (ALE 3.2.1) removed same_file/2, and placed
%  access(exist) in absolute_file_name/3 call instead.
% 1/7/03 - G. Penn

% NOTE: must resolve whether to close empty cat's under lexical rules
% Perhaps we should add an option to the interpreter to "go," stopping only
%   at subsumption-based assert/retract decisions
% Add check for cut-free goals in PS rules - they take scope over rule code,
%  and are prohibited in the manual
% Add benchmarking code written for Kathy B.
% Add named empty categories
% Add proc. attachments to lexical entries (and empty cats, macros?)
% Add more compile-time checking of compatibility
%  in things like rules, relations, lexical rules and constraints (things that
%  compile to code instead of FS's).  These should disable with the new user
%  control predicates also.
% Add list (and other) pretty-printer.
% Add statistical scoring mechanism.
% Make mini-interpreter record lexical rule and lexical origins of derived
%  lexical entries in chart
% Add subsumes/2 built-in to relational language/Prolog

% Make sure to reflect these changes in source-level debugger where approp.
% Aggregate type info in descriptions at each node in order to avoid redundant
%  type inferencing in compiled code - prob. other optimizations are possible
%  too, although must be balanced against transparency of description
%  execution.
% Also compile extensionalise further and everywhere else that functor and
%  arg are used
% remove check_inequal
% maybe add assert option to get around hard limit on number of vars. in 
%  compiled predicates - ultimately should do something better like 
%  automatically detecting when limit is exceeded and adding clauses like 
%  add_to_type3 and featval/4.  The hard limit is actually on temporary 
%  variables.
% get rid of compile_desc/6 - probably will have to change DS to do this right
%  in order to get featval to return a split Tag,SVs
% add indexing mechanism for generation lexicon and parsing chart.  Also
%  index first arguments of definite clauses by type.


% RCS banners
% $Id: ale.pl,v 1.7 1998/03/07 18:38:30 gpenn Rel gpenn $
%
% $Log: ale.pl,v $
% Revision 1.7  1998/03/07 18:38:30  gpenn
% Bug corrections, internal notes
% Stripped out version bannering
% mini-interpreter now always carries dtr and rule info
% match_list bug corrected
% more warnings, removed some unused code
% now turns off character_escapes
% placed compile_iso and compile_check under compile_extensional
% translated abolish/2 calls to abolish/1 ISO standard
%
% Revision 1.6  1997/10/23 15:47:45  gpenn
% Added parsing and generating modes.  Still handles only one
% grammar per session.  ale_gen.pl and ale_parse.pl can glue two
% sessions together for translation.
%
% Revision 1.5  1997/09/27 21:43:36  gpenn
% Added edge subsumption w/ interpreter interface, functional
% descriptions, autonomous intro declaration, default declarations
% for maximal types and types immediately subsumed by bottom.
% Also cleaned up interpreter, and modified treatment of atoms to
% allow non-ground terms.
%
% Revision 1.4  1997/06/10 19:07:57  octav
% Added sem_goal> tags.
%
% Revision 1.2  1997/05/05 19:54:00  gpenn
% bug fix of 1.1
%

% SWI patch code

:- ensure_loaded(library(quintus)).

% replaced consult/1 everywhere with:
swi_consult(X) :- % style_check(-discontiguous),
                  consult(X).

ttynl :- nl(user_output).

if(X,Y,Z) :- (X *-> Y ; Z).

% findall/4 exists in SWI 5.6
%findall(Temp,Goal,NewBag,Remainder) :-
%  findall(Temp,Goal,Bag),
%  append(Bag,Remainder,NewBag).

instance(Ref,(Head:-Body)) :- clause(Head,Body,Ref).

% SWI equivalent is message_hook/3, but implementation (as of 3.2.7) is
%  incomplete - will not trap warnings or informational messages
% :- multifile portray_message/2.

% portray_message(warning,no_match(abolish(_))). % suppress abolish/1 warnings
% portray_message(informational,M) :-
%   portray_message_inf(M).

% portray_message_inf(loading(compiling,AbsFileName)) :-
%   ale_compiling(AbsFileName).                  % suppress compiler throws
% portray_message_inf(loaded(compiled,AbsFileName,user,_,_)) :-
%   ale_compiling(AbsFileName).

% :- prolog_flag(character_escapes,_,on).
% :- use_module(library(terms),[subsumes_chk/2]).

:- set_feature(character_escapes,true).

%subsumes_chk(X,Y) :-
%  \+ \+ (copy_term(Y,Y2),
%         free_variables(Y,YFVs),
%         free_variables(Y2,Y2FVs),
%         X = Y2,
%         numbervars(YFVs,'$VAR',0,_),   % don't use '$VAR' in a_ atoms!
%         YFVs = Y2FVs).

% ------------------------------------------------------------------------------
% same_length(Xs:<list>, Ys:<list>)
% ------------------------------------------------------------------------------
% checks that Xs and Ys are same length; instantiating if necessary
% ------------------------------------------------------------------------------
same_length([],[]).
same_length([_|Xs],[_|Ys]):-
  same_length(Xs,Ys).

% ------------------------------------------------------------------------------
% transitive_closure(Graph:<graph>, Closure:<graph>)
% ------------------------------------------------------------------------------
% Warshall's Algorithm (O'Keefe, Craft of Prolog, p. 172)
% Input: Graph = [V1-Vs1,...,VN-VsN]
%   describes the graph G = <Vertices, Edges> where
%      * Vertices = {V1,..,VN} and
%      * VsI = {VJ | VI -> VJ in Edges}
% Output: Closure is transitive closure of Graph in same form
% ------------------------------------------------------------------------------
transitive_closure(Graph,Closure):-
  warshall(Graph,Graph,Closure).

warshall([],Closure,Closure).
warshall([V-_|G],E,Closure):-
  memberchk(V-Y,E),
  warshall(E,V,Y,NewE),
  warshall(G,NewE,Closure).

warshall([],_,_,[]).
warshall([X-Neibs|G],V,Y,[X-NewNeibs|NewG]):-
  memberchk(V,Neibs),
  !, merge(Neibs,Y,NewNeibs),
  warshall(G,V,Y,NewG).
warshall([X-Neibs|G],V,Y,[X-Neibs|NewG]):-
  warshall(G,V,Y,NewG).

% ------------------------------------------------------------------------------
% vars_of(Term:<term>, VarsIn:<var>s, VarsOut:<var>s)
% ------------------------------------------------------------------------------
% VarsOut is VarsIn appended to variables in Term
% ------------------------------------------------------------------------------
vars_of(Var,VarsIn,[Var|VarsIn]):-
  var(Var), !.
vars_of(A,VarsIn,VarsIn) :-   % recommended by Jan Wielemaker
  atomic(A), !.
vars_of(Term,VarsIn,VarsOut):-
  Term =.. [_|Args],
  vars_of_list(Args,VarsIn,VarsOut).
 
vars_of_list([],VarsIn,VarsIn).
vars_of_list([Arg|Args],VarsIn,VarsOut):-
  vars_of(Arg,VarsIn,VarsMid),
  vars_of_list(Args,VarsMid,VarsOut).

% term_variables/2 exists in SWI 5.6
%term_variables(Term,Vars) :- vars_of(Term,[],Vars).

% ------------------------------------------------------------------------------
% top_sort(Type:<type>,VisIn:<type>s,VisOut:<type>s,TopIn:<type>s,
%          TopOut:<type>s)
% ------------------------------------------------------------------------------
%  Topologically sorts the types accessible by inverse feature paths from
%   Type.  The order used is such that Type will be the first element on the
%   list TopOut.
% ------------------------------------------------------------------------------
top_sort(Type,VisIn,VisOut,TopIn,TopOut) :-
  member(Type,VisIn)
  -> (VisOut = VisIn,
     TopOut = TopIn)
   ; (TopOut = [Type|TopMid],
      esetof(MT,Type^F^(approp(F,MT,Type)),MotherTypes),
      top_sort_list(MotherTypes,[Type|VisIn],VisOut,TopIn,TopMid)).
 
top_sort_list([],Vis,Vis,Top,Top).
top_sort_list([Type|Types],VisIn,VisOut,TopIn,TopOut) :-
  top_sort(Type,VisIn,VisMid,TopIn,TopMid),
  top_sort_list(Types,VisMid,VisOut,TopMid,TopOut).

% Association lists
empty_assoc([]).

get_assoc(Key,Assoc,Value) :-
  get_assoc_act(Assoc,Key,Value).
get_assoc_act([AKey-AValue|AssocRest],Key,Value) :-
  (AKey == Key)
  -> Value = AValue
   ; get_assoc_act(AssocRest,Key,Value).

get_assoc(Key,OldAssoc,OldValue,NewAssoc,NewValue) :-
  get_assoc_act(OldAssoc,Key,OldValue,NewAssoc,NewValue).
get_assoc_act([OAKey-OAValue|OldAssocRest],Key,OldValue,NewAssoc,NewValue) :-
  (OAKey == Key)
  -> NewAssoc = [Key-NewValue|OldAssocRest],
     OldValue = OAValue
   ; NewAssoc = [OAKey-OAValue|NewAssocRest],
     get_assoc_act(OldAssocRest,Key,OldValue,NewAssocRest,NewValue).

put_assoc(Key,OldAssoc,Val,NewAssoc) :-
  put_assoc_act(OldAssoc,Key,Val,NewAssoc).
put_assoc_act([],Key,Val,[Key-Val]).
put_assoc_act([OAKey-OAValue|OldAssocRest],Key,Val,NewAssoc) :-
  (OAKey == Key)
  -> NewAssoc = [Key-Val|OldAssocRest]
   ; NewAssoc = [OAKey-OAValue|NewAssocRest],
     put_assoc_act(OldAssocRest,Key,Val,NewAssocRest).

assoc_to_list(L,L).
ord_list_to_assoc(L,L).

% end SWI patch code

:- dynamic no_interpreter/0.
:- dynamic no_subsumption/0.
:- dynamic subsume_ready/0.
:- dynamic go/1.
:- dynamic suppress_adderrs/0.
:- dynamic parsing/0, generating/0.
:- dynamic lexicon_consult/0.

:- discontiguous if_h/1.
:- discontiguous if_h/2.
:- discontiguous if_b/2.

parse :-
  retractall(generating),
  asserta(parsing),
  nl,write('compiler will produce code for parsing only'),
  nl.

generate :-
  retractall(parsing),
  asserta(generating),
  nl,write('compiler will produce code for generation only'),
  nl.

parse_and_gen :-
  asserta(parsing),
  asserta(generating),
  nl,write('compiler will produce code for parsing and generation'),
  nl.

lex_consult :-
  nl,write('In SWI Prolog, ALE always consults lexicon'),
  nl.

lex_compile :-
  nl,write('Not available in ALE for SWI Prolog'),
  nl.

interp :-
  retractall(no_interpreter),
  nl, write('interpreter is active'),
  nl.

nointerp :-
  asserta(no_interpreter),
  nl, write('interpreter is inactive'),
  nl.

subtest :-
  retractall(no_subsumption),
  compile_subsume,
  nl, write('edge/empty category subsumption checking active'),
  nl.
nosubtest :-
  asserta(no_subsumption),
  nl, write('edge/empty category subsumption checking inactive'),
  nl.

clear :-
  retractall(to_rebuild(_)),
  retractall(edge(_,_,_,_,_,_,_,_)),
  retractall(parsing(_)),
  retractall(num(_)), % edge index
  retractall(go(_)).  % interpreter go flag

noadderrs :-
  asserta(suppress_adderrs),
  nl, write('Errors from adding descriptions will be suppressed.'),
  nl.
adderrs :-
  retractall(suppress_adderrs),
  nl, write('Errors from adding descriptions will be displayed.'),
  nl.

secret_noadderrs :-
  asserta(suppress_adderrs).
secret_adderrs :-
  retractall(suppress_adderrs).

% ==============================================================================
% Operators
% ==============================================================================

% ------------------------------------------------------------------------------
% SRK Descriptions
% ------------------------------------------------------------------------------
:-op(375,fx,a_).
:-op(375,fx,@).
:-op(700,xfx,=@).
%:-op(700,xfx,==).
:-op(775,fx,=\=).
:-op(800,xfy,:).
%:-op(1000,xfy,',').
%:-op(1100,xfy,';').

% ------------------------------------------------------------------------------
% Signatures
% ------------------------------------------------------------------------------
:- dynamic sub_def/2.
:- dynamic max_def/1.

:-op(800,xfx,goal).
:-op(900,xfx,cons).
:-op(800,xfx,intro).
:-op(900,xfx,sub).
:-op(900,xfx,sub_def).
:-op(900,xfx,subs).

% ------------------------------------------------------------------------------
% Grammars
% ------------------------------------------------------------------------------
:-op(1125,xfy,then).
:-op(1150,xfx,===>).
:-op(1150,xfx,--->).
:-op(1150,xfx,macro).
:-op(1150,xfx,+++>).
:-op(1150,fx,empty).
:-op(1175,xfx,rule).
:-op(1175,xfx,lex_rule).
:-op(1160,xfx,morphs).
:-op(1125,xfx,'**>').
:-op(950,xfx,when).
:-op(900,xfx,becomes).
% 5/1/96 Octav - added operator for semantics/1 predicate
:-op(1175,fx,semantics).

% ------------------------------------------------------------------------------
% Definite Clauses
% ------------------------------------------------------------------------------
:-op(1150,xfx,if).

% ------------------------------------------------------------------------------
% Compiler
% ------------------------------------------------------------------------------
:-op(800,xfx,if_h).
:-op(800,xf,if_h).
:-op(800,xfx,if_b).
:-op(800,xf,if_b).
:-op(800,xfx,if_error).   
:-op(800,xfx,if_warning_else_fail).   
:-op(800,xfx,if_warning).

% ------------------------------------------------------------------------------
% I/O
% ------------------------------------------------------------------------------
:-op(1125,fx,mgsat).
:-op(1100,fx,macro).
:-op(1100,fx,query).
:-op(1100,fx,rule).
:-op(1100,fx,lex_rule).
:-op(1100,fx,show_clause).
:-op(1100,fx,rec).
:-op(1100,fx,lex).
:-op(1100,fx,gen).
:-op(800,fx,show_type).
:-op(500,fx,no_write_type).
:-op(500,fx,no_write_feat).  


% ==============================================================================
% Type Inheritance and Unification
% ==============================================================================

% Type:<type> sub Types:<type>s intro FRs:<fv>s                             user
% ------------------------------------------------------------------------------
% Types is set of immediate subtypes of Types and FRs is list
% of appropriate features paired with restrictions on values.
% When FRs is not specified, it is equivalent to '[]'.
% ------------------------------------------------------------------------------

% Type:<type> sub_def Types:<type>s intro FRs:<fv>s
% ------------------------------------------------------------------------------
%  Same as sub except these are asserted by the default type preprocessors
% ------------------------------------------------------------------------------

% Type:<type> subs Types:<types>s intro FRs:<fv>s
% ------------------------------------------------------------------------------
% Subsumption predicate for use in ALE.  If there is a sub_def clause with
%  left-hand argument Type, then subs uses that; otherwise, it uses sub
% ------------------------------------------------------------------------------
T subs Ts :-
  var(T)
  -> ( T sub_def Ts
     ; T sub Ts,
       \+ T sub_def _)
   ; (T sub_def Ts
      -> true
       ; T sub Ts).
     

% ------------------------------------------------------------------------------
% Type:<type> cons Cons:<desc> goal Goal:<goal>                             user
% ------------------------------------------------------------------------------
% Cons is the general description which must be satisfied by all structures of
%  type Type, and Goal is an optional procedural attachment which also must
%  be satisfied when present.  An absent constraint is equivalent to 'bot', 
%  and an absent goal is equivalent to 'true'.
% ------------------------------------------------------------------------------

% ------------------------------------------------------------------------------
% type(Type:<type>)                                                         eval
% ------------------------------------------------------------------------------
% Type is a type
% ------------------------------------------------------------------------------
type(Type):- 
    Type subs _.
type(a_ _).

% ------------------------------------------------------------------------------
% immed_subtypes(Type:<type>, SubTypes:<type>s)                             eval
% ------------------------------------------------------------------------------
% SubTypes is set of immediate subtypes of Type (SubTypes cover Type)
% ------------------------------------------------------------------------------
immed_subtypes(Type,SubTypes):-
    Type subs SubTypes, 
    \+ (SubTypes = (_ intro _))
  ; Type subs SubTypes intro _.

% ------------------------------------------------------------------------------
% imm_sub_type(Type:<type>, TypeSub:<type>)                                 eval
% ------------------------------------------------------------------------------
% TypeSub is immediate subtype of Type 
% ------------------------------------------------------------------------------
imm_sub_type(Type,TypeSub):-
  immed_subtypes(Type,TypeSubs),
  member(TypeSub,TypeSubs).

% ------------------------------------------------------------------------------
% immed_cons(Type:<type>,Cons:<desc>)
% ------------------------------------------------------------------------------
immed_cons(Type,Cons) :-
  type(Type),               % ALE WON'T CATCH A CONSTRAINT DEFINED FOR AN ATOM
  (\+current_predicate(cons,(_ cons _))  %  UNTIL THE COMPILER IS RUN
   -> Cons = none
   ;(Type cons Cons goal _ -> true ; Type cons Cons)).
  
% ------------------------------------------------------------------------------
% sub_type(Type:<type>, TypeSub:<type>)                                    mh(1)
% ------------------------------------------------------------------------------
% TypeSub is subtype of Type
% ------------------------------------------------------------------------------
(sub_type(Type,Type) if_h) :-
  Type subs _.  % dont want a_ atoms here - they get their own clause below
(sub_type(Type,TypeSub) if_h) :-
  setof(Type-TypeSubs, immed_subtypes(Type,TypeSubs), Graph),
  transitive_closure(Graph,NewGraph),
  member(Type-TypeSubs,NewGraph),
  member(TypeSub,TypeSubs),
            [subtyping,cycle,at,Type] if_error
                 TypeSub = Type.
(sub_type(bot,a_ _) if_h).
(sub_type(a_ X,a_ Y) if_h [subsumes_chk(X,Y)]).

% ------------------------------------------------------------------------------
% unify_type(Type1:<type>, Type2:<type>, TypeLUB:<type>)                   mh(1)
% ------------------------------------------------------------------------------
% Type1 unified with Type2 is TypeLUB
% ------------------------------------------------------------------------------
(unify_type(Type1,Type2,TypeLUB) if_h) :-
  setof(TypeUB, ( sub_type(Type1,TypeUB), \+(Type1 = a_ _),
                  sub_type(Type2,TypeUB), \+(Type2 = a_ _)), TypeUBs),
  map_minimal(TypeUBs,[],TypeLUBs),
            [consistent,Type1,and,Type2,have,multiple,mgus,TypeLUBs] if_error
                 ( TypeLUBs = [_,_|_],
                   Type1 @< Type2 ),
  TypeLUBs = [TypeLUB].
(unify_type(bot,a_ X,a_ X) if_h).
(unify_type(a_ X,bot,a_ X) if_h).
(unify_type(a_ X,a_ X,a_ X) if_h).  % subsumes_chk/2 unhooks the vars - need
                                    % to do it ourselves

% ------------------------------------------------------------------------------
% map_minimal(Ss:<types>, SsTemp:<types>, SsMin:<types>)
% ------------------------------------------------------------------------------
% holds if SsMin is the list of minimal types of Ss unioned with SsTemp;
% elements of SsTemp are always incomparable
% ------------------------------------------------------------------------------
map_minimal([],SsMin,SsMin).
map_minimal([S|Ss],SsTemp,SsMin):-
  insert_if_minimal(SsTemp,S,SsTempNew),
  map_minimal(Ss,SsTempNew,SsMin).

% ------------------------------------------------------------------------------
% insert_if_minimal(Ss:<type>s, S:<type>, Ss2:<type>s)
% ------------------------------------------------------------------------------
% Ss2 is minimal elts of (Ss U {S}) where we know Ss are incomparable
% ------------------------------------------------------------------------------
insert_if_minimal([],S,[S]).
insert_if_minimal([S2|Ss2],S,[S2|Ss2]):-
  sub_type(S2,S), !.
insert_if_minimal([S2|Ss2],S,Ss3):-
  sub_type(S,S2), !,
  insert_if_minimal(Ss2,S,Ss3).
insert_if_minimal([S2|Ss2],S,[S2|Ss3]):-
  insert_if_minimal(Ss2,S,Ss3).

% ------------------------------------------------------------------------------
% unify_types(Types:<type>s, Type:<type>)                                
% ------------------------------------------------------------------------------
% Type is unification of Types
% ------------------------------------------------------------------------------
unify_types([],bot).
unify_types([Type|Types],TypeUnif):-
  unify_types(Types,Type,TypeUnif).

% ------------------------------------------------------------------------------
% unify_types(Types:<type>s, Type:<type>, TypeUnif:<type>)                
% ------------------------------------------------------------------------------
% TypeUnif is unification of set consisting of Types and Type
% ------------------------------------------------------------------------------
unify_types([],Type,Type).
unify_types([Type|Types],TypeIn,TypeOut):-
  unify_type(Type,TypeIn,TypeMid),
  unify_types(Types,TypeMid,TypeOut).

% ------------------------------------------------------------------------------
% extensional(Sort:<sort)
% ------------------------------------------------------------------------------
% Sort is an extensional sort.  Extensional sorts are assumed to be maximal.
% ------------------------------------------------------------------------------


% ==============================================================================
% Appropriateness
% ==============================================================================

% ------------------------------------------------------------------------------
% feature(F:<feat>)
% ------------------------------------------------------------------------------
% holds if $F$ is a feature mentioned somewhere in the code
% ------------------------------------------------------------------------------
feature(Feat):-
  setof(F,Type^Subs^R^FRs^((Type subs Subs intro FRs),
                           member(F:R,FRs)), 
        Feats),
  member(Feat,Feats)
 ;setof(F,Type^R^FRs^((Type intro FRs),
                      member(F:R,FRs)),
        Feats),
  member(Feat,Feats).

% ------------------------------------------------------------------------------
% restricts(Type:<type>, Feat:<feat>, TypeRestr:<type>)                     eval
% ------------------------------------------------------------------------------
% Type introduces the feature Feat imposing value restriction TypeRestr 
% ------------------------------------------------------------------------------
restricts(Type,Feat,TypeRestr):-
  Type subs _ intro FRs,
  member(Feat:TypeRestr,FRs)
 ;Type intro FRs,
  member(Feat:TypeRestr,FRs).

% ------------------------------------------------------------------------------
% introduce(?Feat:<feat>, -Type:<type>)                                     eval
% ------------------------------------------------------------------------------
% Type is the most general type appropriate for Feat
% ------------------------------------------------------------------------------
introduce(Feat,Type):-
  setof(T,TypeRestr^restricts(T,Feat,TypeRestr),Types),
  map_minimal(Types,[],TypesMin),
            [feature,Feat,multiply,introduced,at,TypesMin] if_error
                 (\+ TypesMin = [_]),
  TypesMin = [Type].

% ------------------------------------------------------------------------------
% approp(Feat:<feat>, Type:<type>, TypeRestr:<type>)                       mh(1)
% ------------------------------------------------------------------------------
% approp(Feat,Type) = TypeRestr
% ------------------------------------------------------------------------------
(approp(Feat,Type,ValRestr) if_h) :-
  setof(TypeRestr,TypeSubs^(sub_type(TypeSubs,Type),
                            restricts(TypeSubs,Feat,TypeRestr)),
        TypeRestrs),
               [incompatible,restrictions,on,feature,Feat,at,type,Type,
                are,TypeRestrs] if_error
                    (\+ unify_types(TypeRestrs,ValRestr)),    
  unify_types(TypeRestrs,ValRestr).
approp(_,_,_) if_h [fail] :-
  \+(_ subs _ intro _),
  \+(_ intro _).

% ------------------------------------------------------------------------------
% approps(Type:<type>, FRs:<feat_val>s)                                     eval
% ------------------------------------------------------------------------------
% FRs is list of appropriateness declarations for Type
% ------------------------------------------------------------------------------
approps(Type,FRs):-
  type(Type),  % ALE WON'T CATCH FEATURES DEFINED FOR ATOMS UNTIL COMPILER RUNS
  esetof(Feat:TypeRestr, approp(Feat,Type,TypeRestr), FRs).

% ------------------------------------------------------------------------------
% approp_feats(Type:<type>,Fs:<feat>s)
% ------------------------------------------------------------------------------
% Fs is list of appropriate features for Type
% ------------------------------------------------------------------------------
approp_feats(Type,Fs) :-
  type(Type), % ALE WON'T CATCH FEATURES DEFINED FOR ATOMS UNTIL COMPILER RUNS 
  esetof(Feat,TypeRestr^approp(Feat,Type,TypeRestr),Fs).


% ==============================================================================
% Feature Structure Unification
% ==============================================================================

% ------------------------------------------------------------------------------
% ud(FS1:<fs>, FS2:<fs>, IqsIn:<ineq>s, IqsOut:<ineq>s)                     eval
% ------------------------------------------------------------------------------
% unifies FS1 and FS2 (after dereferencing); 
% ------------------------------------------------------------------------------
ud(FS1,FS2,IqsIn,IqsOut):-
  deref(FS1,Ref1,SVs1), deref(FS2,Ref2,SVs2),
  ( (Ref1 == Ref2) -> (IqsOut = IqsIn)
                    ; u(SVs1,SVs2,Ref1,Ref2,IqsIn,IqsOut)
  ).

% ud(FS:<fs>,Tag:<ref>,SVs:<svs>,IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% 5-place version of ud/4
% ------------------------------------------------------------------------------

ud(FS1,Tag2,SVs2,IqsIn,IqsOut) :-
  deref(FS1,RefOut1,SVsOut1), deref(Tag2,SVs2,RefOut2,SVsOut2),
  ( (RefOut1 == RefOut2) -> (IqsOut = IqsIn)
                          ; u(SVsOut1,SVsOut2,RefOut1,RefOut2,IqsIn,IqsOut)
  ).

% ud(Tag1:<ref>,SVs1:<svs>,Tag2:<ref>,SVs2:<svs>,IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% 6-place version of ud/4
% ------------------------------------------------------------------------------

ud(Tag1,SVs1,Tag2,SVs2,IqsIn,IqsOut) :-
  deref(Tag1,SVs1,RefOut1,SVsOut1), deref(Tag2,SVs2,RefOut2,SVsOut2),
  ( (RefOut1 == RefOut2) -> (IqsOut = IqsIn)
                          ; u(SVsOut1,SVsOut2,RefOut1,RefOut2,IqsIn,IqsOut)
  ).

% ------------------------------------------------------------------------------
% deref(FSIn:<fs>, RefOut:<ref>, SVsOut:<svs>)
% ------------------------------------------------------------------------------
% RefOut-SVsOut is result of dereferencing FSIn at top level
% ------------------------------------------------------------------------------
deref(Ref-Vs,RefOut,VsOut):-
  ( var(Ref) -> (RefOut = Ref, VsOut = Vs)
              ; deref(Ref,RefOut,VsOut)
  ).

% ------------------------------------------------------------------------------
% deref_list(RefsIn:<ref>s, RefsOut:<ref>s)
% ------------------------------------------------------------------------------
% applies deref/4 on all elements of RefsIn to get RefsOut
% ------------------------------------------------------------------------------
deref_list([],[]).
deref_list([Ref-Vs|Rest],[RefOut-VsOut|RestOut]) :-
  deref(Ref,Vs,RefOut,VsOut),
  deref_list(Rest,RestOut).

% ------------------------------------------------------------------------------
% deref(RefIn:<ref>,SVsIn:<svs>, RefOut:<ref>, SVsOut:<svs>)
% ------------------------------------------------------------------------------
% RefOut-SVsOut is result of dereferencing FSIn at top level
% ------------------------------------------------------------------------------
deref(Ref,Vs,RefOut,VsOut):-
  ( var(Ref) -> (RefOut = Ref, VsOut = Vs)
              ; deref(Ref,RefOut,VsOut)
  ).

% ------------------------------------------------------------------------------
% fully_deref_prune(RefIn:<ref>,SVsIn:<svs>, RefOut:<ref>, SVsOut:<svs>, 
%                   IqsIn:<ineq>s, IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% In addition to fully dereferencing the given feature structure, this
%  predicate checks the associated inequations both for their satisfaction,
%  and for their relevance, and rebuilds them in terms of the new feature
%  structure.  An inequation is deemed relevant if both of its terms are 
%  substructures of the given feature structure, or if one of its terms is, 
%  and the other one is fully extensional (which means that it and each of its 
%  substructures is of an extensional sort).  Currently, full extensionality is
%  not actually enforced, but rather only a check that the term itself is of an
%  extensional sort is made.
% ------------------------------------------------------------------------------
fully_deref_prune(Tag,SVs,TagOut,SVsOut,IqsIn,IqsOut) :-
  fully_deref(Tag,SVs,TagOut,SVsOut),
  prune(IqsIn,IqsOut). 

% 5/1/96 Octav -- added a clause for the case the inequations list is 
%   uninstantiated
% 5/5/97 -- Octav Popescu - removed to allow for first argument indexing
%prune(Var,Var) :- var(Var), !.			% !!! CHECK IF NECESSARY
prune([],[]).
prune([ineq(Tag1,SVs1,Tag2,SVs2,Ineqs)|IqsIn],IqsOut) :-
  prune_deref(Tag1,SVs1,Tag1Out,SVs1Out,InFlag1),
  prune_deref(Tag2,SVs2,Tag2Out,SVs2Out,InFlag2),
  ((InFlag1 = out)
   -> ((InFlag2 = out)           % both are out
       -> prune(IqsIn,IqsOut)
        ;                         % one is out, and it is intensional 
          (\+(SVs1 = a_ _),       % structure-sharing inside atoms could cause
           functor(SVs1,Sort1,_), %  trouble later - so keep them around
           \+extensional(Sort1))  
         -> prune(IqsIn,IqsOut)
          ; (check_inequal_conjunct(ineq(Tag1Out,SVs1Out,Tag2Out,SVs2Out,
                                         Ineqs),
                                    IqOut,Result),
            prune_act(Result,IqOut,IqsIn,IqsOut)))
    ; ((InFlag2 = out,
        \+(SVs2 = a_ _),
        functor(SVs2,Sort2,_),
        \+extensional(Sort2))
       -> prune(IqsIn,IqsOut)
        ; (check_inequal_conjunct(ineq(Tag1Out,SVs1Out,Tag2Out,SVs2Out,Ineqs),
                                  IqOut,Result),
           prune_act(Result,IqOut,IqsIn,IqsOut)))).

prune_act(done,done,_,_) :-   % conjunct failed
  !,fail.
prune_act(succeed,_,IqsIn,IqsOut) :-  % conjunct succeeded
  !,prune(IqsIn,IqsOut).
prune_act(_,IqOut,IqsIn,[IqOut|IqsOut]) :-  % conjunct temporarily succeeded
  prune(IqsIn,IqsOut).

prune_deref(Tag,SVs,Tag,SVsOut,out) :-
  var(Tag),
  !,
  ((SVs = a_ _) -> (SVsOut = SVs)
                 ; (SVs =.. [Sort|Vs], % some substructures may still be shared
                    prune_deref_feats(Vs,VsOut),
                    SVsOut =.. [Sort|VsOut])
  ).
prune_deref(fully(TagOut,SVsOut),_,TagOut,SVsOut,in).
prune_deref(Tag-SVs,_,TagOut,SVsOut,InFlag) :-
  prune_deref(Tag,SVs,TagOut,SVsOut,InFlag).

prune_deref_feats([],[]).
prune_deref_feats([Ref-SVs|Vs],[RefOut-SVsOut|VsOut]) :-
  prune_deref(Ref,SVs,RefOut,SVsOut,_),
  prune_deref_feats(Vs,VsOut).

% ------------------------------------------------------------------------------
% fully_deref(RefIn:<ref>,SVsIn:<svs>, RefOut:<ref>, SVsOut:<svs>)
% ------------------------------------------------------------------------------
% RefOut-SVsOut is result of recursively dereferencing FSIn;
% destroys RefIn-SVsIn by overwriting Tags
% ------------------------------------------------------------------------------
fully_deref(Tag,SVs,TagOut,SVsOut):-
  ( nonvar(Tag) -> fully_deref_act(Tag,SVs,TagOut,SVsOut)
                 ; Tag = (fully(TagOut,SVsOut)-SVsOut),
                   ((SVs = a_ X) -> SVsOut = a_ X
                                  ; (functor(SVs,Rel,Arity),
                                     functor(SVsOut,Rel,Arity),
                                     fully_deref_args(Arity,SVs,SVsOut))
                   )
  ).

fully_deref_act(fully(TagOut,_),SVs,TagOut,SVs).
fully_deref_act(TagMid-SVsMid,_,TagOut,SVsOut):-
  fully_deref(TagMid,SVsMid,TagOut,SVsOut).

fully_deref_args(0,_,_):-!.
fully_deref_args(N,SVs,SVsOut):-
  arg(N,SVs,TagN-SVsN),
  fully_deref(TagN,SVsN,TagOutN,SVsOutN),
  arg(N,SVsOut,TagOutN-SVsOutN),
  M is N-1,
  fully_deref_args(M,SVs,SVsOut).

% ------------------------------------------------------------------------------
% u(SVs1:<svs>,SVs2:<svs>,Ref1:<ref>,Ref2:<ref>,IqsIn:<ineq>s,
%   IqsOut:<ineqs>)                                                        mh(2)
% ------------------------------------------------------------------------------
% compiles typed version of the Martelli and Montanari unification
% algorithm for dereferenced feature structures Ref1-SVs1 and Ref2-SVs2 
% ------------------------------------------------------------------------------
u(SVs1,SVs2,Ref1,Ref2,IqsIn,IqsOut) if_h SubGoals:-
  unify_type(Type1,Type2,Type3),
  uact(Type3,SVs1,SVs2,Ref1,Ref2,Type1,Type2,IqsIn,IqsOut,SubGoals).

% ------------------------------------------------------------------------------
% uact(Type3,SVs1,SVs2,Ref1,Ref2,Type1,Type2,IqsIn,IqsOut,SubGoals)
% ------------------------------------------------------------------------------
% SubGoals is list of goals required to unify Ref1-SVs1 and Ref2-SVs2,
% where Ref1-SVs1 is of type Type1, Ref2-SVs2 is of type Type2 and
% Type1 unify Type2 = Type3
% ------------------------------------------------------------------------------
uact(a_ X,a_ X,a_ X,Ref,Ref,a_ X,a_ X,Iqs,Iqs,[]) :- !.
uact(a_ X,bot,a_ X,Ref-(a_ X),Ref,bot,a_ X,Iqs,Iqs,[]) :- !.
uact(a_ X,a_ X,bot,Ref,Ref-(a_ X),a_ X,bot,Iqs,Iqs,[]) :- !.
uact(Type3,SVs1,SVs2,Ref1,Ref2,Type1,Type2,IqsIn,IqsOut,SubGoals):-
  approps(Type1,FRs1),    % we know Type1, Type2, and Type3 aren't a_ atoms
  ( (Type1 = Type2)
    -> (Ref1 = Ref2,
        map_feats_eq(FRs1,Vs1,Vs2,IqsIn,IqsOut,SubGoals))
     ; approps(Type2,FRs2),                % Type1 \== Type2,
       ( (Type2 = Type3)
         -> (Ref1 = Ref2-SVs2,
             map_feats_subs(FRs1,FRs2,Vs1,Vs2,IqsIn,IqsOut,SubGoals))
          ; ((Type1 = Type3)
             -> (Ref2 = Ref1-SVs1,
                 map_feats_subs(FRs2,FRs1,Vs2,Vs1,IqsIn,IqsOut,SubGoals))
              ; (Ref1 = Tag3-SVs3, Ref2 = Ref1, % Type1\==Type3,Type2 \== Type3
		 (((FRs2 = []),(FRs1 = []))
		  -> (mgsc(Type3,SVs3,Tag3,IqsIn,IqsOut,SubGoals,[]),
		      Vs2 = [],
	              Vs1 = [])
                   ; (approps(Type3,FRs3),
                      map_feats_unif(FRs1,FRs2,FRs3,Vs1,Vs2,Vs3,IqsIn,IqsMid,
                                     SubGoals,SubGoalsRest),
                      ucons(Type3,Type2,Type1,Tag3,SVs3,IqsMid,IqsOut,
			    SubGoalsRest),
                      SVs3 =.. [Type3|Vs3]))))
       )
  ),
  SVs1 =.. [Type1|Vs1],
  SVs2 =.. [Type2|Vs2].

% ------------------------------------------------------------------------------
% ucons(Type:<type>,ExclType1:<type>,ExclType2:<type>,Tag:<ref>,SVs:<sv>s,
%       IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% Enforce the constraint for Type, and for all supersorts of Type, excluding
%  ExclType1 and ExclType2, on Tag-SVs
% ------------------------------------------------------------------------------
ucons(Type,ET1,ET2,Tag,SVs,IqsIn,IqsOut,SubGoals) :-
  esetof(T,(sub_type(T,Type),  % find set of types whose constraints must be
            \+sub_type(T,ET1), %  satisfied
            \+sub_type(T,ET2)),ConsTypes),
  map_cons(ConsTypes,Tag,SVs,IqsIn,IqsOut,SubGoals,[]).

% ------------------------------------------------------------------------------
% ct(Type:<type>,Tag:<ref>,SVs:<sv>s,Goals:<goal>s,Rest:<goal>s,IqsIn:<ineq>s,
%    IqsOut,<ineq>s)
% ------------------------------------------------------------------------------
% Goals, with tail Rest, are the compiled goals of the description (and
%  clause) attached to Type, enforced on feature structure Tag-SVs
% ------------------------------------------------------------------------------

ct(_Type,_Tag,_SVs,Rest,Rest,Iqs,Iqs) if_b [] :-
  \+ current_predicate(cons,(_ cons _)),
  !.
ct(Type,Tag,SVs,Goals,Rest,IqsIn,IqsOut) if_b [!] :-
  empty_assoc(VarsIn),
  Type cons Cons goal Goal,
  compile_desc(Cons,Tag,SVs,IqsIn,IqsMid,GoalsMid,GoalsMid2,true,VarsIn,
               VarsMid,FSPal,[],FSsMid),
  compile_body(Goal,IqsMid,IqsOut,GoalsMid2,Rest,true,VarsMid,_,FSPal,FSsMid,
               FSsOut),
  build_fs_palette(FSsOut,FSPal,Goals,GoalsMid,[]).
ct(Type,Tag,SVs,Goals,Rest,IqsIn,IqsOut) if_b [!] :-
  empty_assoc(VarsIn),
  Type cons Cons,
  \+ (Cons = (_ goal _)),
  compile_desc(Cons,Tag,SVs,IqsIn,IqsOut,GoalsMid,Rest,true,VarsIn,_,FSPal,[],
               FSsOut),
  build_fs_palette(FSsOut,FSPal,Goals,GoalsMid,[]).
ct(_Type,_Tag,_SVs,Rest,Rest,Iqs,Iqs) if_b [].    % all other types

% ------------------------------------------------------------------------------
% map_cons(Types:<type>s,Tag:<ref>,SVs:<sv>s,IqsIn:<ineq>s,IqsOut:<ineq>s,
%          SubGoals:<goal>s,SubGoalsRest:<goal>s)
% ------------------------------------------------------------------------------
% Given a set of types, strings together the goals and inequations for them.
% ------------------------------------------------------------------------------
map_cons([],_,_,Iqs,Iqs,Goals,Goals).
map_cons([Type|Types],Tag,SVs,IqsIn,IqsOut,SubGoals,SubGoalsRest) :-
  ct(Type,Tag,SVs,SubGoals,SubGoalsMid,IqsIn,IqsMid),
  map_cons(Types,Tag,SVs,IqsMid,IqsOut,SubGoalsMid,SubGoalsRest).

% ------------------------------------------------------------------------------
% map_feats_eq(FRs:<feat>s,Vs1:<fs>s,Vs2:<fs>s,IqsIn:<ineq>s,IqsOut:<ineq>s,
%              Goals:<goal>s)
% ------------------------------------------------------------------------------
% Vs1 and Vs2 set to same length as FRs and a subgoal added to Goals
% to unify value of each feature;
% ------------------------------------------------------------------------------
map_feats_eq([],[],[],Iqs,Iqs,[]).
map_feats_eq([_|FRs],[V1|Vs1],[V2|Vs2],IqsIn,IqsOut,
             [ud(V1,V2,IqsIn,IqsMid)|SubGoals]):-
  map_feats_eq(FRs,Vs1,Vs2,IqsMid,IqsOut,SubGoals).
  
% ------------------------------------------------------------------------------
% map_feats_subs(FRs1:<feat>s, FRs2:<feat>s, Vs1:<fs>s, Vs2:<fs>s, 
%                IqsIn:<ineq>s, IqsOut:<ineq>s, Goals:<goal>s) 
% ------------------------------------------------------------------------------
% Vs1 and Vs2 set to same length as FRs1 and FRs2 and a subgoal 
% added to Goals for each shared feature;  
% ------------------------------------------------------------------------------
map_feats_subs([],FRs,[],Vs,Iqs,Iqs,[]):-
  same_length(FRs,Vs).
map_feats_subs([F:_|FRs1],FRs2,[V1|Vs1],Vs2,IqsIn,IqsOut,
                [ud(V1,V2,IqsIn,IqsMid)|SubGoals]):-
  map_feats_find(F,FRs2,V2,Vs2,FRs2Out,Vs2Out),
  map_feats_subs(FRs1,FRs2Out,Vs1,Vs2Out,IqsMid,IqsOut,SubGoals).

% ------------------------------------------------------------------------------
% map_feats_find(F:<feat>, FRs:<feat>s, V:<fs>, Vs:<fs>s, 
%                FRsOut:<feat>s, VsOut:<fs>s)
% ------------------------------------------------------------------------------
% if F is the Nth element of FRs then V is the Nth element of Vs;
% FRsOut and VsOut are the rest (after the Nth) of FRs and Vs
% ------------------------------------------------------------------------------
map_feats_find(F,[F:_|FRs],V,[V|Vs],FRs,Vs):-!.
map_feats_find(F,[_|FRs],V,[_|Vs],FRsOut,VsOut):-
  map_feats_find(F,FRs,V,Vs,FRsOut,VsOut).

% ------------------------------------------------------------------------------
% map_feats_unif(FRs1:<feat>s,FRs2:<feat>s,FRs3:<feat>s,Vs1:<fs>s,Vs2:<fs>s,
%                 Vs3:<fs>s,IqsIn:<ineq>s,IqsOut:<ineq>s,Goals:<goal>s,
%                 GoalsRest:<goal>s)
% ------------------------------------------------------------------------------
% Vs1, Vs2 and Vs3 set to same length as Feats1, FRs2 and FRs3;
% a subgoal's added to Goals for each feature shared in FRs1 and FRs2;  
% feats shared in Vs1,Vs2 and Vs3 passed; new Vs3 entries are created
% ------------------------------------------------------------------------------
map_feats_unif([],FRs2,FRs3,[],Vs2,Vs3,IqsIn,IqsOut,Goals,GoalsRest):-
  map_new_feats(FRs2,FRs3,Vs2,Vs3,IqsIn,IqsOut,Goals,GoalsRest).
map_feats_unif([F1:R1|FRs1],FRs2,FRs3,Vs1,Vs2,Vs3,IqsIn,IqsOut,Goals,
               GoalsRest):-
  map_feats_unif_ne(FRs2,F1,R1,FRs1,FRs3,Vs1,Vs2,Vs3,IqsIn,IqsOut,Goals,
                    GoalsRest).

map_feats_unif_ne([],F1,R1,FRs1,FRs3,Vs1,[],Vs3,IqsIn,IqsOut,Goals,GoalsRest):-
  map_new_feats([F1:R1|FRs1],FRs3,Vs1,Vs3,IqsIn,IqsOut,Goals,GoalsRest).
map_feats_unif_ne([F2:R2|FRs2],F1,R1,FRs1,FRs3,Vs1,Vs2,Vs3,
                  IqsIn,IqsOut,Goals,GoalsRest):-
  compare(Comp,F1,F2),
  map_feats_unif_act(Comp,F1,F2,R1,R2,FRs1,FRs2,FRs3,Vs1,Vs2,Vs3,
                     IqsIn,IqsOut,Goals,GoalsRest).

map_feats_unif_act(=,F1,_F2,R1,R2,FRs1,FRs2,FRs3,[V1|Vs1],[V2|Vs2],Vs3,
                   IqsIn,IqsOut,[ud(V1,V2,IqsIn,IqsMid)|Goals1],GoalsRest):-
  unify_type(R1,R2,R1UnifyR2),
  map_new_feats_find(F1,R1UnifyR2,FRs3,V1,Vs3,FRs3Out,Vs3Out,IqsMid,IqsMid2,
                     Goals1,Goals2),
  map_feats_unif(FRs1,FRs2,FRs3Out,Vs1,Vs2,Vs3Out,IqsMid2,IqsOut,Goals2,
                 GoalsRest).
map_feats_unif_act(<,F1,F2,R1,R2,FRs1,FRs2,FRs3,[V1|Vs1],Vs2,Vs3,
                   IqsIn,IqsOut,Goals,GoalsRest2):-
  map_new_feats_find(F1,R1,FRs3,V1,Vs3,FRs3Out,Vs3Out,IqsIn,IqsMid,
                     Goals,GoalsRest1),
  map_feats_unif_ne(FRs1,F2,R2,FRs2,FRs3Out,Vs2,Vs1,Vs3Out,
                    IqsMid,IqsOut,GoalsRest1,GoalsRest2).
map_feats_unif_act(>,F1,F2,R1,R2,FRs1,FRs2,FRs3,Vs1,[V2|Vs2],Vs3,
                   IqsIn,IqsOut,Goals,GoalsRest2):-
  map_new_feats_find(F2,R2,FRs3,V2,Vs3,FRs3Out,Vs3Out,IqsIn,IqsMid,
                     Goals,GoalsRest1),
  map_feats_unif_ne(FRs2,F1,R1,FRs1,FRs3Out,Vs1,Vs2,Vs3Out,
                    IqsMid,IqsOut,GoalsRest1,GoalsRest2).

% ------------------------------------------------------------------------------
% map_new_feats(FRs:<feat>s, FRsNew:<feat>s, Vs:<fs>s, VsNew:<fs>s, 
%               IqsIn:<ineq>s,IqsOut:<ineq>s,Gs:<goal>s,GsRest:<goal>s)
% ------------------------------------------------------------------------------
% FRs and FRsNew must be instantiated in alpha order where
% FRs is a sublist of NewFs;
% create Vs and VsNew where Vs and VsNew share a value if the
% feature in Fs and NewFs matches up, otherwise VsNew gets a fresh
% minimum feature structure (_-bot) for a value;
% all necessary value coercion is also performed
% ------------------------------------------------------------------------------
map_new_feats([],FRsNew,[],VsNew,IqsIn,IqsOut,SubGoals,SubGoalsRest):-
  map_new_feats_introduced(FRsNew,VsNew,IqsIn,IqsOut,SubGoals,SubGoalsRest).
map_new_feats([Feat:TypeRestr|FRs],FRsNew,[V|Vs],VsNew,IqsIn,IqsOut,SubGoals,
              SubGoalsRest2):-
  map_new_feats_find(Feat,TypeRestr,FRsNew,V,VsNew,
                     FRsNewLeft,VsNewLeft,IqsIn,IqsMid,SubGoals,SubGoalsRest1),
 map_new_feats(FRs,FRsNewLeft,Vs,VsNewLeft,IqsMid,IqsOut,SubGoalsRest1,
               SubGoalsRest2).

% ------------------------------------------------------------------------------
% map_new_feats_find(Feat,TypeRestr,FRs,V,Vs,FRs2,Vs2,IqsIn,IqsOut,
%                    SubGoals,SubGoalsRest)
% ------------------------------------------------------------------------------
% finds Feat value V in Vs, parallel to FRs, with restriction TypeRestr on V, 
% with FRs2 being left over;  carries out coercion on new feature values
% with SubGoals-SubGoalsRest being the code to do this
% ------------------------------------------------------------------------------
map_new_feats_find(Feat,TypeRestr,[Feat:TypeRestrNew|FRs],
                    V,[V|Vs],FRs,Vs,IqsIn,IqsOut,SubGoals,SubGoalsRest):-
  !,
  ( sub_type(TypeRestrNew,TypeRestr)
    -> (SubGoals = SubGoalsRest,
        IqsOut = IqsIn)
     ; ((TypeRestrNew = a_ X)
        -> (Goal =.. ['add_to_type_a_',SVs,Tag,IqsIn,IqsOut,X],
            SubGoals = [deref(V,Tag,SVs),Goal|SubGoalsRest])
         ; (cat_atoms(add_to_type_,TypeRestrNew,Rel),
            Goal =.. [Rel,SVs,Tag,IqsIn,IqsOut],
            SubGoals = [deref(V,Tag,SVs),Goal|SubGoalsRest]))
  ).
map_new_feats_find(Feat,TypeRestr,[_:TypeRestrNew|FRs],
                   V,[(Tag-SVs)|Vs],FRsNew,VsNew,IqsIn,IqsOut,
                   SubGoals,SubGoalsRest):-
 mgsc(TypeRestrNew,SVs,Tag,IqsIn,IqsMid,SubGoals,SubGoalsMid),
%(   (TypeRestrNew = a_ X)
%  -> Goal =.. ['add_to_type_a_',bot,Tag,IqsIn,IqsMid,X]
%   ; (cat_atoms(add_to_type_,TypeRestrNew,Rel),
%      Goal =.. [Rel,bot,Tag,IqsIn,IqsMid])),
 map_new_feats_find(Feat,TypeRestr,FRs,V,Vs,FRsNew,
                    VsNew,IqsMid,IqsOut,SubGoalsMid,SubGoalsRest).

% ------------------------------------------------------------------------------
% map_new_feats_introduced(FRs,Vs,IqsIn,IqsOut,SubGoals,SubGoalsRest)
% ------------------------------------------------------------------------------
% instantiates Vs to act as values of features in FRs;  SubGoals contains
% type coercions necessary so that Vs satisfy constraints in FRs
% ------------------------------------------------------------------------------
map_new_feats_introduced([],[],Iqs,Iqs,Rest,Rest).
map_new_feats_introduced([_:TypeRestr|FRs],[(Ref-SVs)|Vs],IqsIn,IqsOut,
                         SubGoals,SubGoalsRest):-
 mgsc(TypeRestr,SVs,Ref,IqsIn,IqsMid,SubGoals,SubGoalsMid),  
% ((TypeRestr = a_ X)
%  -> Goal =.. ['add_to_type_a_',bot,Ref,IqsIn,IqsMid,X]
%   ; (cat_atoms(add_to_type_,TypeRestr,Rel),
%      Goal =.. [Rel,bot,Ref,IqsIn,IqsMid])),
 map_new_feats_introduced(FRs,Vs,IqsMid,IqsOut,SubGoalsMid,SubGoalsRest).


% ==============================================================================
% Lexical Rules
% ==============================================================================

% ------------------------------------------------------------------------------
% lex_rule(WordIn,TagIn,SVsIn,WordOut,TagOut,SVsOut,IqsIn,IqsOut)          mh(0)
% ------------------------------------------------------------------------------
% WordOut with category TagOut-SVsOut can be produced from
% WordIn with category TagIn-SVsIn by the application of a single
% lexical rule;  TagOut-SVsOut is fully dereferenced on output;
% Words are converted to character lists and back again
% ------------------------------------------------------------------------------
lex_rule(WordIn,TagIn,SVsIn,WordOut,TagOut,SVsOut,IqsIn,IqsOut) 
                                                   if_h SubGoals :-
  ( (LexRuleName lex_rule DescIn **> DescOut morphs Morphs),
    Cond = true
  ; (LexRuleName lex_rule DescIn **> DescOut if Cond morphs Morphs)
  ),
  empty_assoc(VarsIn),
  compile_desc(DescIn,TagIn,SVsIn,IqsIn,IqsMid,SubGoalsFinal,SubGoalsRest1,
               true,VarsIn,VarsMid,FSPal,[],FSsMid),
  compile_body(Cond,IqsMid,IqsMid2,SubGoalsRest1,SubGoalsMid,true,VarsMid,
               VarsMid2,FSPal,FSsMid,FSsMid2),
  compile_desc(DescOut,TagMid,bot,IqsMid2,IqsMid3,SubGoalsMid,
               [morph(Morphs,WordIn,WordOut),
                fully_deref_prune(TagMid,bot,TagOut,SVsOut,IqsMid3,IqsOut)],
               true,VarsMid2,_,FSPal,FSsMid2,FSsOut),
  build_fs_palette(FSsOut,FSPal,SubGoals,SubGoalsFinal,[]).

% ------------------------------------------------------------------------------
% morph(Morphs,WordIn,WordOut)
% ------------------------------------------------------------------------------
% converst WordIn to list of chars, performs morph_chars using Morphs
% and then converts resulting characters to WordOut
% ------------------------------------------------------------------------------
morph(Morphs,WordIn,WordOut):-
  name(WordIn,CodesIn),
  make_char_list(CodesIn,CharsIn), 
  morph_chars(Morphs,CharsIn,CharsOut),
  make_char_list(CodesOut,CharsOut),
  name(WordOut,CodesOut).

% ------------------------------------------------------------------------------
% morph_chars(Morphs:<seq(<morph>)>, 
%             CharsIn:<list(<char>)>, CharsOut:<list(<char>)>)
% ------------------------------------------------------------------------------
% applies first pattern rewriting in Morphs that matches input CharsIn
% to produce output CharsOut;  CharsIn should be instantiated and
% CharsOut should be uninstantiated for sound result
% ------------------------------------------------------------------------------
morph_chars((Morph,Morphs),CharsIn,CharsOut):-
    morph_template(Morph,CharsIn,CharsOut) 
    -> true
     ; morph_chars(Morphs,CharsIn,CharsOut).
morph_chars(Morph,CharsIn,CharsOut):-
  morph_template(Morph,CharsIn,CharsOut).

% ------------------------------------------------------------------------------
% morph_template(Morph:<morph>, CharsIn:<chars>, CharsOut:<chars>)
% ------------------------------------------------------------------------------
% applies tempalte Morph to CharsIn to produce Chars Out;  first
% breaks Morph into an input and output pattern and optional condition
% ------------------------------------------------------------------------------
morph_template((PattIn becomes PattOut),CharsIn,CharsOut):-
  morph_pattern(PattIn,CharsIn),
  morph_pattern(PattOut,CharsOut).
morph_template((PattIn becomes PattOut when Cond),CharsIn,CharsOut):-
  morph_pattern(PattIn,CharsIn),
  call(Cond),
  morph_pattern(PattOut,CharsOut).

% ------------------------------------------------------------------------------
% morph_pattern(Patt:<pattern>,Chars:<list(<char>)>)
% ------------------------------------------------------------------------------
% apply pattern Patt, which is sequence of atomic patterns,
% to list of characters Chars, using conc/3 to deconstruct Chars
% ------------------------------------------------------------------------------
morph_pattern(Var,CharsIn):-
  var(Var),  
  !, Var = CharsIn.
morph_pattern((AtPatt,Patt),CharsIn):-
  !, make_patt_list(AtPatt,List),
  append(List,CharsMid,CharsIn),
  morph_pattern(Patt,CharsMid).
morph_pattern(AtPatt,CharsIn):-
  make_patt_list(AtPatt,CharsIn).

% ------------------------------------------------------------------------------
% make_patt_list(AtPatt:<atomic_pattern>,List:<list(<char>)>)
% ------------------------------------------------------------------------------
% turns an atomic pattern AtPatt, either a variable, list of characters
% or atom into a list of characters (or possibly a variable);  List
% should not be instantiated
% ------------------------------------------------------------------------------
make_patt_list(Var,Var):-
  var(Var),
  !.
make_patt_list([H|T],[H|TOut]):-
  !, make_patt_list(T,TOut).
make_patt_list([],[]):-
  !.
make_patt_list(Atom,CharList):-
  atom(Atom),
  name(Atom,Name),
  make_char_list(Name,CharList).

% ------------------------------------------------------------------------------
% make_char_list(CharNames:<list(<ascii>)>, CharList:<list(<char>)>)
% ------------------------------------------------------------------------------
% turns list of character ASCII codes and returns list of corresponding
% characters
% ------------------------------------------------------------------------------
make_char_list([],[]).
make_char_list([CharName|Name],[Char|CharList]):-
  name(Char,[CharName]),
  make_char_list(Name,CharList).


% ==============================================================================
% Rounds-Kasper Logic
% ==============================================================================

% ------------------------------------------------------------------------------
% add_to(Phi:<desc>, Tag:<tag>, SVs:<svs>, IqsIn:<ineq>s, IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% Info in Phi is added to FSIn (FSIn already derefenced);
% ------------------------------------------------------------------------------
add_to(X,Ref2,SVs2,Iqs,Iqs) :-
  var(X),
  !,(X = Ref2-SVs2).
add_to(Ref1-SVs1,Ref2,SVs2,IqsIn,IqsOut):-
  !,
  if((deref(Ref1,SVs1,Ref3,SVs3),
      u(SVs2,SVs3,Ref2,Ref3,IqsIn,IqsOut)),
     true,
     (suppress_adderrs -> fail
     ; error_msg((nl, write('add_to could not unify '),
             \+ \+ (duplicates_list([Ref1-SVs1,Ref2-SVs2],IqsIn,[],_,[],_,0,_),
                     nl,tab(5),pp_fs(Ref1-SVs1,[],VisMid,5), nl, 
                     write('and '), pp_fs(Ref2-SVs2,VisMid,VisOut,5),
                     pp_iqs(IqsIn,VisOut,_,5)),
                 ttynl)))).
add_to([],Ref,SVs,IqsIn,IqsOut):-
  !, add_to(e_list,Ref,SVs,IqsIn,IqsOut).
add_to([H|T],Ref,SVs,IqsIn,IqsOut):-
  !, add_to((hd:H,tl:T),Ref,SVs,IqsIn,IqsOut).
add_to(Path1 == Path2,Tag,SVs,IqsIn,IqsOut):-
  !, pathval(Path1,Tag,SVs,TagAtPath1,SVsAtPath1,IqsIn,IqsMid),
  deref(Tag,SVs,TagMid,SVsMid),
  pathval(Path2,TagMid,SVsMid,TagAtPath2,SVsAtPath2,IqsMid,IqsMid2),
  if(u(SVsAtPath1,SVsAtPath2,TagAtPath1,TagAtPath2,IqsMid2,IqsOut),
     true,
     (suppress_adderrs -> fail
     ; error_msg((nl, write('add_to could not unify paths '), 
                 write(Path1), write(' and '), 
                 write(Path2), write(' in '),
                 nl, pp_fs(Tag-SVs,IqsIn,5),
                 ttynl)))).
add_to(=\= Desc,Tag,SVs,IqsIn,IqsOut):-
  !,add_to(Desc,Tag2,bot,IqsIn,IqsMid),
  check_inequal_conjunct(ineq(Tag,SVs,Tag2,bot,done),IqOut,Result),
  ( (Result = succeed)
    -> IqsOut = IqsMid
     ; ((IqOut \== done)
        -> IqsOut = [IqOut|IqsMid]
         ; (suppress_adderrs 
            -> fail
             ; error_msg((nl, write('add_to could not inequate '),
                   nl, pp_fs(Tag2-bot,[],5),
                   nl, write('and '),
                   nl, pp_fs(Tag-SVs,IqsIn,5),
                   ttynl))))).

add_to(Feat:Desc,Ref,SVs,IqsIn,IqsOut):-
  !, 
  if(featval(Feat,SVs,Ref,FSatFeat,IqsIn,IqsMid), 
     (deref(FSatFeat,RefatFeat,SVsatFeat),
      add_to(Desc,RefatFeat,SVsatFeat,IqsMid,IqsOut)),
     (suppress_adderrs
      -> fail
       ; error_msg((nl, write('add_to could not add feature '), write(Feat), 
                    write(' to '), pp_fs(Ref-SVs,IqsIn,5),
                    ttynl)))).
add_to((Desc1,Desc2),Ref,SVs,IqsIn,IqsOut):-
  !, add_to(Desc1,Ref,SVs,IqsIn,IqsMid),
  deref(Ref,SVs,Ref2,SVs2), 
  add_to(Desc2,Ref2,SVs2,IqsMid,IqsOut).
add_to((Desc1;Desc2),Ref,SVs,IqsIn,IqsOut):-
  !, 
  ( add_to(Desc1,Ref,SVs,IqsIn,IqsOut)
  ; add_to(Desc2,Ref,SVs,IqsIn,IqsOut)
  ).
add_to(@ MacroName,Ref,SVs,IqsIn,IqsOut):-
  !, 
  if((MacroName macro Desc),
     add_to(Desc,Ref,SVs,IqsIn,IqsOut),
     error_msg((nl, write('add_to could not add undefined macro '),
                write(MacroName),
                write(' to '), pp_fs(Ref-SVs,IqsIn,5),
                ttynl))).
add_to(Type,Ref,SVs,IqsIn,IqsOut):-
  type(Type),
  !,
  if(add_to_type(Type,SVs,Ref,IqsIn,IqsOut),
     true,
     (suppress_adderrs
      -> fail
       ; error_msg((nl, write('add_to could not add incompatible type '), 
                   write(Type),
                   nl, write('to '), pp_fs(Ref-SVs,IqsIn,5),
                   ttynl)))).
add_to(FunDesc,Ref,SVs,IqsIn,IqsOut) :-   % complex function constraints
  fun(FunDesc),
  !,mg_sat_goal(FunDesc,Fun,IqsIn,IqsMid), % can use for fun. desc.'s too
  fsolve(Fun,Ref,SVs,IqsMid,IqsOut).
add_to(Atom,Ref,SVs,Iqs,Iqs) :-
  atomic(Atom),
  !, 
  error_msg((nl, write('add_to could not add undefined type '), write(Atom),
             nl, write('to '), pp_fs(Ref-SVs,Iqs,5),
             ttynl)).
add_to(Desc,Ref,SVs,Iqs,Iqs):-
  error_msg((nl,write('add_to could not add ill formed complex description '), 
            nl, tab(5), write(Desc),
            nl, write('to '),
            pp_fs(Ref-SVs,Iqs,5),
            ttynl)).

% add_to_list(Descs:<desc>s,FSs:<fs>s,IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
%  add each description in Descs to the respective FS in FSs
% ------------------------------------------------------------------------------
add_to_list([],[],Iqs,Iqs).
add_to_list([Desc|Descs],[FS|FSs],IqsIn,IqsOut) :-
  deref(FS,Tag,SVs),
  add_to(Desc,Tag,SVs,IqsIn,IqsMid),
  add_to_list(Descs,FSs,IqsMid,IqsOut).

% add_to_fresh(Descs:<desc>s,FSs:<fs>s,IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
%  same as add_to_list, but instantiates the FS's first to bottom
% ------------------------------------------------------------------------------
add_to_fresh([],[],Iqs,Iqs).
add_to_fresh([Desc|Descs],[Ref-bot|FSs],IqsIn,IqsOut) :-
  add_to(Desc,Ref,bot,IqsIn,IqsMid),
  add_to_fresh(Descs,FSs,IqsMid,IqsOut).

% ------------------------------------------------------------------------------
% pathval(P:<path>,TagIn:<tag>,SVsIn:<svs>,TagOut:<tag:,SVsOut:<svs>,
%         IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% TagOut-SVsOut is the undereferenced value of dereferenced TagIn-SVsIn
% at path P
% ------------------------------------------------------------------------------
pathval([],Tag,SVs,Tag,SVs,Iqs,Iqs).
pathval([Feat|Path],Tag,SVs,TagOut,SVsOut,IqsIn,IqsOut):-
  if(featval(Feat,SVs,Tag,FSMid,IqsIn,IqsMid),
     (deref(FSMid,TagMid,SVsMid),
      pathval(Path,TagMid,SVsMid,TagOut,SVsOut,IqsMid,IqsOut)),
     (suppress_adderrs
      -> fail
       ; (write('feature '), write(Feat), write(' in path '), 
          write([Feat|Path]), write('could not be added to '), 
          pp_fs(Tag-SVs,[],5),
          fail))).

% ------------------------------------------------------------------------------
% add_to_type(Type:<type>,SVs:<svs>,Ref:<ref>,IqsIn:<ineq>s,
%             IqsOut:<ineq>s)                                              mh(2)
% ------------------------------------------------------------------------------
% adds Type to Ref-SVs -- arranged so that it can be compiled
% ------------------------------------------------------------------------------
add_to_type(Type1,SVs2,Ref,IqsIn,IqsOut) if_h SubGoals :-
  unify_type(Type1,Type2,Type3),
  add_to_typeact(Type2,Type3,Type1,SVs2,Ref,IqsIn,IqsOut,SubGoals).

% ------------------------------------------------------------------------------
% add_to_typeact(Type2,Type3,Type1,SVs,Ref,IqsIn,IqsOut,SubGoals)
% ------------------------------------------------------------------------------
% SubGoals is code to add type Type1 to Ref-SVs of type Type2, with
% result being of Type3
% ------------------------------------------------------------------------------
add_to_typeact(a_ X,a_ X,a_ X,a_ X,_,Iqs,Iqs,[]) :- !.
add_to_typeact(a_ X,a_ X,bot,a_ X,_,Iqs,Iqs,[]) :- !.
add_to_typeact(bot,a_ X,a_ X,bot,_-(a_ X),Iqs,Iqs,[]) :- !.
add_to_typeact(Type2,Type3,Type1,SVs2,Ref,IqsIn,IqsOut,SubGoals):-
  approps(Type2,FRs2),
  (   (sub_type(Type1,Type2))  % if Type1 subsumes Type2, then do nothing
    -> (same_length(FRs2,Vs2),
        SubGoals = [],
        IqsOut = IqsIn)
   ; ((FRs2 = [])        % if Type2 is atomic, then we can use MGSat for Type3
      -> (mgsc(Type3,SVs3,Tag3,IqsIn,IqsOut,SubGoals,[]),
          Ref = (Tag3-SVs3),
	  Vs2 = [])
       ; (approps(Type3,FRs3),   % o.w. need to find out which feat's are new
          map_new_feats(FRs2,FRs3,Vs2,Vs3,IqsIn,IqsMid,SubGoals,SubGoalsRest),
          add_to_typecons(Type3,Type2,Tag3,SVs3,IqsMid,IqsOut,SubGoalsRest),
          ((Vs3 = [])
           -> SVs3 = Type3
            ; (SVs4 =.. [Type3|Vs3],
               SVs3 = SVs4)),
          Ref = (Tag3-SVs3))
  )),
  SVs2 =.. [Type2|Vs2].

% ------------------------------------------------------------------------------
% add_to_typecons(Type:<type>,ExclType:<type>,Tag:<ref>,SVs:<sv>s,
%                 IqsIn:<ineq>s,IqsOut:<ineq>s,SubGoals:<goal>s)
% ------------------------------------------------------------------------------
% Enforce the constraint for Type, and for all supersorts of Type, excluding
%  those in the ideal of ExclType, on Tag-SVs
% ------------------------------------------------------------------------------

add_to_typecons(Type,ET,Tag,SVs,IqsIn,IqsOut,SubGoals) :-
  esetof(T,(sub_type(T,Type),             % find set of types whose constraints
            \+sub_type(T,ET)),ConsTypes), %  must be satisfied
  map_cons(ConsTypes,Tag,SVs,IqsIn,IqsOut,SubGoals,[]).
% this map_cons is the same as the one for ucons

% ------------------------------------------------------------------------------
% featval(F:<feat>,SVs:<SVs>,Ref:<ref>,V:<fs>,
%         IqsIn:<ineq>s,IqsOut:<ineq>s)                                    mh(1)
% ------------------------------------------------------------------------------
% Ref-SVs value for feature F is V -- may involve coercion; 
% Ref-SVs is fully dereferenced;  V may not be
% ------------------------------------------------------------------------------
featval(F,SVs,Tag,V,IqsIn,IqsOut) if_h SubGoals:-
  introduce(F,TypeIntro),
  add_to_type(TypeIntro,SVs,Tag,IqsIn,IqsOut) if_h SubGoals,
     % actually seems to pay to recompute this rather than compile featval
     % add_to_type code in one shot
  deref(Tag,SVs,_NewTag,NewSVs),
  NewSVs =.. [Sort|Vs],   % don't have to worry about atoms as long as
  approps(Sort,FRs),      %  TypeIntro can't be bot (i.e. bot has no features)
  find_featval(F,FRs,Vs,V).

% ------------------------------------------------------------------------------
% find_featval(Feat,FRs,Vs,V)
% ------------------------------------------------------------------------------
% V is element of Vs same distance from front as F:_ is from front of FRs
% ------------------------------------------------------------------------------
find_featval(F,[F:_TypeRestr|_],[V|_Vs],V):-!.
find_featval(F,[_|FRs],[_|Vs],V):-
  find_featval(F,FRs,Vs,V).

% ------------------------------------------------------------------------------
% iso(FS1:<fs>, FS2:<fs>)
% ------------------------------------------------------------------------------
% determines whether structures FS1 and FS2 are isomorphic;
% not currently used, but perhaps necessary for inequations
% ------------------------------------------------------------------------------
iso(FS1,FS2):-
  iso_seq(iso(FS1,FS2,done)).

% ------------------------------------------------------------------------------
% iso_seq(FSSeq:<fs_seq>)
% ------------------------------------------------------------------------------
% takes structure <fs_seq> consisting of done/0 or iso(FS1,FS2,Isos)
% representing list of isomorphisms.  makes sure that all are isomorphic
% ------------------------------------------------------------------------------
iso_seq(done).
iso_seq(iso(FS1,FS2,Isos)):-
  deref(FS1,Tag1,SVs1),
  deref(FS2,Tag2,SVs2),
  ( (Tag1 == Tag2)
    -> iso_seq(Isos)
     ; (Tag1 = Tag2,
        iso_sub_seq(SVs1,SVs2,Isos))).

iso_sub_seq(a_ X,a_ Y,Isos) if_h [X==Y,iso_seq(Isos)]. % ext. like Prolog
iso_sub_seq(SVs1,SVs2,Isos) if_h SubGoal :-
  extensional(Sort),
  \+ (Sort = a_ _),
  approps(Sort,FRs),
  length(FRs,N),
  functor(SVs1,Sort,N),
  functor(SVs2,Sort,N),
  new_isos(N,SVs1,SVs2,Isos,SubGoal).

new_isos(0,_,_,SubGoal,[iso_seq(SubGoal)]) :-
  !.
new_isos(N,SVs1,SVs2,Isos,SubGoal) :-
  arg(N,SVs1,V1),
  arg(N,SVs2,V2),
  M is N-1,
  new_isos(M,SVs1,SVs2,iso(V1,V2,Isos),SubGoal).

% ------------------------------------------------------------------------------
% extensionalise(Ref:<ref>, SVs:<svs>, Iqs:<iqs>)
%-------------------------------------------------------------------------------
% search for extensional types which should be unified in Tag-SVs, and its
%  inequations, and do it.  Extensional types are assumed to be maximal.
%-------------------------------------------------------------------------------
extensionalise(Ref,SVs,Iqs) :-
  ext_act(fs(Ref,SVs,fsdone),edone,done,Iqs).

extensionalise(FS,Iqs) :-
  deref(FS,Ref,SVs),
  ext_act(fs(Ref,SVs,fsdone),edone,done,Iqs).

ext_act(fs(Ref,SVs,FSs),ExtQ,Ineqs,Iqs) :-
  check_pre_traverse(SVs,Ref,ExtQ,FSs,Ineqs,Iqs).
ext_act(fsdone,ExtQ,Ineqs,Iqs) :-
  ext_ineq(Ineqs,ExtQ,Iqs).

ext_ineq(ineq(Ref1,SVs1,Ref2,SVs2,Ineqs),ExtQ,Iqs) :-
  deref(Ref1,SVs1,DRef1,DSVs1),
  deref(Ref2,SVs2,DRef2,DSVs2),
  ext_act(fs(DRef1,DSVs1,fs(DRef2,DSVs2,fsdone)),ExtQ,Ineqs,Iqs).
ext_ineq(done,ExtQ,Iqs) :-
  ext_iqs(Iqs,ExtQ).

ext_iqs([Iq|Iqs],ExtQ) :-
  ext_ineq(Iq,ExtQ,Iqs).
ext_iqs([],_).

extensionalise_list(FSList,Iqs) :-
  list_to_fss(FSList,FSs),
  ext_act(FSs,edone,done,Iqs).

list_to_fss([],fsdone).
list_to_fss([FS|FSList],fs(Tag,SVs,FSs)) :-
  deref(FS,Tag,SVs),
  list_to_fss(FSList,FSs).

check_pre_traverse(SVs,Ref,ExtQ,FSs,Ineqs,Iqs) if_b [!|SubGoals] :-
  type(T),
  ( (T = (a_ _)) -> SVs = T,
                    SubGoals = [traverseQ(ExtQ,Ref,SVs,FSs,ExtQ,Ineqs,Iqs)]
  ; extensional(T) -> approps(T,FRs),
                      length(FRs,N),
                      functor(SVs,T,N),
                      SubGoals = [traverseQ(ExtQ,Ref,SVs,FSs,ExtQ,Ineqs,Iqs)]
  ).
check_pre_traverse(SVs,_,ExtQ,FSs,Ineqs,Iqs) if_b
  [check_post_traverse(SVs,ExtQ,FSs,Ineqs,Iqs)].

check_post_traverse(SVs,ExtQ,FSs,Ineqs,Iqs) if_b [!|SubGoals] :-
  type(T),
  clause(ext_sub_structs(T,SVs,NewFSs,FSs,SubGoals,
                         [ext_act(NewFSs,ExtQ,Ineqs,Iqs)]),true).
check_post_traverse(_,ExtQ,FSs,Ineqs,Iqs) if_b
  [ext_act(FSs,ExtQ,Ineqs,Iqs)].

% ------------------------------------------------------------------------------
% traverseQ(ExtQRest:<ext>s,ExtQ:<ext>s,Ref:<ref>,SVs:<svs>,FSs:<fs>s,
%           Ineqs:<ineq>s,Iqs:<iq>s)
% ------------------------------------------------------------------------------
% Add Ref-SVs to the extensionality queue, ExtQ.  Only ExtQRest remains to
% traverse (ExtQ is the head).  If the difference is unbound, then add Ref-SVs
% to the end.  If the first element on the difference is the same FS as
% Ref-SVs, then no need to add.  If the first element can be extensionally
% identified with Ref-SVs, then stop looking, since now Ref-SVs is the same as
% that FS.  If none of these, then go on to the next element.
% ------------------------------------------------------------------------------
traverseQ(edone,Ref,SVs,FSs,ExtQ,Ineqs,Iqs) :-
  check_post_traverse(SVs,ext(Ref,SVs,ExtQ),FSs,Ineqs,Iqs).
traverseQ(ext(ERef,ESVs,ERest),Ref,SVs,FSs,ExtQ,Ineqs,Iqs) :-
   ERef == Ref -> ext_act(FSs,ExtQ,Ineqs,Iqs)
 ; iso_seq(iso(Ref-SVs,ERef-ESVs,done)) -> ext_act(FSs,ExtQ,Ineqs,Iqs)
 ; traverseQ(ERest,Ref,SVs,FSs,ExtQ,Ineqs,Iqs).

% ------------------------------------------------------------------------------
% check_inequal(IqsIn:<ineq>s,IqsOut:<ineq>s)
%-------------------------------------------------------------------------------
% Checks the inequations in IqsIn.  Inequations are given in CNF, hence
% IqsIn = [Iq_1,...,Iq_n] holds if Iq_1 holds and ... and Iq_n holds
% Iq_i = ineq(Tag1,SVs1,Tag2,SVs2,ineq(...,done)...) holds if FS1 is not 
% structure-shared with FS2 or ... ("done" marks end of list)
%-------------------------------------------------------------------------------
% 5/1/96 Octav -- added a clause for the case the inequations list is 
%   uninstantiated
% 5/5/97 Octav - removed test to allow for first argument indexing
%check_inequal(Var,Var) :- var(Var), !.
check_inequal([],[]).
check_inequal([IqIn|IqsIn],IqsOut) :-
  check_inequal_conjunct(IqIn,IqOut,Result),
  check_inequal_act(Result,IqOut,IqsIn,IqsOut).

check_inequal_act(done,done,_,_) :-  % conjunct not satisfied
  !,fail.
check_inequal_act(succeed,_,IqsIn,IqsOut) :-  % conjunct satisfied
  !,check_inequal(IqsIn,IqsOut).
check_inequal_act(_,IqOut,IqsIn,[IqOut|IqsOut]) :-  % conjunct temporarily
  check_inequal(IqsIn,IqsOut).                      %  satisfied

check_inequal_conjunct(done,done,done).
check_inequal_conjunct(ineq(ITag1,ISVs1,ITag2,ISVs2,IqInRest),IqOut,Result) :-
  deref(ITag1,ISVs1,Tag1,SVs1),
  deref(ITag2,ISVs2,Tag2,SVs2),
  ( (Tag1 == Tag2)
    -> check_inequal_conjunct(IqInRest,IqOut,Result)
     ; ((SVs1 = a_ X) % fold in results of unify_type/3 and atom extensionality
        -> ((SVs2 = a_ Y)
            -> ((X==Y)
                -> check_inequal_conjunct(IqInRest,IqOut,Result) 
                 ; ((\+ \+(X=Y))
                    -> (IqOut = ineq(Tag1,SVs1,Tag2,SVs2,IqOutRest),
                        check_inequal_conjunct(IqInRest,IqOutRest,Result))
                     ; (Result = succeed)))
             ; (functor(SVs2,Sort2,_),
                ((Sort2 \== bot)
                 -> Result = succeed
                  ; (IqOut = ineq(Tag1,SVs1,Tag2,SVs2,IqOutRest),
                     check_inequal_conjunct(IqInRest,IqOutRest,Result)))))
         ; ((SVs2 = a_ _)
            -> (functor(SVs1,Sort1,_),
                ((Sort1 \== bot)
                 -> Result = succeed
                  ; (IqOut = ineq(Tag1,SVs1,Tag2,SVs2,IqOutRest),
                     check_inequal_conjunct(IqInRest,IqOutRest,Result))))
             ; (functor(SVs1,Sort1,_),
                functor(SVs2,Sort2,_),
                (unify_type(Sort1,Sort2,_)
                 -> (check_sub_seq(SVs1,SVs2,IqInRest,IqOut,Result)
                     -> true
                      ; (IqOut = ineq(Tag1,SVs1,Tag2,SVs2,IqOutRest),
                         check_inequal_conjunct(IqInRest,IqOutRest,Result)))
                  ; Result = succeed))))).

check_sub_seq(_,_,_,_,_) if_h [fail] :-  % atoms never make it to check_sub_seq
  \+ (extensional(S),(\+ (S = a_ _))).
                                        
check_sub_seq(SVs1,SVs2,IqInRest,IqOut,Result) if_h SubGoal :-
  extensional(Sort),
  \+ (Sort = a_ _),
  approps(Sort,FRs),
  length(FRs,N),
  functor(SVs1,Sort,N),
  functor(SVs2,Sort,N),
  new_checks(N,SVs1,SVs2,IqInRest,IqOut,Result,SubGoal).

new_checks(0,_,_,SubGoal,IqOut,Result,
           [check_inequal_conjunct(SubGoal,IqOut,Result)]) :-
  !.
new_checks(N,SVs1,SVs2,IqInRest,IqOut,Result,SubGoal) :-
  arg(N,SVs1,VTag1-VSVs1),
  arg(N,SVs2,VTag2-VSVs2),
  M is N-1,
  new_checks(M,SVs1,SVs2,ineq(VTag1,VSVs1,VTag2,VSVs2,IqInRest),
             IqOut,Result,SubGoal).

% ------------------------------------------------------------------------------
% match_list(Sort:<type>,Vs:<vs>,Tag:<var>,SVs:<svs>,Right:<int>,N:<int>,
%            Dtrs:<ints>,DtrsRest:<var>,NextRight:<int>,Chart:<chart>,
%            IqsIn:<iqs>,IqsOut:<iqs>)
% ------------------------------------------------------------------------------
% Run-time predicate compiled into rules.  Matches a list of cats in Chart,
% specified by Sort(Vs), to span an edge to OldRight, the first of which is 
% Tag-SVs, which spans to Right.  Also matches an edge for the next category
% of the current rule to use (necessary because an initial empty-list cats 
% matches nothing).
% ------------------------------------------------------------------------------
match_list(Sort,[HdFS,TlFS],Tag,SVs,Right,N,[N|DtrsMid],DtrsRest,Chart,
           NextRight,IqsIn,IqsOut) :-
  sub_type(ne_list,Sort),
  !,ud(HdFS,Tag,SVs,IqsIn,IqsMid),
  check_inequal(IqsMid,IqsMid2),
  deref(TlFS,_,TlSVs),
  TlSVs =.. [TlSort|TlVs],  % a_ correctly causes error in recursive call
  match_list_rest(TlSort,TlVs,Right,NextRight,DtrsMid,DtrsRest,Chart,IqsMid2,
                  IqsOut).

match_list(Sort,_,_,_,_,_,_,_,_,_,_,_) :-
  error_msg((nl,write('error: cats> value with sort, '),write(Sort),
            write(' is not a valid list argument'))).

% ------------------------------------------------------------------------------
% match_list_rest(Sort<type>,Vs:<vs>,Right:<int>,NewRight:<int>,
%                 DtrsRest:<ints>,DtrsRest2:<var>,Chart:<chart>,IqsIn:<iqs>,
%                 IqsOut:<iqs>)
% ------------------------------------------------------------------------------
% same as match_list, except edge spans from Right to NewRight, and no
%  matches for the next category are necessary
% ------------------------------------------------------------------------------
match_list_rest(e_list,_,Right,Right,DtrsRest,DtrsRest,_,Iqs,Iqs) :- 
  !.
match_list_rest(Sort,[HdFS,TlFS],Right,NewRight,[N|DtrsRest],DtrsRest2,Chart,
                IqsIn,IqsOut) :-
  sub_type(ne_list,Sort),
  !,get_edge(Right,Chart,N,MidRight,Tag,SVs,EdgeIqs,_,_),
  ud(HdFS,Tag,SVs,IqsIn,IqsMid),
  append(IqsMid,EdgeIqs,IqsMid2),
  check_inequal(IqsMid2,IqsMid3),
  deref(TlFS,_,TlSVs),
  TlSVs =.. [TlSort|TlVs],  % a_ correctly causes error in recursive call
  match_list_rest(TlSort,TlVs,MidRight,NewRight,DtrsRest,DtrsRest2,Chart,
                  IqsMid3,IqsOut).
match_list_rest(Sort,_,_,_,_,_,_,_,_) :-
  error_msg((nl,write('error: cats> value with sort, '),write(Sort),
            write(' is not a valid list argument'))).


% ==============================================================================
% Chart Parser
% ==============================================================================

% ------------------------------------------------------------------------------
% rec(+Ws:<word>s, Tag:<var_tag>, SVs:<svs>, Iqs:<ineq>s)
% ------------------------------------------------------------------------------
% Ws can be parsed as category Tag-SVs with inequations Iqs;  Tag-SVs 
%  uninstantiated to start
% ------------------------------------------------------------------------------
:- dynamic num/1.

rec(Ws,Tag,SVs,IqsOut):-
  clear,
  assert(parsing(Ws)),
  asserta(num(0)),
  reverse_count(Ws,[],WsRev,0,Length),
  CLength is Length - 1,
  functor(Chart,chart,CLength),
  build(WsRev,Length,Chart),
  retract(to_rebuild(Index)),
  clause(edge(Index,0,Length,Tag,SVs,IqsIn,_,_),true),
  extensionalise(Tag,SVs,IqsIn),
  check_inequal(IqsIn,IqsOut).

% ------------------------------------------------------------------------------
% rec(+Ws:<word>s, Tag:<var_tag>, SVs:<svs>, Iqs:<ineq>s, ?Desc:<desc>)
% ------------------------------------------------------------------------------
% Like rec/4, but Tag-SVs also satisfies description, Desc.
% ------------------------------------------------------------------------------
rec(Ws,TagOut,SVsOut,IqsOut,Desc) :-
  clear,
  assert(parsing(Ws)),
  asserta(num(0)),
  reverse_count(Ws,[],WsRev,0,Length),
  CLength is Length - 1,
  functor(Chart,chart,CLength),
  build(WsRev,Length,Chart),
  retract(to_rebuild(Index)),
  clause(edge(Index,0,Length,Tag,SVs,IqsIn,_,_),true),
  (secret_noadderrs
  ; secret_adderrs,
    fail),
  add_to(Desc,Tag,SVs,IqsIn,IqsMid),
  deref(Tag,SVs,TagOut,SVsOut),
  extensionalise(TagOut,SVsOut,IqsMid),
  check_inequal(IqsMid,IqsOut),
  (secret_adderrs
  ; secret_noadderrs,
    fail).

% ------------------------------------------------------------------------------
% build(Ws:<word>s, Right:<int>, Chart:<chart>)
% ------------------------------------------------------------------------------
% fills in inactive edges of chart from beginning to Right using 
% Ws, representing words in chart in reverse order.  Chart is the functor
% 'chart' of arity equal to the length of the input string (which is thus
%  bounded at 255).
% ------------------------------------------------------------------------------
build([W|Ws],Right,Chart):-
  RightMinus1 is Right - 1,
  (
% empty_cat(N,Right,Tag,SVs,Iqs,_,_),
%    rule(Tag,SVs,Iqs,Right,Right,empty(N,Right))
%  ;
       [no,lexical,entry,for,W] if_error
              (\+ lex(W,_,_,_) ), 
    lex(W,Tag,SVs,Iqs),
    add_edge(RightMinus1,Right,Tag,SVs,Iqs,[],lexicon,Chart)
  ; ( RightMinus1 =:= 0
      -> true
       ; rebuild_edges(Edges),
         arg(RightMinus1,Chart,Edges),
         build(Ws,RightMinus1,Chart)
    )
  ).
%build([],_):-
%  empty_cat(N,0,Tag,SVs,Iqs,_,_),
%  rule(Tag,SVs,Iqs,0,0,empty(N,0)).
build([],_,_).

% ------------------------------------------------------------------------------ 
% rebuild_edges(Edges:<edge>s)
% ------------------------------------------------------------------------------
% Copy non-looping edges asserted into the database in the most recent pass 
%  (all of the edges from the most recent node) into an edge/8 structure on 
%  the heap for inclusion into the chart.  Copying them once now means that we 
%  only copy an edge once in total rather than every time a rule asks for it.  %  We can do this because we have closed the rules under prefixes of empty 
%  categories; so we know that no edge will be needed until closure at the next
%  node begins.
% ------------------------------------------------------------------------------
rebuild_edges(Edges) :-
  retract(to_rebuild(Index))
  -> clause(edge(Index,_,R,T,S,IQ,D,RN),true),
     Edges = edge(Index,R,T,S,IQ,D,RN,EdgesRest),
     rebuild_edges(EdgesRest)
   ; Edges = nomore.

% ------------------------------------------------------------------------------
% add_edge_deref(Left:<int>, Right:<int>, Tag:<var_tag>, SVs:<svs>, 
%                Iqs:<ineq>s,Dtrs:<fs>s,RuleName,Chart:<chart>)             eval
% ------------------------------------------------------------------------------
% adds dereferenced category Tag-SVs,Iqs as inactive edge from Left to Right;
% check for any rules it might start, then look for categories in Chart
% to complete those rules
% ------------------------------------------------------------------------------
add_edge_deref(Left,Right,Tag,SVs,IqsIn,Dtrs,RuleName,Chart):-
  fully_deref_prune(Tag,SVs,TagOut,SVsOut,IqsIn,IqsOut),
  (no_subsumption
  -> (edge_assert(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,N)
     -> rule(TagOut,SVsOut,IqsOut,Left,Right,N,Chart))
   ; (subsumed(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName)
     -> fail
      ; (edge_assert(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,N)
        -> rule(TagOut,SVsOut,IqsOut,Left,Right,N,Chart)))).

add_edge(Left,Right,TagOut,SVsOut,Iqs,Dtrs,RuleName,Chart):-
  (no_subsumption
  -> (edge_assert(Left,Right,TagOut,SVsOut,Iqs,Dtrs,RuleName,N)
     -> rule(TagOut,SVsOut,Iqs,Left,Right,N,Chart))
   ; (subsumed(Left,Right,TagOut,SVsOut,Iqs,Dtrs,RuleName)
     -> fail
      ; (edge_assert(Left,Right,TagOut,SVsOut,Iqs,Dtrs,RuleName,N)
        -> rule(TagOut,SVsOut,Iqs,Left,Right,N,Chart)))).

gennum(N) :-
  retract(num(N)),
  NewN is N+1,
  asserta(num(NewN)).

gen_emptynum(N) :-
  retract(emptynum(N)),
  NewN is N-1,
  asserta(emptynum(NewN)).

count_edges(N):-
  setof(edge(M,X,Y,Z,W,I,D,R),edge(M,X,Y,Z,W,I,D,R),Es),
  length(Es,N).

% ------------------------------------------------------------------------------
% get_edge(Left:<int>,Chart:<chart>,Index:<int>,Right:<int>,Tag:<ref>,
%          SVs:<svs>,EdgeIqs:<iqs>,Dtrs:<int>s,RuleName:<atom>)
% ------------------------------------------------------------------------------
% Retrieve an edge from the chart, which means either an empty category
% or one of the non-empty edges in Chart
% ------------------------------------------------------------------------------

get_edge(Right,_,empty(N,Right),Right,Tag,SVs,EdgeIqs,Dtrs,RuleName) :-
  empty_cat(N,Right,Tag,SVs,EdgeIqs,Dtrs,RuleName).
get_edge(Left,Chart,N,Right,Tag,SVs,EdgeIqs,Dtrs,RuleName) :-
  arg(Left,Chart,Edges),
  edge_member(Edges,N,Right,Tag,SVs,EdgeIqs,Dtrs,RuleName).
%  clause(edge(Left,N,Right,Tag,SVs,EdgeIqs,Dtrs,RuleName),true).

edge_member(edge(I,R,T,S,IQ,D,RN,Edges),N,Right,Tag,SVs,EdgeIqs,Dtrs,
            RuleName) :-
  I = N, R = Right, T = Tag, S = SVs, IQ = EdgeIqs, D = Dtrs, RN = RuleName
 ; edge_member(Edges,N,Right,Tag,SVs,EdgeIqs,Dtrs,RuleName).  

% ------------------------------------------------------------------------------
% subsumed(Left:<int>,Right:<int>,Tag:<var_tag>,SVs:<svs>,Iqs:<ineq>s,
%          Dtrs:<int>s,RuleName)
% ------------------------------------------------------------------------------
% Check if any edge spanning Left to Right subsumes Tag-SVs, the feature
%  structure of the candidate edge, or vice versa.  Succeeds based on whether
%  or not Tag-SVs is subsumed - but all edges subsumed by Tag-SVs are also
%  retracted.
% ------------------------------------------------------------------------------
subsumed(Left,Right,Tag,SVs,Iqs,Dtrs,RuleName) :-
  clause(to_rebuild(EI),true),
  clause(edge(EI,Left,Right,ETag,ESVs,EIqs,_,_),true), %this may have >1 soln!
  empty_assoc(H),
  empty_assoc(K),
  subsume(s(Tag,SVs,ETag,ESVs,sdone),Iqs,EIqs,<,>,LReln,RReln,H,K),
  subsumed_act(RReln,LReln,EI,Tag,SVs,Iqs,Dtrs,RuleName,Left,Right).

subsumed_act(>,LReln,EI,Tag,SVs,Iqs,Dtrs,RuleName,Left,Right) :- %edge subsumes
  !,edge_discard(LReln,EI,Tag,SVs,Iqs,Dtrs,RuleName,Left,Right). % candidate 
subsumed_act(#,<,EI,Tag,SVs,Iqs,Dtrs,RuleName,Left,_) :- % candidate 
  edge_retract(Left,EI,Tag,SVs,Iqs,Dtrs,RuleName).       % subsumes edge
% subsumed_act(#,#,_,_,_,_,_,_,_,_) fails

% subsume(Ss,Iqs1,Iqs2,LeftRelnIn,RightRelnIn,LeftRelnOut,RightRelnOut,H,K)
% ------------------------------------------------------------------------------
% LeftRelnOut is bound to < if LeftRelnIn is not # and there exists a 
%  subsumption morphism, H (see Carpenter, 1992, p. 41) from Tag1-SVs1 to 
%  Tag2-SVs2, for every s(Tag1,SVs1,Tag2,SVs2,_) in Ss, and from the 
%  inequations in Iqs1 to those in Iqs2.  Otherwise, LeftRelnOut is bound to 
%  #.  RightRelnOut is bound to > if RightRelnIn is not #, and
%  a subsumption morphism, K, exists in the reverse direction, and is bound
%  otherwise to #.  The FS's in the s-structures are expected to be fully
%  dereferenced, with irrelevant inequations pruned off (which can be
%  achieved by using fully_deref_prune).
% ------------------------------------------------------------------------------
subsume(sdone,Iqs,EIqs,LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K) :-
  subsume_iqs(Iqs,EIqs,LRelnIn,LRelnOut,H),  % as a last resort, try to
  subsume_iqs(EIqs,Iqs,RRelnIn,RRelnOut,K).  % disprove subsumption using ineqs
subsume(s(Tag,SVs,ETag,ESVs,Ss),Iqs,EIqs,
         LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K) :-
  get_assoc(Tag,H,HPair)
  -> (get_assoc(ETag,K,KPair)  % first try to disprove subsumption using 
     -> HPair = [HTag|_],      %  observed structure sharing at current roots
        KPair = [KTag|_],
        (KTag == Tag 
        -> (HTag == ETag
           -> ((LRelnIn == #,RRelnIn == #)
              -> LRelnOut = #,RRelnOut = #  % we can quit once we show this
               ; subsume(Ss,Iqs,EIqs,LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K)
              )
            ; LRelnOut = #,
              (RRelnIn == #
              -> RRelnOut = #
               ; subsume(Ss,Iqs,EIqs,#,RRelnIn,#,RRelnOut,H,K)
              )
           )
         ; RRelnOut = #,
           (HTag == ETag
           -> (LRelnIn == #
              -> LRelnOut = #
               ; subsume(Ss,Iqs,EIqs,LRelnIn,#,LRelnOut,#,H,K)
              )
            ; LRelnOut = #, RRelnOut = #
           )
        )
     ; LRelnOut = #,
       (RRelnIn == #
       -> RRelnOut = #
        ; subsume_type(SVs,ESVs,Tag,ETag,Ss,Iqs,EIqs,#,RRelnIn,
                       #,RRelnOut,H,K)
       )
    )
  ; (get_assoc(ETag,K,KPair)
    -> RRelnOut = #,
       (LRelnIn == #
       -> LRelnOut = #
        ; subsume_type(Tag,SVs,ETag,ESVs,Ss,Iqs,EIqs,LRelnIn,#,
                       LRelnOut,#,H,K)
       )
     ; subsume_type(SVs,ESVs,Tag,ETag,Ss,Iqs,EIqs,LRelnIn,RRelnIn,
                    LRelnOut,RRelnOut,H,K)
    ).

% next try to disprove subsumption using type information at root node
subsume_type(bot,(a_ X),Tag,ETag,Ss,Iqs,EIqs,LRelnIn,_RRelnIn,LRelnOut,
             RRelnOut,H,K) if_b [!,RRelnOut = #,
                                   (LRelnIn == #
                                   -> LRelnOut = #
                                    ; put_assoc(Tag,H,[ETag|(a_ X)],NewH),
                                      subsume(Ss,Iqs,EIqs,LRelnIn,#,LRelnOut,#,
                                              NewH,K)
                                   )].
subsume_type((a_ X),bot,Tag,ETag,Ss,Iqs,EIqs,_LRelnIn,RRelnIn,LRelnOut,
             RRelnOut,H,K) if_b [!,LRelnOut = #,
                                   (RRelnIn == #
                                   -> RRelnOut = #
                                    ; put_assoc(ETag,K,[Tag|(a_ X)],NewK),
                                      subsume(Ss,Iqs,EIqs,#,RRelnIn,#,RRelnOut,
                                              H,NewK)
                                   )].
subsume_type((a_ X),(a_ Y),Tag,ETag,Ss,Iqs,EIqs,LRelnIn,RRelnIn,LRelnOut,
             RRelnOut,H,K) if_b [!,(subsumes_chk(X,Y)   % this is all variant/2
                                   -> (subsumes_chk(Y,X) % does anyway
                                      -> ((LRelnIn == # 
                                          -> LRelnOut = #, H = NewH
                                           ; put_assoc(Tag,H,[ETag|(a_ Y)],
                                                       NewH)
                                          ),
                                          (RRelnIn == # 
                                          -> RRelnOut = #, K = NewK
                                           ; put_assoc(ETag,K,[Tag|(a_ X)],
                                                       NewK)
                                          ),
                                          subsume(Ss,Iqs,EIqs,LRelnIn,RRelnIn,
                                                  LRelnOut,RRelnOut,NewH,NewK)
                                         )
                                       ; RRelnOut = #,
                                         (LRelnIn == #
                                         -> LRelnOut = #
                                          ; put_assoc(Tag,H,[ETag|(a_ Y)],
                                                      NewH),
                                            subsume(Ss,Iqs,EIqs,LRelnIn,#,
                                                    LRelnOut,#,NewH,K)
                                         )
                                      )
                                    ; (subsumes_chk(Y,X)
                                      -> LRelnOut = #,
                                         (RRelnIn == #
                                         -> RRelnOut = #
                                          ; put_assoc(ETag,K,[Tag|(a_ X)],
                                                      NewK),
                                            subsume(Ss,Iqs,EIqs,#,RRelnIn,#,
                                                    RRelnOut,H,NewK)
                                         )
                                       ; LRelnOut = #, RRelnOut = #
                                      )
                                   )].
subsume_type(SVs,ESVs,Tag,ETag,Ss,Iqs,EIqs,LRelnIn,RRelnIn,LRelnOut,RRelnOut,
             H,K) if_b SubGoals :-
  Sort subs _,  % dont want a_/1 atoms
  approps(Sort,FRs),
  length(FRs,N),
  length(Vs,N),
  SVs =.. [Sort|Vs],
  subsume_type_act(Sort,FRs,N,Vs,SVs,ESVs,Tag,ETag,Ss,Iqs,EIqs,LRelnIn,RRelnIn,
                   LRelnOut,RRelnOut,H,K,SubGoals).

subsume_type_act(Sort,_FRs,N,Vs,SVs,ESVs,Tag,ETag,Ss,Iqs,EIqs,LRelnIn,RRelnIn,
                 LRelnOut,RRelnOut,H,K,[!,(LRelnIn == # 
                                          -> LRelnOut = #, H = NewH
                                           ; put_assoc(Tag,H,[ETag|ESVs],NewH)
                                          ),
                                          (RRelnIn == # 
                                          -> RRelnOut = #, K = NewK
                                           ; put_assoc(ETag,K,[Tag|SVs],NewK)
                                          ),
                                          subsume(NewSs,Iqs,EIqs,LRelnIn,
                                                  RRelnIn,LRelnOut,RRelnOut,
                                                  NewH,NewK)]) :-
  length(EVs,N),
  append_s(Vs,EVs,Ss,NewSs),
  ESVs =.. [Sort|EVs].
subsume_type_act(Sort,FRs,_N,Vs,_SVs,ESVs,Tag,ETag,Ss,Iqs,EIqs,LRelnIn,
                 _RRelnIn,LRelnOut,RRelnOut,H,K,
                 [!,RRelnOut = #,
                  (LRelnIn == #
                  -> LRelnOut = #
                   ; put_assoc(Tag,H,[ETag|ESVs],NewH),
                     subsume(NewSs,Iqs,EIqs,LRelnIn,#,LRelnOut,#,NewH,K)
                  )]) :-
  sub_type(Sort,ESort), \+ functor(ESort,'a_',1), ESort \== Sort,
  approps(ESort,EFRs),
  length(EFRs,EN),
  length(EVs,EN),
  sub_feats(FRs,EFRs,EVs,SubEVs),
  append_s(Vs,SubEVs,Ss,NewSs),
  ESVs =.. [ESort|EVs].
subsume_type_act(Sort,FRs,_N,Vs,SVs,ESVs,Tag,ETag,Ss,Iqs,EIqs,_LRelnIn,RRelnIn,
                 LRelnOut,RRelnOut,H,K,[!,LRelnOut = #,
                                          (RRelnIn == #
                                          -> RRelnOut = #
                                           ; put_assoc(ETag,K,[Tag|SVs],NewK),
                                             subsume(NewSs,Iqs,EIqs,#,RRelnIn,
                                                     #,RRelnOut,H,NewK)
                                          )]) :-
  sub_type(ESort,Sort), \+ functor(Sort,'a_',1), Sort \== ESort,
  approps(ESort,EFRs),
  length(EFRs,EN),
  length(EVs,EN),
  sub_feats(EFRs,FRs,Vs,SubVs),
  append_s(SubVs,EVs,Ss,NewSs),
  ESVs =.. [ESort|EVs].
subsume_type_act(_,_,_,_,_,_,_,_,_,_,_,_,_,#,#,_,_,[]).
                 % still need 1 arg to multi-hash


subsume_iqs([],_,Reln,Reln,_).
subsume_iqs([Iq|Iqs1],Iqs2,RelnIn,RelnOut,H) :-
  RelnIn == #
  -> RelnOut = #
   ; subsume_iq(Iq,Iqs2,RelnIn,RelnMid,H), % make sure image of each conjunct 
     subsume_iqs(Iqs1,Iqs2,RelnMid,RelnOut,H). % holds in image FS

subsume_iq(done,Iqs2Out,RelnIn,RelnOut,_) :- % negated image of conjunct is 
  check_inequal(Iqs2Out,_)      % satisfied by image FS, so no subsumption 
  -> RelnOut = #                % morphism exists.
   ; RelnOut = RelnIn.    % image of conjunct is satisfied by an 
                          %  inequation conjunct of the image FS (which 
                          %  failed in the check_inequal/2 call)
subsume_iq(ineq(Tag1,SVs1,Tag2,SVs2,IqRest),Iqs2Mid,RelnIn,RelnOut,H) :-
  (get_assoc(Tag1,H,HPair1)   % test which inequated FS has an image
  -> HPair1 = [HTag1|HSVs1],
     (get_assoc(Tag2,H,HPair2)
     -> HPair2 = [HTag2|HSVs2],
        unify_disjunct_image(HTag1,HSVs1,HTag2,HSVs2,IqRest,Iqs2Mid,
                             RelnIn,RelnOut,H)
      ; unify_disjunct_image(HTag1,HSVs1,Tag2,SVs2,IqRest,Iqs2Mid,
                             RelnIn,RelnOut,H)
     )
   ; get_assoc(Tag2,H,HPair2), % inequation was not pruned, so this one exists
     HPair2 = [HTag2|HSVs2],
     unify_disjunct_image(Tag1,SVs1,HTag2,HSVs2,IqRest,Iqs2Mid,
                          RelnIn,RelnOut,H)
     % use an inequated FS with no image itself for matching conjuncts
  )
  -> true
   ; RelnOut = RelnIn.  %  image of conjunct is 
                        %  implicitly encoded in the image FS (since 
                        %  unifying the images of the inequated FSs of
                        %  every disjunct failed earlier in this clause).

unify_disjunct_image(Tag1,SVs1,Tag2,SVs2,IqRest,Iqs2Mid,RelnIn,RelnOut,H) :-
  u(SVs1,SVs2,Tag1,Tag2,Iqs2Mid,Iqs2Out),
  subsume_iq(IqRest,Iqs2Out,RelnIn,RelnOut,H).


% sub_feats(SubFRs,FRs,Vs,SubVs)
% ------------------------------------------------------------------------------
% SubFRs is a sorted sublist of sorted feature:restriction list, FRs.  Vs is
%  a list of values of features of FRs in order.  SubVs is the sublist of Vs 
%  consisting of values of features of SubFRs in order.
% ------------------------------------------------------------------------------
sub_feats([],_,_,[]) :- 
  !.
sub_feats([Feat:_|SubFRs],[Feat:_|FRs],[V|Vs],[V|SubVs]) :-
  !,sub_feats(SubFRs,FRs,Vs,SubVs).
sub_feats(SubFRs,[_|FRs],[_|Vs],SubVs) :-
  sub_feats(SubFRs,FRs,Vs,SubVs).

% append_s(Vs,EVs,Ss,NewSs)
% ------------------------------------------------------------------------------
% NewSs is Ss plus in-order pairs of FS's from Vs and EVs (which are the same
%  length), in s-structures.
% ------------------------------------------------------------------------------
append_s([],[],Ss,Ss).
append_s([Tag-SVs|Vs],[ETag-ESVs|EVs],Ss,s(Tag,SVs,ETag,ESVs,NewSs)) :-
  append_s(Vs,EVs,Ss,NewSs).

% edge_discard(LReln:<var>/#,I:<int>,Tag:<var_tag>,SVs:<sv>s,Iqs:<ineq>s,
%             Dtrs:<int>s,RuleName,Left:<int>,Right:<int>)
% ------------------------------------------------------------------------------
% Discard edge Tag-SVs, with inequations Iqs, daughters Dtrs, created by rule
%  RuleName, because it is subsumed by the edge with index I.  If LReln is a
%  variable, then the two are equal - otherwise, LReln is #, which indicates
%  strict subsumption.
% ------------------------------------------------------------------------------
edge_discard(_,_,_,_,_,_,_,_,_) :-
  no_interpreter,
  !.
edge_discard(LReln,I,Tag,SVs,Iqs,Dtrs,RuleName,Left,Right) :-
  length(Dtrs,ND),
  !,print_edge_discard(LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).

print_edge_discard(LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  nl,pp_fs(Tag-SVs,Iqs),
  nl,write('Edge created for category above:'),
%  nl,write('     index: '),write(I),
  nl,write('      from: '),write(Left),write(' to: '),write(Right),
  nl,write('    string: '),write_out(Left,Right),
  nl,write('      rule: '),write(RuleName),
  nl,write(' # of dtrs: '),write(ND),nl,
  print_edge_discard_act(LReln,I),
  nl,query_discard(LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).

print_edge_discard_act(<,I) :-
  !,nl,write('is equal to an existing edge, index:'),write(I),write('.').
print_edge_discard_act(#,I) :-
  nl,write('is subsumed by an existing edge, index:'),write(I),write('.').

query_discard(_,_,_,_,_,_,_,_,_,_) :-
  go(_),
  !.
query_discard(LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  nl,write('Action(noadd,continue,break,dtr-#,existing,abort)? '),
  nl,read(Response),
  query_discard_act(Response,LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).

query_discard_act(noadd,_,_,_,_,_,_,_,_,_,_) :- !.
query_discard_act(continue,_,_,_,_,_,_,_,_,_,_) :- 
  !,fail.
query_discard_act(break,LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  !,break,
  print_edge_discard(LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).
query_discard_act(dtr-D,LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  nth_index(Dtrs,D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule),
  !,length(DDtrs,DND),
  print_dtr_edge(D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule,DND),
  print_edge_discard(LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).
query_discard_act(existing,LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  clause(edge(I,Left,Right,ETag,ESVs,EIqs,EDtrs,ERuleName),true),
  !,edge_act(I,Left,Right,ETag,ESVs,EIqs,EDtrs,ERuleName),  
  print_edge_discard(LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).
query_discard_act(abort,_,_,_,_,_,_,_,_,_,_) :-
  !,abort.
query_discard_act(_,LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  query_discard(LReln,I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).

% edge_retract(Left:<int>,I:<int>,Tag:<var_tag>,SVs:<svs>,Iqs:<ineq>s,
%              Dtrs:<int>s,RuleName:<atom>)
% ------------------------------------------------------------------------------
% Retract edge with index I because it is subsumed by Tag-SVs, with inequations
%  Iqs, daughters Dtrs, created by rule RuleName
% ------------------------------------------------------------------------------
edge_retract(Left,I,_,_,_,_,_) :-
  no_interpreter,
  retract(to_rebuild(I)),
  retract(edge(I,Left,_,_,_,_,_,_)),
  !,fail.     % failure-drive through all subsumed edges

edge_retract(Left,I,Tag,SVs,Iqs,Dtrs,RuleName) :-
  !,clause(edge(I,Left,Right,ETag,ESVs,EIqs,EDtrs,ERuleName),true),
  length(EDtrs,NED),
  print_edge_retract(I,Left,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                     Tag,SVs,Iqs,Dtrs,RuleName).

print_edge_retract(I,Left,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                   Tag,SVs,Iqs,Dtrs,RuleName) :-
  nl,pp_fs(ETag-ESVs,EIqs),
  nl,write('Edge created for category above:'),
  nl,write('     index: '),write(I),
  nl,write('      from: '),write(Left),write(' to: '),write(Right),
  nl,write('    string: '),write_out(Left,Right),
  nl,write('      rule: '),write(ERuleName),
  nl,write(' # of dtrs: '),write(NED),nl,
  nl,write('is subsumed by an incoming edge.'),
  nl,query_retract(Left,I,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                   Tag,SVs,Iqs,Dtrs,RuleName).

query_retract(Left,I,_,_,_,_,_,_,_,_,_,_,_,_) :-
  go(_),
  retract(edge(I,Left,_,_,_,_,_,_)),
  retract(to_rebuild(I)),
  !,fail.
query_retract(Left,I,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
              Tag,SVs,Iqs,Dtrs,RuleName) :-
  nl,write('Action(retract,continue,break,dtr-#,incoming,abort)? '),
  nl,read(Response),
  query_retract_act(Response,Left,I,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                    Tag,SVs,Iqs,Dtrs,RuleName).
query_retract_act(retract,Left,I,_,_,_,_,_,_,_,_,_,_,_,_) :-
  retract(edge(I,Left,_,_,_,_,_,_)),
  retract(to_rebuild(I)),
  !,fail.
query_retract_act(remain,_,_,_,_,_,_,_,_,_,_,_,_,_,_) :-
  !,fail.
query_retract_act(continue,_,_,_,_,_,_,_,_,_,_,_,_,_,_) :-
  !.
query_retract_act(break,Left,I,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                  Tag,SVs,Iqs,Dtrs,RuleName) :-
  !,break,
  print_edge_retract(I,Left,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                     Tag,SVs,Iqs,Dtrs,RuleName).
query_retract_act(dtr-D,Left,I,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                  Tag,SVs,Iqs,Dtrs,RuleName) :-
  nth_index(EDtrs,D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule),
  !,length(DDtrs,DND),
  print_dtr_edge(D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule,DND),
  print_edge_retract(I,Left,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                     Tag,SVs,Iqs,Dtrs,RuleName).
query_retract_act(incoming,Left,I,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                  Tag,SVs,Iqs,Dtrs,RuleName) :-
  !,length(Dtrs,ND),
  (print_incoming_edge(Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND)
   -> true
    ; print_edge_retract(I,Left,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                         Tag,SVs,Iqs,Dtrs,RuleName)).
query_retract_act(abort,_,_,_,_,_,_,_,_,_,_,_,_,_,_) :-
  !,abort.
query_retract_act(_,Left,I,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                  Tag,SVs,Iqs,Dtrs,RuleName) :-
  query_retract(Left,I,Right,ETag,ESVs,EIqs,EDtrs,ERuleName,NED,
                Tag,SVs,Iqs,Dtrs,RuleName).

print_incoming_edge(Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  nl,pp_fs(Tag-SVs,Iqs),
  nl,write('Incoming Edge: '),
  nl,write('      from: '),write(Left),write(' to: '),write(Right),
  nl,write('    string: '),write_out(Left,Right),
  nl,write('      rule:  '),write(RuleName),
  nl,write(' # of dtrs: '),write(ND),
  query_incoming_edge(Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).

query_incoming_edge(Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  nl,write('Action(noadd,dtr-#,existing,abort)?' ),
  nl,read(Response),
  query_incoming_act(Response,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).
query_incoming_act(noadd,_,_,_,_,_,_,_,_) :-
  !.
query_incoming_act(existing,_,_,_,_,_,_,_,_) :-
  !,fail.
query_incoming_act(abort,_,_,_,_,_,_,_,_) :-
  !,abort.
query_incoming_act(dtr-D,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  nth_index(Dtrs,D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule),
  !,length(DDtrs,DND),
  print_dtr_edge(D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule,DND),
  print_incoming_edge(Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).
query_incoming_act(_,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  query_incoming_edge(Left,Right,Tag,SVs,Iqs,Dtrs,RuleName,ND).

% ==============================================================================
% Interpreter
% ==============================================================================

edge_assert(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,N) :- 
  no_interpreter,                                      
  !,gennum(N),
  asserta(to_rebuild(N)),
  asserta(edge(N,Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName)). 

edge_assert(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,N) :-
  !,nl,
  length(Dtrs,ND),
  (print_edge(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND)
  -> gennum(N),
     asserta(to_rebuild(N)),
     asserta(edge(N,Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName))).

print_edge(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND) :-
  nl,pp_fs(TagOut-SVsOut,IqsOut),
  nl,write('Edge created for category above: '),
  nl,write('      from: '),write(Left),write(' to: '),write(Right),
  nl,write('    string: '),write_out(Left,Right),
  nl,write('      rule:  '),write(RuleName),
  nl,write(' # of dtrs: '),write(ND),
  nl,query_edge(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND).

query_edge(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND) :-
  go(Left),               % right-to-left parser triggers on left
  !,retractall(go(_)),
  query_edge(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND).
query_edge(_,_,_,_,_,_,_,_) :-
  go(_),
  !.
query_edge(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND) :-
  nl,write('Action(add,noadd,go(-#),break,dtr-#,abort)? '),
  nl,read(Response),
  query_edge_act(Response,Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND).

query_edge_act(add,_,_,_,_,_,_,_,_) :-
  !.
query_edge_act(noadd,_,_,_,_,_,_,_,_) :- 
  !,fail.
query_edge_act(go,_,_,_,_,_,_,_,_) :-
  !,asserta(go(go)).
query_edge_act(go-G,_,_,_,_,_,_,_,_) :-
  !,asserta(go(G)).
query_edge_act(break,Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND) :-
  !,break,
  print_edge(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND).
query_edge_act(dtr-D,Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND):-
  nth_index(Dtrs,D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule),
  !,length(DDtrs,DND),
  print_dtr_edge(D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule,DND),
  print_edge(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND).
query_edge_act(abort,_,_,_,_,_,_,_,_) :-
  !,abort.
query_edge_act(_,Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND) :-
  query_edge(Left,Right,TagOut,SVsOut,IqsOut,Dtrs,RuleName,ND).

print_dtr_edge(D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule,DND) :-
  nl,pp_fs(DTag-DSVs,DIqs),
  nl,write('Daughter number '), write(D),
  nl,write('      from: '),write(DLeft),write(' to: '),write(DRight),
  nl,write('    string: '),write_out(DLeft,DRight),
  nl,write('      rule:  '),write(DRule),
  nl,write(' # of dtrs: '),write(DND),
  query_dtr_edge(D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule,DND).

query_dtr_edge(D,I,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule,DND) :-
  nl,write('Action(retract,dtr-#,parent,abort)?' ),
  nl,read(Response),
  query_dtr_act(Response,D,I,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule,DND).
query_dtr_act(parent,_,_,_,_,_,_,_,_,_,_) :-
  !.
query_dtr_act(retract,_,I,DLeft,_,_,_,_,_,_,_) :-
  retract(edge(I,DLeft,_,_,_,_,_,_)),  % will fail on empty cats
  !.
query_dtr_act(abort,_,_,_,_,_,_,_,_,_,_) :-
  !,abort.
query_dtr_act(dtr-DD,D,I,Left,Right,Tag,SVs,Iqs,Dtrs,Rule,ND) :-
  nth_index(Dtrs,DD,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule),
  !,length(DDtrs,DND),
  print_dtr_edge(DD,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule,DND),
  print_dtr_edge(D,I,Left,Right,Tag,SVs,Iqs,Dtrs,Rule,ND).
query_dtr_act(_,D,I,Left,Right,Tag,SVs,Iqs,Dtrs,Rule,ND) :-
  query_dtr_edge(D,I,Left,Right,Tag,SVs,Iqs,Dtrs,Rule,ND).

nth_index([I|Is],N,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule) :- 
  N =:= 1
  -> DI = I,
     (I = empty(E,DLeft)
     -> empty_cat(E,DLeft,DTag,DSVs,DIqs,DDtrs,DRule),
        DLeft = DRight
      ; (clause(edge(I,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule),true)
        -> true
         ; error_msg((nl,write('edge has been retracted')))
        )
     )
   ; NMinus1 is N-1,
     nth_index(Is,NMinus1,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule).


% ==============================================================================
% Functional Description Resolution/Compilation
% ==============================================================================

% fsolve(Fun:<fun>,Ref:<ref>,SVs:<svs>,IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
%  Solve function constraint, Fun, along with its argument descriptions.
% ------------------------------------------------------------------------------
fsolve(_,_,_,_,_) if_b [fail] :-
  \+ current_predicate(+++>,+++>(_,_)).
fsolve(Fun,Tag,SVs,IqsIn,IqsOut) if_b Goals :-
  current_predicate(+++>,+++>(_,_)),
  empty_assoc(VarsIn),
  (FHead +++> FResult),
  FHead =.. [Rel|ArgDescs],
  compile_descs(ArgDescs,Args,IqsIn,IqsMid,GoalsMid,
                [check_inequal(IqsMid,IqsMid2)|GoalsMid2],true,VarsIn,VarsMid,
                FSPal,[],FSsMid),
  Fun =.. [Rel|Args],
  compile_desc(FResult,Tag,SVs,IqsMid2,IqsOut,GoalsMid2,[],true,VarsMid,_,FSPal,
               FSsMid,FSsOut),
  build_fs_palette(FSsOut,FSPal,Goals,GoalsMid,[]).


% ==============================================================================
% Definite Clause Resolution/Compilation
% ==============================================================================

% ------------------------------------------------------------------------------
% compile_body(GoalDesc,IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,VarsOut,
%              FSPal,FSsIn,FSsOut)
% ------------------------------------------------------------------------------
% compiles arbitrary Goal.
% PGoals is instantiated to list of Prolog goals required to add
% arguments relations in Goal and then call the procedure to solve them.
% IqsIn and IqsOut are uninstantiated at compile time.  
% ------------------------------------------------------------------------------
% 4/1/96 - Octav -- changed compile_body/7 to take an extra argument that's
% used for computing the Goals list as difference list
compile_body(((GD1,GD2),GD3),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_body((GD1,(GD2,GD3)),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut).
compile_body(((IfD -> ThenD ; ElseD),PGD),IqsIn,IqsOut,
             [(IfG -> ThenG ; ElseG)|PGoalsMid],PGoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_body(IfD,IqsIn,IqsMid,IfGoals,[],CBSafe,VarsIn,VarsIf,FSPal,FSsIn,
                 FSsIf),
  compile_body(ThenD,IqsMid,IqsMid2,ThenGoals,[],false,VarsIf,VarsThen,FSPal,
               FSsIf,FSsThen),
  compile_body(ElseD,IqsIn,IqsMid2,ElseGoals,[],false,VarsIn,VarsElse,FSPal,
               FSsIn,FSsElse),
  goal_list_to_seq(IfGoals,IfG),
  goal_list_to_seq(ThenGoals,ThenG),
  goal_list_to_seq(ElseGoals,ElseG),
  vars_merge(VarsThen,VarsElse,VarsMid),
  fss_merge(FSsThen,FSsElse,FSsMid),
  compile_body(PGD,IqsMid2,IqsOut,PGoalsMid,PGoalsRest,CBSafe,VarsMid,VarsOut,
               FSPal,FSsMid,FSsOut).
compile_body(((GD1;GD2),GD3),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_body(((GD1,GD3);(GD2,GD3)),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,
                  VarsIn,VarsOut,FSPal,FSsIn,FSsOut).
compile_body((\+ GD1, GD2),IqsIn,IqsOut,[(\+ PGoal)|PGoalsMid],PGoalsRest,
             CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_body(GD1,IqsIn,_,PGoalsList,[],CBSafe,VarsIn,_,FSPal,FSsIn,_),
  goal_list_to_seq(PGoalsList,PGoal),
  compile_body(GD2,IqsIn,IqsOut,PGoalsMid,PGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
               FSsIn,FSsOut).
compile_body((Desc1 =@ Desc2,GD),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_desc(Desc1,Tag1,bot,IqsIn,IqsMid,PGoals,PGoalsMid,CBSafe,
                  VarsIn,VarsMid,FSPal,FSsIn,FSsMid),
  compile_desc(Desc2,Tag2,bot,IqsMid,IqsMid2,PGoalsMid,
               [deref(Tag1,bot,DTag1,DSVs1),
                deref(Tag2,bot,DTag2,DSVs2),
                ext_act(fs(DTag1,DSVs1,fs(DTag2,DSVs2,fsdone)),edone,done,
                        IqsMid2),
                check_inequal(IqsMid2,IqsMid3),
                deref(DTag1,DSVs1,Tag1Out,_),
                deref(DTag2,DSVs2,Tag2Out,_),
                (Tag1Out == Tag2Out)|PGoalsMid2],
               CBSafe,VarsMid,VarsMid2,FSPal,FSsMid,FSsMid2),
  compile_body(GD,IqsMid3,IqsOut,PGoalsMid2,PGoalsRest,CBSafe,VarsMid2,
               VarsOut,FSPal,FSsMid2,FSsOut).
compile_body((true,GD),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut):-
  !, compile_body(GD,IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
                  FSsIn,FSsOut).
compile_body((fail,_),Iqs,Iqs,[fail|PGoalsRest],PGoalsRest,_,Vars,Vars,_,FSs,FSs):-
  !.
compile_body((!,PGD),IqsIn,IqsOut,[!|PGoalsMid],PGoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_body(PGD,IqsIn,IqsOut,PGoalsMid,PGoalsRest,CBSafe,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut).
compile_body(((IfD -> ThenD),PGD),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,
             VarsIn,VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_body(((IfD -> ThenD ; fail),PGD),IqsIn,IqsOut,PGoals,PGoalsRest,
                 CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut).
compile_body((prolog(Goal),GD),IqsIn,IqsOut,[Goal|PGoalsMid],PGoalsRest,CBSafe,
             VarsIn,VarsOut,FSPal,FSsIn,FSsOut) :-
  !, term_variables(Goal,HookVarsList),
  hook_vars_merge(HookVarsList,VarsIn,VarsMid),
  compile_body(GD,IqsIn,IqsOut,PGoalsMid,PGoalsRest,CBSafe,VarsMid,VarsOut,FSPal,
               FSsIn,FSsOut).
compile_body((AGD,GD2),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut):-
  !, AGD =.. [Rel|ArgDescs],
  compile_descs_fresh(ArgDescs,Args,IqsIn,IqsMid,PGoals,[AGoal|PGoalsMid],
                      CBSafe,VarsIn,VarsMid,FSPal,FSsIn,FSsMid),
  append(Args,[IqsMid,IqsMid2],CompiledArgs),
  cat_atoms('fs_',Rel,CompiledRel),
  AGoal =.. [CompiledRel|CompiledArgs],
  compile_body(GD2,IqsMid2,IqsOut,PGoalsMid,PGoalsRest,CBSafe,VarsMid,VarsOut,
               FSPal,FSsMid,FSsOut).
compile_body((IfD -> ThenD ; ElseD),IqsIn,IqsOut,
             [(IfG -> ThenG ; ElseG)|PGoalsRest],PGoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_body(IfD,IqsIn,IqsMid,IfGoals,[],CBSafe,VarsIn,VarsIf,FSPal,FSsIn,
                 FSsIf),
  compile_body(ThenD,IqsMid,IqsOut,ThenGoals,[],false,VarsIf,VarsThen,FSPal,
               FSsIf,FSsThen),
  compile_body(ElseD,IqsIn,IqsOut,ElseGoals,[],false,VarsIn,VarsElse,FSPal,
               FSsIn,FSsElse),
  goal_list_to_seq(IfGoals,IfG),
  goal_list_to_seq(ThenGoals,ThenG),
  goal_list_to_seq(ElseGoals,ElseG),
  vars_merge(VarsThen,VarsElse,VarsOut),
  fss_merge(FSsThen,FSsElse,FSsOut).
compile_body((GD1;GD2),IqsIn,IqsOut,[(PGoal1;PGoal2)|PGoalsRest],PGoalsRest,_,
             VarsIn,VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_body(GD1,IqsIn,IqsOut,PGoals1,[],false,VarsIn,VarsDisj1,FSPal,
                  FSsIn,FSsDisj1),
  compile_body(GD2,IqsIn,IqsOut,PGoals2,[],false,VarsIn,VarsDisj2,FSPal,FSsIn,
               FSsDisj2),
  goal_list_to_seq(PGoals1,PGoal1),
  goal_list_to_seq(PGoals2,PGoal2),
  vars_merge(VarsDisj1,VarsDisj2,VarsOut),
  fss_merge(FSsDisj1,FSsDisj2,FSsOut).
compile_body((\+ GD),Iqs,Iqs,[(\+ PGoal)|PGoalsRest],PGoalsRest,CBSafe,
             VarsIn,VarsIn,FSPal,FSs,FSs) :-  % vars will be unbound, so dont thread
  !, compile_body(GD,Iqs,_,PGoalsList,[],CBSafe,VarsIn,_,FSPal,FSs,_),
  goal_list_to_seq(PGoalsList,PGoal).
compile_body((Desc1 =@ Desc2),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_desc(Desc1,Tag1,bot,IqsIn,IqsMid,PGoals,PGoalsMid,CBSafe,
                  VarsIn,VarsMid,FSPal,FSsIn,FSsMid),
  compile_desc(Desc2,Tag2,bot,IqsMid,IqsMid2,PGoalsMid,
               [deref(Tag1,bot,DTag1,DSVs1),
                deref(Tag2,bot,DTag2,DSVs2),
                ext_act(fs(DTag1,DSVs1,fs(DTag2,DSVs2,fsdone)),edone,done,
                        IqsMid2),
                check_inequal(IqsMid2,IqsOut),
                deref(DTag1,DSVs1,Tag1Out,_),
                deref(DTag2,DSVs2,Tag2Out,_),
                (Tag1Out == Tag2Out)|PGoalsRest],
               CBSafe,VarsMid,VarsOut,FSPal,FSsMid,FSsOut).
compile_body(!,Iqs,Iqs,[!|PGoalsRest],PGoalsRest,_,Vars,Vars,_,FSs,FSs):-
  !.
compile_body((IfD -> ThenD),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_body((IfD -> ThenD ; fail),IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,
                 VarsIn,VarsOut,FSPal,FSsIn,FSsOut).
compile_body(true,Iqs,Iqs,PGoals,PGoals,_,Vars,Vars,_,FSs,FSs):-
  !.
compile_body(fail,Iqs,Iqs,[fail|PGoalsRest],PGoalsRest,_,Vars,Vars,_,FSs,FSs):-
  !.
compile_body(prolog(Goal),Iqs,Iqs,[Goal|PGoalsRest],PGoalsRest,_,VarsIn,
             VarsOut,_,FSs,FSs) :-
  !, term_variables(Goal,HookVarsList),
  hook_vars_merge(HookVarsList,VarsIn,VarsOut).
compile_body(AtGD,IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut):-
  AtGD =.. [Rel|ArgDescs],
  compile_descs_fresh(ArgDescs,Args,IqsIn,IqsMid,PGoals,[AtGoal|PGoalsRest],
                      CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut),
  append(Args,[IqsMid,IqsOut],CompiledArgs),
  cat_atoms('fs_',Rel,CompiledRel),
  AtGoal =.. [CompiledRel|CompiledArgs].

% ------------------------------------------------------------------------------
% goal_list_to_seq(Goals:<goal>s, GoalsSeq:<goal_seq>)
% ------------------------------------------------------------------------------
%
% ------------------------------------------------------------------------------
goal_list_to_seq([],true).
goal_list_to_seq([G|Gs],GsSeq) :-
  ((G = true)
   -> goal_list_to_seq(Gs,GsSeq)
    ; goal_list_to_seq_act(Gs,G,GsSeq)).

goal_list_to_seq_act([],G,G).
goal_list_to_seq_act([G2|Gs],G,(G,GsSeq)):-
  goal_list_to_seq_act(Gs,G2,GsSeq).
  
% ------------------------------------------------------------------------------
% compile_descs(Descs,Vs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,
%               FSPal,FSsIn,FSsOut)
% ------------------------------------------------------------------------------
% compiles descriptions Descs to constraint Vs into diff list Goals-GoalsRest
% ------------------------------------------------------------------------------
compile_descs([],[],Iqs,Iqs,Goals,Goals,_,Vars,Vars,_,FSs,FSs).
compile_descs([ArgDesc|ArgDescs],[Arg|Args],IqsIn,IqsOut,
              SubGoals,SubGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut):-
  compile_desc(ArgDesc,Arg,IqsIn,IqsMid,SubGoals,SubGoalsMid,CBSafe,VarsIn,
               VarsMid,FSPal,FSsIn,FSsMid),
  compile_descs(ArgDescs,Args,IqsMid,IqsOut,SubGoalsMid,SubGoalsRest,CBSafe,
                VarsMid,VarsOut,FSPal,FSsMid,FSsOut).

% ------------------------------------------------------------------------------
% compile_descs_fresh(Descs,Vs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
%                     VarsOut,FSPal,FSsIn,FSsOut)
% ------------------------------------------------------------------------------
% similar to compile_descs, except that Vs are instantiated to Ref-bot
% before compiling Descs
% ------------------------------------------------------------------------------
compile_descs_fresh([],[],Iqs,Iqs,Goals,Goals,_,Vars,Vars,_,FSs,FSs).
compile_descs_fresh([ArgDesc|ArgDescs],[Arg|Args],IqsIn,IqsOut,
                    SubGoals,SubGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,
                    FSsOut):-
  ( var(ArgDesc)    -> ( get_assoc(ArgDesc,VarsIn,Seen,VarsMid2,seen)
                         -> ( Seen == seen -> Arg = ArgDesc, 
                                              SubGoals = SubGoalsMid2
                            ; % Seen == tricky,
                              SubGoals = [(var(ArgDesc)
                              -> Arg = Ref-bot, ArgDesc = Arg
                               ; Arg = ArgDesc)|SubGoalsMid2]
                            )
                       ; Arg = ArgDesc, 
                         SubGoals = [ArgDesc = Ref-bot|SubGoalsMid2],
                         put_assoc(ArgDesc,VarsIn,seen,VarsMid2)
                       ),
                       IqsMid = IqsIn,
                       FSsMid2 = FSsIn
  ; ArgDesc = Tag-SVs -> deref(Tag,SVs,DTag,DSVs),
                         find_fs(FSsIn,DTag,DSVs,SubGoals,SubGoalsMid2,Arg,
                                 FSPal,FSsMid2),
                         IqsMid = IqsIn, 
                         VarsMid2 = VarsIn
  ; root_struct(ArgDesc,RStruct,DRest) -> 
    ( var(RStruct) -> ( get_assoc(RStruct,VarsIn,Seen,VarsMid,seen)
                         -> ( Seen == seen -> Arg = RStruct, 
                                              SubGoals = SubGoalsMid
                            ; % Seen == tricky,
                              SubGoals = [(var(RStruct)
                              -> Arg = Ref-bot, RStruct = Arg
                               ; Arg = RStruct)|SubGoalsMid]
                            )
                      ; Arg = RStruct, 
                        SubGoals = [RStruct = Ref-bot|SubGoalsMid],
                        put_assoc(RStruct,VarsIn,seen,VarsMid)
                      ),
                      FSsMid = FSsIn
    ; RStruct = Tag-SVs,
      deref(Tag,SVs,DTag,DSVs),
      find_fs(FSsIn,DTag,DSVs,SubGoals,SubGoalsMid,Arg,FSPal,FSsMid),
      VarsMid = VarsIn
    ),
    compile_desc(DRest,Arg,IqsIn,IqsMid,SubGoalsMid,SubGoalsMid2,CBSafe,
                 VarsMid,VarsMid2,FSPal,FSsMid,FSsMid2)
  ; % some other description - need a new FS
    Arg = Ref-bot,
    compile_desc(ArgDesc,Ref,bot,IqsIn,IqsMid,SubGoals,SubGoalsMid2,CBSafe,
                 VarsIn,VarsMid2,FSPal,FSsIn,FSsMid2)
  ),
  compile_descs_fresh(ArgDescs,Args,IqsMid,IqsOut,SubGoalsMid2,SubGoalsRest,
                      CBSafe,VarsMid2,VarsOut,FSPal,FSsMid2,FSsOut).

% ------------------------------------------------------------------------------
% root_struct(+Desc:<desc>,-RootStruct:<var_or_fs>,-DRest:<desc>)
% ------------------------------------------------------------------------------
% Find a variable that can be used to refer the feature structure described
%  by Desc.  If there is one, then we can use that variable as the argument
%  of the predicate being assembled in compile_descs_fresh/12.
% ------------------------------------------------------------------------------
root_struct((D1,D2),RStruct,DRest) :-
   is_root(D1),is_root(D2) -> ( RStruct = D1, DRest = D2
                              ; RStruct = D2, DRest = D1)
 ; is_root(D1) -> ( RStruct = D1, DRest = D2
                  ; root_struct(D2,RStruct,D2Rest),
                    DRest = (D1,D2Rest))
 ; is_root(D2) -> ( RStruct = D2, DRest = D1
                  ; root_struct(D1,RStruct,D1Rest),
                    DRest = (D1Rest,D2))
 ; ( root_struct(D1,RStruct,D1Rest),
     DRest = (D1Rest,D2)
   ; root_struct(D2,RStruct,D2Rest),
     DRest = (D1,D2Rest)).

root_struct((D1;D2),RStruct,DRest) :-
   (is_root(D1),is_root(D2)) -> D1 == D2,
                                RStruct = D1, DRest = bot
 ; is_root(D1) -> root_struct(D2,RStruct,D2Rest),
                  D1 == RStruct,
                  DRest = D2Rest
 ; is_root(D2) -> root_struct(D1,RStruct,D1Rest),
                  D2 == RStruct,
                  DRest = D1Rest
 ; root_struct(D1,RStruct,D1Rest),
   root_struct(D2,RStruct2,D2Rest),
   RStruct == RStruct2,
   DRest = (D1Rest;D2Rest).

is_root(D) :-
   var(D) -> true
 ; functor(D,-,2).

% ==============================================================================
% Phrase Structure Rule Compiler
% ==============================================================================

:-dynamic curr_lex_rule_depth/1.
curr_lex_rule_depth(2).

% ------------------------------------------------------------------------------
% lex_rule_depth(N:<int>)
% ------------------------------------------------------------------------------
% asserts curr_lex_rule_depth/1 to N -- controls lexical rule depth
% ------------------------------------------------------------------------------
lex_rule_depth(N):-
  retractall(curr_lex_rule_depth(_)),
  assert(curr_lex_rule_depth(N)).

% ------------------------------------------------------------------------------
% lex(Word:<word>, Tag:<var_tag>, SVs:<svs>, IqsOut:<ineq>s)               mh(0)
% ------------------------------------------------------------------------------
% Word has category Tag-SVs
% ------------------------------------------------------------------------------
(lex(Word,Tag,SVs,IqsOut) if_h) :-
  (WordStart ---> Desc),
  lex_act(Word,Tag,SVs,IqsOut,WordStart,Desc).

lex_act(Word,Tag,SVs,IqsOut,WordStart,Desc) :-
  if(add_to(Desc,TagStart,bot,[],IqsMid),
     (curr_lex_rule_depth(Max),
      lex_close(0,Max,WordStart,TagStart,bot,Word,TagMid,SVsMid,
                IqsMid,IqsMid2),  
      fully_deref_prune(TagMid,SVsMid,Tag,SVs,IqsMid2,IqsOut)),
     error_msg((nl,write('lex: unsatisfiable lexical entry for '),
                write(WordStart)))).

% ------------------------------------------------------------------------------
% lex_close(WordIn:<word>,TagIn:<var_tag>, SVsIn:<svs>,
%           WordOut:<word>,TagOut:<var_tag>, SVsOut:<svs>, IqsIn:<ineq>s,
%           IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% If WordIn has category TagIn-SVsIn, then WordOut has category
% TagOut-SVsOut;  computed by closing under lexical rules
% ------------------------------------------------------------------------------
lex_close(_,_,Word,Tag,SVs,Word,Tag,SVs,Iqs,Iqs).
lex_close(N,Max,WordIn,TagIn,SVsIn,WordOut,TagOut,SVsOut,IqsIn,IqsOut):-
  current_predicate(lex_rule,lex_rule(_,_,_,_,_,_,_,_)),
  N < Max,
  lex_rule(WordIn,TagIn,SVsIn,WordMid,TagMid,SVsMid,IqsIn,IqsMid),
  NPlus1 is N + 1,
  lex_close(NPlus1,Max,WordMid,TagMid,SVsMid,WordOut,TagOut,SVsOut,IqsMid,
            IqsOut).

% ------------------------------------------------------------------------------
% empty_cat(N:<neg>, Node:<int>, Tag:<var_tag>, SVs:<svs>, Iqs:<ineq>s, 
%           Dtrs:<ints>, RuleName:<atom>)                                  mh(0)
% ------------------------------------------------------------------------------
empty_cat(_,_,_,_,_,_,_) if_h [fail] :-
  \+ current_predicate(empty,empty(_)),
  findall(rule(Dtrs,_,Mother,RuleName,PrevDtrs,PrevDtrs,[]),
        (RuleName rule Mother ===> Dtrs),
        Rules),
  assert(alec_closed_rules(Rules)),
  !.
empty_cat(N,Node,TagOut,SVsOut,IqsOut,Dtrs,RuleName) if_h []:-
  findall(empty(M,_,FTag,FSVs,FIqs,[],empty),
   (empty(Desc),
    add_to(Desc,Tag,bot,[],IqsIn),
    gen_emptynum(M),
%  curr_lex_rule_depth(Max),             % should we be closing empty cats
%  lex_close(0,Max,e,Tag,bot,_,TagMid,SVsMid,IqsIn,IqsMid), % under lex. rules?
    fully_deref_prune(Tag,bot,FTag,FSVs,IqsIn,FIqs)),
   BasicEmptys),
  (no_subsumption
  -> MinimalEmptys = BasicEmptys
   ; minimise_emptys(BasicEmptys,[],MinimalEmptys)
  ),
  close_emptys(MinimalEmptys,ClosedEmptys,ClosedRules),
  (no_subsumption
  -> MinimalClosedEmptys = ClosedEmptys
   ; minimise_emptys(ClosedEmptys,[],MinimalClosedEmptys)
  ),
  ( member(empty(N,Node,TagOut,SVsOut,IqsOut,Dtrs,RuleName),MinimalClosedEmptys)
  ; assert(alec_closed_rules(ClosedRules)),
    fail
  ).

% ------------------------------------------------------------------------------
% minimise_emptys(+Emptys:<empty>s,+Accum:<empty>s,?MinimalEmptys:<empty>s)
% ------------------------------------------------------------------------------
% MinimalEmptys is the minimal list resulting from combining Emptys and
% Accum.  A list of empty(N,Node,Tag,SVs,Iqs,Dtrs,RuleName) terms is minimal 
% iff no term on the list subsumes any other term.
% ------------------------------------------------------------------------------ 
minimise_emptys([],MinimalEmptys,MinimalEmptys).
minimise_emptys([BE|BasicEmptys],Accum,MinimalEmptys) :-
  minimise_emptys_act(Accum,BE,BasicEmptys,NewAccum,NewAccum,MinimalEmptys).

minimise_emptys_act([],B,BsRest,NewAccum,[B],MEs) :-
  minimise_emptys(BsRest,NewAccum,MEs).
minimise_emptys_act([A|AsRest],B,BsRest,NewAccum,NARest,MEs) :-
  A = empty(_,_,ATag,ASVs,AIqs,_,_),
  B = empty(_,_,BTag,BSVs,BIqs,_,_),
  empty_assoc(H),
  empty_assoc(K),
  subsume(s(ATag,ASVs,BTag,BSVs,sdone),AIqs,BIqs,<,>,LReln,RReln,H,K),
  me_subsume_act(LReln,RReln,A,B,AsRest,BsRest,NewAccum,NARest,MEs).

me_subsume_act(<,_,A,_,AsRest,BsRest,NewAccum,[A|AsRest],MEs) :-
  nl,write('EFD-closure discarded a subsumed empty category'),
  minimise_emptys(BsRest,NewAccum,MEs).
me_subsume_act(#,>,_,B,AsRest,BsRest,NewAccum,NARest,MEs) :-
  nl,write('EFD-closure discarded a subsumed empty category'),  
  minimise_emptys_act(AsRest,B,BsRest,NewAccum,NARest,MEs).
me_subsume_act(#,#,A,B,AsRest,BsRest,NewAccum,[A|NARest],MEs) :-
  minimise_emptys_act(AsRest,B,BsRest,NewAccum,NARest,MEs).

% ------------------------------------------------------------------------------
% close_emptys(+Emptys:<empty>s,-ClosedEmptys:<empty>s,-ClosedRules:<rule>s)
% ------------------------------------------------------------------------------
% Close Emptys under the rules in the database to obtain ClosedEmptys.  In
%  the process, we also close those rules closed under empty category prefixes,
%  to obtain ClosedRules.
% ------------------------------------------------------------------------------
close_emptys(Emptys,ClosedEmptys,ClosedRules) :-
  findall(rule(Dtrs,_,Mother,RuleName,PrevDtrs,PrevDtrs,[]),
        (RuleName rule Mother ===> Dtrs),
        Rules),
  efd_iterate(Emptys,Rules,[],[],[],ClosedEmptys,ClosedRules).

% ------------------------------------------------------------------------------
% efd_iterate(+Es:<empty>s,+Rs:<rule>s,+NRs:<rule>s,+EAs:<empty>s,+RAs:<rule>s,
%             -ClosedEmptys:<empty>s,-ClosedRules:<rule>s)
% ------------------------------------------------------------------------------
% The Empty-First-Daughter closure algorithm closes a given collection of
%  base empty categories and base extended PS rules breadth-first under 
%  prefixes of empty category daughters.  This has the following benefits:
%  1) it corrects a long-standing problem in ALE with combining empty 
%     categories.  Because any permutation of empty categories can, in
%     principle, be combined to form a new empty category, ALE cannot perform
%     depth-first closure under a leftmost empty category as it can with 
%     normal edges;
%  2) it corrects a problem that non-ISO-compatible Prologs, including SICStus 
%     Prolog, have with asserted predicates that results in empty category
%     leftmost daughters not being able to combine with their own outputs;
%  3) it allows parsers to establish a precondition that rules only need to
%     be closed with non-empty leftmost daughters at run-time.  As a result,
%     when a new mother category is created and closed under rules as the
%     leftmost daughter, it cannot combine with other edges created with the
%     same left node.  This allows ALE, at each step in its right-to-left pass
%     throught the string, to copy all of the edges in the internal database
%     back onto the heap before they can be used again, and thus reduces
%     edge copying to a constant 2/edge for non-empty edges (edges with 
%     different left and right nodes).  Keeping a copy of the chart on the
%     heap also allows for more sophisticated indexing strategies that would
%     otherwise be overwhelmed by the cost of copying the edge before matching.
%
% Let Es,Rs,NEs,NRs,EAs, and RAs be lists.  Initialise Es to the base empty 
%  categories, and Rs to the base rules, and the others to []
% 
% loop:
% while Es =/= [] do
%   for each E in Es do
%     for each R in Rs do
%       match E against the leftmost unmatched category description of R
%       if it does not match, continue
%       if the leftmost category was the rightmost (unary rule), then
%         add the new empty category to NEs
%       otherwise, add the new rule (with leftmost category marked as matched)
%         to NRs
%     od
%   od
%   EAs := Es + EAs
%   Rs := Rs + RAs, RAs := []
%   Es := NEs, NEs := []
% od
% if NRs = [], 
%  then end: EAs are the closed empty cats, Rs are the closed rules
%  else
%    Es := EAs, EAs := []
%    RAs := Rs, Rs := NRs, NRs := []
%    go to loop
%
% This algorithm terminates for exactly those grammars in which bottom-up
%  parsing over empty categories terminates, i.e., it is no worse than pure
%  bottom-up parsing.
% ------------------------------------------------------------------------------
efd_iterate([],Rules,NewRules,EmptyAccum,_RuleAccum,  % RuleAccum is []
            ClosedEmptys,ClosedRules) :-
  !,
  (NewRules == []
  -> ClosedEmptys = EmptyAccum, ClosedRules = Rules
   ; efd_iterate(EmptyAccum,NewRules,[],[],Rules,ClosedEmptys,ClosedRules)
  ).
efd_iterate(Emptys,Rules,NewRules,EmptyAccum,RuleAccum,
            ClosedEmptys,ClosedRules) :-
  apply_once(Emptys,Rules,NewEmptysandRules),
  split_emptys_rules(NewEmptysandRules,NewRules,NewRules1,NewEmptys),
  append(Emptys,EmptyAccum,EmptyAccum1),
  append(Rules,RuleAccum,Rules1),
  efd_iterate(NewEmptys,Rules1,NewRules1,EmptyAccum1,[],
              ClosedEmptys,ClosedRules).

% ------------------------------------------------------------------------------
% apply_once(+Es:<empty>s,+Rs:<empty>s,-NEsorRs:<empty_or_rule>s)
% ------------------------------------------------------------------------------
% the two for-loops of the EFD-closure algorithm above.
% ------------------------------------------------------------------------------
apply_once(Emptys,Rules,NewEmptysandRules) :-
  findall(EmptyorRule,
          (member(Empty,Emptys),
           member(rule(Dtrs,Node,Mother,RuleName,PrevDtrs,PrevDtrsMid,Iqs),
                  Rules),
           match_cat_to_next_cat(Dtrs,Mother,RuleName,PrevDtrs,PrevDtrsMid,Iqs,
                                 Empty,EmptyorRule,Node)),
          NewEmptysandRules).

% ------------------------------------------------------------------------------
% split_emptys_rules(+NEsorRs:<empty_or_rule>s,+NRsOld:<rule>s,
%                    -NRsNew:<rule>s,-NEsNew:<empty>s)
% ------------------------------------------------------------------------------
% classifies the results of apply_once/3 as empty cats or rules, and adds them
% to NEs or NRs, respectively.
% ------------------------------------------------------------------------------

split_emptys_rules([],NewRulesRest,NewRulesRest,[]).
split_emptys_rules([Item|Items],NewRulesRest,NewRules,NewEmptys) :-
  functor(Item,Functor,_),
  ((Functor == rule)
  -> NewRules = [Item|NewRulesMid],
%     nl,write('EFD-closure generated a partial rule'),
     split_emptys_rules(Items,NewRulesRest,NewRulesMid,NewEmptys)
   ; % Functor == empty,
     NewEmptys = [Item|NewEmptysMid],
%     nl,write('EFD-closure generated an empty category'),
     split_emptys_rules(Items,NewRulesRest,NewRules,NewEmptysMid)
  ).

% ------------------------------------------------------------------------------
% match_cat_to_next_cat(+Dtrs:<dtr>s,+Mother:<desc>,+RuleName:<atom>,
%                       +PrevDtrs:<empty/2>s,-PrevDtrsRest:<var_empty/2>s,
%                       +RuleIqs:<ineq>s,+Empty:<empty>,
%                       -EmptyorRule:<empty_or_rule>,-Node:<var_int>)
% ------------------------------------------------------------------------------
% interpretive matching of empty category to leftmost category description
% plus all procedural attachments up to the next category description.
% ------------------------------------------------------------------------------
match_cat_to_next_cat((cat> Dtr,Rest),Mother,RuleName,PrevDtrs,
                      [empty(N,Node)|PrevDtrsMid],RuleIqs,
                      empty(N,Node,Tag,SVs,Iqs,_,_),EmptyorRule,Node) :-
  append(Iqs,RuleIqs,IqsIn),
  add_to(Dtr,Tag,SVs,IqsIn,IqsMid),
  check_inequal(IqsMid,IqsMid2),
  match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,IqsMid2,
                    EmptyorRule,Node).
match_cat_to_next_cat((cat> Dtr),Mother,RuleName,PrevDtrs,[empty(N,Node)],
                      RuleIqs,empty(N,Node,Tag,SVs,Iqs,_,_),
                      empty(NewN,Node,TagOut,SVsOut,IqsOut,PrevDtrs,RuleName),
                      Node) :-
  append(Iqs,RuleIqs,IqsIn),
  add_to(Dtr,Tag,SVs,IqsIn,IqsMid),
  add_to(Mother,Tag2,bot,IqsMid,IqsMid2),
  fully_deref_prune(Tag2,bot,TagOut,SVsOut,IqsMid2,IqsOut),
  gen_emptynum(NewN).
match_cat_to_next_cat((sem_head> Dtr,Rest),Mother,RuleName,PrevDtrs,
                      [empty(N,Node)|PrevDtrsMid],RuleIqs,
                      empty(N,Node,Tag,SVs,Iqs,_,_),EmptyorRule,Node) :-
  append(Iqs,RuleIqs,IqsIn),
  add_to(Dtr,Tag,SVs,IqsIn,IqsMid),
  check_inequal(IqsMid,IqsMid2),
  match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,IqsMid2,
                    EmptyorRule,Node).
match_cat_to_next_cat((sem_head> Dtr),Mother,RuleName,PrevDtrs,[empty(N,Node)],
                      RuleIqs,empty(N,Node,Tag,SVs,Iqs,_,_),
                      empty(NewN,Node,TagOut,SVsOut,IqsOut,PrevDtrs,RuleName),
                      Node) :-
  append(Iqs,RuleIqs,IqsIn),
  add_to(Dtr,Tag,SVs,IqsIn,IqsMid),
  add_to(Mother,Tag2,bot,IqsMid,IqsMid2),
  fully_deref_prune(Tag2,bot,TagOut,SVsOut,IqsMid2,IqsOut),
  gen_emptynum(NewN).
match_cat_to_next_cat((cats> Dtrs,Rest),Mother,RuleName,PrevDtrs,PrevDtrsMid,
                      RuleIqs,Empty,EmptyorRule,Node) :-
  add_to(Dtrs,DtrsTag,bot,RuleIqs,IqsIn),
  deref(DtrsTag,bot,_DTag,DSVs),
  functor(DSVs,DtrsType,_),
  (sub_type(ne_list,DtrsType)
  -> arg(1,DSVs,HdFS),
     Empty = empty(N,Node,Tag,SVs,Iqs,_,_),
     append(Iqs,IqsIn,IqsMid),
     ud(HdFS,Tag,SVs,IqsMid,IqsMid2),
     check_inequal(IqsMid2,IqsMid3),
     arg(2,DSVs,TlFS),
     deref(TlFS,TlTag,TlSVs),
     functor(TlSVs,TlType,_),
     (sub_type(ne_list,TlType)
     -> PrevDtrsMid = [empty(N,Node)|PrevDtrsRest],
        EmptyorRule = rule((remainder(TlTag,TlSVs),Rest),Node,Mother,RuleName,
                           PrevDtrs,PrevDtrsRest,IqsMid3)
      ; (sub_type(e_list,TlType)
        -> PrevDtrsMid = [empty(N,Node)|PrevDtrsMid2],
           match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid2,
                             IqsMid3,EmptyorRule,Node)
         ; error_msg((nl,write('error: cats> value with sort, '),write(TlType),
                      write(' is not a valid list argument')))
        )
     )
   ; (sub_type(e_list,DtrsType)
     -> match_cat_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,
                              RuleIqs,Empty,EmptyorRule,Node)
      ; error_msg((nl,write('error: cats> value with sort, '),write(DtrsType),
                   write(' is not a valid list argument')))
     )
  ).
match_cat_to_next_cat((cats> Dtrs),Mother,RuleName,PrevDtrs,PrevDtrsMid,
                      RuleIqs,empty(N,Node,Tag,SVs,Iqs,_,_),EmptyorRule,
                      Node) :-
  append(Iqs,RuleIqs,IqsIn),
  add_to(Dtrs,DtrsTag,bot,IqsIn,IqsMid),
  deref(DtrsTag,bot,_DTag,DSVs),
  functor(DSVs,DtrsType,_),
  (sub_type(ne_list,DtrsType)
  -> arg(1,DSVs,HdFS),
     ud(HdFS,Tag,SVs,IqsMid,IqsMid2),
     check_inequal(IqsMid2,IqsMid3),
     arg(2,DSVs,TlFS),
     deref(TlFS,TlTag,TlSVs),
     functor(TlSVs,TlType,_),
     (sub_type(ne_list,TlType)
     -> PrevDtrsMid = [empty(N,Node)|PrevDtrsRest],
        EmptyorRule = rule(remainder(TlTag,TlSVs),Node,Mother,RuleName,PrevDtrs,
                           PrevDtrsRest,IqsMid3)
      ; (sub_type(e_list,TlType)
        -> add_to(Mother,Tag2,bot,IqsMid3,IqsMid4),
           fully_deref_prune(Tag2,bot,TagOut,SVsOut,IqsMid4,IqsOut),
           PrevDtrsMid = [empty(N,Node)],
           EmptyorRule = empty(NewN,Node,TagOut,SVsOut,IqsOut,PrevDtrs,
                               RuleName),
           gen_emptynum(NewN)
         ; error_msg((nl,write('error: cats> value with sort, '),write(TlType),
                      write(' is not a valid list argument')))
        )
     )
   ; (sub_type(e_list,DtrsType)
     -> error_msg((nl,write('error: rule '),write(RuleName),
                   write(' has no daughters')))
      ; error_msg((nl,write('error: cats> value with sort, '),write(DtrsType),
                   write(' is not a valid list argument')))
     )
  ).
match_cat_to_next_cat((remainder(_,RSVs),Rest),Mother,RuleName,PrevDtrs,
                      PrevDtrsMid,RuleIqs,empty(N,Node,Tag,SVs,Iqs,_,_),
                      EmptyorRule,Node) :-
  append(Iqs,RuleIqs,IqsIn),
  arg(1,RSVs,HdFS),
  ud(HdFS,Tag,SVs,IqsIn,IqsMid2),
  check_inequal(IqsMid2,IqsMid3),
  arg(2,RSVs,TlFS),
  deref(TlFS,TlTag,TlSVs),
  functor(TlSVs,TlType,_),
  (sub_type(ne_list,TlType)
  -> PrevDtrsMid = [empty(N,Node)|PrevDtrsRest],
     EmptyorRule = rule(remainder(TlTag,TlSVs),Node,Mother,RuleName,PrevDtrs,
                        PrevDtrsRest,IqsMid3)
   ; (sub_type(e_list,TlType)
     -> PrevDtrsMid = [empty(N,Node)|PrevDtrsMid2],
        match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid2,IqsMid3,
                          EmptyorRule,Node)
      ; error_msg((nl,write('error: cats> value with sort, '),write(TlType),
                   write(' is not a valid list argument')))
     )
  ).
match_cat_to_next_cat(remainder(_,RSVs),Mother,RuleName,PrevDtrs,PrevDtrsMid,
                      RuleIqs,empty(N,Node,Tag,SVs,Iqs,_,_),EmptyorRule,
                      Node) :-
  append(Iqs,RuleIqs,IqsIn),
  arg(1,RSVs,HdFS),
  ud(HdFS,Tag,SVs,IqsIn,IqsMid2),
  check_inequal(IqsMid2,IqsMid3),
  arg(2,RSVs,TlFS),
  deref(TlFS,TlTag,TlSVs),
  functor(TlSVs,TlType,_),
  (sub_type(ne_list,TlType)
  -> PrevDtrsMid = [empty(N,Node)|PrevDtrsRest],
     EmptyorRule = rule(remainder(TlTag,TlSVs),Node,Mother,RuleName,PrevDtrs,
                        PrevDtrsRest,IqsMid3)
   ; (sub_type(e_list,TlType)
     -> add_to(Mother,Tag2,bot,IqsMid3,IqsMid4),
        fully_deref_prune(Tag2,bot,TagOut,SVsOut,IqsMid4,IqsOut),
        PrevDtrsMid = [empty(N,Node)],
        EmptyorRule = empty(NewN,Node,TagOut,SVsOut,IqsOut,PrevDtrs,RuleName),
        gen_emptynum(NewN)
      ; error_msg((nl,write('error: cats> value with sort, '),write(TlType),
                   write(' is not a valid list argument')))
     )
  ).
match_cat_to_next_cat((goal> GoalDesc,Rest),Mother,RuleName,PrevDtrs,
                      PrevDtrsMid,RuleIqs,Empty,EmptyorRule,Node) :-
  query_goal(GoalDesc,Goal,RuleIqs,IqsMid),
  call(Goal),
  check_inequal(IqsMid,IqsMid2),
  match_cat_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,IqsMid2,
                        Empty,EmptyorRule,Node).
match_cat_to_next_cat((goal> _),_,RuleName,_,_,_,_,_,_) :-
  error_msg((nl,write('error: rule '),write(RuleName),
             write(' has no daughters'))).
match_cat_to_next_cat((sem_goal> GoalDesc,Rest),Mother,RuleName,PrevDtrs,
                      PrevDtrsMid,RuleIqs,Empty,EmptyorRule,Node) :-
  query_goal(GoalDesc,Goal,RuleIqs,IqsMid),
  call(Goal),
  check_inequal(IqsMid,IqsMid2),
  match_cat_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,IqsMid2,
                        Empty,EmptyorRule,Node).
match_cat_to_next_cat((sem_goal> _),_,RuleName,_,_,_,_,_,_) :-
  error_msg((nl,write('error: rule '),write(RuleName),
             write(' has no daughters'))).

% ------------------------------------------------------------------------------
% match_to_next_cat(+Dtrs:<dtr>s,+Mother:<desc>,+RuleName:<atom>,
%                   +PrevDtrs:<empty/2>s,-PrevDtrsRest:<var_empty/2>s,
%                   +RuleIqs:<ineq>s,-EmptyorRule:<empty_or_rule>,
%                   -Node:<var_int>)
% ------------------------------------------------------------------------------
% Same as match_cat_to_next_cat/9 but leftmost category has already been
% matched.  Now interpret all procedural attachments until next category
% is encountered or no daughters remain.
% ------------------------------------------------------------------------------

match_to_next_cat((cat> Dtr,Rest),Mother,RuleName,PrevDtrs,PrevDtrsRest,Iqs,
                  rule((cat> Dtr,Rest),Node,Mother,RuleName,PrevDtrs,
                       PrevDtrsRest,Iqs),
                  Node).
match_to_next_cat((cat> Dtr),Mother,RuleName,PrevDtrs,PrevDtrsRest,Iqs,
                  rule((cat> Dtr),Node,Mother,RuleName,PrevDtrs,PrevDtrsRest,
                       Iqs),
                  Node).
match_to_next_cat((sem_head> Dtr,Rest),Mother,RuleName,PrevDtrs,PrevDtrsRest,
                  Iqs,
                  rule((sem_head> Dtr,Rest),Node,Mother,RuleName,PrevDtrs,
                       PrevDtrsRest,Iqs),
                  Node).
match_to_next_cat((sem_head> Dtr),Mother,RuleName,PrevDtrs,PrevDtrsRest,Iqs,
                  rule((sem_head> Dtr),Node,Mother,RuleName,PrevDtrs,PrevDtrsRest,
                       Iqs),
                  Node).
match_to_next_cat((cats> Dtrs,Rest),Mother,RuleName,PrevDtrs,PrevDtrsMid,IqsIn,
                  EmptyorRule,Node) :-
  add_to(Dtrs,DtrsTag,bot,IqsIn,IqsMid),
  check_inequal(IqsMid,IqsMid2),
  deref(DtrsTag,bot,DTag,DSVs),
  functor(DSVs,DtrsType,_),
  (sub_type(ne_list,DtrsType)
  -> EmptyorRule = rule((remainder(DTag,DSVs),Rest),Node,Mother,RuleName,PrevDtrs,
                        PrevDtrsMid,IqsMid2)
   ; (sub_type(e_list,DtrsType)
     -> match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,IqsMid2,
                          EmptyorRule,Node)
      ; error_msg((nl,write('error: cats> value with sort, '),write(DtrsType),
                   write(' is not a valid list argument')))
     )
  ).
match_to_next_cat((cats> Dtrs),Mother,RuleName,PrevDtrs,PrevDtrsMid,IqsIn,
                  EmptyorRule,Node) :-
  add_to(Dtrs,DtrsTag,bot,IqsIn,IqsMid),
  check_inequal(IqsMid,IqsMid2),
  deref(DtrsTag,bot,DTag,DSVs),
  functor(DSVs,DtrsType,_),
  (sub_type(ne_list,DtrsType)
  -> EmptyorRule = rule(remainder(DTag,DSVs),Node,Mother,RuleName,PrevDtrs,
                        PrevDtrsMid,IqsMid2)
   ; (sub_type(e_list,DtrsType)
     -> add_to(Mother,Tag,bot,IqsMid2,IqsMid3),
        fully_deref_prune(Tag,bot,TagOut,SVsOut,IqsMid3,IqsOut),
        PrevDtrsMid = [],
        EmptyorRule = empty(NewN,Node,TagOut,SVsOut,IqsOut,PrevDtrs,RuleName),
        gen_emptynum(NewN)
      ; error_msg((nl,write('error: cats> value with sort, '),write(DtrsType),
                   write(' is not a valid list argument')))
     )
  ).
match_to_next_cat((goal> GoalDesc,Rest),Mother,RuleName,PrevDtrs,PrevDtrsMid,
                  IqsIn,EmptyorRule,Node) :-
  query_goal(GoalDesc,Goal,IqsIn,IqsMid),
  call(Goal),
  check_inequal(IqsMid,IqsMid2),
  match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,IqsMid2,
                    EmptyorRule,Node).
match_to_next_cat((goal> GoalDesc),Mother,RuleName,PrevDtrs,[],IqsIn,
                  empty(NewN,Node,TagOut,SVsOut,IqsOut,PrevDtrs,RuleName),
                  Node) :-
  query_goal(GoalDesc,Goal,IqsIn,IqsMid),
  call(Goal),
  check_inequal(IqsMid,IqsMid2),
  add_to(Mother,Tag,bot,IqsMid2,IqsMid3),
  fully_deref_prune(Tag,bot,TagOut,SVsOut,IqsMid3,IqsOut),
  gen_emptynum(NewN).
match_to_next_cat((sem_goal> GoalDesc,Rest),Mother,RuleName,PrevDtrs,
                  PrevDtrsMid,IqsIn,EmptyorRule,Node) :-
  query_goal(GoalDesc,Goal,IqsIn,IqsMid),
  call(Goal),
  check_inequal(IqsMid,IqsMid2),
  match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,IqsMid2,
                    EmptyorRule,Node).
match_to_next_cat((sem_goal> GoalDesc),Mother,RuleName,PrevDtrs,[],IqsIn,
                  empty(NewN,Node,TagOut,SVsOut,IqsOut,PrevDtrs,RuleName),
                  Node) :-
  query_goal(GoalDesc,Goal,IqsIn,IqsMid),
  call(Goal),
  check_inequal(IqsMid,IqsMid2),
  add_to(Mother,Tag,bot,IqsMid2,IqsMid3),
  fully_deref_prune(Tag,bot,TagOut,SVsOut,IqsMid3,IqsOut),
  gen_emptynum(NewN).

% ------------------------------------------------------------------------------
% rule(Tag:<var_tag>, SVs:<svs>, Iqs:<ineq>s, Left:<int>, Right:<int>,
%      N:<int>,Chart:<chart>)                                              mh(0)
% ------------------------------------------------------------------------------
% adds the result of any rule of which Tag-SVs from Left to Right
% might be the first element and the rest of the categories are in the chart
% ------------------------------------------------------------------------------
rule(Tag,SVs,Iqs,Left,Right,N,Chart) if_h SubGoals :-
  retract(alec_closed_rules(ClosedRules)),
  empty_assoc(VarsIn),
  member(rule(Daughters,Left,Mother,RuleName,PrevDtrs,PrevDtrsRest,RuleIqs),
         ClosedRules),
  append(RuleIqs,Iqs,IqsIn),
  compile_dtrs(Daughters,Tag,SVs,IqsIn,Left,Right,N,SubGoalsMid,[],PrevDtrs,
               PrevDtrsRest,Mother,RuleName,Chart,true,VarsIn,_,FSPal,[],
               FSsOut),
  build_fs_palette(FSsOut,FSPal,SubGoals,SubGoalsMid,RuleIqs).

% ------------------------------------------------------------------------------
% compile_dtrs(Dtrs,Tag,SVs,Iqs,Left,Right,N,PGoals,PGoalsRest,Dtrs,DtrsRest,
%              Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut)
% ------------------------------------------------------------------------------
% compiles description Dtrs to apply rule to first category Tag-SVs,
% at position Left-Right in chart, producing a list of Prolog goals
% diff list PGoals-PGoalsRest;  Mother is result produced
% ------------------------------------------------------------------------------
compile_dtrs((cat> Dtr,Rest),Tag,SVs,IqsIn,Left,Right,N,PGoals,PGoalsRest,
             Dtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut):-
  !, compile_desc(Dtr,Tag,SVs,IqsIn,IqsMid,PGoals,
                  [check_inequal(IqsMid,IqsOut)|PGoalsMid],CBSafe,VarsIn,
                  VarsMid,FSPal,FSsIn,FSsMid),
  DtrsMid = [N|DtrsRest],
  compile_dtrs_rest(Rest,Left,Right,IqsOut,PGoalsMid,PGoalsRest,Mother,
                    Dtrs,DtrsRest,RuleName,Chart,CBSafe,VarsMid,VarsOut,FSPal,
                    FSsMid,FSsOut).
% 5/1/96 Octav -- added a clause for 'sem_head>' label
% (sem_head> daughters behave just like cat> daughters during parsing)
compile_dtrs((sem_head> Dtr,Rest),Tag,SVs,IqsIn,Left,Right,N,PGoals,PGoalsRest,
             Dtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut):-
  !, compile_desc(Dtr,Tag,SVs,IqsIn,IqsMid,PGoals,
                  [check_inequal(IqsMid,IqsOut)|PGoalsMid],CBSafe,VarsIn,
                  VarsMid,FSPal,FSsIn,FSsMid),
  DtrsMid = [N|DtrsRest],
  compile_dtrs_rest(Rest,Left,Right,IqsOut,PGoalsMid,PGoalsRest,Mother,
                    Dtrs,DtrsRest,RuleName,Chart,CBSafe,VarsMid,VarsOut,FSPal,
                    FSsMid,FSsOut).
compile_dtrs((cats> Dtrs,Rest),Tag,SVs,IqsIn,Left,Right,N,PGoals,PGoalsRest,
             PrevDtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,
             FSPal,FSsIn,FSsOut) :-
  !,compile_desc(Dtrs,Tag2,bot,IqsIn,IqsMid,PGoals,
       [check_inequal(IqsMid,IqsMid2),
        deref(Tag2,bot,_,DescSVs),
        DescSVs =.. [Sort|Vs], 
        ((Sort == e_list) ->
          PGoal_elist
        ; (match_list(Sort,Vs,Tag,SVs,Right,N,DtrsMid,DtrsRest,Chart,NextRight,
                     IqsMid2,IqsOut),  % a_ correctly causes error
           PGoal_nelist))|PGoalsRest],CBSafe,VarsIn,VarsMid,FSPal,FSsIn,FSsMid), 
  compile_dtrs_rest(Rest,Left,NextRight,IqsOut,PGoalsMid_nelist,[],
               Mother,PrevDtrs,DtrsRest,RuleName,Chart,CBSafe,VarsMid,
               Vars_nelist,FSPal,FSsMid,FSs_nelist),
  compile_dtrs(Rest,Tag,SVs,IqsMid2,Left,Right,N,PGoalsMid_elist,[],
               PrevDtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsMid,
               Vars_elist,FSPal,FSsMid,FSs_elist),
  goal_list_to_seq(PGoalsMid_nelist,PGoal_nelist),
  goal_list_to_seq(PGoalsMid_elist,PGoal_elist),
  vars_merge(Vars_nelist,Vars_elist,VarsOut),
  fss_merge(FSs_nelist,FSs_elist,FSsOut).
compile_dtrs((remainder(RTag,RSVs),Rest),Tag,SVs,IqsIn,Left,Right,N,PGoals,
             PGoalsRest,Dtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,
             FSPal,FSsIn,FSsOut) :-
  !,PGoals = [arg(Arg,FSPal,RVar),
              arg(2,RVar,RVarSVs),
              RVarSVs =.. [Sort|Vs],
              match_list(Sort,Vs,Tag,SVs,Right,N,DtrsMid,DtrsRest,Chart,NextRight,
                         IqsIn,IqsMid)|PGoalsMid],
  FSsMid = [seen(RTag,RSVs,RVar,Arg)|FSsIn],
  compile_dtrs_rest(Rest,Left,NextRight,IqsMid,PGoalsMid,PGoalsRest,Mother,
                    Dtrs,DtrsRest,RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,
                    FSsMid,FSsOut).
compile_dtrs((goal> Goal,Rest),Tag,SVs,IqsIn,Left,Right,N,PGoals,PGoalsRest,
             Dtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut):-
  !, compile_body(Goal,IqsIn,IqsMid,PGoals,PGoalsMid,CBSafe,VarsIn,VarsMid,
                  FSPal,FSsIn,FSsMid),
  compile_dtrs(Rest,Tag,SVs,IqsMid,Left,Right,N,PGoalsMid,PGoalsRest,
               Dtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsMid,VarsOut,FSPal,
               FSsMid,FSsOut).
% 6/1/97 Octav -- added a clause for 'sem_goal>' label
% (sem_goal> daughters behave just like goal> daughters during parsing)
compile_dtrs((sem_goal> Goal,Rest),Tag,SVs,IqsIn,Left,Right,N,PGoals,
             PGoalsRest,Dtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,
             FSPal,FSsIn,FSsOut):-
  !, compile_body(Goal,IqsIn,IqsMid,PGoals,PGoalsMid,CBSafe,VarsIn,VarsMid,FSPal,
                  FSsIn,FSsMid),
  compile_dtrs(Rest,Tag,SVs,IqsMid,Left,Right,N,PGoalsMid,PGoalsRest,
               Dtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsMid,VarsOut,FSPal,
               FSsMid,FSsOut).
compile_dtrs((cat> Dtr),Tag,SVs,IqsIn,Left,Right,N,PGoals,PGoalsRest,Dtrs,
             [N],Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_desc(Dtr,Tag,SVs,IqsIn,IqsMid,PGoals,
                  [check_inequal(IqsMid,IqsMid2)|PGoalsMid],CBSafe,VarsIn,
                  VarsMid,FSPal,FSsIn,FSsMid),
  compile_desc(Mother,Tag2,bot,IqsMid2,IqsOut,PGoalsMid,
               [add_edge_deref(Left,Right,Tag2,bot,IqsOut,Dtrs,RuleName,Chart)|
                PGoalsRest],CBSafe,VarsMid,VarsOut,FSPal,FSsMid,FSsOut).
% 5/1/96 Octav -- added a clause for 'sem_head>' label
% (behaves the same as cat> during parsing)
compile_dtrs((sem_head> Dtr),Tag,SVs,IqsIn,Left,Right,N,PGoals,PGoalsRest,
	     Dtrs,[N],Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut):-
  !, compile_desc(Dtr,Tag,SVs,IqsIn,IqsMid,PGoals,
                  [check_inequal(IqsMid,IqsMid2)|PGoalsMid],CBSafe,VarsIn,
                  VarsMid,FSPal,FSsIn,FSsMid),
  compile_desc(Mother,Tag2,bot,IqsMid2,IqsOut,PGoalsMid,
               [add_edge_deref(Left,Right,Tag2,bot,IqsOut,Dtrs,RuleName,Chart)|
                PGoalsRest],CBSafe,VarsMid,VarsOut,FSPal,FSsMid,FSsOut).
% don't check inequations after mother since add_edge_deref does that
compile_dtrs((cats> Dtrs),Tag,SVs,IqsIn,Left,Right,N,PGoals,PGoalsRest,
             PrevDtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,
             FSPal,FSsIn,FSsOut) :-
  !,compile_desc(Dtrs,Tag3,bot,IqsIn,IqsMid,PGoals,
      [check_inequal(IqsMid,IqsMid2),
       deref(Tag3,bot,_,DescSVs),
       DescSVs =.. [Sort|Vs], 
       ((Sort == e_list) ->
         fail
       ; (match_list(Sort,Vs,Tag,SVs,Right,N,DtrsMid,[],Chart,NextRight,
                     IqsMid2,IqsMid3),
          PGoal))|PGoalsRest],CBSafe,VarsIn,VarsMid,FSPal,FSsIn,FSsMid), % a_ 
  compile_desc(Mother,Tag2,bot,IqsMid3,IqsOut,PGoalsMid,   %  correctly causes error
          [add_edge_deref(Left,NextRight,Tag2,bot,IqsOut,PrevDtrs,RuleName,
                          Chart)],
          CBSafe,VarsMid,VarsOut,FSPal,FSsMid,FSsOut),
  goal_list_to_seq(PGoalsMid,PGoal).
compile_dtrs(remainder(RTag,RSVs),Tag,SVs,IqsIn,Left,Right,N,PGoals,PGoalsRest,
             Dtrs,DtrsMid,Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut) :-
  !,PGoals = [arg(Arg,FSPal,RVar),
              arg(2,RVar,RVarSVs),
              RVarSVs =.. [Sort|Vs],
              match_list(Sort,Vs,Tag,SVs,Right,N,DtrsMid,[],Chart,NextRight,
                         IqsIn,IqsMid)|PGoalsRest],
  FSsMid = [seen(RTag,RSVs,RVar,Arg)|FSsIn],
  compile_desc(Mother,Tag2,bot,IqsMid,IqsOut,PGoalsRest,
               [add_edge_deref(Left,NextRight,Tag2,bot,IqsOut,Dtrs,RuleName,Chart)],
               CBSafe,VarsIn,VarsOut,FSPal,FSsMid,FSsOut).
compile_dtrs(Foo,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_):-
  !,       [invalid,line,Foo,in,rule] if_error
              true,
  fail.

% ------------------------------------------------------------------------------
% compile_dtrs_rest(Dtrs,Left,Right,IqsMid,PGoals,PGoalsRest,Mother,
%                   PrevDtrs,DtrsRest,RuleName,CBSafe,VarsIn,VarsOut,FSPal,
%                   FSsIn,FSsOut)
% ------------------------------------------------------------------------------
% same as compile_dtrs, only after first category on RHS of rule is
% found;  thus looks for an edge/4 if a cat> or cats> spec is found
% ------------------------------------------------------------------------------
compile_dtrs_rest((cat> Dtr,Rest),Left,Right,IqsMid,
            [get_edge(Right,Chart,N,NewRight,Tag,SVs,EdgeIqs,_,_)|PGoals],
            PGoalsRest,Mother,PrevDtrs,[N|DtrsRest],RuleName,Chart,CBSafe,VarsIn,
            VarsOut,FSPal,FSsIn,FSsOut):-
  !,compile_desc(Dtr,Tag,SVs,IqsMid,IqsMid2,PGoals,
                 [append(IqsMid2,EdgeIqs,IqsMid3),
                  check_inequal(IqsMid3,IqsOut)|PGoalsMid],CBSafe,VarsIn,
                 VarsMid,FSPal,FSsIn,FSsMid),
  compile_dtrs_rest(Rest,Left,NewRight,IqsOut,PGoalsMid,PGoalsRest,Mother,
                    PrevDtrs,DtrsRest,RuleName,Chart,CBSafe,VarsMid,VarsOut,FSPal,
                    FSsMid,FSsOut).
% 5/1/96 - Octav -- added a clause for 'sem_head>' label
compile_dtrs_rest((sem_head> Dtr,Rest),Left,Right,IqsMid,
             [get_edge(Right,Chart,N,NewRight,Tag,SVs,EdgeIqs,_,_)|PGoals],
             PGoalsRest,Mother,PrevDtrs,[N|DtrsRest],RuleName,Chart,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !,compile_desc(Dtr,Tag,SVs,IqsMid,IqsMid2,PGoals,
                 [append(IqsMid2,EdgeIqs,IqsMid3),
                  check_inequal(IqsMid3,IqsOut)|PGoalsMid],CBSafe,VarsIn,
                 VarsMid,FSPal,FSsIn,FSsMid),
  compile_dtrs_rest(Rest,Left,NewRight,IqsOut,PGoalsMid,PGoalsRest,Mother,
                    PrevDtrs,DtrsRest,RuleName,Chart,CBSafe,VarsMid,VarsOut,FSPal,
                    FSsMid,FSsOut).
compile_dtrs_rest((cats> Dtrs,Rest),Left,Right,IqsMid,PGoals,PGoalsRest,
                  Mother,PrevDtrs,DtrsRest,RuleName,Chart,CBSafe,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_desc(Dtrs,Tag,bot,IqsMid,IqsMid2,PGoals,
                           [check_inequal(IqsMid2,IqsMid3),
                            deref(Tag,bot,_,SVs),
                            SVs =.. [Sort|Vs],
     match_list_rest(Sort,Vs,Right,NewRight,DtrsRest,DtrsRest2,Chart,IqsMid3,
                     IqsOut)|PGoalsMid],CBSafe,VarsIn,VarsMid,FSPal,FSsIn,
                     FSsMid),                                % a_ causes error
  compile_dtrs_rest(Rest,Left,NewRight,IqsOut,PGoalsMid,PGoalsRest,Mother,
                    PrevDtrs,DtrsRest2,RuleName,Chart,CBSafe,VarsMid,VarsOut,
                    FSPal,FSsMid,FSsOut).
compile_dtrs_rest((goal> Goal,Rest),Left,Right,IqsMid,PGoals,PGoalsRest,
                  Mother,PrevDtrs,DtrsRest,RuleName,Chart,CBSafe,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_body(Goal,IqsMid,IqsMid2,PGoals,PGoalsMid,CBSafe,VarsIn,VarsMid,
                  FSPal,FSsIn,FSsMid),
  compile_dtrs_rest(Rest,Left,Right,IqsMid2,PGoalsMid,PGoalsRest,Mother,
                    PrevDtrs,DtrsRest,RuleName,Chart,CBSafe,VarsMid,VarsOut,
                    FSPal,FSsMid,FSsOut).
% 6/1/97 Octav -- added a clause for 'sem_goal>' label
% (sem_goal> daughters behave just like goal> daughters during parsing)
compile_dtrs_rest((sem_goal> Goal,Rest),Left,Right,IqsMid,PGoals,PGoalsRest,
                  Mother,PrevDtrs,DtrsRest,RuleName,Chart,CBSafe,VarsIn,VarsOut,
                  FSPal,FSsIn,FSsOut):-
  !, compile_body(Goal,IqsMid,IqsMid2,PGoals,PGoalsMid,CBSafe,VarsIn,VarsMid,FSPal,
                  FSsIn,FSsMid),
  compile_dtrs_rest(Rest,Left,Right,IqsMid2,PGoalsMid,PGoalsRest,Mother,
                    PrevDtrs,DtrsRest,RuleName,Chart,CBSafe,VarsMid,VarsOut,FSPal,
                    FSsMid,FSsOut).
compile_dtrs_rest((cat> Dtr),Left,Right,IqsMid,
              [get_edge(Right,Chart,N,NewRight,Tag,SVs,EdgeIqs,_,_)|PGoals],
              PGoalsRest,Mother,PrevDtrs,[N],RuleName,Chart,CBSafe,VarsIn,VarsOut,
              FSPal,FSsIn,FSsOut):-
  !,compile_desc(Dtr,Tag,SVs,IqsMid,IqsMid2,PGoals,
                 [append(IqsMid2,EdgeIqs,IqsMid3),
                  check_inequal(IqsMid3,IqsMid4)|PGoalsMid],CBSafe,VarsIn,
                 VarsMid,FSPal,FSsIn,FSsMid),
  compile_desc(Mother,Tag2,bot,IqsMid4,IqsOut,PGoalsMid,
               [add_edge_deref(Left,NewRight,Tag2,bot,IqsOut,
                               PrevDtrs,RuleName,Chart)|PGoalsRest],CBSafe,VarsMid,
               VarsOut,FSPal,FSsMid,FSsOut).
% 5/1/96 - Octav -- added a clause for 'sem_head>' label
compile_dtrs_rest((sem_head> Dtr),Left,Right,IqsMid,
              [get_edge(Right,Chart,N,NewRight,Tag,SVs,EdgeIqs,_,_)|PGoals],
              PGoalsRest,Mother,PrevDtrs,[N],RuleName,Chart,CBSafe,VarsIn,VarsOut,
              FSPal,FSsIn,FSsOut):-
  !,compile_desc(Dtr,Tag,SVs,IqsMid,IqsMid2,PGoals,
                 [append(IqsMid2,EdgeIqs,IqsMid3),
                  check_inequal(IqsMid3,IqsMid4)|PGoalsMid],CBSafe,VarsIn,
                 VarsMid,FSPal,FSsIn,FSsMid),
  compile_desc(Mother,Tag2,bot,IqsMid4,IqsOut,PGoalsMid,
               [add_edge_deref(Left,NewRight,Tag2,bot,IqsOut,
                               PrevDtrs,RuleName,Chart)|PGoalsRest],CBSafe,VarsMid,
               VarsOut,FSPal,FSsMid,FSsOut).
% don't check inequations after mother since add_edge_deref does that
compile_dtrs_rest((cats> Dtrs),Left,Right,IqsMid,PGoals,PGoalsRest,
                  Mother,PrevDtrs,DtrsRest,RuleName,Chart,CBSafe,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_desc(Dtrs,Tag,bot,IqsMid,IqsMid2,PGoals,
                          [check_inequal(IqsMid2,IqsMid3),
                           deref(Tag,bot,_,SVs),
                           SVs =.. [Sort|Vs],
          match_list_rest(Sort,Vs,Right,NewRight,DtrsRest,[],Chart,IqsMid3,IqsMid4)|
                           PGoalsMid],CBSafe,VarsIn,VarsMid,FSPal,FSsIn,FSsMid), 
                                                                 % a_ causes error
  compile_desc(Mother,Tag2,bot,IqsMid4,IqsOut,PGoalsMid,
               [add_edge_deref(Left,NewRight,Tag2,bot,IqsOut,
                               PrevDtrs,RuleName,Chart)|PGoalsRest],CBSafe,VarsMid,
               VarsOut,FSPal,FSsMid,FSsOut).
% don't check inequations after mother since add_edge_deref does that
compile_dtrs_rest((goal> Goal),Left,Right,IqsMid,PGoals,PGoalsRest,Mother,
                  PrevDtrs,[],RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,
                  FSsOut):-
  !, compile_body(Goal,IqsMid,IqsMid2,PGoals,PGoalsMid,CBSafe,VarsIn,VarsMid,FSPal,
                  FSsIn,FSsMid),
  compile_desc(Mother,Tag2,bot,IqsMid2,IqsOut,PGoalsMid,
               [add_edge_deref(Left,Right,Tag2,bot,IqsOut,
                               PrevDtrs,RuleName,Chart)|PGoalsRest],CBSafe,VarsMid,
               VarsOut,FSPal,FSsMid,FSsOut).
% 6/1/97 Octav -- added a clause for 'sem_goal>' label
% (sem_goal> daughters behave just like goal> daughters during parsing)
% don't check inequations after mother since add_edge_deref does that
compile_dtrs_rest((sem_goal> Goal),Left,Right,IqsMid,PGoals,PGoalsRest,Mother,
                  PrevDtrs,[],RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,
                  FSsOut):-
  !, compile_body(Goal,IqsMid,IqsMid2,PGoals,PGoalsMid,CBSafe,VarsIn,VarsMid,FSPal,
                  FSsIn,FSsMid),
  compile_desc(Mother,Tag2,bot,IqsMid2,IqsOut,PGoalsMid,
               [add_edge_deref(Left,Right,Tag2,bot,IqsOut,
                               PrevDtrs,RuleName,Chart)|PGoalsRest],CBSafe,VarsMid,
               VarsOut,FSPal,FSsMid,FSsOut).
% don't check inequations after mother since add_edge_deref does that
compile_dtrs_rest(Foo,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_):-
       [invalid,line,Foo,in,rule] if_error
            true,
  !, fail.

% ------------------------------------------------------------------------------
% compile_desc(Desc:<desc>, FS:<fs>, IqsIn:<ineq>s, IqsOut:<ineq>s, 
%              Goals:<goal>s, GoalsRest:<goal>s, CBSafe:<bool>, VarsIn:<avl>,
%              VarsOut:<avl>, FSPal:<var>, FSsIn:<fs>s, FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% Goals are the Prolog goals required to add the description Desc
% to the feature structure FS.  IqsIn and IqsOut are uninstantiated at
% compile time.  VarsIn and VarsOut are description-level variables that
% have been seen or may have been seen already.  If a variable has definitely
% not been seen yet and CBSafe is true, then it is safe to bind that variable
% at compile-time.
% ------------------------------------------------------------------------------
compile_desc(X,FS2,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,_,FSs,FSs) :-
  var(X),
  !,
  ( get_assoc(X,VarsIn,Seen,VarsOut,seen)         % have we seen it before?
    -> ( Seen == seen -> Goals = [ud(X,FS2,IqsIn,IqsOut)|GoalsRest] % yes
       ; % Seen == tricky,                        % maybe - check at run-time
         Goals = [(var(X)
                  -> X=FS2, IqsOut = IqsIn
                   ; ud(X,FS2,IqsIn,IqsOut))|GoalsRest]
       )                                            % otherwise, no -
  ; ( CBSafe == true -> X = FS2,  Goals = GoalsRest % bind var at compile-time
    ; % CBSafe == false,                            %  if safe
      Goals = [X = FS2|GoalsRest]                   % otherwise at run-time
    ),
    IqsOut = IqsIn,
    put_assoc(X,VarsIn,seen,VarsOut)  % mark as seen
  ).
compile_desc(Tag1-SVs1,FS2,IqsIn,IqsOut,Goals,GoalsRest,_CBSafe,Vars,Vars,FSPal,
             FSsIn,FSsOut):-
  !,
  deref(Tag1,SVs1,DTag1,DSVs1),
%  (var(DSVs1) -> write(user_error,'variable SV'),
%                 Goals = [ud(FS2,DTag1,DSVs1,IqsIn,IqsOut)|GoalsRest],
%                 FSsOut = FSsIn
  find_fs(FSsIn,DTag1,DSVs1,Goals,[ud(FSVar,FS2,IqsIn,IqsOut)|GoalsRest],
            FSVar,FSPal,FSsOut).
%  ).
compile_desc([],FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut):-
  !, compile_desc(e_list,FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut).
compile_desc([H|T],FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut):-
  !, compile_desc((hd:H,tl:T),FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut).
compile_desc(Path1 == Path2,FS,IqsIn,IqsOut,Goals,GoalsRest,_,Vars,Vars,_,FSs,FSs):-
  !, compile_pathval(Path1,FS,FSatPath1,IqsIn,IqsMid,Goals,GoalsMid),
  compile_pathval(Path2,FS,FSatPath2,IqsMid,IqsMid2,
                  GoalsMid,[ud(FSatPath1,FSatPath2,IqsMid2,IqsOut)|GoalsRest]).
compile_desc(=\= Desc,FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_desc(Desc,Tag2,bot,IqsIn,IqsMid,Goals,
      [FS = Tag-SVs,
       check_inequal_conjunct(ineq(Tag,SVs,Tag2,bot,done),IqOut,Result),
       ((Result = succeed) -> IqsOut = IqsMid
       ; (IqOut \== done, IqsOut = [IqOut|IqsMid]))
      |GoalsRest],CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut).
compile_desc(Feat:Desc,FS,IqsIn,IqsOut,[deref(FS,Tag,SVs),Goal|GoalsMid],
             GoalsRest,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut):-
  !,     [description,uses,unintroduced,feature,Feat] if_error
              (\+ approp(Feat,_,_)),
  cat_atoms('featval_',Feat,Rel),
  Goal =.. [Rel,SVs,Tag,FSatFeat,IqsIn,IqsMid],
  compile_desc(Desc,FSatFeat,IqsMid,IqsOut,GoalsMid,GoalsRest,CBSafe,VarsIn,
               VarsOut,FSPal,FSsIn,FSsOut).
compile_desc((Desc1,Desc2),FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_desc(Desc1,FS,IqsIn,IqsMid,Goals,GoalsMid,CBSafe,VarsIn,VarsMid,FSPal,
                  FSsIn,FSsMid),
  compile_desc(Desc2,FS,IqsMid,IqsOut,GoalsMid,GoalsRest,CBSafe,VarsMid,
               VarsOut,FSPal,FSsMid,FSsOut).
compile_desc((Desc1;Desc2),FS,IqsIn,IqsOut,
             [(Goals1Seq;Goals2Seq)|GoalsRest],GoalsRest,_,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut):-
  !, compile_desc(Desc1,FS,IqsIn,IqsOut,Goals1,[],false,VarsIn,VarsDisj1,FSPal,
                  FSsIn,FSsDisj1),
  compile_desc(Desc2,FS,IqsIn,IqsOut,Goals2,[],false,VarsIn,VarsDisj2,FSPal,FSsIn,
               FSsDisj2),
  goal_list_to_seq(Goals1,Goals1Seq), 
  goal_list_to_seq(Goals2,Goals2Seq),
  vars_merge(VarsDisj1,VarsDisj2,VarsOut),
  fss_merge(FSsDisj1,FSsDisj2,FSsOut).
compile_desc(@ MacroName,FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !,      [undefined,macro,MacroName,used,in,description] if_error
               (\+ (MacroName macro Desc)),
  (MacroName macro Desc),
  compile_desc(Desc,FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
               FSsIn,FSsOut).
compile_desc(a_ X,FS,IqsIn,IqsOut,[deref(FS,Tag,SVs),Goal|GoalsRest],
             GoalsRest,_,Vars,Vars,_,FSs,FSs) :-
  !, Goal =.. ['add_to_type_a_',SVs,Tag,IqsIn,IqsOut,X].
compile_desc(FunDesc,FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut):-
  fun(FunDesc),
  !,compile_fun(FunDesc,FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
                FSsIn,FSsOut).
compile_desc(Type,FS,IqsIn,IqsOut,[deref(FS,Tag,SVs),Goal|GoalsRest],
             GoalsRest,_,Vars,Vars,_,FSs,FSs):-
       [undefined,type,Type,used,in,description] if_error
            (\+ type(Type)),
  type(Type),
  cat_atoms('add_to_type_',Type,AddtotypeType),
  Goal =.. [AddtotypeType,SVs,Tag,IqsIn,IqsOut].

% ------------------------------------------------------------------------------
% compile_desc(Desc:<desc>, Tag:<ref>, SVs:<svs>, IqsIn:<ineq>s, 
%              IqsOut:<ineq>s, Goals:<goal>s, GoalsRest:<goal>s, CBSafe:<bool>,
%              VarsIn:<avl>, VarsOut:<avl>, FSPal:<var>, FSsIn:<fs>s,
%              FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% 10-place version of compile_desc/9
% ------------------------------------------------------------------------------
compile_desc(X,Tag2,SVs2,IqsIn,IqsOut,Goals,GoalsRest,_CBSafe,VarsIn,VarsOut,_,FSs,
             FSs) :-
  var(X),
  !,
  ( get_assoc(X,VarsIn,Seen,VarsOut,seen)         % have we seen it before?
    -> ( Seen == seen -> Goals = [ud(X,Tag2,SVs2,IqsIn,IqsOut)|GoalsRest] % yes
       ; % Seen == tricky,                        % maybe - check at run-time
         Goals = [(var(X)
                  -> X=Tag2-SVs2, IqsOut = IqsIn
                   ; ud(X,Tag2,SVs2,IqsIn,IqsOut))|GoalsRest]
       )                                            % otherwise, no -
  ; Goals = [X = Tag2-SVs2|GoalsRest],  % bind at run-time even if safe at compile-
                                        %  time to reduce structure copying in 
    IqsOut = IqsIn,                     %  compiled code
    put_assoc(X,VarsIn,seen,VarsOut)  % mark as seen
  ).
compile_desc(Tag1-SVs1,Tag2,SVs2,IqsIn,IqsOut,Goals,GoalsRest,_,Vars,Vars,FSPal,
             FSsIn,FSsOut):-
  !,
  deref(Tag1,SVs1,DTag1,DSVs1),
%  (var(DSVs1) -> write(user_error,'variable SV'),
%                 Goals = [ud(DTag1,DSVs1,Tag2,SVs2,IqsIn,IqsOut)|GoalsRest],
%                 FSsOut = FSsIn
  find_fs(FSsIn,DTag1,DSVs1,Goals,[ud(FSVar,Tag2,SVs2,IqsIn,IqsOut)|GoalsRest],
          FSVar,FSPal,FSsOut).
%  ).
compile_desc([],Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut):-
  !, compile_desc(e_list,Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut).
compile_desc([H|T],Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_desc((hd:H,tl:T),Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,
                  VarsIn,VarsOut,FSPal,FSsIn,FSsOut).
compile_desc(Path1 == Path2,Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,_,Vars,Vars,_,FSs,
             FSs):-
  !, compile_pathval(Path1,Tag,SVs,FSatPath1,IqsIn,IqsMid,Goals,GoalsMid),
  compile_pathval(Path2,Tag,SVs,FSatPath2,IqsMid,IqsMid2,
                  GoalsMid,[ud(FSatPath1,FSatPath2,IqsMid2,IqsOut)|GoalsRest]).
compile_desc(=\= Desc,Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_desc(Desc,Tag2,bot,IqsIn,IqsMid,Goals,
      [check_inequal_conjunct(ineq(Tag,SVs,Tag2,bot,done),IqOut,Result),
       ((Result = succeed) -> IqsOut = IqsMid
       ; (IqOut \== done, IqsOut = [IqOut|IqsMid]))
      |GoalsRest],CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut).
compile_desc(Feat:Desc,Tag,SVs,IqsIn,IqsOut,
             [deref(Tag,SVs,TagOut,SVsOut),Goal|GoalsMid],
             GoalsRest,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut):-
  !,     [description,uses,unintroduced,feature,Feat] if_error
              (\+ approp(Feat,_,_)),
  cat_atoms('featval_',Feat,Rel),
  Goal =.. [Rel,SVsOut,TagOut,FSatFeat,IqsIn,IqsMid],
  compile_desc(Desc,FSatFeat,IqsMid,IqsOut,GoalsMid,GoalsRest,CBSafe,VarsIn,
               VarsOut,FSPal,FSsIn,FSsOut).
compile_desc((Desc1,Desc2),Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !, compile_desc(Desc1,Tag,SVs,IqsIn,IqsMid,Goals,GoalsMid,CBSafe,VarsIn,
                  VarsMid,FSPal,FSsIn,FSsMid),
  compile_desc(Desc2,Tag,SVs,IqsMid,IqsOut,GoalsMid,GoalsRest,CBSafe,VarsMid,
               VarsOut,FSPal,FSsMid,FSsOut).
compile_desc((Desc1;Desc2),Tag,SVs,IqsIn,IqsOut,
             [(Goals1Seq;Goals2Seq)|GoalsRest],GoalsRest,_,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut):-
  !, compile_desc(Desc1,Tag,SVs,IqsIn,IqsOut,Goals1,[],false,VarsIn,VarsDisj1,FSPal,
                  FSsIn,FSsDisj1),
  compile_desc(Desc2,Tag,SVs,IqsIn,IqsOut,Goals2,[],false,VarsIn,VarsDisj2,FSPal,
               FSsIn,FSsDisj2),
  goal_list_to_seq(Goals1,Goals1Seq), 
  goal_list_to_seq(Goals2,Goals2Seq),
  vars_merge(VarsDisj1,VarsDisj2,VarsOut),
  fss_merge(FSsDisj1,FSsDisj2,FSsOut).
compile_desc(@ MacroName,Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  !,      [undefined,macro,MacroName,used,in,description] if_error
               (\+ (MacroName macro Desc)),
  (MacroName macro Desc),
  compile_desc(Desc,Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
               VarsOut,FSPal,FSsIn,FSsOut).
compile_desc(a_ X,Tag,SVs,IqsIn,IqsOut,
             [deref(Tag,SVs,TagOut,SVsOut),Goal|GoalsRest],GoalsRest,_,Vars,
             Vars,_,FSs,FSs) :-
  !, Goal =.. ['add_to_type_a_',SVsOut,TagOut,IqsIn,IqsOut,X].
compile_desc(FunDesc,Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut):-
  fun(FunDesc),
  !,compile_fun(FunDesc,Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
                VarsOut,FSPal,FSsIn,FSsOut).
compile_desc(Type,Tag,SVs,IqsIn,IqsOut,
             [deref(Tag,SVs,TagOut,SVsOut),Goal|GoalsRest],GoalsRest,_,Vars,
             Vars,_,FSs,FSs):-
       [undefined,type,Type,used,in,description] if_error
            (\+ type(Type)),
  type(Type),
  cat_atoms('add_to_type_',Type,AddtotypeType),
  Goal =.. [AddtotypeType,SVsOut,TagOut,IqsIn,IqsOut].

% ------------------------------------------------------------------------------
% vars_merge(+Vars1:<avl>,+Vars2:<avl>,-VarsMerge:<avl>)
% ------------------------------------------------------------------------------
% Given two AVL's of variables marked tricky or seen, produce a new AVL whose
% domain is the union of the two inputs, and whose values are defined as
% follows:
%
% Vs1/Vs2  |  -       tricky    seen
% ------------------------------------
% -        |  -       tricky    tricky
% tricky   |  tricky  tricky    tricky
% seen     |  tricky  tricky    seen
%
% Tricky variables are those that we cannot guarantee we will have seen and
% cannot guarantee that we will have not seen by the execution of the next
% item added to the Goal list.
% ------------------------------------------------------------------------------
vars_merge(Vars1,Vars2,VarsMerge) :-
  assoc_to_list(Vars1,VarsList1),
  assoc_to_list(Vars2,VarsList2),
  vars_merge_list(VarsList1,VarsList2,VarsListMerge),
  ord_list_to_assoc(VarsListMerge,VarsMerge).

vars_merge_list([],VarsList,VarsList).
vars_merge_list([Var1-Seen1|VarsList1],VarsList2,VarsListMerge) :-
  vars_merge_nelist(VarsList2,Var1,Seen1,VarsList1,VarsListMerge).

vars_merge_nelist([],Var1,Seen1,VarsList1,[Var1-Seen1|VarsList1]).
vars_merge_nelist([Var2-Seen2|VarsList2],Var1,Seen1,VarsList1,VarsListMerge) :-
  compare(Comp,Var1,Var2),
  vars_merge_nelist_act(Comp,Var1,Seen1,Var2,Seen2,VarsList1,VarsList2,
                        VarsListMerge).

vars_merge_nelist_act(=,VarMerge,Seen1,_VarMerge,Seen2,VarsList1,VarsList2,
                      [VarMerge-SeenMerge|VarsListMerge]) :-
  ( Seen1==seen,Seen2==seen -> SeenMerge = seen
  ; SeenMerge = tricky
  ),
  vars_merge_list(VarsList1,VarsList2,VarsListMerge).

vars_merge_nelist_act(<,Var1,_,Var2,Seen2,VarsList1,VarsList2,
                      [Var1-tricky|VarsListMerge]) :-
  vars_merge_nelist(VarsList1,Var2,Seen2,VarsList2,VarsListMerge).
vars_merge_nelist_act(>,Var1,Seen1,Var2,_,VarsList1,VarsList2,
                      [Var2-tricky|VarsListMerge]) :-
  vars_merge_nelist(VarsList2,Var1,Seen1,VarsList1,VarsListMerge).

% ------------------------------------------------------------------------------
% hook_vars_merge(+HookVarsList:<var>s,+VarsIn:<avl>,-VarsMerge:<avl>)
% ------------------------------------------------------------------------------
% Adds hook variables to AVL of seen/tricky variables.  Since we can only
%  assume that the user leaves a var. unbound or bound to a legitimate FS,
%  it works as follows:
%
%  Hookvar was: -      ---> tricky
%               tricky ---> tricky
%               seen   ---> seen
% ------------------------------------------------------------------------------
hook_vars_merge([],Vars,Vars).
hook_vars_merge([HVar|HookVarsList],VarsIn,VarsMerge) :-
   get_assoc(HVar,VarsIn,_Seen)   % if it is there at all, leave it unchanged
   -> hook_vars_merge(HookVarsList,VarsIn,VarsMerge)
    ; put_assoc(HVar,VarsIn,tricky,VarsMid),   % otherwise, add it as tricky
      hook_vars_merge(HookVarsList,VarsMid,VarsMerge).

% ------------------------------------------------------------------------------
% find_fs(+FSsIn:<fs>s,+Tag:<tag>,+SVs:<svs>,-Goals:<goal>s,-GoalsRest:<goal>s,
%         -FSVar:<var>,+FSPal:<var>,-FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% Determine whether Tag-SVs has been seen before, or may have been seen before
% (tricky) in the current execution path.  If it was seen, use the same
% variable for it as before.  If it was not seen, add it to the register of
% FSs, FSsOut, and add an arg/3 call to the execution path that binds its
% variable to an argument of the FS palette (which argument will be determined
% by build_fs_palette/5).
% ------------------------------------------------------------------------------
find_fs(FSsIn,Tag,_,Goals,Goals,FSVar,_,FSsOut) :-
  find_fs_seen(FSsIn,Tag,FSVar,FSsOut,FSsOut),
  !.
find_fs(FSsIn,Tag,_,[(var(FSVar) -> arg(Arg,FSPal,FSVar) ; true)|GoalsRest],
        GoalsRest,FSVar,FSPal,FSsOut) :-
  find_fs_tricky(FSsIn,Tag,FSVar,Arg,FSsOut,FSsOut),
  !.
find_fs(FSsIn,Tag,SVs,[arg(Arg,FSPal,FSVar)|GoalsRest],GoalsRest,FSVar,FSPal,
        [seen(Tag,SVs,FSVar,Arg)|FSsIn]).

find_fs_seen(FSsIn,Tag,FSVar,FSsOut,FSsOutRest) :-
  FSsIn = [FSInFirst|FSsInRest],
  ( FSInFirst = seen(SeenTag,_,STVar,_)
  -> ( SeenTag == Tag
     -> FSVar = STVar,
        FSsOutRest = FSsIn
      ; FSsOutRest = [FSInFirst|FSsOutRest2],
        find_fs_seen(FSsInRest,Tag,FSVar,FSsOut,FSsOutRest2)
     )
   ; FSsOutRest = [FSInFirst|FSsOutRest2],
     find_fs_seen(FSsInRest,Tag,FSVar,FSsOut,FSsOutRest2)
  ).

find_fs_tricky(FSsIn,Tag,FSVar,Arg,FSsOut,FSsOutRest) :-
  FSsIn = [FSInFirst|FSsInRest],
  ( FSInFirst = tricky(TrickyTag,TrickySVs,TTVar,Arg)
  -> ( TrickyTag == Tag
     -> FSVar = TTVar,
        FSsOutRest = [seen(TrickyTag,TrickySVs,TTVar,Arg)|FSsInRest]
      ; FSsOutRest = [FSInFirst|FSsOutRest2],
        find_fs_tricky(FSsInRest,Tag,FSVar,Arg,FSsOut,FSsOutRest2)
     )
   ; FSsOutRest = [FSInFirst|FSsOutRest2],
     find_fs_tricky(FSsInRest,Tag,FSVar,Arg,FSsOut,FSsOutRest2)
  ).

% ------------------------------------------------------------------------------
% build_fs_palette(+FSs:<fs>s,+FSPal:<var>,-Goals:<goal>s,+GoalsRest:<goal>s,
%                  +Iqs:<ineq>s)
% ------------------------------------------------------------------------------
% The FS-palette is a collection of instantiated feature structures that occur
%  in compiled code as a result of EFD-closure in the parser compiler, or
%  lexical rule closure in the generator compiler.  These are asserted into
%  the internal database and reloaded at run-time at the neck of every FS-
%  bearing rule in order to improve compile-time efficiency, and reduce copying
%  of structure in the compiled code.
% Building the FS-palette involves determining which argument position each
%  FS occurs in (this position is linked to the arg/3 call in the code that
%  binds a variable to its FS), and adding extra tags to the palette and 
%  arg/3 calls at the neck to ensure that structure-sharing with tags in
%  inequations is not lost.
% ------------------------------------------------------------------------------
build_fs_palette([],_,Goals,Goals,_).
build_fs_palette([SeenorTricky|FSs],FSPal,[instance(Ref,Inst),
                                           arg(1,Inst,FSPal)|GoalsMid],
                 GoalsRest,Iqs) :-
  build_fs_palette_args(FSs,SeenorTricky,1,ArgNum,PalArgs,PalArgsRest),
  build_fs_palette_iqs(Iqs,SeenorTricky,FSs,ArgNum,FSPal,PalArgsRest,GoalsMid,
                       GoalsRest,[]),
  AssertedFSPal =.. [fspal|PalArgs],
  assert(AssertedFSPal,Ref),
  assert(fspal_ref(Ref)).

build_fs_palette_args([],SeenorTricky,ArgIn,ArgOut,[Tag-SVs|Rest],Rest) :-
  arg(1,SeenorTricky,Tag),
  arg(2,SeenorTricky,SVs),
  arg(4,SeenorTricky,ArgIn),
  ArgOut is ArgIn + 1.
build_fs_palette_args([SeenorTricky2|FSs],SeenorTricky,ArgIn,ArgOut,
                      [Tag-SVs|PalArgs],Rest) :-
  arg(1,SeenorTricky,Tag),
  arg(2,SeenorTricky,SVs),
  arg(4,SeenorTricky,ArgIn),
  NewArg is ArgIn + 1,
  build_fs_palette_args(FSs,SeenorTricky2,NewArg,ArgOut,PalArgs,Rest).

build_fs_palette_iqs([],_,_,_,_,[],Goals,Goals,_).
build_fs_palette_iqs([Ineq|Iqs],SeenorTricky,FSs,ArgIn,FSPal,PalArgs,Goals,
                     GoalsRest,TagsIn) :-
  build_fs_palette_ineq(Ineq,SeenorTricky,FSs,ArgIn,ArgOut,FSPal,PalArgs,
                        PalArgsRest,Goals,GoalsMid,TagsIn,TagsOut),
  build_fs_palette_iqs(Iqs,SeenorTricky,FSs,ArgOut,FSPal,PalArgsRest,GoalsMid,
                       GoalsRest,TagsOut).

build_fs_palette_ineq(done,_,_,Arg,Arg,_,PalArgs,PalArgs,Goals,Goals,Tags,
                      Tags).
build_fs_palette_ineq(ineq(Tag1,_,Tag2,_,IneqRest),SeenorTricky,FSs,ArgIn,
                      ArgOut,FSPal,PalArgs,PalArgsRest,Goals,GoalsRest,TagsIn,
                      TagsOut) :-
  ( member_eq(Tag1,TagsIn)
  -> TagsMid = TagsIn, PalArgs = PalArgsMid, 
     Goals = GoalsMid, ArgNext = ArgIn
   ; fspal_member_eq(FSs,SeenorTricky,Tag1)
     -> TagsMid = [Tag1|TagsIn],
        PalArgs = [Tag1|PalArgsMid],
        Goals = [arg(ArgIn,FSPal,Tag1)|GoalsMid],
        ArgNext is ArgIn + 1
      ; TagsMid = TagsIn, PalArgs = PalArgsMid, 
        Goals = GoalsMid, ArgNext = ArgIn
  ),
  ( member_eq(Tag2,TagsMid)
  -> TagsMid2 = TagsMid, PalArgsMid = PalArgsMid2,
     GoalsMid = GoalsMid2, ArgNext2 = ArgNext
   ; fspal_member_eq(FSs,SeenorTricky,Tag2)
     -> TagsMid2 = [Tag2|TagsMid],
        PalArgsMid = [Tag2|PalArgsMid2],
        GoalsMid = [arg(ArgNext,FSPal,Tag2)|GoalsMid2],
        ArgNext2 is ArgNext + 1
      ; TagsMid2 = TagsMid, PalArgsMid = PalArgsMid2,
        GoalsMid = GoalsMid2, ArgNext2 = ArgNext
  ),
  build_fs_palette_ineq(IneqRest,SeenorTricky,FSs,ArgNext2,ArgOut,FSPal,
                        PalArgsMid2,PalArgsRest,GoalsMid2,GoalsRest,TagsMid2,
                        TagsOut).

fspal_member_eq([],SeenorTricky,Tag2) :-
   arg(1,SeenorTricky,Tag1),
   Tag1 == Tag2
 ; arg(2,SeenorTricky,SVs),
   term_variables(SVs,Tags),
   member_eq(Tag2,Tags).
fspal_member_eq([SeenorTricky2|FSs],SeenorTricky,Tag2) :-
   arg(1,SeenorTricky,Tag1),
   Tag1 == Tag2
 ; arg(2,SeenorTricky,SVs),
   term_variables(SVs,Tags),
   member_eq(Tag2,Tags)
 ; fspal_member_eq(FSs,SeenorTricky2,Tag2).

% ------------------------------------------------------------------------------
% fss_merge(+FSs1:<fs>s,+FSs2:<fs>s,-MergedFSs:<fs>s)
% ------------------------------------------------------------------------------
% Merge two lists of seen/tricky FSs (used to build FS-palette).
% ------------------------------------------------------------------------------
fss_merge(FSs1,FSs2,FSsMerge) :-
  key_fss(FSs1,KFSs1),
  key_fss(FSs2,KFSs2),
  keysort(KFSs1,SortedKFSs1),
  keysort(KFSs2,SortedKFSs2),
  kfss_merge(SortedKFSs1,SortedKFSs2,FSsMerge).

kfss_merge([],KFSs,FSsMerge) :-
  dekey_fss(KFSs,FSsMerge).
kfss_merge([Tag1-Entry1|KFSs1],KFSs2,FSsMerge) :-
  kfss_merge_nelist(KFSs2,Tag1,Entry1,KFSs1,FSsMerge).

kfss_merge_nelist([],_Tag1,Entry1,KFSs1,[Entry1|FSs1]) :-
  dekey_fss(KFSs1,FSs1).
kfss_merge_nelist([Tag2-Entry2|KFSs2],Tag1,Entry1,KFSs1,FSsMerge) :-
  compare(Comp,Tag1,Tag2),
  kfss_merge_nelist_act(Comp,Tag1,Entry1,Tag2,Entry2,KFSs1,KFSs2,FSsMerge).

kfss_merge_nelist_act(=,Tag,Entry1,_Tag,Entry2,KFSs1,KFSs2,[MergeEntry|FSsMerge]) :-
  arg(3,Entry1,Var),
  arg(3,Entry2,Var),  % unify FS variables in entries
  functor(Entry1,Kind1,_),
  functor(Entry2,Kind2,_),
  ( Kind1 == seen         % determine merged Kind according to table above
  -> ( Kind2 == seen 
     -> MergeKind = seen
      ; % Kind2 == tricky,
        MergeKind = tricky
     )
   ; % Kind1 = tricky,
     MergeKind = tricky
  ),
  functor(MergeEntry,MergeKind,4),
  arg(1,MergeEntry,Tag),
  arg(3,MergeEntry,Var),
  arg(2,Entry1,SVs),
  arg(2,MergeEntry,SVs),
  arg(4,Entry1,PalArg),
  arg(4,MergeEntry,PalArg),
  kfss_merge(KFSs1,KFSs2,FSsMerge).
kfss_merge_nelist_act(<,Tag1,Entry1,Tag2,Entry2,KFSs1,KFSs2,
                      [MergeEntry|FSsMerge]) :-
  functor(MergeEntry,tricky,4),
  arg(1,MergeEntry,Tag1),
  arg(2,Entry1,SVs1),
  arg(2,MergeEntry,SVs1),
  arg(3,Entry1,Var1),
  arg(3,MergeEntry,Var1),
  arg(4,Entry1,PalArg),
  arg(4,MergeEntry,PalArg),
  kfss_merge_nelist(KFSs1,Tag2,Entry2,KFSs2,FSsMerge).
kfss_merge_nelist_act(>,Tag1,Entry1,Tag2,Entry2,KFSs1,KFSs2,
                      [MergeEntry|FSsMerge]) :-
  functor(MergeEntry,tricky,4),
  arg(1,MergeEntry,Tag2),
  arg(2,Entry2,SVs2),
  arg(2,MergeEntry,SVs2),
  arg(3,Entry2,Var2),
  arg(3,MergeEntry,Var2),
  arg(4,Entry2,PalArg),
  arg(4,MergeEntry,PalArg),
  kfss_merge_nelist(KFSs2,Tag1,Entry1,KFSs1,FSsMerge).

% ------------------------------------------------------------------------------
% key_fss(+FSs:<fs>s,-KeyedFSs:<fs>s)
% ------------------------------------------------------------------------------
% Key a list of FSs by their tags.
% ------------------------------------------------------------------------------
key_fss([],[]).
key_fss([FSEntry|FSs],[Tag-FSEntry|KFSs]) :-
  arg(1,FSEntry,Tag),
  key_fss(FSs,KFSs).

dekey_fss([],[]).
dekey_fss([_-FSEntry|KFSs],[FSEntry|FSsMerge]) :-
  dekey_fss(KFSs,FSsMerge).

% ------------------------------------------------------------------------------
% compile_pathval(Path:<path>,FSIn:<fs>,FSOut:<fs>,
%                 IqsIn:<ineq>s,IqsOut:<ineq>s,
%                 Goals:<goal>s, GoalsRest:<goal>s)
% ------------------------------------------------------------------------------
% Goals-GoalsRest is difference list of goals needed to determine that
% FSOut is the (undereferenced) value of dereferenced FSIn at Path;
% might instantiate Tag or substructures in SVs in finding path value
% ------------------------------------------------------------------------------
compile_pathval([],FS,FS,Iqs,Iqs,Goals,Goals) :- !.
compile_pathval([Feat|Feats],FS,FSAtPath,IqsIn,IqsOut,
                [deref(FS,Tag,SVs),Goal|GoalsMid],GoalsRest):-
  !,   [undefined,feature,Feat,used,in,path,[Feat|Feats]] if_error
            (\+ approp(Feat,_,_)),
  cat_atoms('featval_',Feat,Rel),
  Goal =.. [Rel,SVs,Tag,FSAtFeat,IqsIn,IqsMid],
  compile_pathval(Feats,FSAtFeat,FSAtPath,IqsMid,IqsOut,GoalsMid,GoalsRest).
compile_pathval(P,_,_,_,_,_,_) :-
  error_msg((nl,write('pathval: illegal path specified - '),
                write(P))).

% ------------------------------------------------------------------------------
% compile_pathval(Path:<path>,RefIn:<ref>,SVsIn:<svs>,FSOut:<fs>,
%                 IqsIn:<ineq>s,IqsOut:<ineq>s,
%                 Goals:<goal>s, GoalsRest:<goal>s)
% ------------------------------------------------------------------------------
% 8-place version of compile_pathval/7
% ------------------------------------------------------------------------------
compile_pathval([],Tag,SVs,Tag-SVs,Iqs,Iqs,Goals,Goals) :- !.
compile_pathval([Feat|Feats],Tag,SVs,FSAtPath,IqsIn,IqsOut,
                [deref(Tag,SVs,TagOut,SVsOut),Goal|GoalsMid],GoalsRest):-
  !,   [undefined,feature,Feat,used,in,path,[Feat|Feats]] if_error
            (\+ approp(Feat,_,_)),
  cat_atoms('featval_',Feat,Rel),
  Goal =.. [Rel,SVsOut,TagOut,FSAtFeat,IqsIn,IqsMid],
  compile_pathval(Feats,FSAtFeat,FSAtPath,IqsMid,IqsOut,GoalsMid,GoalsRest).
compile_pathval(P,_,_,_,_,_,_,_) :-
  error_msg((nl,write('pathval: illegal path specified - '),
                write(P))).

% ------------------------------------------------------------------------------
% compile_fun(Fun:<fun>,FS:<fs>,IqsIn:<ineq>s,IqsOut:<ineq>s,
%             Goals:<goal>s,GoalsRest:<goal>s,CBSafe:<bool>,VarsIn:<var>s,
%             VarsOut:<var>s,FSPal:<var>,FSsIn:<fs>s,FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% Goals-RoalsRest is difference list of goals needed to determine that FS
%  satisfies functional constraint Fun
% ------------------------------------------------------------------------------
compile_fun(FunDesc,FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
            FSsIn,FSsOut) :-
  FunDesc =.. [Rel|ArgDescs],
  compile_descs_fresh(ArgDescs,Args,IqsIn,IqsMid,Goals,
                      [deref(FS,Tag,SVs),
                       fsolve(Fun,Tag,SVs,IqsMid,IqsOut)|GoalsRest],
                      CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut),
  Fun =.. [Rel|Args].

% ------------------------------------------------------------------------------
% compile_fun(Fun:<fun>,Ref:<ref>,SVs:<svs>,IqsIn:<ineq>s,IqsOut:<ineq>s,
%             Goals:<goal>s,GoalsRest:<goal>s,CBSafe:<bool>,VarsIn:<var>s,
%             VarsOut:<var>s,FSPal:<var>,FSsIn:<fs>s,FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% 7-place version of compile_fun/6
% ------------------------------------------------------------------------------
compile_fun(FunDesc,Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
            VarsOut,FSPal,FSsIn,FSsOut) :-
  FunDesc =.. [Rel|ArgDescs],
  compile_descs_fresh(ArgDescs,Args,IqsIn,IqsMid,Goals,
                      [fsolve(Fun,Tag,SVs,IqsMid,IqsOut)|GoalsRest],
                      CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut),
  Fun =.. [Rel|Args].

% ==============================================================================
% Compiler
% ==============================================================================

% ------------------------------------------------------------------------------
% compile_gram(File:<file>)
% ------------------------------------------------------------------------------
% compiles grammar from File;  all commands set up same way, with optional
% argument for file, which is recompiled, if necessary
% ------------------------------------------------------------------------------

:- dynamic ale_compiling/1.
:- dynamic alec/1.
:- dynamic lexicon_updating/0.
:- multifile user:term_expansion/2.
:- multifile alec_catch_hook/2.

alec_announce(Message) :-
  write(user_error,Message),nl(user_error),flush_output(user_error).

term_expansion(end_of_file,Code) :-
  prolog_load_context(file,File),
  (ale_compiling(File) -> % current_stream(File,_,S),
                          % seek(S,-1,current,_), % reset end_of_file
                          alec_catch(Code)
                        ; (Code = end_of_file)).

term_expansion((WordStart ---> Desc),[(WordStart ---> Desc),
                                      (:- multifile (lex)/4),
                                      (:- dynamic (lex)/4)|Code]) :-
  lexicon_updating,
  secret_noadderrs,
  bagof(lex(Word,Tag,SVs,IqsOut),lex_act(Word,Tag,SVs,IqsOut,WordStart,Desc),
        Code),
  secret_adderrs.

%term_expansion((empty Desc),[(empty Desc),
%                             (:- multifile (empty_cat)/3),
%                             (:- dynamic (empty_cat)/3)|Code]) :-
%  lexicon_updating,
%  secret_noadderrs,
%  bagof(empty_cat(TagOut,SVsOut,IqsOut),
%        (add_to(Desc,Tag,bot,[],IqsIn),
%         fully_deref_prune(Tag,bot,TagOut,SVsOut,IqsIn,IqsOut)),
%        Code),
%  secret_adderrs.

touch(File) :-
  open(File,update,S),
  write(S,':- true.'),nl(S),
  close(S).

alec_catch(Code) :-
  retract(alec(Stage))
  -> alec_catch_hook(Stage,Code)
   ; (Code = [end_of_file]).

alec_catch_hook(subtype,[(:- discontiguous (sub_type)/2)|Code]) :-
  !,compile_sub_type(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(unifytype,[(:- discontiguous (unify_type)/3)|Code]) :-
  !,compile_unify_type(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(approp,[(:- discontiguous (approp)/3)|Code]) :-
  !,compile_approp(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(ext,Code) :-
  !,compile_ext(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(iso,Code) :-
  !,multi_hash(0,(iso_sub_seq)/3,Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(check,Code) :-
  !,multi_hash(0,(check_sub_seq)/5,Code,CodeMid),
  multi_hash(0,(check_pre_traverse)/6,CodeMid,CodeMid2),
  multi_hash(0,(check_post_traverse)/5,CodeMid2,
                [(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(fun,Code) :-
  !,compile_fun(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(fsolve,Code) :-
  !,multi_hash(0,(fsolve)/5,Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(cons,Code) :-
  !,compile_cons(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(mgsc,[(:- alec_catch(CodeRest))|CodeRest]) :-
  !,compile_mgsc_assert.
alec_catch_hook(addtype,[(:- discontiguous (add_to_type)/5)|Code]) :-
  !,compile_add_to_type(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(featval,[(:- discontiguous (featval)/6)|Code]) :-
  !,compile_featval(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(u,[(:- discontiguous (u)/6)|Code]) :-
  !,compile_u(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(subsume,[(:- discontiguous (subsume_type)/13)|Code]) :-
  !,compile_subsume(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(dcs,Code) :-
  !,compile_dcs(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(lexrules,Code) :-
  !,compile_lex_rules(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(lex,Code) :-
  !,compile_lex(Code,[(:- alec_catch(CodeRest))|CodeRest]).
% alec_catch_hook(empty,Code) :-
%   !,compile_empty(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(rules,Code) :-
  !,compile_rules(Code,[(:- alec_catch(CodeRest))|CodeRest]).
alec_catch_hook(generate,Code) :-
  !,compile_generate(Code,[end_of_file]).
alec_catch_hook(_,Code) :-
  retract(ale_compiling(_)),
  (Code = [end_of_file]).

compile_gram(File):-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish_preds,
  assert(alec(subtype)),assert(alec(unifytype)),assert(alec(approp)),
  assert(alec(ext)),assert(alec(iso)),assert(alec(check)),assert(alec(fun)),
  assert(alec(fsolve)),assert(alec(cons)),assert(alec(mgsc)),
  assert(alec(addtype)),assert(alec(featval)),
  assert(alec(u)),assert(alec(subsume)),assert(alec(dcs)),
  assert(alec(lexrules)),assert(alec(lex)), % assert(alec(empty)),
  assert(alec(rules)),assert(alec(generate)),
  swi_consult(File),
  retract(ale_compiling(_)).

abolish_preds :-
  abolish((empty)/1), abolish((rule)/2), abolish((lex_rule)/2), 
  abolish(('--->')/2), abolish((sub)/2), 
  abolish((if)/2), abolish((macro)/2), 
  abolish((ext)/1), abolish((cons)/2),
  abolish((intro)/2),
% 5/1/96 - Octav -- added abolish/2 calls for generation predicates
  abolish((semantics)/1),
  abolish(('+++>')/2).

compile_gram :-
  touch('.alec_sub'),
  absolute_file_name('.alec_sub',[file_type(txt),file_errors(fail),
                                        solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(subtype)),assert(alec(unifytype)),assert(alec(approp)),
  assert(alec(ext)),assert(alec(iso)),assert(alec(check)),assert(alec(fun)),
  assert(alec(fsolve)),assert(alec(cons)),assert(alec(mgsc)),
  assert(alec(addtype)),assert(alec(featval)),
  assert(alec(u)),assert(alec(subsume)),assert(alec(dcs)),
  assert(alec(lexrules)),assert(alec(lex)),  % assert(alec(empty)),
  assert(alec(rules)),assert(alec(generate)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_sig(File):-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish((sub)/2),abolish((ext)/1),
  abolish((intro)/2),
  assert(alec(subtype)),assert(alec(unifytype)),assert(alec(approp)),
  assert(alec(ext)),assert(alec(iso)),assert(alec(check)),
  swi_consult(File),
  retract(ale_compiling(_)).

compile_sig :-
  touch('.alec_sub'),
  absolute_file_name('.alec_sub',[file_type(txt),file_errors(fail),
                                        solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(subtype)),assert(alec(unifytype)),assert(alec(approp)),
  assert(alec(ext)),assert(alec(iso)),assert(alec(check)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_sub_type(File):-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish((sub)/2),abolish((intro)/2),
  assert(alec(subtype)),
  swi_consult(File),
  retract(ale_compiling(_)).

compile_sub_type :-
  touch('.alec_sub'),
  absolute_file_name('.alec_sub',[file_type(txt),file_errors(fail),
                                        solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(subtype)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).
  
compile_sub_type(Code,CodeRest) :-
  alec_announce('Compiling sub-types...'),
  abolish((sub_type)/2),
  retractall(_ sub_def _),
  ([no,types,defined] if_warning_else_fail
    (\+current_predicate(sub,_ sub _),
     \+current_predicate(intro,_ intro _),
     Code = [(:- alec_catch(CodeRest)|CodeRest)])
  ; (current_predicate(sub,_ sub _) ->
           [S,subsumes,bot] if_error
             (S sub Ss, 
              (member(bot,Ss)   % fails if Ss = _ intro _
              ; Ss = (Ts intro _),
                member(bot,Ts))),
           [subtype/feature,specification,given,for,'a_/1',atom] if_error
                ( (a_ _) sub _ ),
           ['a_/1',atom,declared,subsumed,by,type,Type] if_error
                ( immed_subtypes(Type,SubTypes),
                  member(a_ _,SubTypes) ),
           [Type,multiply,defined] if_error
                ( bagof(S,Subs^(S sub Subs),Types),
                  duplicated(Type,Types) ),
           [illegal,variable,occurence,in,Type,sub,SubTypes,intro,FRs] if_error
              (Type sub SubTypes intro FRs,
               (var(Type)
               ;member(SubType,SubTypes),
                var(SubType)
               ;member(F:R,FRs),
                (var(F)
                ;var(R)))), % R can be a variable if parametric types are added
           [illegal,variable,occurence,in,Type,sub,SubTypes] if_error
              (Type sub SubTypes,
               \+(SubTypes = (_ intro _)),
               (var(Type)
               ;member(SubType,SubTypes),
                var(SubType)))
           ; true),
    (current_predicate(intro,_ intro _) ->
           [illegal,variable,occurence,in,Type,intro,FRs] if_error
              (Type intro FRs,
               (var(Type)
               ;member(F:R,FRs),
                (var(F)
                ;var(R)))),  % R can be a variable if parametric types added
           [feature,specification,given,for,'a_/1',atom] if_error
                ( (a_ _) intro _ )
           ; true)),
  ensure_sub_intro,
  maximal_defaults,
  bottom_defaults,
           [unary,branch,from,Type,to,SubType] if_warning
                immed_subtypes(Type,[SubType]),
  multi_hash(1,(sub_type)/2,Code,CodeRest).
  
maximal_defaults :-
  _ sub Xs,
  (Xs = (SubTypes intro Intros) ->
     (member(SubType,SubTypes)
     ;member(_:SubType,Intros))
    ;member(SubType,Xs)),
  \+SubType = (a_ _),
  \+SubType subs _,
  SubType \== bot,
  assert(max_def(SubType)),
  assert(SubType sub_def []),
  fail.
maximal_defaults :-
  IType intro Intros,
  (\+IType = (a_ _),
   \+IType subs _,
   IType \== bot,
   SubType = IType
  ; member(_:SubType,Intros),
    \+SubType = (a_ _),
    \+SubType subs _,
    SubType \== bot),
  assert(max_def(SubType)),
  assert(SubType sub_def []),
  fail.
maximal_defaults :-
  current_predicate(ext,ext(_)),
  ext(Exts),
  member(EType,Exts),
  \+ EType = (a_ _),
  \+ EType subs _,
  EType \== bot,
  assert(max_def(EType)),
  assert(EType sub_def []),
  fail.
maximal_defaults :-
   max_def(_)
   ->( write_list([assuming,the,following,are,maximal,'type(s): ']),
       retract(max_def(Type)),
       write(Type),write(' '),
       fail
     ; ttynl)
   ; true.

bottom_defaults :-
  setof(Type,(type(Type),
              \+imm_sub_type(_,Type),
              Type \== bot,
              \+Type = (a_ _)),BDTypes),
  !,ttynl,
  write_list([assuming,the,'type(s):']),
  nl,write_list(BDTypes),
  nl,write_list([are,immediately,subsumed,by,bottom]),nl,
  (bot sub Xs ->
   (Xs = (BotTypes intro BotIntros) ->    % bottom declared with intro
     append(BDTypes,BotTypes,NewBotTypes),
     assert(bot sub_def NewBotTypes intro BotIntros)
   ;append(BDTypes,Xs,NewBotTypes),       % bottom declared w/o intro
    assert(bot sub_def NewBotTypes))
  ;assert(bot sub_def BDTypes)).        % bottom not declared
bottom_defaults :-    
   (bot subs _) -> true       % bot declared and no other types necessary
 ; assert(bot sub_def []).    % bot not declared and no other types necessary

ensure_sub_intro :-
 (\+current_predicate(sub,(_ sub _)) -> assertz((_ sub _ :- fail)) ; true),
 (\+current_predicate(intro,(_ intro _)) -> assertz((_ intro _ :- fail)) 
  ; true).

compile_unify_type :-
  touch('.alec_unify'),
  absolute_file_name('.alec_unify',[file_type(txt),file_errors(fail),
                                          solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(unifytype)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_unify_type(Code,CodeRest) :-
  alec_announce('Compiling type unification...'),
  abolish((unify_type)/3),
  multi_hash(1,(unify_type)/3,Code,CodeRest).

compile_approp(File) :-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish((sub)/2),abolish((intro)/2),
  assert(alec(approp)),
  swi_consult(File),
  retract(ale_compiling(_)).

compile_approp :-
  touch('.alec_approp'),
  absolute_file_name('.alec_approp',[file_type(txt),file_errors(fail),
                                           solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(approp)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_approp(Code,CodeRest) :-
  alec_announce('Compiling appropriateness...'),
  abolish((approp)/3),
  [bot,has,appropriate,features] if_error
        ((bot sub _ intro [_:_|_])
        ;(bot intro [_:_|_])),
  [no,features,introduced] if_warning
        (\+ (_ sub _ intro [_:_|_]),
         \+ (_ intro [_:_|_])),
  [multiple,specification,for,F,in,declaration,of,S] if_error
            ( S sub _ intro FRs,
              duplicated(F:_,FRs)
            ; S intro FRs2,
              duplicated(F:_,FRs2)),
  [multiple,feature,specifications,for,type,S] if_error
       (S sub _ intro _,
        S intro _
       ;bagof(IType,FRs^(IType intro FRs),ITypes),
        duplicated(S,ITypes)),            % multiple sub/2 taken care of above
  [atom,'a_',X,is,ground,in,declaration,of,S] if_warning
            ( ( S sub _ intro FRs
              ; S intro FRs),
              member((_:(a_ X)),FRs),
              ground(X)),
  multi_hash(1,(approp)/3,Code,[
  (:- retractall(subsume_ready),assert(subsume_ready)),
  (:- [appropriateness,cycle,following,path,Fs,from,type,S] if_error
       ( type(S), feat_cycle(S,Fs) )),
  (:- [upward,closure,fails,for,F,in,S1,and,S2] if_error
     ( approp(F,S1,T1), approp(F,S2,T2),
       sub_type(S1,S2),
       \+sub_type(T1,T2))),
  (:- [homomorphism,condition,fails,for,F,in,S1,and,S2] if_warning
       ( approp(F,S1,T1), approp(F,S2,T2),
         unify_type(S1,S2,S3),
         approp(F,S3,T3),
         unify_type(T1,T2,T1UnifyT2),
         \+sub_type(T3,T1UnifyT2)))|CodeRest]).
                 % must check with sub_type because of atoms


compile_extensional(File) :-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish((ext)/1),
  assert(alec(ext)),assert(alec(iso)),assert(alec(check)),
  swi_consult(File),
  compile_ext_sub_assert,
  retract(ale_compiling(_)).

compile_extensional :-
  touch('.alec_ext'),
  absolute_file_name('.alec_ext',[file_type(txt),file_errors(fail),
                                  solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(ext)),assert(alec(iso)),assert(alec(check)),
  swi_consult(AbsFileName),
  compile_ext_sub_assert,
  retract(ale_compiling(_)).

compile_ext(Code,CodeRest) :-
  alec_announce('Compiling extensionality declarations...'),
  abolish((extensional)/1),abolish((iso_sub_seq)/3),abolish((check_sub_seq)/5),
  abolish((check_pre_traverse)/6),abolish((check_post_traverse)/5),
  retractall(ext_sub_type(_)),retractall(ext_sub_structs(_,_,_,_,_,_)),
 ((\+current_predicate(ext,ext(_))
    ; ext([]))
  -> (Code = [extensional(a_ _)|CodeRest])
   ;(ext(Exts),
     compile_ext_act(Exts,Code,CodeRest))).

compile_ext_act([],[extensional(a_ _)|CodeRest],CodeRest).
compile_ext_act([a_ _|Exts],Code,CodeRest) :-
  !,compile_ext_act(Exts,Code,CodeRest).
compile_ext_act([E|Exts],[extensional(E)|CodeMid],CodeRest) :-
  [extensional,type,E,is,not,maximal] if_error
    (sub_type(E,S),
     S \== E),
  compile_ext_act(Exts,CodeMid,CodeRest).

compile_ext_sub_assert :-
  setof(T,E^(extensional(E),sub_type(T,E)),ExtSuperTypes),
  member(T,ExtSuperTypes),
  assert(ext_sub_type(T)),
  fail.
compile_ext_sub_assert :-
  esetof(ValueType-MotherType,F^(approp(F,MotherType,ValueType)),
         TposeApprops),
  vertices_edges_to_ugraph([],TposeApprops,TposeAppropGraph),
  top_sort(TposeAppropGraph,AppropTypes),
  compile_ext_sub_assert_act(AppropTypes).

compile_ext_sub_assert_act([]).
compile_ext_sub_assert_act([T|Ts]) :-
  approps(T,FRs),
  compile_ext_sub_assert_type(FRs,Vs,NewFSs,FSs,Goals,GoalsRest),
  ( Goals == GoalsRest -> compile_ext_sub_assert_act(Ts)
  ; SVs =.. [T|Vs],
    assert(ext_sub_structs(T,SVs,NewFSs,FSs,Goals,GoalsRest)),
    compile_ext_sub_assert_act(Ts)
  ).

compile_ext_sub_assert_type([],[],FSs,FSs,Goals,Goals).
compile_ext_sub_assert_type([_:R|FRs],[V|Vs],NewFSs,FSs,Goals,GoalsRest) :-
   ext_sub_type(R) -> NewFSs = fs(Tag,SVs,FSsMid),
                      Goals = [deref(V,Tag,SVs)|GoalsMid],
                      compile_ext_sub_assert_type(FRs,Vs,FSsMid,FSs,GoalsMid,
                                                  GoalsRest)
 ; clause(ext_sub_structs(R,V,NewFSs,FSsMid,Goals,GoalsMid),true) ->
   % this is available if needed because we topologically sorted the types
                      compile_ext_sub_assert_type(FRs,Vs,FSsMid,FSs,GoalsMid,
                                                  GoalsRest)
 ; compile_ext_sub_assert_type(FRs,Vs,NewFSs,FSs,Goals,GoalsRest).
    
compile_cons(File) :-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish((cons)/2),
  assert(alec(cons)),
  swi_consult(File),
  retract(ale_compiling(_)).

compile_cons :-
  touch('.alec_cons'),
  absolute_file_name('.alec_cons',[file_type(txt),file_errors(fail),
                                   solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(cons)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_cons(Code,CodeRest) :-
  alec_announce('Compiling type constraints...'),
  abolish((ct)/7),
  (current_predicate(cons,(_ cons _)) ->
            [bot,has,constraints] if_error
                 ( bot cons _ ),
            [multiple,constraint,declarations,for,CType] if_error
                 (bagof(CT,Cons^(CT cons Cons),CTypes),
                  duplicated(CType,CTypes)),
            [constraint,declaration,given,for,atom] if_error
                 ((a_ _) cons _ ),
  ['=@',accessible,by,procedural,attachment,calls,from,constraint,for,Type]
            if_warning (current_predicate(if,(_ if _)),
                        find_xeqs([],EGs),
                        Type cons _ goal Gs,
                        find_xeq_act(Gs,EGs))
  ; true),
  multi_hash(0,(ct)/7,Code,CodeRest).

find_xeqs(Accum,EGs) :-
  findall(EG,find_xeq(Accum,EG),NewAccum,Accum),
  find_xeqs_act(NewAccum,Accum,EGs).

find_xeqs_act(EGs,EGs,EGs) :- !.
find_xeqs_act(NewAccum,_,EGs) :-
  find_xeqs(NewAccum,EGs).

find_xeq(Accum,G/N) :-
  (Head if Body),
  functor(Head,G,N),
  \+member(G/N,Accum),
  find_xeq_act(Body,Accum).

find_xeq_act(=@(_,_),_) :- !.
find_xeq_act((G1,_),Accum) :-
  find_xeq_act(G1,Accum),
  !.
find_xeq_act((_,G2),Accum) :-
  find_xeq_act(G2,Accum),
  !.
find_xeq_act((G1 -> G2),Accum) :-
  ( find_xeq_act(G1,Accum)
  ; find_xeq_act(G2,Accum)
  ),
  !.
find_xeq_act((G1;_),Accum) :-
  find_xeq_act(G1,Accum),
  !.
find_xeq_act((_;G2),Accum) :-
  find_xeq_act(G2,Accum),
  !.
find_xeq_act((\+ G),Accum) :-
  find_xeq_act(G,Accum),
  !.
find_xeq_act(At,Accum) :-
  functor(At,AG,AN),
  member(AG/AN,Accum).

compile_logic:-
  touch('.alec_mgsat'),
  absolute_file_name('.alec_mgsat',[file_type(txt),file_errors(fail),
                                    solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(mgsc)),
  assert(alec(addtype)),assert(alec(featval)),
  assert(alec(u)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_mgsat:-
  touch('.alec_mgsat'),
  absolute_file_name('.alec_mgsat',[file_type(txt),file_errors(fail),
                                    solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(mgsc)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_mgsc_assert :-
  alec_announce('Compiling most general satisfiers...'),  
  abolish((mgsc)/7),
  setof(T,Subs^(T subs Subs),Types),
  top_sort_list(Types,[],_,[],AppropTypes),
  assert(mgsc((a_ X),(a_ X),_,Iqs,Iqs,CGs,CGs)),
  map_mgsat(AppropTypes).

map_mgsat([]).
map_mgsat([T|AppropTypes]) :-
  approps(T,FRs),
  map_mgsat_act(FRs,Vs,IqsIn,IqsMid,ConsGoals,ConsGoalsMid),
  SVs =.. [T|Vs],
  mgsat_cons(T,Tag,SVs,IqsMid,IqsOut,ConsGoalsMid,ConsGoalsRest),
  assert(mgsc(T,SVs,Tag,IqsIn,IqsOut,ConsGoals,ConsGoalsRest)),
  map_mgsat(AppropTypes).
  
map_mgsat_act([],[],Iqs,Iqs,ConsGoals,ConsGoals).
map_mgsat_act([_:TypeRestr|FRs],[(Tag-SVs)|Vs],IqsIn,IqsOut,ConsGoals,
	      ConsGoalsRest) :-
  mgsc(TypeRestr,SVs,Tag,IqsIn,IqsMid,ConsGoals,ConsGoalsMid),
  map_mgsat_act(FRs,Vs,IqsMid,IqsOut,ConsGoalsMid,ConsGoalsRest).

mgsat_cons(Type,Tag,SVs,IqsIn,IqsOut,ConsGoals,ConsGoalsRest) :-
  esetof(T,sub_type(T,Type),ConsTypes),
  map_cons(ConsTypes,Tag,SVs,IqsIn,IqsOut,ConsGoals,ConsGoalsRest).

compile_add_to_type :-
  touch('.alec_addtype'),
  absolute_file_name('.alec_addtype',[file_type(txt),file_errors(fail),
                                      solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(addtype)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_add_to_type(Code,CodeRest) :-
  alec_announce('Compiling type promotion...'),
  abolish((add_to_type)/5),
  multi_hash(1,(add_to_type)/5,Code,CodeRest).
 
compile_add_to_type3(Code,CodeRest) :-
  findall((Goal :-
             deref(FS,Tag,SVs),
             Goal2),
          ((Type subs _),   % types other than a_/1 atoms
           cat_atoms('add_to_type_',Type,Rel),
           Goal =.. [Rel,FS,IqsIn,IqsOut],
           Goal2 =.. [Rel,SVs,Tag,IqsIn,IqsOut]),
          Code,
          [('add_to_type_a_'(FS,IqsIn,IqsOut,X) :-
              deref(FS,Tag,SVs),
              'add_to_type_a_'(SVs,Tag,IqsIn,IqsOut,X))|CodeRest]).
           
compile_featval :-
  touch('.alec_featval'),
  absolute_file_name('.alec_featval',[file_type(txt),file_errors(fail),
                                      solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(featval)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_featval(Code,CodeRest) :-
  alec_announce('Compiling feature selection...'),
  abolish((featval)/6),
  ( ((_ sub _ intro _)
    ; (_ intro _))
    -> multi_hash(1,(featval)/6,Code,CodeRest)
  ; (Code = CodeRest)).

compile_featval4(Code,CodeRest) :-
  setof(Clause,
        Feat^Goal^Goal2^Rel^Type^Subs^FRs^R^( 
                          (Clause = (Goal :-
                                       deref(FS,Tag,SVs),
                                       Goal2)),
                          ( (Type subs Subs intro FRs),
                            member(Feat:R,FRs),
                            cat_atoms('featval_',Feat,Rel),
                            Goal =.. [Rel,FS,FSOut,IqsIn,IqsOut],
                            Goal2 =.. [Rel,SVs,Tag,FSOut,IqsIn,IqsOut]
                          ; (Type intro FRs),
                            member(Feat:R,FRs),
                            cat_atoms('featval_',Feat,Rel),
                            Goal =.. [Rel,FS,FSOut,IqsIn,IqsOut],
                            Goal2 =.. [Rel,SVs,Tag,FSOut,IqsIn,IqsOut])),
        CodeNoEnd),
  append(CodeNoEnd,CodeRest,Code).

compile_u :-
  touch('.alec_u'),
  absolute_file_name('.alec_u',[file_type(txt),file_errors(fail),
                                    solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(u)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_u(Code,CodeRest) :-
  alec_announce('Compiling unification...'),
  abolish((u)/6),
  multi_hash(1,(u)/6,Code,CodeRest).

compile_subsume :-
  no_subsumption
  -> true
   ; (clause(subsume_ready,true),parsing)
     -> touch('.alec_subsume'),
        absolute_file_name('.alec_subsume',[file_type(txt),file_errors(fail),
                                      solutions(first)],AbsFileName),
        assert(ale_compiling(AbsFileName)),
        assert(alec(subsume)),
        swi_consult(AbsFileName),
        retract(ale_compiling(_))
      ; true.

compile_subsume(Code,CodeRest) :-
  no_subsumption
  -> CodeRest = Code
   ; (retract(subsume_ready),parsing)
     -> alec_announce('Compiling subsumption checking...'),
        abolish((subsume_type)/13),
        multi_hash(1,(subsume_type)/13,Code,CodeRest)
      ; CodeRest = Code.

compile_grammar(File):-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish((empty)/1),abolish((rule)/2),
  abolish((lex_rule)/2),
% 5/1/96 - Octav -- added abolish/2 calls for generation predicates
  abolish(('--->')/2),
  abolish((semantics)/1),
  assert(alec(lexrules)),assert(alec(lex)),  % assert(alec(empty)),
  assert(alec(rules)),assert(alec(generate)),
  swi_consult(File),
  retract(ale_compiling(_)).

compile_grammar :-
  touch('.alec_lr'),
  absolute_file_name('.alec_lr',[file_type(txt),file_errors(fail),
                                    solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(lexrules)),assert(alec(lex)), % assert(alec(empty)),
  assert(alec(rules)),assert(alec(generate)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_lex_rules(File):-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish((lex_rule)/2),
  assert(alec(lexrules)),
  swi_consult(File),
  retract(ale_compiling(_)).

compile_lex_rules :-
  touch('.alec_lr'),
  absolute_file_name('.alec_lr',[file_type(txt),file_errors(fail),
                                    solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(lexrules)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_lex_rules(Code,CodeRest) :-
  abolish((lex_rule)/8),
 (parsing ->
  alec_announce('Compiling lexical rules...'),
  ( [no,lexical,rules,found] if_warning_else_fail
        (\+ current_predicate(lex_rule,lex_rule(_,_)))
    -> (Code = CodeRest)
% 5/1/96 - Octav -- added test to signal lack of 'morphs' specification
     ; ([lexical,rule,RuleName,lacks,morphs,specification] if_error
          ((RuleName lex_rule _ **> _ if _)
          ;(RuleName lex_rule _ **> _)),
        multi_hash(0,(lex_rule)/8,Code,CodeRest))
  )
 ; (Code = CodeRest)).

compile_lex(File):-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
% 5/1/96 - Octav -- added abolish/2 calls for generation predicates
  abolish(('--->')/2),
  assert(alec(lex)),
  swi_consult(File),
  retract(ale_compiling(_)).

compile_lex :-
  touch('.alec_lex'),
  absolute_file_name('.alec_lex',[file_type(txt),file_errors(fail),
                                    solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
% 5/1/96 - Octav -- added abolish/2 calls for generation predicates
  assert(alec(lex)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_lex(CodeStart,CodeRest) :-
  (lexicon_consult
  -> (CodeStart = [(:- multifile (lex)/4),(:- dynamic (lex)/4)|Code])
   ; (CodeStart = Code)),
  abolish((lex)/4),
  secret_noadderrs,
  (parsing ->
  alec_announce('Compiling lexicon...'),
  ( [no,lexicon,found] if_warning_else_fail
      (\+ current_predicate('--->',(_ ---> _)))
    -> (CodeRest = Code)
     ; multi_hash(0,(lex)/4,Code,CodeRest))
  ; (CodeRest = Code)),
  secret_adderrs.

% update_lex(+File)
% -----------------
% add the lexical entries in File to the lexicon, closing under lexical rules.
update_lex(File) :-
  lexicon_consult,
  assert(lexicon_updating),
  swi_consult(File),
  retract(lexicon_updating).

% retract_lex(+LexSpec)
% ---------------------
% retract the lexical entries specified by LexSpec, not closing under lexical
%  rules.  LexSpec is either a word, or a list of words.
retract_lex(LexSpec) :-
  LexSpec = [_|_]
   -> retract_lex_list(LexSpec)
    ; retract_lex_one(LexSpec).

retract_lex_list([]).
retract_lex_list([Lex|LexRest]) :-
  retract_lex_one(Lex),
  retract_lex_list(LexRest).

retract_lex_one(Word) :-
  lex(Word,Tag,SVs,IqsIn),
  nl, write('WORD: '), write(Word),
  nl, write('ENTRY: '),
  extensionalise(Tag,SVs,IqsIn),
  check_inequal(IqsIn,IqsOut),
  pp_fs(Tag-SVs,IqsOut), 
  ttynl, write('RETRACT? '),ttyflush,read(y),
  retract(lex(Word,Tag,SVs,IqsIn)),
  fail.
retract_lex_one(_).

retractall_lex(LexSpec) :-
  LexSpec = [_|_]
   -> retractall_lex_list(LexSpec)
    ; retractall(lex(LexSpec,_,_,_)).
retractall_lex_list([]).
retractall_lex_list([Lex|LexRest]) :-
  retractall(lex(Lex,_,_,_)),
  retract_lex_list(LexRest).

% export_words(+Stream,+Delimiter)
% --------------------------------
% Write the words in the current lexicon in a Delimiter-separated list to
%  Stream
export_words(Stream,Delimiter) :-
  setof(Word,Tag^SVs^Iqs^lex(Word,Tag,SVs,Iqs),Words),
  export_words_act(Words,Stream,Delimiter).
export_words_act([],_,_).
export_words_act([W|Ws],Stream,Delimiter) :-
  write(Stream,W),write(Stream,Delimiter),
  export_words_act(Ws,Stream,Delimiter).

:- dynamic emptynum/1.

%compile_empty(File):-
%  absolute_file_name(File,[file_type(prolog),file_errors(error),
%                           access(exist),solutions(all)],AbsFileName),
%  !,assert(ale_compiling(AbsFileName)),
%  abolish((empty)/1),
%  assert(alec(empty)),
%  swi_consult(File),
%  retract(ale_compiling(_)).

%compile_empty :-
%  touch('.alec_empty'),
%  absolute_file_name('.alec_empty',[file_type(txt),file_errors(fail),
%                                    solutions(first)],AbsFileName),
%  assert(ale_compiling(AbsFileName)),
%  assert(alec(empty)),
%  swi_consult(AbsFileName),
%  retract(ale_compiling(_)).

%compile_empty(CodeStart,CodeRest) :-
%  (lexicon_consult
%  -> (CodeStart = [(:- multifile (empty_cat)/3),
%                   (:- dynamic (empty_cat)/3)|Code])
%   ; (CodeStart = Code)),
%  abolish((empty_cat)/3),
%  secret_noadderrs,
%  (parsing -> (alec_announce('Compiling empty categories...'),
%               multi_hash(0,(empty_cat)/3,Code,CodeRest))
%            ; (Code = CodeRest)),
%  secret_adderrs.
 
compile_rules(File):-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
% 5/1/96 - Octav -- added abolish/2 calls for generation predicates
  abolish((rule)/2),abolish((empty)/1),
  assert(alec(rules)),
  swi_consult(File),
  retract(ale_compiling(_)).

%retract_empty :-
%  empty_cat(Tag,SVs,IqsIn),
%  extensionalise(Tag,SVs,IqsIn),
%  check_inequal(IqsIn,IqsOut),
%  nl, write('EMPTY CATEGORY: '), 
%  pp_fs(Tag-SVs,IqsOut,4),
%  ttynl, write('RETRACT? '),ttyflush,read(y),
%  retract(empty_cat(Tag,SVs,IqsIn)),
%  fail.
%retract_empty.

%retractall_empty :-
%  retractall(empty_cat(_,_,_)).

compile_rules :-
  touch('.alec_rules'),
  absolute_file_name('.alec_rules',[file_type(txt),file_errors(fail),
                                    solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
% 5/1/96 - Octav -- added abolish/2 calls for generation predicates
  assert(alec(rules)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

retract_fs_palettes :-
  retract(fspal_ref(Ref)),
  erase(Ref),
  fail
 ; true.

compile_rules(Code,CodeRest) :-
  alec_announce('Compiling empty categories and phrase structure rules...'),
  abolish((empty_cat)/7), retractall(emptynum(_)), assert(emptynum(-1)),
  abolish((rule)/7), abolish((chain_rule)/12), 
  abolish((non_chain_rule)/8),abolish((chained)/7), 
  retract_fs_palettes,
  ( [no,phrase,structure,rules,found] if_warning_else_fail
         (\+ current_predicate(rule,rule(_,_)))
    -> (Code = CodeRest)
% 5/1/96 - Octav -- added 'sem_head>' in the list of labels tested for
  ; [rule,RuleName,has,no,'cat>','cats>',or,'sem_head>',specification]
      if_error ((RuleName rule _ ===> Body),
                \+ cat_member(Body),
                \+ cats_member(Body),
	        \+ sem_head_member(Body)),
% 5/1/96 - Octav -- added check for multiple occurences of 'sem_head>' label
    [rule,RuleName,has,multiple,'sem_head>',specifications]
      if_error ((RuleName rule _ ===> Body),
	        multiple_heads(Body)),
% 6/10/97 - Octav -- added check for bad 'sem_goal>' labels
    [rule,RuleName,has,wrongly,placed,'sem_goal>',specifications]
      if_error ((RuleName rule _ ===> Body),
                bad_sem_goal(Body)),
    (parsing -> (secret_noadderrs,
                 multi_hash(0,(empty_cat)/7,Code,CodeRule),
                 secret_adderrs,
                 multi_hash(0,(rule)/7,CodeRule,CodeGen))
              ; (CodeGen = Code)),
% 5/1/96 - Octav -- added secret_noadderrs/0 to prevent printing 'unification
%   failure' messages during chaining compilation
% 7/1/98 - Gerald -- changed secret_noadderrs/0 calls to have scope only
%   over relevant (non-chain) lexical compilation
  (generating ->
% 5/1/96 - Octav -- added compilation of chain rules for generation
   (( [no,chain,rules,found] if_warning_else_fail
         (\+ ((_ rule _ ===> Body), split_dtrs(Body,_,_,_,_,_)))
      -> (CodeNotChained = CodeGen)
    ; multi_hash(0,(chain_rule)/12,CodeGen,CodeChained),
      multi_hash(0,(chained)/7,CodeChained,CodeNotChained)),
% 5/1/96 - Octav - added compilation of non_chain rules for generation
    ( [no,non_chain,rules,found] if_warning_else_fail
         (\+ ((_ rule _ ===> Body), \+ split_dtrs(Body,_,_,_,_,_)),
          \+ current_predicate(empty,empty(_)),
          \+ current_predicate('--->',(_ ---> _)))
      -> (CodeNotChained = CodeRest)
    ; multi_hash(0,(non_chain_rule)/8,CodeNotChained,CodeRest)))
  ; (CodeGen = CodeRest))).

% 5/1/96 - Octav -- added rules to compile the generation predicate
compile_generate(File) :-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish((semantics)/1),
  assert(alec(generate)),
  swi_consult(File),
  retract(ale_compiling(_)).

compile_generate :-
  touch('.alec_gen'),
  absolute_file_name('.alec_gen',[file_type(txt),file_errors(fail),
                                    solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(generate)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_generate(Code,CodeRest) :-
  abolish((generate)/6),
  (generating ->
  alec_announce('Compiling semantics directive...'),
  (  [no,semantics,directive,found] if_warning_else_fail
      (\+ current_predicate(semantics,semantics(_)))
  -> (Code = CodeRest)
  ; semantics(Pred), functor(Goal,Pred,2),
    ([no,Pred,definite,clause,found] if_warning_else_fail
      (\+ (current_predicate(if,(_ if _)), (Goal if _)))
    -> (Code = CodeRest)
     ; multi_hash(0,(generate)/6,Code,CodeRest)))
  ; (Code = CodeRest)).

compile_dcs(File):-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish((if)/2),
  assert(alec(dcs)),
  swi_consult(File),
  retract(ale_compiling(_)).

compile_dcs :-
  touch('.alec_dcs'),
  absolute_file_name('.alec_dcs',[file_type(txt),file_errors(fail),
                                    solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(dcs)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_dcs(Code,CodeRest) :-
  alec_announce('Compiling definite clauses...'),
  [no,definite,clauses,found] if_warning
    (\+ current_predicate(if,if(_,_))),
  current_predicate(if,if(_,_))
  -> empty_assoc(VarsIn),
     findall((CompiledHead :- CompiledBody),
             ((Head if Body),
              Head =.. [Rel|ArgDescs],
              compile_descs(ArgDescs,Args,IqsIn,IqsMid,CompiledBodyMid,
                            [check_inequal(IqsMid,IqsMid2)|CompiledBodyRest],
                            true,VarsIn,VarsMid,FSPal,[],FSsMid),
              append(Args,[IqsIn,IqsOut],CompiledArgs),
              cat_atoms('fs_',Rel,CompiledRel),
              CompiledHead =.. [CompiledRel|CompiledArgs],
              compile_body(Body,IqsMid2,IqsOut,CompiledBodyRest,[],true,
                            VarsMid,_,FSPal,FSsMid,FSsOut),
              build_fs_palette(FSsOut,FSPal,CompiledBodyList,CompiledBodyMid,
                               []),
              goal_list_to_seq(CompiledBodyList,CompiledBody)),
             Code,CodeRest)
   ; CodeRest = Code.

compile_fun(File):-
  absolute_file_name(File,[file_type(prolog),file_errors(error),
                           access(exist),solutions(all)],AbsFileName),
  !,assert(ale_compiling(AbsFileName)),
  abolish(('+++>')/2),
  assert(alec(fun)),
  assert(alec(fsolve)),
  swi_consult(File),
  retract(ale_compiling(_)).

compile_fun :-
  touch('.alec_fun'),
  absolute_file_name('.alec_fun',[file_type(txt),file_errors(fail),
                                  solutions(first)],AbsFileName),
  assert(ale_compiling(AbsFileName)),
  assert(alec(fun)),
  assert(alec(fsolve)),
  swi_consult(AbsFileName),
  retract(ale_compiling(_)).

compile_fun(Code,CodeRest) :-
  alec_announce('Compiling functional descriptions...'),
  abolish((fsolve)/5),abolish((fun)/1),
  ([no,functional,descriptions,found] if_warning_else_fail
      (\+ current_predicate(+++>,+++>(_,_)))
  -> (Code = [(fun(_) :- !,fail)|CodeRest])
  ;  (setof(Functor/Arity,F^((F +++> _),
                             functor(F,Functor,Arity)),Functions),
      compile_fun_act(Functions,Code,CodeRest))
  ).

compile_fun_act([],Code,Code).
compile_fun_act([(Functor/Arity)|Functions],
                [fun(Template)|CodeMid],CodeRest) :-
  functor(Template,Functor,Arity),
  compile_fun_act(Functions,CodeMid,CodeRest).

% ------------------------------------------------------------------------------
% cat_member(Dtrs)
% ------------------------------------------------------------------------------
% true if Dtrs has at least one category member
% ------------------------------------------------------------------------------
cat_member((cat> _)).
cat_member((cat> _, _)):-!.
cat_member((_,Body)):-
  cat_member(Body).

% ------------------------------------------------------------------------------
% sem_head_member(+Dtrs:<desc>s)
% ------------------------------------------------------------------------------
% true if Dtrs has at least one sem_head> member
% ------------------------------------------------------------------------------
sem_head_member((sem_head> _)).
sem_head_member((sem_head> _,_)):-!.
sem_head_member((_,Body)):-
  sem_head_member(Body).

% ------------------------------------------------------------------------------
% sem_goal_member(+Dtrs:<desc>s)
% ------------------------------------------------------------------------------
% true if Dtrs has at least one sem_goal> member
% ------------------------------------------------------------------------------
sem_goal_member((sem_goal> _)).
sem_goal_member((sem_goal> _,_)):-!.
sem_goal_member((_,Body)):-
  sem_goal_member(Body).

% ------------------------------------------------------------------------------
% cats_member(Dtrs)
% ------------------------------------------------------------------------------
% true if Dtrs has at least one cats member
% ------------------------------------------------------------------------------
cats_member((cats> _)).
cats_member((cats> _, _)):- !.  % doesn't check for cats> [] or elist!
cats_member((_,Body)):-
  cats_member(Body).

% ------------------------------------------------------------------------------
% multiple_heads(+Dtrs:<desc>s)
% ------------------------------------------------------------------------------
% checks whether Dtrs has multiple sem_head> members
% ------------------------------------------------------------------------------
multiple_heads((sem_head> _,Dtrs)) :- !,
  sem_head_member(Dtrs).
multiple_heads((_,Dtrs)) :-
  multiple_heads(Dtrs).

% ------------------------------------------------------------------------------
% bad_sem_goal(+Dtrs:<desc>s)
% ------------------------------------------------------------------------------
% checks whether Dtrs has wrongly placed sem_goal> members
% ------------------------------------------------------------------------------
bad_sem_goal(Dtrs) :-       % there's a sem_head
  split_dtrs(Dtrs,_,_,_,DtrsBefore,DtrsAfter), !,
  (sem_goal_member(DtrsBefore)
   -> true
    ; sem_goal_member(DtrsAfter)).
bad_sem_goal(Dtrs) :-       % there's no sem_head
  sem_goal_member(Dtrs).

% ------------------------------------------------------------------------------
% if_h(Goal:<goal>, SubGoals:<goal>s)                                      +user
% ------------------------------------------------------------------------------
% accounts for multi-hash goals with no subgoals given
% ------------------------------------------------------------------------------
Goal if_h [] :-
  Goal if_h.

% ------------------------------------------------------------------------------
% multi_hash(N:<int>, Fun/Arity:<fun_sym>/<int>,Code:<goals>,CodeRest:<goals>)
% ------------------------------------------------------------------------------
% for each solution T1,...,TK of ?- G(T1,...,TK) if_h SubGoals. 
%   G(f1(X11,...,X1J1),V2,...,VK):-
%       G_f1(V2,...,VK,X11,...,X1J1).
%   ...
%   G_f1_f2_..._fN(TN+1,...,TK,X11,...,X1J1,X21,..,X2J2,...,XN1,..,XNJN):-
%     SubGoals.
% order matters for clauses listed with if_b, but not with if_h
% clauses with if_b must have subgoals listed, even if empty (for order)
% Will not behave properly with if_b on discontiguous user declarations for N>0
% ------------------------------------------------------------------------------

multi_hash(N,(Fun)/Arity,Code,CodeRest):-
  length(Args,Arity),
  Goal =.. [Fun|Args],
  ( setof(sol(Args,SubGoals), if_h(Goal,SubGoals), Sols)
    -> true
     ; bagof(sol(Args,SubGoals), if_b(Goal,SubGoals), Sols)
  ),
  mh(N,Sols,Fun,Code,CodeRest).

mh(0,Sols,Fun,Code,CodeRest):-
  !, mh_zero(Sols,Fun,Code,CodeRest).
mh(N,Sols,Fun,Code,CodeRest):-
  mh_nonzero(Sols,Fun,N,Code,CodeRest).

mh_zero([],_,Code,Code).
mh_zero([sol(Args,SubGoals)|Sols],Fun,[Clause|CodeMid],CodeRest) :-
  Goal =.. [Fun|Args],
  (SubGoals = []
    -> (Clause = Goal)
     ; (goal_list_to_seq(SubGoals,SubGoalSeq),
        Clause = (Goal :- SubGoalSeq))),
  mh_zero(Sols,Fun,CodeMid,CodeRest).

mh_nonzero([],_,_,Code,Code).
mh_nonzero([sol(Args,SubGoals)],Fun,_,[Clause|CodeRest],CodeRest):-
  !, Goal =.. [Fun|Args],
  (SubGoals = []
   -> (Clause = Goal)
    ; (goal_list_to_seq(SubGoals,SubGoalSeq),
       Clause = (Goal :- SubGoalSeq))).

mh_nonzero([sol([Arg|Args],SubGoals)|Sols],Fun,N,Code,CodeRest):-
  nonvar(Arg), 
  functor(Arg,FunArg,Arity),
  Arg =.. [_|ArgsArg],
  ( (Sols = [sol([Arg2|_],_)|_],
     nonvar(Arg2), functor(Arg2,FunArg,Arity))
    -> (cat_atoms('_',FunArg,FunTail),
        cat_atoms(Fun,FunTail,FunNew),
        same_length(Args,OtherArgs),
        Goal =.. [Fun,Arg|OtherArgs],
        append(OtherArgs,ArgsArg,ArgsNew), 
        SubGoal =.. [FunNew|ArgsNew],
        append(Args,ArgsArg,ArgsOld),
        (Code = [(Goal :-
                    SubGoal)|CodeMid]),
        SolsSub = [sol(ArgsOld,SubGoals)|SolsSubRest],
        mh_arg(FunArg,Arity,Sols,SolsSub,SolsSubRest,Fun,FunNew,N,
               CodeMid,CodeRest))
  ; Goal =.. [Fun,Arg|Args],
    (Code = [Clause|CodeMid]),
    (SubGoals = []
     -> (Clause = Goal)
      ; (goal_list_to_seq(SubGoals,SubGoalSeq),
         Clause = (Goal :- SubGoalSeq))),
    mh_nonzero(Sols,Fun,N,CodeMid,CodeRest)
  ).

mh_arg(FunMatch,Arity,[sol([Arg|Args],SubGoals)|Sols],SolsSub,SolsSubMid,
       Fun,FunNew,N,Code,CodeRest):-
  nonvar(Arg),
  Arg =.. [FunMatch|ArgsSub],  % formerly cut here - standard order ensures
  length(ArgsSub,Arity),       %  correctness for if_h in both cases
  !,append(Args,ArgsSub,ArgsNew),
  SolsSubMid = [sol(ArgsNew,SubGoals)|SolsSubRest],
  mh_arg(FunMatch,Arity,Sols,SolsSub,SolsSubRest,Fun,FunNew,N,
         Code,CodeRest).
mh_arg(_,_,Sols,SolsSub,[],Fun,FunNew,N,Code,CodeRest):-
  NMinusOne is N-1,
  mh(NMinusOne,SolsSub,FunNew,Code,CodeMid),
  mh_nonzero(Sols,Fun,N,CodeMid,CodeRest).

% ==============================================================================
% Debugger / Top Level I/O
% ==============================================================================

% ------------------------------------------------------------------------------
% show_type(Type:<type>)
% ------------------------------------------------------------------------------
% Displays information about Type, including appropriate features, immediate
% subtypes, supertypes, and constraints.  Continues by allowing to browse 
% super or subtypes
% ------------------------------------------------------------------------------
show_type(Type):-
  type(Type),
  nl,  write('TYPE: '), write(Type),
  immed_subtypes(Type,SubTypes),
  nl, write('SUBTYPES: '), write(SubTypes),
  ( setof(T,T2^(sub_type(T,Type),
                T \== Type,
                \+ (sub_type(T2,Type),
                    T2 \== Type, T2 \== T,
                    sub_type(T,T2))),SuperTypes)
    -> true
  ; SuperTypes = []
  ),
  nl, write('SUPERTYPES: '), write(SuperTypes),
  (current_predicate(cons,(_ cons _))
   -> ((Type cons Cons goal _)
       -> true
        ; Type cons Cons
          -> true
           ; Cons = none)
    ; Cons = none),
  nl, write('IMMEDIATE CONSTRAINT: '), write(Cons),
  add_to(Type,Tag,bot,[],IqsIn),
  deref(Tag,bot,Ref,SVs),
  extensionalise(Ref,SVs,IqsIn),
  check_inequal(IqsIn,IqsOut),
  nl, write('MOST GENERAL SATISFIER: '), 
  pp_fs(Ref-SVs,IqsOut,5).

% ------------------------------------------------------------------------------
% show_cons(Type:<type>)
%-------------------------------------------------------------------------------
show_cons(Type):-
  immed_cons(Type,Cons),
  nl, write('Immediate Constraint for type: '),write(Type),
  nl, write(Cons).

% ------------------------------------------------------------------------------
% mgsat(Desc:<desc>)
% ------------------------------------------------------------------------------
% prints out most general satisfiers of Desc
% ------------------------------------------------------------------------------
mgsat(Desc):-
   nl, write('MOST GENERAL SATISFIER OF: '), write(Desc), nl,
  \+ \+
  (add_to(Desc,Tag,bot,[],Iqs),
   deref(Tag,bot,Ref,SVs),
   extensionalise(Ref,SVs,Iqs),
   check_inequal(Iqs,CheckedIqs),
   pp_fs(Ref-SVs,CheckedIqs),
   nl, query_proceed).

% ------------------------------------------------------------------------------
% iso_desc(Desc1:<desc>, Desc2:<desc>)
% ------------------------------------------------------------------------------
% checks if Desc1 and Desc2 create extensionally identical structures
% ------------------------------------------------------------------------------
iso_desc(D1,D2):-
  add_to(D1,Tag1,bot,[],IqsMid),
  add_to(D2,Tag2,bot,IqsMid,_),
  iso_seq(iso(Tag1-bot,Tag2-bot,done)).

% ------------------------------------------------------------------------------
% rec(Words:<word>s)
% ------------------------------------------------------------------------------
% basic predicate to parse Words;  prints out recognized categories
% one at a time
% ------------------------------------------------------------------------------
rec(Words):-
  nl, write('STRING: '),
  nl, number_display(Words,0), 
  ttynl, rec(Words,Tag,SVs,Iqs),
  nl, write('CATEGORY: '),nl, ttyflush, 
  pp_fs(Tag-SVs,Iqs), 
  nl, query_proceed.

% ------------------------------------------------------------------------------
% rec(Words:<word>s,Desc:<desc>)
% ------------------------------------------------------------------------------
% Like rec/1, but solution FSs must satisfy Desc
% ------------------------------------------------------------------------------
rec(Words,Desc):-
  nl, write('STRING: '),
  nl, number_display(Words,0), 
  ttynl, rec(Words,Tag,SVs,Iqs,Desc),
  nl, write('CATEGORY: '),nl, ttyflush, 
  pp_fs(Tag-SVs,Iqs), 
  nl, query_proceed.

% ------------------------------------------------------------------------------
% rec_best(+WordsList:list(<word>s),Desc)
% ------------------------------------------------------------------------------
% Parses every list of words in WordsList until one succeeds, satisfying Desc,
%  or there are no more lists.  If one succeeds, then rec_best/2 will backtrack
%  through all of its solutions that satisfy Desc, but not through the
%  subsequent lists of words in WordsList.

rec_best([],_) :-
  fail.
rec_best([Ws|WordsList],Desc) :-
  if(rec(Ws,Tag,SVs,Iqs,Desc),
     (nl,write('STRING: '),
      nl,number_display(Ws,0),
      nl,write('CATEGORY: '),nl,ttyflush,
      pp_fs(Tag-SVs,Iqs),
      nl,query_proceed),
     rec_best(WordsList,Desc)).

% ------------------------------------------------------------------------------
% rec_list(+WordsList:list(<word>s),Desc)
% ------------------------------------------------------------------------------
% Parses every list of words in WordsList until one succeeds, satisfying Desc,
%  or there are no more lists.  Unlike rec_best/2, rec_list/2 will backtrack
%  through all of the solutions of a list that succeeds, and then continue
%  parsing the subsequent lists of words in WordsList.

rec_list([],_) :-
  fail.
rec_list([Ws|WordsList],Desc) :-
  rec(Ws,Tag,SVs,Iqs,Desc),
  nl,write('STRING: '),
  nl,number_display(Ws,0),
  nl,write('CATEGORY: '),nl,ttyflush,
  pp_fs(Tag-SVs,Iqs),
  nl,query_proceed
; rec_list(WordsList,Desc).

% ------------------------------------------------------------------------------
% rec_list(+WordsList:list(<word>s),Desc,SolnsList:list(<fs(FS,Iqs)>s))
% ------------------------------------------------------------------------------
% Like rec_list/2, but collects the solutions in a list of lists, one for each
%  list of words in WordsList.  Each solution is a pair, fs(FS,Iqs).
% ------------------------------------------------------------------------------
rec_list([],_,[]).
rec_list([Ws|WordsList],Desc,[Solns|SolnsList]) :-
  bagof(fs(DTag-DSVs,IqsOut),(rec(Ws,Tag,SVs,IqsIn,Desc),
                              fully_deref_prune(Tag,SVs,DTag,DSVs,IqsIn,
                                                IqsOut)),
        Solns),
  rec_list(WordsList,Desc,SolnsList).

% ------------------------------------------------------------------------------
% lex(Word:<word>)
% ------------------------------------------------------------------------------
% prints out all categories for Word, querying user in between
% ------------------------------------------------------------------------------
lex(Word):-
  lex(Word,Tag,SVs,IqsIn),
  nl, write('WORD: '), write(Word),
  nl, write('ENTRY: '),
  extensionalise(Tag,SVs,IqsIn),
  check_inequal(IqsIn,IqsOut),
  pp_fs(Tag-SVs,IqsOut), 
  nl, query_proceed.

% ------------------------------------------------------------------------------
% query(GoalDesc:<goal_desc>)
% ------------------------------------------------------------------------------
% given a goal description GoalDesc, finds most general satisfier of it
% and then calls it as a goal
% ------------------------------------------------------------------------------
query(GoalDesc):-
  \+ \+
  (nl, query_goal(GoalDesc,Args,[],Goal,[],IqsMid),
   call(Goal),
   extensionalise_list(Args,IqsMid),
   check_inequal(IqsMid,IqsOut),
   duplicates_list(Args,IqsOut,[],_,[],_,0,_),
   pp_query_goal(Goal,[],VisMid,0),
   nl, pp_iqs(IqsOut,VisMid,_,0),
   nl, query_proceed).

query_goal((GD1,GD2),(G1,G2),IqsIn,IqsOut):-
  !, query_goal(GD1,G1,IqsIn,IqsMid),
  query_goal(GD2,G2,IqsMid,IqsOut).
query_goal((GD1 -> GD2 ; GD3),(G1 -> G2 ; G3),IqsIn,IqsOut) :-
  !,query_goal(GD1,G1,IqsIn,IqsMid),
  query_goal(GD2,G2,IqsMid,IqsOut),
  query_goal(GD3,G3,IqsIn,IqsOut).
query_goal((GD1;GD2),G,IqsIn,IqsOut):-
  !, ( query_goal(GD1,G,IqsIn,IqsOut)
     ; query_goal(GD2,G,IqsIn,IqsOut)
     ).
query_goal((\+ GD1),(\+ G1),IqsIn,IqsOut):-
  !, query_goal(GD1,G1,IqsIn,IqsOut).
query_goal(prolog(Hook),prolog(Hook),Iqs,Iqs) :-
  !.
query_goal(true,true,Iqs,Iqs) :-
  !.
query_goal(fail,fail,Iqs,Iqs) :-
  !.
query_goal(!,!,Iqs,Iqs) :-
  !.
query_goal((GD1 -> GD2),(G1 -> G2),IqsIn,IqsOut) :-
  !,query_goal(GD1,G1,IqsIn,IqsMid),
  query_goal(GD2,G2,IqsMid,IqsOut).
query_goal((Desc1 =@ Desc2),Goal,IqsIn,IqsOut) :-
  !, query_goal_args([Desc1,Desc2],[FS1,FS2],IqsIn,IqsMid),
  Goal = (deref(FS1,DTag1,DSVs1),
          deref(FS2,DTag2,DSVs2),
          ext_act(fs(DTag1,DSVs1,fs(DTag2,DSVs2,fsdone)),edone,done,IqsMid),
          check_inequal(IqsMid,IqsOut),
          deref(DTag1,DSVs1,Tag1Out,_),
          deref(DTag2,DSVs2,Tag2Out,_),
          (Tag1Out == Tag2Out)).
query_goal(AtGD,AtG,IqsIn,IqsOut):-
  AtGD =.. [Rel|ArgDescs],
  query_goal_args(ArgDescs,CompiledArgs,IqsIn,IqsOut),
  cat_atoms('fs_',Rel,CompiledRel),
  AtG =.. [CompiledRel|CompiledArgs].

query_goal_args([],[IqsIn,IqsOut],IqsIn,IqsOut).
query_goal_args([D|Ds],[Tag-bot|Args],IqsIn,IqsOut):-
  add_to(D,Tag,bot,IqsIn,IqsMid),
  query_goal_args(Ds,Args,IqsMid,IqsOut).

query_goal((GD1,GD2),DtrCats,DtrCatsRest,(G1,G2),IqsIn,IqsOut):-
  !, query_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid),
  query_goal(GD2,DtrCatsMid,DtrCatsRest,G2,IqsMid,IqsOut).
query_goal((GD1 -> GD2 ; GD3),DtrCats,DtrCatsRest,(G1 -> G2 ; G3),IqsIn,IqsOut)
           :-
  !,query_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid),
  query_goal(GD2,DtrCatsMid,DtrCatsMid2,G2,IqsMid,IqsOut),
  query_goal(GD3,DtrCatsMid2,DtrCatsRest,G3,IqsIn,IqsOut).
query_goal((GD1;GD2),DtrCats,DtrCatsRest,(G1;G2),IqsIn,IqsOut):-
  !,query_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsOut),
  query_goal(GD2,DtrCatsMid,DtrCatsRest,G2,IqsIn,IqsOut).
query_goal((\+ GD1),DtrCats,DtrCatsRest,(\+ G1),IqsIn,IqsOut):-
  !, query_goal(GD1,DtrCats,DtrCatsRest,G1,IqsIn,IqsOut).
query_goal(prolog(Hook),DtrCats,DtrCats,prolog(Hook),Iqs,Iqs) :-
  !.
query_goal(true,DtrCats,DtrCats,true,Iqs,Iqs) :-
  !.
query_goal(fail,DtrCats,DtrCats,fail,Iqs,Iqs) :-
  !.
query_goal(!,DtrCats,DtrCats,!,Iqs,Iqs) :-
  !.
query_goal((GD1 -> GD2),DtrCats,DtrCatsRest,(G1 -> G2),IqsIn,IqsOut) :-
  !,query_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid),
  query_goal(GD2,DtrCatsMid,DtrCatsRest,G2,IqsMid,IqsOut).
query_goal((Desc1 =@ Desc2),DtrCats,DtrCatsRest,Goal,IqsIn,IqsOut) :-
  !, query_goal_args([Desc1,Desc2],DtrCats,DtrCatsRest,[FS1,FS2],IqsIn,IqsMid),
  Goal = (deref(FS1,DTag1,DSVs1),
          deref(FS2,DTag2,DSVs2),
          ext_act(fs(DTag1,DSVs1,fs(DTag2,DSVs2,fsdone)),edone,done,IqsMid),
          check_inequal(IqsMid,IqsOut),
          deref(DTag1,DSVs1,Tag1Out,_),
          deref(DTag2,DSVs2,Tag2Out,_),
          (Tag1Out == Tag2Out)).
query_goal(AtGD,DtrCats,DtrCatsRest,AtG,IqsIn,IqsOut):-
  AtGD =.. [Rel|ArgDescs],
  query_goal_args(ArgDescs,DtrCats,DtrCatsRest,CompiledArgs,IqsIn,IqsOut),
  cat_atoms('fs_',Rel,CompiledRel),
  AtG =.. [CompiledRel|CompiledArgs].

query_goal_args([],DtrCats,DtrCats,[IqsIn,IqsOut],IqsIn,IqsOut).
query_goal_args([D|Ds],[Tag-bot|DtrCats],DtrCatsRest,[Tag-bot|Args],
                IqsIn,IqsOut):-
  add_to(D,Tag,bot,IqsIn,IqsMid),
  query_goal_args(Ds,DtrCats,DtrCatsRest,Args,IqsMid,IqsOut).


pp_query_goal(\+ Goal,VisIn,VisOut,Col):-
  !, write('\\+ '), write('( '), 
  NewCol is Col+5, pp_query_goal(Goal,VisIn,VisOut,NewCol),
  nl, tab(Col), tab(3), write(')').
pp_query_goal((G1 -> G2 ; G3),VisIn,VisOut,Col) :-
  !, write('(  '), NewCol is Col + 3,
  pp_query_goal(G1,VisIn,VisMid,NewCol),
  nl, tab(Col), write('-> '),
  pp_query_goal(G2,VisMid,VisMid2,NewCol),
  nl, tab(Col), write(';  '),
  pp_query_goal(G3,VisMid2,VisOut,NewCol),
  nl, tab(Col), write(')').
pp_query_goal((Goal1;Goal2),VisIn,VisOut,Col):-
  !, write('( '), NewCol is Col + 2,
  pp_query_goal(Goal1,VisIn,VisMid,NewCol),
  nl, tab(Col), write('; '),
  pp_query_goal(Goal2,VisMid,VisOut,NewCol),
  nl, tab(Col), write(')').
pp_query_goal((Goal1,Goal2),VisIn,VisOut,Col):-
  !, pp_query_goal(Goal1,VisIn,VisMid,Col), write(','),
  nl, tab(Col), pp_query_goal(Goal2,VisMid,VisOut,Col).
pp_query_goal(prolog(Hook),Vis,Vis,_) :-
  !, write(prolog(Hook)).
pp_query_goal(Desc1 =@ Desc2,VisIn,VisOut,Col) :-
  !, write('('),
  NewCol is Col+3,
  pp_fs(Desc1,VisIn,VisMid,NewCol), nl, tab(Col),
  write('=@'), nl, tab(NewCol),
  pp_fs(Desc2,VisMid,VisOut,NewCol), nl, tab(Col),
  write(')').
pp_query_goal(true,Vis,Vis,_) :-
  !, write(true).
pp_query_goal(!,Vis,Vis,_) :-
  !, write(!).
pp_query_goal((G1 -> G2),VisIn,VisOut,Col) :-
  !, write('(  '), NewCol is Col + 3,
  pp_query_goal(G1,VisIn,VisMid,NewCol),
  nl, tab(Col), write('-> '),
  pp_query_goal(G2,VisMid,VisOut,NewCol),
  nl, tab(Col), write(')').
pp_query_goal(fail,Vis,Vis,_) :-
  !, write(fail).
pp_query_goal(Goal,VisIn,VisOut,Col):-  % also handles !
  Goal =.. [CompiledRel|Args],
  name('fs_',FSChars),
  name(CompiledRel,CompiledRelChars),
  append(FSChars,RelChars,CompiledRelChars),
  name(Rel,RelChars),
  write(Rel),
  ( Args = [_,_]  % the inequations
    -> VisOut = VisIn
  ; write('('),
    name(Rel,Name),
    length(Name,N),
    NewCol is Col+N+1,
    pp_query_goal_args(Args,VisIn,VisOut,NewCol)
  ).

pp_query_goal_args([Arg,_,_],VisIn,VisOut,Col):-  % one left plus inequations
  !, pp_fs(Arg,VisIn,VisOut,Col), write(')').
pp_query_goal_args([Arg|Args],VisIn,VisOut,Col):-
  pp_fs(Arg,VisIn,VisMid,Col), write(','), nl, tab(Col),
  pp_query_goal_args(Args,VisMid,VisOut,Col).

% ------------------------------------------------------------------------------
% mg_sat_goal(GoalDesc,Goal,IqsIn,IqsOut)                                   eval
% ------------------------------------------------------------------------------
% Goal is most general satisfier of GoalDesc
% (also used for functional descriptions)
% ------------------------------------------------------------------------------
mg_sat_goal((GD1 -> GD2 ; GD3),(G1 -> G2 ; G3),IqsIn,IqsOut) :-
  !, mg_sat_goal(GD1,G1,IqsIn,IqsMid),
  mg_sat_goal(GD2,G2,IqsMid,IqsOut),
  mg_sat_goal(GD3,G3,IqsIn,IqsOut).
mg_sat_goal((GDesc1;GDesc2),(G1;G2),IqsIn,IqsOut):-  
  !, mg_sat_goal(GDesc1,G1,IqsIn,IqsOut),   
  mg_sat_goal(GDesc2,G2,IqsIn,IqsOut).
mg_sat_goal(!,!,Iqs,Iqs):-!.
mg_sat_goal((GD1 -> GD2),(G1 -> G2),IqsIn,IqsOut) :-
  !, mg_sat_goal(GD1,G1,IqsIn,IqsMid),
  mg_sat_goal(GD2,G2,IqsMid,IqsOut).
mg_sat_goal((GDesc1,GDesc2),(G1,G2),IqsIn,IqsOut):-
  !, mg_sat_goal(GDesc1,G1,IqsIn,IqsMid),
  mg_sat_goal(GDesc2,G2,IqsMid,IqsOut).
mg_sat_goal(prolog(Hook),prolog(Hook),Iqs,Iqs) :-
  !.
mg_sat_goal(GoalDesc,Goal,IqsIn,IqsOut):-  % also handles =@,\+
  GoalDesc =.. [Rel|ArgDescs],
  mg_sat_list(ArgDescs,Args,IqsIn,IqsOut),
  Goal =.. [Rel|Args].

% ------------------------------------------------------------------------------
% mg_sat_list(GoalDescs,Goals,IqsIn,IqsOut)
% ------------------------------------------------------------------------------
% maps mg_sat_goal on GoalDescs
% ------------------------------------------------------------------------------
mg_sat_list([],[],Iqs,Iqs).
mg_sat_list([ArgDesc|ArgDescs],[Ref-bot|Args],IqsIn,IqsOut):-
  add_to(ArgDesc,Ref,bot,IqsIn,IqsMid),
  mg_sat_list(ArgDescs,Args,IqsMid,IqsOut).

% ------------------------------------------------------------------------------
% macro(MacroName:<name>)
% ------------------------------------------------------------------------------
% prints out possible instantiations of macro named MacroName
% ------------------------------------------------------------------------------
macro(MacroName):-
  MacroName = VarName,
  \+ \+
  ((VarName macro Desc),
   add_to(Desc,Tag,bot,[],IqsMid),
   satisfy_dtrs_goal(VarName,MacroArgs,[],MacroSat,IqsMid,IqsMid2),
   ArgsOut = [Tag-bot|MacroArgs],
   extensionalise_list(ArgsOut,IqsMid2),
   check_inequal(IqsMid2,IqsMid3),
   duplicates_list(ArgsOut,IqsMid3,[],_,[],_,0,_),
   nl, write('MACRO: '), nl, tab(4), pp_goal(MacroSat,[],VisMid,4),
   nl, write('ABBREVIATES:'), nl, tab(4), pp_fs(Tag-bot,VisMid,VisOut,4),
   nl, pp_iqs(IqsMid3,VisOut,_,4),
   nl, query_proceed).

insert_vars(MacroName,VarName):-
  MacroName =.. [Rel|Args],
  insert_vars_list(Args,ArgsVars),
  VarName =.. [Rel|ArgsVars].

insert_vars_list([],[]).
insert_vars_list([X|Xs],[(_,X)|XsVar]):-
  insert_vars_list(Xs,XsVar).

% ------------------------------------------------------------------------------
% empty
% ------------------------------------------------------------------------------
% displays empty categories
% ------------------------------------------------------------------------------
(empty) :-
  empty_cat(I,-1,Tag,SVs,IqsIn,Dtrs,RuleName),
  extensionalise(Tag,SVs,IqsIn),
  check_inequal(IqsIn,IqsOut),
  length(Dtrs,ND),
  print_empty(I,Tag,SVs,IqsOut,Dtrs,RuleName,ND).

print_empty(I,Tag,SVs,IqsOut,Dtrs,RuleName,ND) :-
  nl, write('EMPTY CATEGORY: '), 
  pp_fs(Tag-SVs,IqsOut,4),
  (no_interpreter 
  -> nl, query_proceed
   ; nl, write('     index: '),(functor(I,empty,2)
                               -> arg(1,I,E),
                                  write(E)
                                ; write(I)),
     nl, write('      rule: '),write(RuleName),
     nl, write(' # of dtrs: '),write(ND),
     nl, query_empty(I,Tag,SVs,IqsOut,Dtrs,RuleName,ND)
  ).

query_empty(I,Tag,SVs,IqsOut,Dtrs,RuleName,ND) :-
  write('Action(dtr-#,continue,abort)? '),
  nl,read(Response),
  query_empty_act(Response,I,Tag,SVs,IqsOut,Dtrs,RuleName,ND).

query_empty_act(continue,_,_,_,_,_,_,_) :-
  !,fail.
query_empty_act(abort,_,_,_,_,_,_,_) :-
  !,abort.
query_empty_act(dtr-D,I,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  nth_index(Dtrs,D,empty(DI,-1),-1,-1,DTag,DSVs,DIqs,DDtrs,DRule),
  !,length(DDtrs,DND),
  ( print_empty(DI,DTag,DSVs,DIqs,DDtrs,DRule,DND)
  ; print_empty(I,Tag,SVs,Iqs,Dtrs,RuleName,ND)
  ).
query_empty_act(_,I,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  !,query_empty(I,Tag,SVs,Iqs,Dtrs,RuleName,ND).

% ------------------------------------------------------------------------------
% edge(N:<int>, M:<int>)
% ------------------------------------------------------------------------------
% prints out edges from N to M, querying user in between
% ------------------------------------------------------------------------------
edge(I) :-
  (I < 0
  -> empty_cat(I,N,Tag,SVs,Iqs,Dtrs,RuleName),
     M = N
   ; clause(edge(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName),true)
  ) -> (nl, write('COMPLETED CATEGORY SPANNING: '),
        write_out(M,N),
        nl, edge_act(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName))
     ; error_msg((nl,write('edge/1: edge has been retracted'),nl)).

edge(M,N):-
  (M < N
  -> (M >=0 
     -> nl, write('COMPLETED CATEGORIES SPANNING: '),
        write_out(M,N),
        nl, clause(edge(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName),true), % not indexed
        nl, edge_act(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName),
        fail
      ; error_msg((nl,write('edge/2: arguments must be non-negative'))))
   ; error_msg((nl,write('edge/2: first argument must be < second argument')))
  ).

edge_act(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName) :-
  length(Dtrs,ND),
  print_edgeout(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName,ND).

print_edgeout(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  nl,pp_fs(Tag-SVs,Iqs),
  (no_interpreter
  -> nl,query_proceed
   ; nl,write('Edge created for category above: '),
     nl,write('     index: '),(functor(I,empty,2)
                              -> arg(1,I,E),
                                 write(E)
                               ; write(I)),
     nl,write('      from: '),write(M),write(' to: '),write(N),
     nl,write('    string: '),write_out(M,N),
     nl,write('      rule:  '),write(RuleName),
     nl,write(' # of dtrs: '),write(ND),
     query_edgeout(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName,ND)
  ).

query_edgeout(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  nl,write('Action(retract,dtr-#,continue,abort)? '),
  nl,read(Response),
  query_edgeout_act(Response,I,M,N,Tag,SVs,Iqs,Dtrs,RuleName,ND).

query_edgeout_act(retract,I,M,_,_,_,_,_,_,_) :-
  retract(edge(I,M,_,_,_,_,_,_)), % will fail on empty cats
  !.  
query_edgeout_act(dtr-D,I,M,N,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  nth_index(Dtrs,D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule),
  !,length(DDtrs,DND),
  print_dtr_edge(D,DI,DLeft,DRight,DTag,DSVs,DIqs,DDtrs,DRule,DND),
  print_edgeout(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName,ND).
query_edgeout_act(continue,_,_,_,_,_,_,_,_,_) :-
  !.
query_edgeout_act(abort,_,_,_,_,_,_,_,_,_) :-
  !,abort.
query_edgeout_act(_,I,M,N,Tag,SVs,Iqs,Dtrs,RuleName,ND) :-
  query_edgeout(I,M,N,Tag,SVs,Iqs,Dtrs,RuleName,ND).

write_out(M,N):-
  parsing(Ws),
  all_but_first(M,Ws,WsRest),
  K is N-M,
  write_first(K,WsRest).

all_but_first(0,Ws,Ws):-!.
all_but_first(M,[_|Ws],WsOut):-
  K is M-1,
  all_but_first(K,Ws,WsOut).

write_first(0,_):-!.
write_first(N,[W|Ws]):-
  write(W), write(' '),
  K is N-1,
  write_first(K,Ws).

% ------------------------------------------------------------------------------
% lex_rule(RuleName:<name>)
% ------------------------------------------------------------------------------
% Displays lexical rule with name RuleName
% ------------------------------------------------------------------------------
lex_rule(RuleName):-
  \+ \+
  lexrule2(RuleName).

lexrule2(RuleName):-
  (( (RuleName lex_rule Desc1 **> Desc2 if Cond morphs Morphs)
   ; (RuleName lex_rule Desc1 **> Desc2 morphs Morphs),
     Cond = none
   ),
   nl, write('LEX RULE: '), write(RuleName), 
   add_to(Desc1,Tag1,bot,[],IqsMid),
   add_to(Desc2,Tag2,bot,IqsMid,IqsMid2),
   satisfy_dtrs_goal(Cond,Args,[],Goal,IqsMid2,IqsMid3),
   ArgsOut = [Tag1-bot,Tag2-bot|Args],
   extensionalise_list(ArgsOut,IqsMid3),
   check_inequal(IqsMid3,IqsMid4),
   duplicates_list(ArgsOut,IqsMid4,[],_,[],_,0,_),
   nl, write('INPUT CATEGORY: '), 
   nl, tab(4), pp_fs(Tag1-bot,[],VisMid1,4),
   nl, write('OUTPUT CATEGORY: '),
   nl, tab(4), pp_fs(Tag2-bot,VisMid1,VisMid2,4),
   ( (Cond = none,
      VisMid3 = VisMid2)
     -> true
   ; (nl, write('CONDITION: '), 
      nl, tab(4), pp_goal(Goal,VisMid2,VisMid3,4))
   ),
   nl, write('MORPHS: '),
   numbervars(Morphs,0,_),
   pp_morphs(Morphs),
   nl, pp_iqs(IqsMid4,VisMid3,_,4),
   nl, query_proceed).

pp_morphs((Morph,Morphs)):-
  !, nl, tab(4), pp_morph(Morph),
  pp_morphs(Morphs).
pp_morphs(Morph):-
  nl, tab(4), pp_morph(Morph).

pp_morph((P1 becomes P2)):-
  pp_patt(P1), write(' becomes '), pp_patt(P2).
pp_morph((P1 becomes P2 when Cond)):-
  pp_patt(P1), write(' becomes '), pp_patt(P2),
  nl, tab(8), write('when '), write(Cond).
  
pp_patt((X,Xs)):-
  !, pp_at_patt(X), write(','),
  pp_patt(Xs).
pp_patt(X):-
  pp_at_patt(X).

pp_at_patt(Atom):-
  atom(Atom),
  !, name(Atom,Codes),
  make_char_list(Codes,Chars),
  write(Chars).
pp_at_patt(List):-
  write(List).

% ------------------------------------------------------------------------------
% show_clause(PredSpec:<predspec>)
% ------------------------------------------------------------------------------
% Displays definite clauses in feature structure format
% ------------------------------------------------------------------------------
show_clause(Spec):-
  \+ \+ show_clause2(Spec).

show_clause2(Spec):-
  (( Spec = Name/Arity
     -> true
   ; Spec = Name
   ),
   (Head if Body),
   functor(Head,Name,Arity),
   satisfy_dtrs_goal(Head,Cats,CatsRest,HeadGoal,[],IqsMid),
   satisfy_dtrs_goal(Body,CatsRest,[],BodyGoal,IqsMid,IqsMid2),
   extensionalise_list(Cats,IqsMid2),
   check_inequal(IqsMid2,IqsMid3),
   duplicates_list(Cats,IqsMid3,[],_,[],_,0,_),
   nl, write('HEAD: '), pp_goal(HeadGoal,[],Vis,6),
   nl, write('BODY: '), pp_goal(BodyGoal,Vis,Vis2,6),
   nl, pp_iqs(IqsMid3,Vis2,_,6),
   nl, query_proceed).

% ------------------------------------------------------------------------------
% rule(RuleName:<name>)
% ------------------------------------------------------------------------------
% Displays rule with name RuleName
% ------------------------------------------------------------------------------
rule(RuleName):-
  \+ \+
  ((RuleName rule Moth ===> DtrsDesc),
  nl, write('RULE: '), write(RuleName),
  add_to(Moth,TagMoth,bot,[],IqsMid),
  satisfy_dtrs(DtrsDesc,DtrCats,[],Dtrs,IqsMid,IqsMid2),
  CatsOut = [TagMoth-bot|DtrCats],
  extensionalise_list(CatsOut,IqsMid2),
  check_inequal(IqsMid2,IqsMid3),
  duplicates_list(CatsOut,IqsMid3,[],_,[],_,0,_),
  nl, nl, write('MOTHER: '), nl, nl, tab(2), pp_fs(TagMoth-bot,[],VisMid,2),
  nl, nl, write('DAUGHTERS/GOALS: '),   
  show_rule_dtrs(Dtrs,VisMid,VisMid2),
  nl, pp_iqs(IqsMid3,VisMid2,_,2),
  nl, query_proceed).

show_rule_dtrs([],Vis,Vis).
show_rule_dtrs([(cat> C)|Dtrs],VisIn,VisOut):-
  nl, nl, write('CAT  '), pp_fs(C,VisIn,VisMid,5),
  show_rule_dtrs(Dtrs,VisMid,VisOut).
% 5/1/96 - Octav -- added clause for sem_head> label
show_rule_dtrs([(sem_head> C)|Dtrs],VisIn,VisOut):-
  nl, nl, write('SEM_HEAD  '), pp_fs(C,VisIn,VisMid,10),
  show_rule_dtrs(Dtrs,VisMid,VisOut).
show_rule_dtrs([(cats> Cs)|Dtrs],VisIn,VisOut):-
  nl, nl, write('CATs '), pp_fs(Cs,VisIn,VisMid,5),
  show_rule_dtrs(Dtrs,VisMid,VisOut).
show_rule_dtrs([(goal> G)|Dtrs],VisIn,VisOut):-
  nl, nl, write('GOAL  '), pp_goal(G,VisIn,VisMid,6),
  show_rule_dtrs(Dtrs,VisMid,VisOut).
% 6/1/97 - Octav -- added clause for sem_goal> label
show_rule_dtrs([(sem_goal> G)|Dtrs],VisIn,VisOut):-
  nl, nl, write('SEM_GOAL  '), pp_goal(G,VisIn,VisMid,10),
  show_rule_dtrs(Dtrs,VisMid,VisOut).

pp_goal(Goal):-
  Goal =.. [_|Args],
  duplicates_list(Args,[],[],_,[],_,0,_),
  pp_goal(Goal,[],_,0).

pp_goal(\+ Goal,VisIn,VisOut,Col):-
  !, write('\\+ '), write('( '), 
  NewCol is Col+5, pp_goal(Goal,VisIn,VisOut,NewCol),
  nl, tab(Col), tab(3), write(')').
pp_goal((G1 -> G2 ; G3),VisIn,VisOut,Col) :-
  !, write('(  '),  NewCol is Col + 3,
  pp_goal(G1,VisIn,VisMid,NewCol),
  nl, tab(Col), write('-> '),
  pp_goal(G2,VisMid,VisMid2,NewCol),
  nl, tab(Col), write(';  '),
  pp_goal(G3,VisMid2,VisOut,NewCol),
  nl, tab(Col), write(')').
pp_goal((Goal1;Goal2),VisIn,VisOut,Col):-
  !, write('( '), NewCol is Col + 2,
  pp_goal(Goal1,VisIn,VisMid,NewCol),
  nl, tab(Col), write('; '),
  pp_goal(Goal2,VisMid,VisOut,NewCol),
  nl, tab(Col), write(')').
pp_goal((Goal1,Goal2),VisIn,VisOut,Col):-
  !, pp_goal(Goal1,VisIn,VisMid,Col), write(','),
  nl, tab(Col), pp_goal(Goal2,VisMid,VisOut,Col).
pp_goal(prolog(Hook),Vis,Vis,_) :-
  !, write(prolog(Hook)).
pp_goal(Desc1 =@ Desc2,VisIn,VisOut,Col) :-
  !, write('(  '),
  NewCol is Col+3,
  pp_fs(Desc1,VisIn,VisMid,NewCol), nl, tab(Col),
  write('=@'), nl, tab(NewCol),
  pp_fs(Desc2,VisMid,VisOut,NewCol), nl, tab(Col),
  write(')').
pp_goal((G1 -> G2),VisIn,VisOut,Col) :-
  !, write('(  '),  NewCol is Col + 3,
  pp_goal(G1,VisIn,VisMid,NewCol),
  nl, tab(Col), write('-> '),
  pp_goal(G2,VisMid,VisOut,NewCol),
  nl, tab(Col), write(')').
pp_goal(Goal,VisIn,VisOut,Col):-  % also handles !
  Goal =.. [Rel|Args],
  write(Rel),
  ( Args = []
    -> VisOut = VisIn
  ; write('('),
    name(Rel,Name),
    length(Name,N),
    NewCol is Col+N+1,
    pp_goal_args(Args,VisIn,VisOut,NewCol)
  ).

pp_goal_args([],Vis,Vis,_):-
  write(')').
pp_goal_args([Arg],VisIn,VisOut,Col):-
  !, pp_fs(Arg,VisIn,VisOut,Col), write(')').
pp_goal_args([Arg|Args],VisIn,VisOut,Col):-
  pp_fs(Arg,VisIn,VisMid,Col), write(','), nl, tab(Col),
  pp_goal_args(Args,VisMid,VisOut,Col).

satisfy_dtrs((cat> Desc),[Tag-bot|DtrCatsRest],DtrCatsRest,
             [(cat> Tag-bot)],IqsIn,IqsOut):-
  !, add_to(Desc,Tag,bot,IqsIn,IqsOut).
% 5/1/96 - Octav -- added clause for sem_head> label
satisfy_dtrs((sem_head> Desc),[Tag-bot|DtrCatsRest],DtrCatsRest,
             [(sem_head> Tag-bot)],IqsIn,IqsOut):-
  !, add_to(Desc,Tag,bot,IqsIn,IqsOut).
satisfy_dtrs((cats> Descs),[Tag-bot|DtrCatsRest],DtrCatsRest,
             [(cats> Tag-bot)],IqsIn,IqsOut) :-
  !, add_to(Descs,Tag,bot,IqsIn,IqsOut).
satisfy_dtrs((goal> GoalDesc),DtrCats,DtrCatsRest,
             [(goal> Goal)],IqsIn,IqsOut):-
  !, satisfy_dtrs_goal(GoalDesc,DtrCats,DtrCatsRest,Goal,IqsIn,IqsOut).
% 6/1/97 - Octav -- added clause for sem_goal> label
satisfy_dtrs((sem_goal> GoalDesc),DtrCats,DtrCatsRest,
             [(sem_goal> Goal)],IqsIn,IqsOut):-
  !, satisfy_dtrs_goal(GoalDesc,DtrCats,DtrCatsRest,Goal,IqsIn,IqsOut).
satisfy_dtrs(((cat> Desc),Dtrs),[Tag-bot|DtrCatsMid],DtrCatsRest,
             [(cat> Tag-bot)|DtrsSats],IqsIn,IqsOut):-
  !, add_to(Desc,Tag,bot,IqsIn,IqsMid),
  satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,IqsMid,IqsOut).
% 5/1/96 - Octav -- added clause for sem_head> label
satisfy_dtrs(((sem_head> Desc),Dtrs),[Tag-bot|DtrCatsMid],DtrCatsRest,
             [(sem_head> Tag-bot)|DtrsSats],IqsIn,IqsOut):-
  !, add_to(Desc,Tag,bot,IqsIn,IqsMid),
  satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,IqsMid,IqsOut).
satisfy_dtrs(((cats> Descs),Dtrs),[Tag-bot|DtrCatsMid],DtrCatsRest,
             [(cats> Tag-bot)|DtrsSats],IqsIn,IqsOut):-
  !, add_to(Descs,Tag,bot,IqsIn,IqsMid),
  satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,IqsMid,IqsOut).
satisfy_dtrs(((goal> GoalDesc),Dtrs),DtrCats,DtrCatsRest,
              [goal> Goal|DtrsSats],IqsIn,IqsOut):-
  satisfy_dtrs_goal(GoalDesc,DtrCats,DtrCatsMid,Goal,IqsIn,IqsMid),
  satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,IqsMid,IqsOut).
% 6/1/97 - Octav -- added clause for sem_goal> label
satisfy_dtrs(((sem_goal> GoalDesc),Dtrs),DtrCats,DtrCatsRest,
              [sem_goal> Goal|DtrsSats],IqsIn,IqsOut):-
  satisfy_dtrs_goal(GoalDesc,DtrCats,DtrCatsMid,Goal,IqsIn,IqsMid),
  satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,IqsMid,IqsOut).

satisfy_dtrs_goal((GD1,GD2),DtrCats,DtrCatsRest,
                  (G1,G2),IqsIn,IqsOut):-
  !, satisfy_dtrs_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid),
  satisfy_dtrs_goal(GD2,DtrCatsMid,DtrCatsRest,G2,IqsMid,IqsOut).
satisfy_dtrs_goal((GD1 -> GD2 ; GD3),DtrCats,DtrCatsRest,
                  (G1 -> G2 ; G3),IqsIn,IqsOut) :-
  !, satisfy_dtrs_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid),
  satisfy_dtrs_goal(GD2,DtrCatsMid,DtrCatsMid2,G2,IqsMid,IqsMid2),
  satisfy_dtrs_goal(GD3,DtrCatsMid2,DtrCatsRest,G3,IqsMid2,IqsOut).
satisfy_dtrs_goal((GD1;GD2),DtrCats,DtrCatsRest,
                  (G1;G2),IqsIn,IqsOut):-
  !, satisfy_dtrs_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid),
  satisfy_dtrs_goal(GD2,DtrCatsMid,DtrCatsRest,G2,IqsMid,IqsOut).
satisfy_dtrs_goal((\+ GD1),DtrCats,DtrCatsRest,
                  (\+ G1),IqsIn,IqsOut):-
  !, satisfy_dtrs_goal(GD1,DtrCats,DtrCatsRest,G1,IqsIn,IqsOut).
satisfy_dtrs_goal(prolog(Hook),DtrCats,DtrCats,prolog(Hook),Iqs,Iqs) :-
  !.
satisfy_dtrs_goal((GD1 -> GD2),DtrCats,DtrCatsRest,
                  (G1 -> G2),IqsIn,IqsOut) :-
  !, satisfy_dtrs_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid),
  satisfy_dtrs_goal(GD2,DtrCatsMid,DtrCatsRest,G2,IqsMid,IqsOut).
satisfy_dtrs_goal(AtGD,DtrCats,DtrCatsRest,AtG,IqsIn,IqsOut):-
  AtGD =.. [Rel|ArgDescs],
  same_length(ArgDescs,Args),
  AtG =.. [Rel|Args],
  satisfy_dtrs_goal_args(ArgDescs,DtrCats,DtrCatsRest,Args,IqsIn,IqsOut).

satisfy_dtrs_goal_args([],DtrCats,DtrCats,[],Iqs,Iqs).
satisfy_dtrs_goal_args([D|Ds],[Tag-bot|DtrCats],DtrCatsRest,[Tag-bot|Args],
                       IqsIn,IqsOut):-
  add_to(D,Tag,bot,IqsIn,IqsMid),
  satisfy_dtrs_goal_args(Ds,DtrCats,DtrCatsRest,Args,IqsMid,IqsOut).
  

% ==============================================================================
% Pretty Printing
% ==============================================================================

% ------------------------------------------------------------------------------
% pp_fs(FS:<fs>,Iqs:<ineq>s)
% ------------------------------------------------------------------------------
% pretty prints FS with inequations Iqs
% ------------------------------------------------------------------------------
pp_fs(FS,Iqs):-
  \+ \+ ( duplicates(FS,Iqs,[],_,[],_,0,_),
          nl, 
          pp_fs(FS,[],VisOut,0),
          nl,
          pp_iqs(Iqs,VisOut,_,0)).

pp_fs(FS,Iqs,N):-
  \+ \+ ( duplicates(FS,Iqs,[],_,[],_,0,_),
          nl, 
          tab(N), pp_fs(FS,[],VisOut,N),
          nl,
          pp_iqs(Iqs,VisOut,_,N)).

% ------------------------------------------------------------------------------
% duplicates(FS:<fs>, Iqs:<ineq>s, DupsIn:<ref>s, DupsOut:<ref>s, 
%            VisIn:<ref>s, VisOut:<ref>s, NumIn:<int>, NumOut:<int>)
% ------------------------------------------------------------------------------
% DupsOut is the result of adding the duplicate references
% in FS and Iqs to those in DupsIn.  VisIn are those nodes already
% visited and VisOut are those visited in FS.  NumIn is
% the current number for variables and NumOut is the
% next available after numbering only the shared refs in FS.
% ------------------------------------------------------------------------------
duplicates(FS,Iqs,DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut) :-
  duplicates_fs(FS,DupsIn,DupsMid,VisIn,VisMid,NumIn,NumMid),
  duplicates_iqs(Iqs,DupsMid,DupsOut,VisMid,VisOut,NumMid,NumOut).
duplicates_fs(FS,DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut):-
  deref_pp(FS,Ref,SVs),
  ( member_eq(Ref,DupsIn)
    -> DupsOut = DupsIn, VisOut = VisIn, NumOut = NumIn
     ; (member_eq(Ref,VisIn)
        -> (DupsOut = [Ref|DupsIn], VisIn = VisOut, 
            Ref = NumIn, NumOut is NumIn + 1)
         ; ((SVs = a_ _)
            -> DupsIn = DupsOut, VisOut = [Ref|VisIn], NumOut = NumIn
             ; (SVs =.. [_|Vs],
                duplicates_list(Vs,[],DupsIn,DupsOut,[Ref|VisIn],VisOut,
                                NumIn,NumOut))))).
duplicates_iqs([],Dups,Dups,Vis,Vis,Num,Num).
duplicates_iqs([Iq|Iqs],DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut) :-
  duplicates_ineq(Iq,DupsIn,DupsMid,VisIn,VisMid,NumIn,NumMid),
  duplicates_iqs(Iqs,DupsMid,DupsOut,VisMid,VisOut,NumMid,NumOut).

duplicates_ineq(done,Dups,Dups,Vis,Vis,Num,Num).
duplicates_ineq(ineq(Tag1,SVs1,Tag2,SVs2,Ineqs),DupsIn,DupsOut,VisIn,VisOut,
                NumIn,NumOut):-
  duplicates_fs(Tag1-SVs1,DupsIn,DupsMid1,VisIn,VisMid1,NumIn,NumMid1),
  duplicates_fs(Tag2-SVs2,DupsMid1,DupsMid2,VisMid1,VisMid2,NumMid1,NumMid2),
  duplicates_ineq(Ineqs,DupsMid2,DupsOut,VisMid2,VisOut,NumMid2,NumOut).

duplicates_list([],Iqs,DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut) :-
  duplicates_iqs(Iqs,DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut).
duplicates_list([V|Vs],Iqs,DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut):-
  duplicates_fs(V,DupsIn,DupsMid,VisIn,VisMid,NumIn,NumMid),
  duplicates_list(Vs,Iqs,DupsMid,DupsOut,VisMid,VisOut,NumMid,NumOut).

% ------------------------------------------------------------------------------
% pp_iqs(Iqs:<ineq>s, VisIn:<var>s, VisOut:<var>s,Col:<int>)
% ------------------------------------------------------------------------------
% pretty-prints a list of inequations, indented Col columns
%-------------------------------------------------------------------------------
pp_iqs([],Vis,Vis,_).
pp_iqs([ineq(Tag1,SVs1,Tag2,SVs2,Ineqs)|Iqs],VisIn,VisOut,Col) :-
  (Ineqs = done -> true
   ;write('(')),
  pp_ineq(ineq(Tag1,SVs1,Tag2,SVs2,Ineqs),VisIn,VisMid,Col),
  (Ineqs = done -> true
   ;write(')')),
  (Iqs = []
   -> nl
   ; write(','),
     nl,
     pp_iqs(Iqs,VisMid,VisOut,Col)).

pp_ineq(done,Vis,Vis,_).
pp_ineq(ineq(Tag1,SVs1,Tag2,SVs2,Ineqs),VisIn,VisOut,Col) :-
  tab(Col),pp_fs(Tag1-SVs1,VisIn,VisMid1,Col),
  write('  =\\=  '),
  NewCol is Col+7,
  pp_fs(Tag2-SVs2,VisMid1,VisMid2,NewCol),
  nl,
  (Ineqs = done -> true
   ;write(';')),
  pp_ineq(Ineqs,VisMid2,VisOut,Col).

% ------------------------------------------------------------------------------
% pp_fs(FS:<fs>,VisIn:<var>s, VisOut:<var>s, Col:<int>)
% ------------------------------------------------------------------------------
% prints FS where VisOut is the result of adding all of the
% referents of substructures in FS to VisIn
% Col is where printing begins for FS
% ------------------------------------------------------------------------------
pp_fs(FS,VisIn,VisOut,Col):-
  deref_pp(FS,Ref,SVs),
  ( var(Ref) -> true                            % print ref if shared (nonvar)
  ; write('['), write(Ref), write(']'),
    ( member_eq(Ref,VisIn) -> true
    ; write(' ')
    )
  ),
  ( member_eq(Ref,VisIn) 
    -> VisOut = VisIn
     ; (SVs = a_ X)
       -> (no_write_type_flag(a_ X)
           -> true
            ; write(a_ X)
          ),
          VisOut = [Ref|VisIn]
        ; SVs =.. [Type|Vs],              % print FS if not already visited
          approps(Type,FRs),
          ( no_write_type_flag(Type)
            -> pp_vs_unwritten(FRs,Vs,[Ref|VisIn],VisOut,Col)
          ; write(Type),   
            pp_vs(FRs,Vs,[Ref|VisIn],VisOut,Col) 
          )
  ).

:- dynamic no_write_type_flag/1.
:- dynamic no_write_feat_flag/1.

write_types:-
  write_type(_).

write_feats:-
  write_feat(_).

write_type(Type):-
  retractall(no_write_type_flag(Type)).

write_feat(Feat):-
  retractall(no_write_feat_flag(Feat)).

no_write_type(Type):-
  retractall(no_write_type_flag(Type)),
  assert(no_write_type_flag(Type)).

no_write_feat(Feat):-
  retractall(no_write_feat_flag(Feat)),
  assert(no_write_feat_flag(Feat)).

% ------------------------------------------------------------------------------
% deref_pp(FS1:<fs>, FS2:<d_fs>)
% ------------------------------------------------------------------------------
% FS2 is the result of dereferencing FS1 where Ref might
% be constant due to printing refs
% ------------------------------------------------------------------------------
deref_pp(Ref-SVs,RefOut,SVsOut):-
   (nonvar(Ref), \+ atomic(Ref))
   -> deref_pp(Ref,RefOut,SVsOut)
    ; RefOut = Ref, SVsOut = SVs.

% ------------------------------------------------------------------------------
% pp_vs(FRs:<fs>, Vs:<vs>, Dups:<var>s, 
%        VisIn:<var>s, VisOut:<var>s, Col:<int>)
% ------------------------------------------------------------------------------
% prints Vs at Col 
% ------------------------------------------------------------------------------
pp_vs([],[],Vis,Vis,_).
pp_vs([F:_|FRs],[V|Vs],VisIn,VisOut,Col):-
  ( no_write_feat_flag(F),
    VisMid = VisIn 
  -> true
  ; nl, tab(Col),
    write_feature(F,LengthF), 
    NewCol is Col + LengthF +1,
    pp_fs(V,VisIn,VisMid,NewCol)
  ),
  pp_vs(FRs,Vs,VisMid,VisOut,Col).

pp_vs_unwritten([],[],Vis,Vis,_).
pp_vs_unwritten([F:_|FRs],[V|Vs],VisIn,VisOut,Col):-
  ( no_write_feat_flag(F),
    VisMid = VisIn
  -> true
  ; write_feature(F,LengthF), 
    NewCol is Col + LengthF +1,
    pp_fs(V,VisIn,VisMid,NewCol)
  ),
  pp_vs(FRs,Vs,VisMid,VisOut,Col).

write_feature(F,LengthF):-
  name(F,NameF),
  count_and_capitalize(NameF,0,LengthF),
  write(' ').

count_and_capitalize([],Length,Length).
count_and_capitalize([L|Ls],LengthIn,Length):-
  capitalize(L,LCap),
  write(LCap),
  LengthInPlus1 is LengthIn + 1,
  count_and_capitalize(Ls,LengthInPlus1,Length).

capitalize(X,XCap):-
  ( (name(a,[Name_a]), name(z,[Name_z]),
     Name_a =< X, X =< Name_z)
    -> name('A',[Name_A]),  
       Gap is Name_A - Name_a,
       NameXCap is X + Gap,
       name(XCap,[NameXCap])
     ; name(XCap,[X])
  ).


% ==============================================================================
% Utilities
% ==============================================================================

% ------------------------------------------------------------------------------
% cat_atoms/3
% ------------------------------------------------------------------------------
cat_atoms(A1,A2,A3):-
  name(A1,L1),
  name(A2,L2),
  append(L1,L2,L3),
  name(A3,L3).

% ------------------------------------------------------------------------------
% esetof(X:Alpha, Goal:<goal>, Xs:<list(Alpha)>)
% ------------------------------------------------------------------------------
% setof returning empty list if no solutions
% ------------------------------------------------------------------------------
esetof(X,Goal,Xs) :-
  if(setof(X,Goal,Xs),
     true,
     (Xs = [])).

% ------------------------------------------------------------------------------
% member_eq(X:<term>, Xs:<term>s)
% ------------------------------------------------------------------------------
% X is strictly == equal to a member of list Xs
% ------------------------------------------------------------------------------
member_eq(X,[Y|Ys]):-
    X==Y
  ; member_eq(X,Ys).

% ------------------------------------------------------------------------------
% select_eq(X:<term>, Xs:<term>s, XsLeft:<term>s)
% ------------------------------------------------------------------------------
% X is strictly == equal to a member of list Xs with XsLeft left over
% ------------------------------------------------------------------------------
select_eq(X,[Y|Ys],Zs):-
    X==Y,
    Zs = Ys
  ; Zs = [Y|Zs2],
    select_eq(X,Ys,Zs2).

% ------------------------------------------------------------------------------
% reverse_count(ListIn:<list>,Acc:<list>,ListOut:<list>,
%               CountIn:<int>,CountOut:<int>)
% ------------------------------------------------------------------------------
% using accumulators, reverses ListIn into ListOut, with initial segment
% Acc;  CountIn is current count (of Acc) and CountOut is result;  call
% by:  reverse_count(ListIn,[],ListOut,0,Count)
% ------------------------------------------------------------------------------
reverse_count([],Xs,Xs,Count,Count).
reverse_count([X|Xs],Ys,Zs,CountIn,Count):-
  CountInPlus1 is CountIn+1,
  reverse_count(Xs,[X|Ys],Zs,CountInPlus1,Count).

% ------------------------------------------------------------------------------
% query_proceed
% ------------------------------------------------------------------------------
% prompts user for n. response, otherwise proceeds
% ------------------------------------------------------------------------------
query_proceed:-
  ttynl, write('ANOTHER?  '), ttyflush, read(n).

% ------------------------------------------------------------------------------
% number_display/2
% ------------------------------------------------------------------------------
number_display([],M):-
  !,write(M).  % need cut for variable 1st arguments
number_display([W|Ws],N):-
  write(N), write(' '), write(W), write(' '),
  SN is N + 1,
  number_display(Ws,SN).

% ------------------------------------------------------------------------------
% error_msg(Goal:<goal>)
% ------------------------------------------------------------------------------
% tells user, solves Goal, then goes back to old file being told
% ------------------------------------------------------------------------------
error_msg(Goal):-
  telling(FileName),
  tell(user),
  Goal,
  told,
  tell(FileName),
  fail.  

% ------------------------------------------------------------------------------
% if_error(Msg,Cond)
% ------------------------------------------------------------------------------
% if condition Cond holds, provides Msg as error message;  always succeeds
% ------------------------------------------------------------------------------
if_error(Msg,Cond):-
  telling(FileName),
  tell(user),
  ( Cond, 
    ttynl, 
    write_list(['  **ERROR: '|Msg]),
    ttynl, ttynl,
    fail
  ; told,
    tell(FileName)
  ).

% ------------------------------------------------------------------------------
% if_warning_else_fail(Msg,Cond)
% ------------------------------------------------------------------------------
% if Cond holds, provides warning message Msg, otherwise fails
% ------------------------------------------------------------------------------
if_warning_else_fail(Msg,Cond):-
  if_warning(Msg,Cond),
  Cond.

% ------------------------------------------------------------------------------
% if_warning(Msg,Cond)
% ------------------------------------------------------------------------------
% if condition Cond holds, prints out Msg;  always succeeds
% ------------------------------------------------------------------------------
if_warning(Msg,Cond):-
  telling(FileName),
  tell(user),
  ( Cond, 
    write_list(['  *Warning: '|Msg]),
    ttynl,ttynl,
    fail
  ; told,
    tell(FileName)
  ).

% ------------------------------------------------------------------------------
% write_list(Xs)
% ------------------------------------------------------------------------------
% writes out elements of Xs with spaces between elements
% ------------------------------------------------------------------------------
write_list([]).
write_list([X|Xs]):-
  write(X), write(' '), write_list(Xs).

% ------------------------------------------------------------------------------
% query_user(Query)
% ------------------------------------------------------------------------------
% writes Query and then tries to read a y. from user
% ------------------------------------------------------------------------------
query_user(QueryList):-
  ttynl, ttynl, write_list(QueryList),
  read(y).

% ------------------------------------------------------------------------------
% duplicated(X,Xs)
% ------------------------------------------------------------------------------
% holds if X occurs more than once in Xsd
% ------------------------------------------------------------------------------
duplicated(X,[X|Xs]):-
  member(X,Xs).
duplicated(X,[_|Xs]):-
  duplicated(X,Xs).

% ------------------------------------------------------------------------------
% feat_cycle(S:<type>, Fs:<path>)
% ------------------------------------------------------------------------------
% holds if following the path Fs in the appropriateness definitions
% leads from S to S.  calls an auxiliary function which avoids infinite
% loops and tracks the features so far followed in reverse with an accumulator
% ------------------------------------------------------------------------------
feat_cycle(S,Fs):-
  feat_cycle2(S,S,[S],[],Fs).

% ------------------------------------------------------------------------------
% feat_cycle2(S1:<type), S2:<type), Ss:<list(<type>)>, 
%             FsIn:<path>, FsOut:<path>)
% ------------------------------------------------------------------------------
% assumes following reverse of FsIn led to S2 from S1, visiting
% Ss along the way.  FsOut is the result of appending a path that will
% get from S2 back to S1 to the reverse of FsIn
% ------------------------------------------------------------------------------
feat_cycle2(S1,S2,_Ss,FsIn,FsOut):-
  approp(F,S2,S1),
  reverse([F|FsIn],FsOut).
feat_cycle2(S1,S2,Ss,FsIn,FsOut):-
  approp(F,S2,S3),
  \+ member(S3,Ss),
  feat_cycle2(S1,S3,[S2|Ss],[F|FsIn],FsOut).

% 5/1/96 - Octav -- added the generator

% ==============================================================================
% Generator
% ==============================================================================

% ------------------------------------------------------------------------------
% split_dtrs(+Dtrs:<dtr>s, -Head:<desc>,
%            -SemGoalBefore:<goal>, -SemGoalAfter:<goal>,
%            -DtrsBefore:<dtr>s, -DtrsAfter:<dtr>s)
% ------------------------------------------------------------------------------
% splits the RHS of a chain rule into Head, SemGoalBefore the Head, SemGoalAfter
% the Head, DtrsBefore the Head, and DtrsAfter the Head
% ------------------------------------------------------------------------------
split_dtrs((sem_goal> SemGoalBefore,sem_head> Head,sem_goal> SemGoalAfter,
            DtrsAfter),
           Head,SemGoalBefore,SemGoalAfter,empty,DtrsAfter) :- !.
split_dtrs((sem_goal> SemGoalBefore,sem_head> Head,sem_goal> SemGoalAfter),
           Head,SemGoalBefore,SemGoalAfter,empty,empty) :- !.
split_dtrs((sem_goal> SemGoalBefore,sem_head> Head,DtrsAfter),
           Head,SemGoalBefore,empty,empty,DtrsAfter) :- !.
split_dtrs((sem_goal> SemGoalBefore,sem_head> Head),
           Head,SemGoalBefore,empty,empty,empty) :- !.
split_dtrs((sem_head> Head,sem_goal> SemGoalAfter,DtrsAfter),
           Head,empty,SemGoalAfter,empty,DtrsAfter) :- !.
split_dtrs((sem_head> Head,sem_goal> SemGoalAfter),
           Head,empty,SemGoalAfter,empty,empty) :- !.
split_dtrs((sem_head> Head,DtrsAfter),Head,empty,empty,empty,DtrsAfter) :- !.
split_dtrs((sem_head> Head),Head,empty,empty,empty,empty) :- !.
split_dtrs((Dtr,RestDtrs),Head,SemGoalBefore,SemGoalAfter,
           (Dtr,DtrsBefore),DtrsAfter) :- !,
  split_dtrs(RestDtrs,Head,SemGoalBefore,SemGoalAfter,DtrsBefore,DtrsAfter).

% ------------------------------------------------------------------------------
% Run-time generation support
% ------------------------------------------------------------------------------

% ------------------------------------------------------------------------------
% gen(+Cat:<desc>)
% gen(+Tag:<tag>, +SVs:<svs>, +Iqs:<ineq>)
% ------------------------------------------------------------------------------
% top-level user calls to generate a sentence from a descriptor Cat
% or a FS specified by Tag, SVs, Iqs
% ------------------------------------------------------------------------------
gen(Cat) :-
  add_to(Cat,Tag,bot,[],Iqs),
  gen(Tag,bot,Iqs).

gen(Tag,SVs,Iqs) :-
%  secret_noadderrs,
  nl, write('CATEGORY: '), nl, ttyflush,
  pp_fs(Tag-SVs,Iqs), nl,
  gen(Tag,SVs,Iqs,Words),
  nl, write('STRING: '),
  nl, write_list(Words),
  nl, query_proceed.
%,
%  secret_adderrs

% ------------------------------------------------------------------------------
% gen(+Tag:<tag>, +SVs:<svs>, +IqsIn:<ineq>s, -Words:<word>s)
% ------------------------------------------------------------------------------
% top-level functional interface for the generator
% generates the list of Words from the semantic specification of Tag-SVs,Iqs
% ------------------------------------------------------------------------------
gen(Tag,SVs,IqsIn,Words) :-
%  fully_deref_prune(Tag,SVs,NewTag,NewSVs,IqsIn,IqsPrunned),
  generate(Tag,SVs,IqsIn,IqsOut,Words,[]),
  deref(Tag,SVs,TagOut,SVsOut),
  extensionalise(TagOut,SVsOut,IqsOut),
  check_inequal(IqsOut,_).   

% ------------------------------------------------------------------------------
% generate(+Tag:<tag>, +SVs:<svs>, +IqsIn:<ineq>s, -IqsOut:<ineq>s,
%          +Words:<word>s, +RestWords:<word>s)
% ------------------------------------------------------------------------------
% recursively generates the difference list Words-RestWords from the root
% Tag-SVs,IqsIn
% ------------------------------------------------------------------------------
generate(Tag,SVs,IqsIn,IqsOut,Words,RestWords) if_h
    [GoalIndex,GoalPivot,
     check_inequal(IqsMid2,IqsMid3),
     non_chain_rule(PivotTag,bot,Tag,SVs,IqsMid3,IqsOut,Words,
                    RestWords)] :-
  semantics(Pred),
  cat_atoms('fs_',Pred,CompiledPred),
  functor(GoalIndex,CompiledPred,4),
  arg(1,GoalIndex,Tag-SVs),
  arg(2,GoalIndex,IndexTag-bot),
  arg(3,GoalIndex,IqsIn),
  arg(4,GoalIndex,IqsMid),
  functor(GoalPivot,CompiledPred,4),
  arg(1,GoalPivot,PivotTag-bot),
  arg(2,GoalPivot,IndexTag-bot),
  arg(3,GoalPivot,IqsMid),
  arg(4,GoalPivot,IqsMid2).

% ------------------------------------------------------------------------------
% generate_list(+Sort:<sort>, +Vs:<vs>, +IqsIn:<ineq>s, -IqsOut:<ineq>s,
%               -Words:<word>s, +RestWords:<word>s)
% ------------------------------------------------------------------------------
% generates a list of words Words-RestWords from a variable list of descriptions
% Sort(Vs)
% ------------------------------------------------------------------------------
generate_list(e_list,_,Iqs,Iqs,Words,Words) :- 
  !.
generate_list(Sort,[HdFS,TlFS],IqsIn,IqsOut,Words,RestWords) :-
  sub_type(ne_list,Sort), 
  !,deref(HdFS,DtrTag,DtrSVs),
  generate(DtrTag,DtrSVs,IqsIn,IqsDtr,Words,MidWords),
  deref(TlFS,_,TlSVs), TlSVs =.. [TlSort|TlVs],
  generate_list(TlSort,TlVs,IqsDtr,IqsOut,MidWords,RestWords).
generate_list(Sort,_,_,_,_,_) :-
  error_msg((nl,write('error: cats> value with sort, '),write(Sort),
            write(' is not a valid list argument'))).


% ------------------------------------------------------------------------------
% Compiler
% ------------------------------------------------------------------------------

:- dynamic current_chain_length/1.
current_chain_length(4).

% ------------------------------------------------------------------------------
% chain_length(N:<int>)
% ------------------------------------------------------------------------------
% asserts chain_length/1 to N -- controls depth of chain rules application
% ------------------------------------------------------------------------------
chain_length(N):-
  retractall(current_chain_length(_)),
  assert(current_chain_length(N)).

% ------------------------------------------------------------------------------
% non_chain_rule(+PivotTag:<tag>,
%                +PivotSVs:<svs>, +RootTag:<tag>, +RootSVs:<svs>,
%                +IqsIn:<ineq>s, -IqsOut:<ineq>s,
%                -Words:<word>s, -RestWords:<word>s)
% ------------------------------------------------------------------------------
% compiles nonheaded grammar rules, lexical entries and empty categories into
% non_chain_rule predicates which unifies the mother against the
% PivotTag-PivotSVs FS, generates top-down the RHS, and connects the mother FS
% to the next chain rule
% the result Words-RestWords is the final list of words which includes the list
% NewWords-RestNewWords corresponding to the expansion of the current rule
% ------------------------------------------------------------------------------
non_chain_rule(PivotTag,PivotSVs,RootTag,RootSVs,IqsIn,IqsOut,
               Words,RestWords) if_b SubGoals :-
  current_predicate(empty,empty(_)),
  empty_assoc(VarsIn),
  empty(Desc),
  compile_desc(Desc,PivotTag,PivotSVs,IqsIn,IqsMid,SubGoalsMid,
               [check_inequal(IqsMid,IqsMid2),
                current_chain_length(Max),
                \+ \+ chained(0,Max,PivotTag,PivotSVs,RootTag,RootSVs,IqsMid2),
                chain_rule(0,Max,PivotTag,PivotSVs,RootTag,RootSVs,IqsMid2,
                        IqsOut,Words,Words,Words,RestWords)],true,VarsIn,_,
                        FSPal,[],FSsOut),
  build_fs_palette(FSsOut,FSPal,SubGoals,SubGoalsMid,[]).
non_chain_rule(PivotTag,PivotSVs,RootTag,RootSVs,IqsIn,IqsOut,
               Words,RestWords) if_b SubGoals :-
(secret_noadderrs,fail % turn off adderrs for lexical compilation
; current_predicate('--->', (_ ---> _)),
  empty_assoc(VarsIn),
  (WordStart ---> DescStart),
  curr_lex_rule_depth(LRMax),
  gen_lex_close(0,LRMax,WordStart,DescStart,WordOut,DescOut,[],IqsLex),
  append(IqsLex,IqsIn,IqsMid),
  compile_desc(DescOut,PivotTag,PivotSVs,IqsMid,IqsMid2,SubGoalsMid,
               [check_inequal(IqsMid2,IqsMid3),
                current_chain_length(Max),
                \+ \+ chained(0,Max,PivotTag,PivotSVs,RootTag,RootSVs,IqsMid3),
                chain_rule(0,Max,PivotTag,PivotSVs,RootTag,RootSVs,IqsMid3,
                           IqsOut,[WordOut|NewWords],NewWords,Words,
                           RestWords)],true,VarsIn,_,FSPal,[],FSsOut),
  build_fs_palette(FSsOut,FSPal,SubGoals,SubGoalsMid,IqsLex)
; secret_adderrs,fail).  % turn on again
non_chain_rule(PivotTag,PivotSVs,RootTag,RootSVs,IqsIn,IqsOut,
               Words,RestWords) if_b PGoals :-
  current_predicate(rule, (_ rule _)),
  empty_assoc(VarsIn),
  (_RuleName rule Mother ===> Dtrs),
  \+ split_dtrs(Dtrs,_,_,_,_,_),  % i.e., not a chain rule
  compile_desc(Mother,PivotTag,PivotSVs,IqsIn,IqsMother,
               PGoalsMid,[check_inequal(IqsMother,IqsMotherCkd),
                          current_chain_length(Max),
                          \+ \+ chained(0,Max,PivotTag,PivotSVs,RootTag,
                                        RootSVs,IqsMotherCkd)
                      |PGoalsDtrs],true,VarsIn,VarsMid,FSPal,[],FSsMid),
  compile_gen_dtrs(Dtrs,IqsMotherCkd,IqsDtrs,HeadWords,RestHeadWords,
                   PGoalsDtrs,
                   [chain_rule(0,Max,PivotTag,PivotSVs,RootTag,RootSVs,IqsDtrs,
                               IqsOut,HeadWords,RestHeadWords,Words,
                               RestWords)],true,VarsMid,_,FSPal,FSsMid,FSsOut),
  build_fs_palette(FSsOut,FSPal,PGoals,PGoalsMid,[]).

% ------------------------------------------------------------------------------
% chain_rule(+PivotTag:<tag>, +PivotSVs:<svs>, +RootTag:<tag>, +RootSVs:<svs>,
%            +IqsIn:<ineq>s, -IqsOut:<ineq>s, +HeadWords:<word>s,
%            +RestHeadWords:<word>s, -Words:<word>s, RestWords:<word>s)
% ------------------------------------------------------------------------------
% compiles headed grammar rules into chain_rule predicates which unify the head
% agains the PivotTag-PivotSVS FS, generates top-down the rest of the RHS,
% and connects the mother FS to the next chain rule
% the result is the list Words-RestWords which includes the sublist
% HeadWords-RestHeadWords corresponding to the head
% ------------------------------------------------------------------------------
chain_rule(_,_,PivotTag,PivotSVs,RootTag,RootSVs,IqsIn,  % keep this clause
    IqsOut,Words,RestWords,Words,RestWords) if_b   % first after multi-hashing 
  [ud(PivotTag,PivotSVs,RootTag,RootSVs,IqsIn,IqsOut)]. 
chain_rule(N,Max,PivotTag,PivotSVs,RootTag,RootSVs,IqsIn,IqsOut,
           HeadWords,RestHeadWords,Words,RestWords) if_b 
  [N < Max|PGoalsSG] :-
  current_predicate(rule,(_ rule _)),
  empty_assoc(VarsIn),
  (_RuleName rule Mother ===> Dtrs),
  split_dtrs(Dtrs,Head,SGBefore,SGAfter,DtrsBefore,DtrsAfter),
  ((SGBefore == empty)
  -> IqsSGBefore = IqsIn, PGoalsHead = PGoalsSGBefore, VarsMid = VarsIn,
     FSsMid = []
   ; compile_body(SGBefore,IqsIn,IqsSGBefore,PGoalsSGBefore,PGoalsHead,true,
                  VarsIn,VarsMid,FSPal,[],FSsMid)),
  compile_desc(Head,PivotTag,PivotSVs,IqsSGBefore,IqsHead,PGoalsHead,
            [check_inequal(IqsHead,IqsHeadCkd)|PGoalsMother],true,VarsMid,
            VarsMid2,FSPal,FSsMid,FSsMid2),
  ((SGAfter == empty)
  -> IqsSGAfter = IqsHeadCkd, PGoalsSGAfter = PGoalsMother, VarsMid3=VarsMid2,
     FSsMid3 = FSsMid2
   ; compile_body(SGAfter,IqsHeadCkd,IqsSGAfter,PGoalsMother,PGoalsSGAfter,
                  true,VarsMid2,VarsMid3,FSPal,FSsMid2,FSsMid3)),
  compile_desc(Mother,MotherTag,bot,IqsSGAfter,IqsMother,PGoalsSGAfter,
               [check_inequal(IqsMother,IqsMotherCkd),
                SN is N + 1,
                \+ \+ chained(SN,Max,MotherTag,bot,RootTag,RootSVs,
                              IqsMotherCkd)
               |PGoalsLeft],true,VarsMid3,VarsMid4,FSPal,FSsMid3,FSsMid4),
  compile_gen_dtrs(DtrsBefore,IqsMotherCkd,IqsDtrsBefore,NewWords,HeadWords,
                   PGoalsLeft,PGoalsRight,true,VarsMid4,VarsMid5,FSPal,FSsMid4,
                   FSsMid5),
  compile_gen_dtrs(DtrsAfter,IqsDtrsBefore,IqsDtrsAfter,
                   RestHeadWords,RestNewWords,PGoalsRight,
                   [chain_rule(SN,Max,MotherTag,bot,RootTag,RootSVs,
                               IqsDtrsAfter,IqsOut,NewWords,RestNewWords,Words,
                               RestWords)],true,VarsMid5,_,FSPal,FSsMid5,FSsOut),
  build_fs_palette(FSsOut,FSPal,PGoalsSG,PGoalsSGBefore,[]).

% ------------------------------------------------------------------------------
% compile_gen_dtrs(+Dtrs:<desc>, +IqsIn:<ineq>s, -IqsOut:<ineq>s,
%                  -Words:<word>s, -RestWords:<word>s,
%                  -Goals:<goal>s, -GoalsRest:<goal>s, +VarsIn:<avl>,
%                  -VarsOut:<avl>, +FSPal:<var>, +FSsIn:<fs>s, -FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% compiles the top-down expansion of a sequence Dtrs of RHS items
% (daughters or goals)
% ------------------------------------------------------------------------------
compile_gen_dtrs(empty,IqsIn,IqsIn,Words,Words,PGoals,PGoals,_,Vars,Vars,_,FSs,
                 FSs) :- 
  !.
compile_gen_dtrs((cat> Dtr),IqsIn,IqsOut,Words,RestWords,
                 PGoalsDtr,PGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_desc(Dtr,Tag,bot,IqsIn,IqsDtr,PGoalsDtr,
                 [check_inequal(IqsDtr,IqsDtrCkd),
                  generate(Tag,bot,IqsDtrCkd,IqsOut,Words,RestWords)
                 |PGoalsRest],CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut).
compile_gen_dtrs((cat> Dtr,RestDtrs),IqsIn,IqsOut,Words,RestWords,
                 PGoalsDtr,PGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_desc(Dtr,Tag,bot,IqsIn,IqsDtr,PGoalsDtr,
                 [check_inequal(IqsDtr,IqsDtrCkd),
                  generate(Tag,bot,IqsDtrCkd,IqsRest,Words,WordsMid)
                 |PGoalsDtrs],CBSafe,VarsIn,VarsMid,FSPal,FSsIn,FSsMid),
  compile_gen_dtrs(RestDtrs,IqsRest,IqsOut,WordsMid,RestWords,
                   PGoalsDtrs,PGoalsRest,CBSafe,VarsMid,VarsOut,FSPal,FSsMid,
                   FSsOut).
compile_gen_dtrs((goal> Goal),IqsIn,IqsOut,Words,Words,
                 PGoalsBody,PGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut) :-
  !,compile_body(Goal,IqsIn,IqsOut,PGoalsBody,PGoalsRest,CBSafe,VarsIn,
                 VarsOut,FSPal,FSsIn,FSsOut).
compile_gen_dtrs((goal> Goal,RestDtrs),IqsIn,IqsOut,Words,RestWords,
                 PGoalsBody,PGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut) :- 
  !,compile_body(Goal,IqsIn,IqsBody,PGoalsBody,PGoalsDtrs,CBSafe,VarsIn,
                 VarsMid,FSPal,FSsIn,FSsMid),
  compile_gen_dtrs(RestDtrs,IqsBody,IqsOut,Words,RestWords,
                   PGoalsDtrs,PGoalsRest,CBSafe,VarsMid,VarsOut,FSPal,FSsMid,
                   FSsOut).
compile_gen_dtrs((cats> Dtrs),IqsIn,IqsOut,Words,RestWords,
                 PGoalsDtrs,PGoalsRest,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut) :- 
  !,compile_desc(Dtrs,Tag,bot,IqsIn,IqsList,PGoalsDtrs,
                 [check_inequal(IqsList,IqsListCkd),
                  deref(Tag,bot,_,SVs),
                  SVs =.. [Sort|Vs],
                  generate_list(Sort,Vs,IqsListCkd,IqsOut,Words,RestWords)
                 |PGoalsRest],CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut).
compile_gen_dtrs((cats> Dtrs,RestDtrs),IqsIn,IqsOut,Words,RestWords,
                 PGoalsDtrs,PGoalsRest,VarsIn,VarsOut,FSPal,FSsIn,FSsOut) :- 
  !,compile_desc(Dtrs,Tag,bot,IqsIn,IqsList,PGoalsDtrs,
                 [check_inequal(IqsList,IqsListCkd),
                  deref(Tag,bot,_,SVs),
                  SVs =.. [Sort|Vs],
                  generate_list(Sort,Vs,IqsListCkd,IqsGen,Words,NewWords)
                 |PGoalsRestDtrs],CBSafe,VarsIn,VarsMid,FSPal,FSsIn,FSsMid),
  compile_gen_dtrs(RestDtrs,IqsGen,IqsOut,NewWords,RestWords,
                   PGoalsRestDtrs,PGoalsRest,CBSafe,VarsMid,VarsOut,FSPal,FSsMid,
                   FSsOut).

% ------------------------------------------------------------------------------
% chained(+PivotTag:<tag>, +PivotSVs:<svs>, +RootTag:<tag>,
%         +RootSVs:<svs>, +IqsIn:<ineq>s, -IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% checks whether PivotTag-PivotSVs and RootTag-RootSVs can be connected through
% a chain of grammar rules
% ------------------------------------------------------------------------------
chained(_,_,PivotTag,PivotSVs,RootTag,RootSVs,Iqs) if_b    % keep this clause
  [ud(PivotTag,PivotSVs,RootTag,RootSVs,Iqs,_)].    % first after multi-hashing
chained(N,Max,PivotTag,PivotSVs,RootTag,RootSVs,IqsIn) if_b [N<Max|PGoals] :-
  current_predicate(rule,(_ rule _)),
  empty_assoc(VarsIn),
  (_Rule rule Mother ===> Body),
  split_dtrs(Body,HeadIn,_,_,_,_),
  compile_desc(HeadIn,PivotTag,PivotSVs,IqsIn,IqsHead,PGoalsMid,
               [check_inequal(IqsHead,IqsHeadCkd)|PGoalsPivot],true,VarsIn,
               VarsMid,FSPal,[],FSsMid),
  compile_desc(Mother,NewPTag,bot,IqsHeadCkd,IqsMother,PGoalsPivot,
               [check_inequal(IqsMother,IqsMotherCkd),
                SN is N + 1,
                chained(SN,Max,NewPTag,bot,RootTag,RootSVs,IqsMotherCkd)],
               true,VarsMid,_,FSPal,FSsMid,FSsOut),
  build_fs_palette(FSsOut,FSPal,PGoals,PGoalsMid,[]).

% ------------------------------------------------------------------------------
% gen_lex_close(+N:<int>, +Max:<int>, +WordIn:<word>, +MotherIn:<desc>,
%               -WordOut<word>, -MotherOut:<desc>, 
%               +IqsIn:<ineq>s, -IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% computes the closure of lexical entries under lexical rules to get additional
% lexical grammar rules MotherOut ===> DtrsOut
% ------------------------------------------------------------------------------
gen_lex_close(_,_,Word,Desc,Word,Desc,Iqs,Iqs).
gen_lex_close(N,Max,WordStart,DescStart,WordEnd,DescEnd,IqsIn,IqsOut) :-
  current_predicate(lex_rule,(_ lex_rule _)),
  N < Max,
  add_to(DescStart,TagIn,bot,IqsIn,IqsMid),
  ( (RuleName lex_rule DescIn **> DescOut morphs Morphs),
    Cond = true
  ; (RuleName lex_rule DescIn **> DescOut if Cond morphs Morphs)
  ),
  deref(TagIn,bot,DTagIn,DSVs),
  add_to(DescIn,DTagIn,DSVs,IqsMid,IqsMid2),
  query_goal(Cond,Goal,IqsMid2,IqsMid3),
  call(Goal),
  check_inequal(IqsMid3,IqsMid4),
  morph(Morphs,WordStart,WordOut),
  SN is N + 1,
  gen_lex_close(SN,Max,WordOut,DescOut,WordEnd,DescEnd,IqsMid4,IqsOut).

% ------------------------------------------------------------------------------

% 5/15/96 - Octav -- changed to display the new version and add the banner to
% the version/0 message
:- nl,write('
ALE Version 3.2.1; December, 2001
Copyright (C) 1992-1995, Bob Carpenter and Gerald Penn
Coopyright (C) 1998,1999,2001, Gerald Penn	   
All rights reserved'),nl,
   nointerp,
   nosubtest,
   parse,
   assert(lexicon_consult).

%to_file(File) :-
%  bagof(e(I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName),
%        edge(I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName),
%        Es),
%  tell(File),
%  to_file_act(Es),
%  nl,told.

%to_file_act([]).
%to_file_act([e(I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName)|Es]) :-
%  write('edge('),write(I),comma,write(Left),comma,write(Right),comma,
%  write(Tag),comma,write(SVs),comma,write(Iqs),comma,write(Dtrs),comma,
%  write(RuleName),write(').'),
%  nl,to_file_act(Es).

%comma :- write(',').

%same(A, B) :-
%        edge(A, C, D, E, F, G, _,_),
%        edge(B, C, D, E, F, G, _,_).

%subfind(I,J,LReln,RReln) :-
%  edge(I,Left,Right,Tag,SVs,Iqs,_,_),
%  edge(J,Left,Right,STag,SSVs,SIqs,_,_),
%  subsume([s(Tag,SVs,STag,SSVs)],Iqs,SIqs,<,>,LReln,RReln,[],[]),
%  comparable(LReln,RReln).

%comparable(LReln,RReln) :-
%  (LReln \== #,! ; RReln \== #).

% [269,266,263,260,220,214,177,171]

subsume(Desc1,Desc2,LReln,RReln) :-
  add_to(Desc1,Tag1,bot,[],Iqs1),
  add_to(Desc2,Tag2,bot,[],Iqs2),
  fully_deref_prune(Tag1,bot,DTag1,DSVs1,Iqs1,DIqs1),
  fully_deref_prune(Tag2,bot,DTag2,DSVs2,Iqs2,DIqs2),
  subsume([s(DTag1,DSVs1,DTag2,DSVs2)],DIqs1,DIqs2,<,>,LReln,RReln,[],[]).
