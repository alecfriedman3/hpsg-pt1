
% ---------------   Load ALE  ----------------

% ale must be located one directory up 
init :- 
   compile('../ale_swi.pl'),
   ldg.

ldg :- 
  compile_gram('grammar.pl').
  %  compile_sig('signature'),
  %  compile_fun('macros'),
  %  compile_cons('cons'),
  %  compile_logic,
  %  compile_subsume,
  %  compile_dcs('if_rules'),
  %  compile_lex_rules('lex_rules'),
  %  compile_lex('lexicon'),
  %  compile_rules('phrase_rules').


% Grammar consistency check

p :- 
   time( rec_list([
                           [she,walks], 
                           [she,walked]
                         ],
                           phrase, _) ).
