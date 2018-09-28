% Signature
% ------------------------------------------------------------------------------

bot sub [sign, syn, pos, valence, list, agr, num, per, gnd, case, bool, pform, mod].

  sign sub [syn_sign, lex_sign]
  intro [syn : syn, dtrs : list].
        syn_sign sub [phrase, word].
        lex_sign sub [word, lexeme]. 
              lexeme sub [n_lxm, v_lxm].
                                 v_lxm sub [intr_v_lxm, trans_v_lxm].
                                 n_lxm sub [sing_n_lxm,plur_n_lxm].
                                           sing_n_lxm sub [count_sing_n_lxm,mass_sing_n_lxm].
  syn sub [] 
      intro [val : valence,
               head: pos].
  pos sub [adj, prep, agr_pos, adv].
      prep sub []
  intro [pform: pform].
      agr_pos sub [det, verb, noun]
                    intro [agr : agr].
            det sub []
                   intro [count : bool].
             noun sub []
                   intro [case : case].
      adv sub [].
   agr sub []
         intro [num : num,
                  per : per,
                  gnd : gnd].
  num sub [sg, pl].
  per sub [fst, snd, trd].
  gnd sub [fem,mas,neut].
  case sub [acc, nom].
  valence sub [] 
               intro [spr :list,
                      comps: list,
                      mod: mod].
  list sub [e_list, ne_list].
    ne_list sub [] 
            intro [hd: syn_sign, 
                   tl:list].
  bool sub [minus, plus].
  pform sub [on, with].
  on sub [].
  with sub [].
  mod sub [none, mod_sign].
  none sub [].
  mod_sign sub [left, right]
      intro [sign: sign].
    left sub [].
    right sub [].


% Macros
% ------------------------------------------------------------------------------

 np(X,Y) macro (syn: (head : (noun,                        
                                              agr : X,
                                              case : Y),
                            val : (  spr :  [ ],
                                      comps: [ ] ))).

 det(X,Y) macro (syn: (head : (det,                        
                                              agr : X,
                                              count : Y),
                                  val : (  spr :  [ ],
                                        comps: [ ] ))).

pp(X) macro (syn: (head : (prep,
                pform : X),
                                  val : (  spr :  [ ],
                                        comps: [  ] ))).
vp(X) macro (syn: (head : (verb,                        
                                              agr : X),
                            val : (  spr :  [ ],
                                      comps: [ ] ))).

p(X) macro (syn: (head : (prep,
                pform : X),
                                  val : (  spr :  [ ],
                                        comps: [ @np(_, acc) ] ))).

% Type constraints
% ------------------------------------------------------------------------------

% All common nouns are nominal, third person, require a determiner and no complements.
%
n_lxm cons (syn:(head: (noun, 
                                       agr : (X, per : trd)),
                             val :    (spr : [  @det(X,_)  ],
                                        comps : [ ] ) ) ).

% "Singulare tantum" nouns are singular (e.g. cat, dog, house, gold, fun, etc.)

sing_n_lxm cons (syn:(head: (agr : (num: sg)))).


% "Plurale tantum" nouns are plural (e.g. pants, trunks, scissors, etc.) 

plur_n_lxm cons (syn:(head: (agr : (num: pl)))).


% Count nouns (cat, dog, house, etc.) are COUNT +

count_sing_n_lxm cons (syn: (val : (spr : [ @det(_, plus) ] ))). 


% Mass nouns (e.g. gold, wheat, cash, fun, etc.) are COUNT -

mass_sing_n_lxm cons (syn: (val : (spr : [  @det(_, minus) ] ))). 


% Verbal lexemes select a nominative NP subject and agree with it.
%
v_lxm cons (syn:(head: (verb, agr : X),
                             val :    (spr : [  @np(X,nom)  ] ) )).


% All intransitive verbal lexemes require no complements.
%
intr_v_lxm cons (syn:(val : (comps : [   ] ) )).


% Transitive verbal lexemes require one accusative NP complement.
%
trans_v_lxm cons (syn:(val : (comps : [  @np(_,acc)  ] ) )).

% word has empty list dtrs
word cons (dtrs : e_list).

% Lexical Rules
% ------------------------------------------------------------------------------

% Singular noun lexical rule 

sing_n lex_rule  
   (n_lxm, (syn : Y))
   **> (word, (syn : Y))
 morphs
    X becomes X.

% Plural noun lexical rule 

plur_n lex_rule  
   (count_sing_n_lxm, (syn : (head : (agr : (gnd : G,
                                                                   per : P)),
                                               val : (spr : [ @det(_,B) ],
                                                        comps: C))))
       **> (word, (syn : (head : (noun, 
                                               agr : (Y, (gnd: G,
                                                            per : P,
                                                            num : pl))),
                                    val : (spr : [ @det(Y,B) ],
                                             comps : C))))
 morphs
  sheep becomes sheep,
  (X,e) becomes (X,es),
  (X) becomes (X,s).


% Past tense lexical rule

past_v lex_rule  
   (v_lxm, 
         (syn: (Y)))
   **> (word, (syn:Y))
  morphs
    see becomes saw,
    fall becomes fell,
    (X,e) becomes (X,ed),
    (X) becomes (X,ed).


% Present tense lexical rule (case 1)

thirdper_v1 lex_rule  
   (v_lxm, 
        (syn: (Y)))
   **> (word, (syn: (Y,head : (agr :(num: sg, 
                                     per: trd)))))
  morphs
    X becomes (X,s).


% Present tense lexical rule (case 2)

thirdper_v2 lex_rule  
   (v_lxm, 
         (syn: (Y, head : (agr : (num: sg, (per : fst ; per: snd) ;
                                  (num : pl))))))
   **> (word, (syn: Y))
  morphs
   X becomes X.

                

% Lexicon
% ------------------------------------------------------------------------------

% Common nouns

cat --->
  count_sing_n_lxm,       
   (syn : head : agr : gnd : neut).

sheep --->
  count_sing_n_lxm,                        
   (syn : head : agr : gnd : neut).

girl --->
   count_sing_n_lxm,                        
   (syn : head : agr : gnd : fem).

boy --->
  count_sing_n_lxm,
   (syn : head : agr : gnd : mas).

cash --->
  mass_sing_n_lxm,                    
   (syn : head : agr : gnd : neut).



% Determiners 

the --->
  word,                        
   @det(_, _).

some --->
  word,                        
   @det( _  , _).

each --->
  word,                        
   @det( _ , plus).
   
much --->
  word,                        
   @det( _  , minus).

this --->
  word,                        
   @det(  (num: sg)  , _).
   
these --->
  word,                        
   @det(  (num: pl)  ,plus).



% Proper names

mia --->
  word,                        
  @np( (num : sg,
             per : trd,
             gnd : fem), _ ).

tom --->
  word,                        
  @np( (num : sg,
             per : trd,
             gnd : mas), _ ).


% Pronouns 
             
i --->
  word,                        
  @np( (num : sg,
             per : fst), nom ).

me --->
  word,                        
  @np( (num : sg,
             per : fst), acc ).

you --->
  word,                        
  @np( (per : snd), _ ).

she --->
  word,                        
  @np( (num : sg,
             per : trd,
             gnd : fem), nom ).

he --->
  word,                        
  @np( (num : sg,
             per : trd,
             gnd : mas), nom ).

her --->
  word,                        
  @np( (num : sg,
             per : trd,
             gnd : fem), acc ).

him --->
  word,                        
  @np( (num : sg,
             per : trd,
             gnd : mas), acc ).

it --->
  word,                        
  @np( (num : sg,
             per : trd,
             gnd: neut), _ ).

they --->
  word,                        
  @np( (num : pl,
             per : trd), nom ).

them --->
  word,                        
  @np( (num : pl,
             per : trd), acc ).

we --->
  word,                        
  @np( (num : pl,
             per : fst), nom ).

us --->
  word,                        
  @np( (num : pl,
             per : fst), acc ).


% Verbs
 
smile --->                              
  intr_v_lxm.

fall --->                              
  intr_v_lxm.


see --->                              
  trans_v_lxm.

% propositional verbs

collaborated --->
  word,
  (syn: 
  (head : verb,
  val : (
    spr : [@np(_, nom)],
    comps : [@pp(with)]
  ))).

depended --->
  word,
  (syn: 
  (head : verb,
  val : (
    spr : [@np(_, nom)],
    comps : [@pp(on)]
  ))).

% Prepositions

on --->
  word,
  @p(on).

with --->
  word,
  @p(with).

% Adverbs

repeatedly --->
    word,
    (syn:
        (head: adv,
        val: (
            spr: e_list,
            comps: e_list,
            mod: (sign: @vp(_))
        ))
    ).

yesterday --->
    word,
    (syn:
        (head: adv,
        val: (
            spr: e_list,
            comps: e_list,
            mod: (left, sign: @vp(_))
        ))
    ).


% Grammar Rules
% ------------------------------------------------------------------------------

head_spr_struc rule
(phrase,(dtrs: [X, K],
  syn:(head : Y, 
                    val : (spr:[], comps:[]))))
===>
cat> (X), 
cat> (K, syn_sign, syn:(head : Y,
                                val : (spr:[X], comps:[]))).


head_comps_struc rule
(phrase,(syn:(head : Z, 
                    val : (spr: X, comps:[]))))
===>
cat> (word, syn:(head : Z,
                 val : (spr: X, comps: (Y,ne_list) ))),
cats> (Y). 


% r_head_mod_struc rule
% (phrase, (syn: (val: Y)))
% ===>
% cat> (syn:
%         (val: 
%           (spr: e_list,
%           comps: e_list,
%           mod: 
%             (right, sign: X)
%           )
%         )
%       ),
% cat> (X, syn: (val: Y)).


% l_head_mod_struc rule
% (phrase, (syn: (val: Y)))
% ===>
% cat> (X, syn: (val: Y)),
% cat> (syn:
%         (val: 
%           (spr: e_list,
%           comps: e_list,
%           mod: 
%             (left, sign: X)
%           )
%         )
%       ).




% Consistency check
% ------------------------------------------------------------------------------


p(Type) :-
        repeat,
            s(Type,N,S),
            parse_s(S,N),
            !.

parse_s(stop,0).
                  
parse_s(S,N) :-  
         write('Parsing sentence '), write(N), write('... '),
        (call(time(rec(S,_,_,_))) ; (tab(18), write('Failed.'), nl)),!,
         fail.
         
% Grammatical
s(g,1,[i,smile]).
s(g,2,[you,smile]).
s(g,3,[she,smiles]).
s(g,4,[you,smile]).
s(g,5,[they,smile]).
s(g,6,[we,smile]).
s(g,7,[i,saw,her]).
s(g,8,[the,cat,fell]).
s(g,9,[each,cat,fell]).
s(g,10,[these,cats,fell]).
s(g,11,[much,cash,fell]).

% Ungrammatical
s(u,1,[i,smiles]).
s(u,2,[you,smiles]).
s(u,3,[she,smile]).
s(u,4,[they,smiles]).
s(u,5,[we,smiles]).
s(u,6,[i,saw,she]).
s(u,7,[the,cat,fall]).
s(u,8,[each,cash,fell]).
s(u,9,[these,cat,fell]).
s(u,10,[much,cats,fell]).
s(u,11,[cat,fell]).

s(_,0,stop).



