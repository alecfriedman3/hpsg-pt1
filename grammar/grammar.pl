% Signature
% ------------------------------------------------------------------------------

bot sub [sign, syn, pos, valence, list, agr, num, per, gnd, case, bool].

  sign sub [syn_sign, lex_sign]
	intro [syn : syn].
        syn_sign sub [phrase, word].
        lex_sign sub [word, lexeme]. 
              lexeme sub [n_lxm, v_lxm].
                       v_lxm sub [intr_v_lxm, trans_v_lxm].
  syn sub [] 
      intro [val : valence,
               head: pos].
  pos sub [adj, prep, agr_pos].
      agr_pos sub [det, verb, noun]
                    intro [agr : agr].
            det sub []
                   intro [count : bool].
             noun sub []
                   intro [case : case]. 
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
                       comps: list].
  list sub [e_list, ne_list].
    ne_list sub [] 
            intro [hd: syn_sign, 
                   tl:list].
  bool sub [minus, plus].


% Macros
% ------------------------------------------------------------------------------

 np(X,Y) +++> (syn: (head : (noun,                        
                                              agr : X,
                                              case : Y),
                            val : (  spr :  [ ],
                                      comps: [ ] ))).



% Type constraints
% ------------------------------------------------------------------------------

n_lxm cons ( syn:(head: noun,
                              val : (spr : [   ],
                                      comps: [  ] ) )).

 v_lxm cons (syn:(head: (verb, agr : X),
                             val :    (spr : [  np(X,nom)  ] ) )).

intr_v_lxm cons (syn:(val : (comps : [   ] ) )).

trans_v_lxm cons (syn:(val : (comps : [  np(_,acc)  ] ) )).


% Lexical Rules
% ------------------------------------------------------------------------------

% Singular noun lexical rule 

singn_n lex_rule  
   (n_lxm, (syn : Y))
   **> (word, (syn : Y))
 morphs
    X becomes X.

% Past tense lexical rule

past_v lex_rule  
   (v_lxm, 
         (syn: (Y)))
   **> (word, (syn:Y))
  morphs
    see becomes saw,
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

% Nominals

mia --->
  n_lxm,                        
  (syn:(head: (agr : (num : sg,
                              per : trd,
                              gnd : fem)))).

i --->
  n_lxm,                        
  (syn:(head: (case : nom,
                        agr : (num : sg,
                                 per : fst)))).

me --->
  n_lxm,                        
  (syn:(head: (case : acc,
                        agr : (num : sg,
                                 per : fst)))).

you --->
  n_lxm,                        
  (syn:(head: (agr : (per : snd)))).

she --->
  n_lxm,                        
  (syn:(head: (case : nom,
                        agr : (num : sg,
                                 per : trd,
                                 gnd: fem)))).

he --->
  n_lxm,                        
  (syn:(head: (case : nom,
                        agr : (num : sg,
                                 per : trd, 
                                 gnd : mas)))).

her --->
  n_lxm,                        
  (syn:(head: (case : acc,
                        agr : (num : sg,
                                 per : trd,
                                 gnd : fem)))).

him --->
  n_lxm,                        
  (syn:(head: (case : acc,
                        agr : (num : sg,
                                 per : trd,
                                 gnd : mas )))).




% Verbs
 
smile --->                              
  intr_v_lxm.

see --->                              
  trans_v_lxm.


% Grammar Rules
% ------------------------------------------------------------------------------

head_spr_struc rule
(phrase,(syn:(head : Y, 
                    val : (spr:[], comps:[]))))
===>
cat> (X), 
cat> (syn_sign, syn:(head : Y,
                                val : (spr:[X], comps:[]))).


head_comps_struc rule
(phrase,(syn:(head : Z, 
                    val : (spr: X, comps:[]))))
===>
cat> (word, syn:(head : Z,
                 val : (spr: X, comps: (Y,ne_list) ))),
cats> (Y). 
