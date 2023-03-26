(*START ------------------------------------------------------------------------- *)
open preamble
open basis
open ml_monad_translator_interfaceLib

open stringTheory
open wordsTheory
open listTheory
open degTypesTheory
open degTheory
open degChainTheory

val _ = new_theory "degProperties";
val _ = translation_extends "basisProg";
val _ = ParseExtras.temp_tight_equality ();

(*CONSTS ------------------------------------------------------------------------ *)
val const_defs =  [BlindSigIsNotEqual_def, EmptyStartDateError_def, InvalidBlindSig_def, InvalidCommissionSecretKey_def, IssueBallotsAlreadyStarted_def, IssueBallotsAlreadyStopped_def, RequiredParamIsMissing_def, RequiredParamValueMissing_def, RevoteIsBlockedError_def, SenderIsNotBlindSigIssueRegistrator_def, SenderIsNotIssueBallotsRegistrator_def, SenderIsNotVotingRegistrator_def, ServersDoNotContainSenderPubKey_def, ServersListIsEmpty_def, StartDateAlreadyInStateError_def, StartDateHasNotComeYet_def, VotingAlreadyStarted_def, VotingIsNotInProgress_def, VotingIsNotYetFinished_def, WRN_PARAMS_def]

Definition chooseFunction_def:
chooseFunction (f : num) = 
    (λparams. case (f : num) of
      1 => updateServerList params
    | 2 => addMainKey params
    | 3 => startVoting
    | 4 => blindSigIssue params 
    | 5 => vote params
    | 6 => finishVoting
    | 7 => commissionDecryption params
    | 8 => results params
    |  _ => fail "No function to consider")
End 

Definition execute_def:
execute (f:num) (params:SCvalue list) : (State, SCvalue, Exn) M =
  do
    v <- chooseFunction f params;
    return v
  od
End

Definition set_state_context_def:
  set_state_context (ctxt : Context): (State, unit, Exn) M
  = λ state. let new_state = state with context := ctxt in (Success (), new_state)
End

Definition scReceive_def:
  scReceive (ctxt : Context) (data : Data) : (State, SCvalue, Exn) M = 
  do
    _ <- set_state_context ctxt;
    execute (get_functionSignature data) (get_params data);
  od 
End

Definition scInit_def:
  scInit (ctxt : Context) (setup : Setup) : (State, SCvalue, Exn) M = 
     do
     _ <- set_state_context ctxt;
     initiateVoting (get_setupparams setup);
     od
End

Definition SCdeg_def:
  SCdeg = <| init := scInit; receive := scReceive|>
End

(* BEGIN tactics*)
fun dummy_tac q : tactic
    = all_tac

fun lambda_comb (COMB pt) = pt
  | lambda_comb _ = raise Fail "not a lambda COMB"

fun lambdagetpair (COMB pt) = pt
  | lambdagetpair (LAMB pt) = pt
  | lambdagetpair _ = raise Fail "wrong constructor"

fun term_by_bin ([]:int list) (t:term) : term = t
  | term_by_bin (he::ta) t =
    (let
      val p = t |> dest_term |> lambdagetpair
      val st = (if he=0 then (fst p) else (snd p))
    in
      term_by_bin ta st
    end)

(* GET SUBTERM TACTICS *)

(* redundant! it is similar to "strip_comb" function, but works when term con *)
(*see also strip_fun for types*)
fun term_as_list te : term list =
    (term_as_list (rator te)) @ [(rand te)] handle _ => [te]

fun list_as_term li : term = List.foldl (mk_comb o swap) (hd li) (tl li)

val get_head = hd o term_as_list
val get_args = tl o term_as_list

(* otherwise "val gener:term = ``COND``" gives <<HOL message: inventing new type variable names: 'a>> *)
fun fst_subterm_matches gener s1 s2 w =
     let
       val l = term_as_list w
       val insta = (el 1 l)
       val sub = (match_term gener insta)
         handle _ => raise ERR s1 s2
     in
       w
     end

val gener_ALL : term = ``(!) : (α -> bool) -> bool``
val checkALL : term -> term = fst_subterm_matches gener_ALL "checkALL" "Not a FORALL term"

val gener_EX : term = ``(?) : (α -> bool) -> bool``
val checkEX : term -> term = fst_subterm_matches gener_EX "checkEX" "Not an EX term"

val gener_NEG : term = ``(~) : bool -> bool``
val checkNEG : term -> term = fst_subterm_matches gener_NEG "checkNEG" "Not a NEG term"

val gener_IF : term = ``COND : bool -> α -> α -> α``
val checkIF : term -> term = fst_subterm_matches gener_IF "checkIF" "Not an IF term"

val gener_EQ : term = ``(=) : α -> α -> bool``
val checkEQ : term -> term = fst_subterm_matches gener_EQ "checkEQ" "Not an EQ term"

val Cases_on_term: term -> tactic
     = fn (te : term) => (Cases_on ([ANTIQUOTE te]) >> simp []) : tactic

val get_first_arg  = (el 1) o get_args
val get_second_arg = (el 2) o get_args

(** Functions for the term destruction **)

fun term_by_num [] t = t
  | term_by_num (he::ta) t =
      term_by_num ta (el he $ term_as_list $ t)

(** Functions for the explicit term destruction **)

(* ∀ *)
val get_forall_body : term -> term
   = term_by_bin [1,1] o checkALL

(* ∃ *)
val get_exists_body : term -> term
   = term_by_bin [1,1] o checkEX

(* get left subterm of equality *)
val get_eq_left : term -> term
  = term_by_num [2] o checkEQ

(* get right subterm of equality *)
val get_eq_right : term -> term
  = term_by_num [3] o checkEQ

(* get neg's arg *)
val get_neg : term -> term
  = term_by_num [2] o checkNEG

(* get IF's condition *)
val get_if_cond : term -> term
  = term_by_num [2] o checkIF

val get_cond_term = get_if_cond
(* see HOL/src/portbleML/Portable.sml *)
val to_quotation : term -> term quotation
  = single o ANTIQUOTE

(* get the conclusion of the goal *)
val get_concl : goal -> term = snd

(* get ==>'s antecedent *)
val get_antecedent : term -> term
  = term_by_num [2] (* o checkIMP  TODO! "($==>:bool=>bool=>bool)" *)

(* Using something obtained from the goal as the argument
   to a function that creates a tactic.

Use cases:
1) for debug
  use_goal (print_term o get_neg o get_if_cond o get_eq_left o get_exists_body o get_concl) dummy_tac >>
2) for reasoning:
  use_goal (to_quotation o get_neg o get_if_cond o get_eq_left o get_exists_body o get_concl) Cases_on >>
*)

fun use_goal (obt:goal->'a) (tacf:'a->tactic) : tactic
    = (fn x as (asl, w) => tacf (obt x) x)

fun print_endline x = print (x ^ "\n")
val print_term = print_endline o term_to_string
(* END tactics *)

(* Tactic GET CASE ARGUMENT *)
val get_case_arg = get_first_arg

val if_inside_casestmnt_tac : tactic =
 ((fn x => (Cases_on_term o get_first_arg o get_first_arg o snd) x x):tactic)

val addErr_inside_casestmnt_tac : tactic =
 ((fn x => (Cases_on_term o get_second_arg o get_first_arg o snd) x x):tactic)

fun USE_LAST_HYP (fu:term->tactic) : tactic =
  (fn x as (asl:term list, w:term) =>
  (case asl of
   he :: ta => fu he
   | _ => raise ERR "USE_LAST_HYP" "there are no hypotheses"
  ) x)

val FOR_ALL_HYP = REPEAT o USE_LAST_HYP

val UNDISCH_LAST = USE_LAST_HYP UNDISCH_TAC

val UNDISCH_ALL = FOR_ALL_HYP UNDISCH_TAC

val SYM_TAC : tactic = irule EQ_SYM


Theorem vote_params_error:
∀ state. ∀  params.   
(¬(check_types params [TypeWord8List; TypeNum; TypeNum]) ⇒  vote params state  = fail WRN_PARAMS state)
Proof
  rw []>>
  fs [vote_def]>>
  simp [ml_monadBaseTheory.st_ex_bind_def] >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  simp [boolTheory.FUN_EQ_THM] >>
  simp [get_state_def] >>
  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  simp [assert_def] >>
  simp [raise_Fail_def, check_types_def]
QED

Theorem initiateVoting_params_error:
∀ state. ∀  params.   
(¬(check_types params [TypeNum; TypeString; TypeNumListList; TypeNum; TypeNum; TypeNumOption; TypeNumOption; TypeNumList; TypeNumList; TypeNum; TypeNum; TypeBool]) ⇒  initiateVoting params state  = fail WRN_PARAMS state)
Proof
  rw []>>
  fs [initiateVoting_def]>>
  simp [ml_monadBaseTheory.st_ex_bind_def] >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  simp [boolTheory.FUN_EQ_THM] >>
  simp [get_state_def] >>
  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  simp [assert_def] >>
  simp [raise_Fail_def, check_types_def]
QED


Theorem results_params_error:
∀ state. ∀  params.   
(results params state  = fail WRN_PARAMS state) ⇔ (¬(check_types params [TypeNumList]))
Proof
  rw []>>
  simp [results_def]>>
  simp [ml_monadBaseTheory.st_ex_bind_def] >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  simp [boolTheory.FUN_EQ_THM] >>
  simp [get_state_def] >>
  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  simp [assert_def] >>
  simp [raise_Fail_def, check_types_def]>>
  rw[]>>EVAL_TAC>>UNDISCH_ALL>>rw[]>>
  EVAL_TAC >> every_case_tac >>
  fs [ml_monadBaseTheory.st_ex_bind_def] >>
  fs [ml_monadBaseTheory.st_ex_return_def] >>
  fs [boolTheory.FUN_EQ_THM] >>
  fs [get_state_def] >>
  fs [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs [assert_def] >>
  fs [raise_Fail_def, check_types_def]>>
  rw[]>>EVAL_TAC>>UNDISCH_ALL>>rw[]
QED

Theorem results_authentification_error:
∀ state. ∀  params.
(results params state  = fail ServersDoNotContainSenderPubKey state) ⇔ 
(check_types params [TypeNumList] ∧
∃ l. params = [SCNumList l] ∧
find_entity state.servers state.context.msg_sender = NONE) 
(* попробовать доказать и в таком виде:  ¬(MEM state.context.msg_sender state.servers) *)
Proof  
  rw []>>
  simp [results_def]>>
  simp [ml_monadBaseTheory.st_ex_bind_def] >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  simp [boolTheory.FUN_EQ_THM] >>
  simp [get_state_def] >>
  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  simp [assert_def] >>
  simp [raise_Fail_def, check_types_def]>>
  rw[]>>EVAL_TAC>>UNDISCH_ALL>>rw[]>>
  EVAL_TAC >>every_case_tac >>
  fs [ml_monadBaseTheory.st_ex_bind_def] >>
  fs [ml_monadBaseTheory.st_ex_return_def] >>
  fs [boolTheory.FUN_EQ_THM] >>
  fs [get_state_def] >>
  fs [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs [assert_def] >>
  fs [raise_Fail_def, check_types_def]>>
  rw[]>>EVAL_TAC>>UNDISCH_ALL>>rw[]
QED

Theorem results_status_error:
∀ state. ∀  params.
(results params state  = fail VotingIsNotYetFinished state) ⇔ 
(check_types params [TypeNumList] ∧
∃ l. params = [SCNumList l] ∧
find_entity state.servers state.context.msg_sender ≠ NONE ∧
state.votingBase.status ≠ Completed)
Proof  
  rw []>>
  simp [results_def]>>
  simp [ml_monadBaseTheory.st_ex_bind_def] >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  simp [boolTheory.FUN_EQ_THM] >>
  simp [get_state_def] >>
  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  simp [assert_def] >>
  simp [raise_Fail_def, check_types_def]>>
  rw[]>>EVAL_TAC>>UNDISCH_ALL>>rw[]>>
  EVAL_TAC >>every_case_tac >>
  fs [ml_monadBaseTheory.st_ex_bind_def] >>
  fs [ml_monadBaseTheory.st_ex_return_def] >>
  fs [boolTheory.FUN_EQ_THM] >>
  fs [get_state_def] >>
  fs [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs [assert_def] >>
  fs [raise_Fail_def, check_types_def]>>
  rw[]>>EVAL_TAC>>UNDISCH_ALL>>rw[]
QED

(* TO DO:

3) Доказать что функции startVoting и finishVoting выдадут ошибку ServersDoNotContainSenderPubKey в случае вызова не от сервера
4) Доказать что функция blindSigIsuue выдаст ошибку WRN_PARAMS в случае вызова с неправильными параметрами  
6) Доказать что функция blindSigIsuue выдаст ошибки EmptyStartDateError и StartDateHasNotComeYet в случае вызова при неустановленной дате начала голосования и при вызове до начала голосования соответственно + что эта ошибка сохранится в ключе стейта blindSigFail
*)

(* 5 *)
Theorem blindSigIssue_authentification_error:
∀ s1. ∀  params.
(blindSigIssue params s1  = fail SenderIsNotBlindSigIssueRegistrator s2) ⇔ 
(check_types params [TypeNumStringList] ∧
∃ l. params = [SCNumStringList l] ∧
(s1.blindSigIssueRegistrator ≠ s1.context.msg_sender) ∧
(s1 with  <|transactionCount := SUC s1.transactionCount; 
           blindSigFail :=
            (SUC s1.transactionCount,SenderIsNotBlindSigIssueRegistrator)::
                s1.blindSigFail|> = s2))
Proof 
 rw [] >>
  simp [blindSigIssue_def]>>
  simp [ml_monadBaseTheory.st_ex_bind_def] >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  simp [boolTheory.FUN_EQ_THM] >>
  simp [get_state_def] >>
  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  simp [assert_def] >>
  simp [raise_Fail_def, check_types_def]>>
  rw[]>>EVAL_TAC>>UNDISCH_ALL>>rw[]>>
  EVAL_TAC >>every_case_tac >>
  fs [ml_monadBaseTheory.st_ex_bind_def] >>
  fs [ml_monadBaseTheory.st_ex_return_def] >>
  fs [boolTheory.FUN_EQ_THM] >>
  fs [get_state_def] >>
  fs [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs [assert_def] >>
  fs [raise_Fail_def, check_types_def]>>
  rw[]>>EVAL_TAC>>UNDISCH_ALL>>rw[] >> 
  fs [set_state_blindSigFail_def] >> fs const_defs
QED


(* 6.1 *)
Theorem blindSigIssue_Start1_error: 
∀ s1. ∀  params.
(blindSigIssue params s1  = fail EmptyStartDateError s2) ⇔ 
(check_types params [TypeNumStringList] ∧
∃ l. params = [SCNumStringList l] ∧
(s1.blindSigIssueRegistrator = s1.context.msg_sender) ∧ 
((s1.votingBase.dateStart = NONE)) ∧
(s1 with  <|transactionCount := SUC s1.transactionCount; 
           blindSigFail :=
            (SUC s1.transactionCount,EmptyStartDateError)::
                s1.blindSigFail|> = s2))
Proof 
  rw [] >>
  simp [blindSigIssue_def]>>
  simp [ml_monadBaseTheory.st_ex_bind_def] >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  simp [boolTheory.FUN_EQ_THM] >>
  simp [get_state_def] >>
  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  simp [assert_def] >>
  simp [raise_Fail_def, check_types_def]>>
  rw[]>>EVAL_TAC>>UNDISCH_ALL>>rw[]>>
  EVAL_TAC >>every_case_tac >>
  fs [ml_monadBaseTheory.st_ex_bind_def] >>
  fs [ml_monadBaseTheory.st_ex_return_def] >>
  fs [boolTheory.FUN_EQ_THM] >>
  fs [get_state_def] >>
  fs [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs [assert_def] >>
  fs [raise_Fail_def, check_types_def]>>
  rw[]>>EVAL_TAC>>UNDISCH_ALL>>rw[] >> 
  fs [set_state_blindSigFail_def] >> fs const_defs
QED


(* Свойство: При корректном функционировании системы итоги голосования должны быть подведены.*)

Theorem help1:
∀e caddr.
¬(get_envContractStates e caddr = NONE) ⇒
get_envContractStates e caddr = SOME (THE (get_envContractStates e caddr))
Proof
  rw [] >> Cases_on ‘get_envContractStates e caddr’ >> fs [] >> rw [THE_DEF]
QED

Theorem commissionKey_isFeasible:
∀ e1 s1. 
  get_envContracts e1 caddr = SOME SCdeg ∧ 
  get_envContractStates e1 caddr = SOME s1 ∧
  s1.votingBase.status = Active ∧
  s1.servers = (h :: t) ∧
  s1.commissionDecryption = 0 ∧
  s1.commissionKey = "" ∧
  s1.votingBase.dateStart = NONE ⇒
  ∃ e2.
  ChainStep e1 e2 ∧    
  get_envContracts e2 caddr = SOME SCdeg ∧
  get_envContractStates e2 caddr ≠ NONE ∧
  ((THE (get_envContractStates e2 caddr)).votingBase.status = Active) ∧
  ((THE (get_envContractStates e2 caddr)).servers = (h :: t)) ∧
  ((THE (get_envContractStates e2 caddr)).votingBase.dateStart = NONE) ∧
  ((THE (get_envContractStates e2 caddr)).commissionDecryption = 0) ∧
  ((THE (get_envContractStates e2 caddr)).commissionKey ≠ "")  
Proof
  rw [] >> fs [get_envContracts_def, get_envContractStates_def] >>
  rw [ChainStep_cases, ActionEvaluation_cases] >> rw [set_contract_state_def, get_envContractStates_def, get_envContracts_def] >>
  Q.EXISTS_TAC ‘(set_contract_state caddr (s1 with <|context := <|msg_sender:= h; block_number:= s1.context.block_number + 1; block_timestamp:= s1.context.block_timestamp + 100|>; mainKey := "mainKey" ; dkgKey := "dkgKey" ; commissionKey := "commissionKey" |>) e1)’ >> 
  rw [] >- (EXISTS_TAC ``(<| actFrom := h; actType := Call caddr <|functionSignature := 2; params := [SCString "mainKey"; SCString "commissionKey"; SCString "dkgKey"] |> |>)`` >> rw [get_actType_def] >> DISJ2_TAC >>
Q.EXISTS_TAC ‘h’ >> Q.EXISTS_TAC ‘caddr’ >> Q.EXISTS_TAC ‘SCdeg’ >> Q.EXISTS_TAC ‘s1’ >> 
Q.EXISTS_TAC ‘<|functionSignature := 2; params := [SCString "mainKey"; SCString "commissionKey"; SCString "dkgKey"]|>’ >> 
Q.EXISTS_TAC ‘s1.context.block_timestamp + 100’ >>
rw [build_act_def] >>rw [SCdeg_def, get_receive_def, scReceive_def, get_functionSignature_def, execute_def, chooseFunction_def, addMainKey_def, set_state_mainKey_def, set_state_dkgKey_def, set_state_commissionKey_def] >>  
  fs [ml_monadBaseTheory.st_ex_bind_def] >>
  fs [ml_monadBaseTheory.st_ex_return_def] >>
  fs [boolTheory.FUN_EQ_THM] >>
  fs [get_state_def] >>
  fs [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs [assert_def] >>
  fs [raise_Fail_def, check_types_def]>>
  rw []>>EVAL_TAC>>UNDISCH_ALL>>rw[] >> EVAL_TAC >> rw [] >> fs [INDEX_FIND_def] >> EVAL_TAC >> fs [typeOf_def, get_params_def]) >>
  rw [set_contract_state_def, get_envContractStates_def, UPDATE_def]
QED

Theorem startDate_isFeasible:
∀ e1 s1. 
  get_envContracts e1 caddr = SOME SCdeg ∧ 
  get_envContractStates e1 caddr = SOME s1 ∧
  s1.votingBase.status = Active ∧ 
  s1.servers = (h :: t) ∧
  s1.commissionDecryption = 0 ∧
  s1.votingBase.dateStart = NONE ⇒
  ∃ e2.
  ChainStep e1 e2 ∧    
  get_envContracts e2 caddr = SOME SCdeg ∧
  get_envContractStates e2 caddr ≠ NONE ∧
  ((THE (get_envContractStates e2 caddr)).votingBase.status = Active) ∧
  ((THE (get_envContractStates e2 caddr)).servers = (h :: t)) ∧
  ((THE (get_envContractStates e2 caddr)).votingBase.dateStart ≠ NONE) ∧
  (THE (THE (get_envContractStates e2 caddr)).votingBase.dateStart ≤ (THE (get_envContractStates e2 caddr)).context.block_timestamp) ∧
  ((THE (get_envContractStates e2 caddr)).commissionDecryption = 0)  
Proof
    rw [] >> fs [get_envContracts_def, get_envContractStates_def] >>
  rw [ChainStep_cases, ActionEvaluation_cases] >> rw [set_contract_state_def, get_envContractStates_def, get_envContracts_def] >>
  Q.EXISTS_TAC ‘(set_contract_state caddr (s1 with <|context := <|msg_sender:= h; block_number:= s1.context.block_number + 1; block_timestamp:= s1.context.block_timestamp + 100|>; votingBase := s1.votingBase with dateStart := SOME (s1.context.block_timestamp + 100) |>) e1)’ >> 
  rw [] >- (EXISTS_TAC ``(<| actFrom := h; actType := Call caddr <|functionSignature := 3; params := [] |> |>)`` >> rw [get_actType_def] >> DISJ2_TAC >>
Q.EXISTS_TAC ‘h’ >> Q.EXISTS_TAC ‘caddr’ >> Q.EXISTS_TAC ‘SCdeg’ >> Q.EXISTS_TAC ‘s1’ >> 
Q.EXISTS_TAC ‘<|functionSignature := 3; params := [] |>’ >> 
Q.EXISTS_TAC ‘s1.context.block_timestamp + 100’ >>
rw [build_act_def] >>rw [SCdeg_def, get_receive_def, scReceive_def, get_functionSignature_def, execute_def, chooseFunction_def, startVoting_def, set_state_votingBase_def] >>  
  fs [ml_monadBaseTheory.st_ex_bind_def] >>
  fs [ml_monadBaseTheory.st_ex_return_def] >>
  fs [boolTheory.FUN_EQ_THM] >>
  fs [get_state_def] >>
  fs [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs [assert_def] >>
  fs [raise_Fail_def, check_types_def]>>
  rw []>>EVAL_TAC>>UNDISCH_ALL>>rw[] >> EVAL_TAC >> rw [] >> fs [INDEX_FIND_def] >> EVAL_TAC >> fs [typeOf_def, get_params_def]) >>
  rw [set_contract_state_def, get_envContractStates_def, UPDATE_def]
QED

Theorem stopDate_isFeasible:
∀ e1 s1. 
  get_envContracts e1 caddr = SOME SCdeg ∧ 
  get_envContractStates e1 caddr = SOME s1 ∧
  s1.votingBase.status = Active ∧
  s1.servers = (h :: t) ∧
  s1.commissionDecryption = 0 ∧
  s1.votingBase.dateStart ≠ NONE ∧
  (THE s1.votingBase.dateStart ≤ s1.context.block_timestamp) ⇒
  ∃ e2.
  ChainStep e1 e2 ∧    
  get_envContracts e2 caddr = SOME SCdeg ∧
  get_envContractStates e2 caddr ≠ NONE ∧
  ((THE (get_envContractStates e2 caddr)).votingBase.status = Completed) ∧
  ((THE (get_envContractStates e2 caddr)).servers = (h :: t)) ∧
  ((THE (get_envContractStates e2 caddr)).commissionDecryption = 0)  
Proof
  rw [] >> fs [get_envContracts_def, get_envContractStates_def] >>
  rw [ChainStep_cases, ActionEvaluation_cases] >> rw [set_contract_state_def, get_envContractStates_def, get_envContracts_def] >>
  Q.EXISTS_TAC ‘(set_contract_state caddr (s1 with <|context := <|msg_sender:= h; block_number:= s1.context.block_number + 1; block_timestamp:= s1.context.block_timestamp + 86400000|>; votingBase := s1.votingBase with <| dateEnd := SOME (s1.context.block_timestamp + 86400000); status := Completed |> |>) e1)’ >> 
  rw [] >- (EXISTS_TAC ``(<| actFrom := h; actType := Call caddr <|functionSignature := 6; params := [] |> |>)`` >> rw [get_actType_def] >> DISJ2_TAC >>
Q.EXISTS_TAC ‘h’ >> Q.EXISTS_TAC ‘caddr’ >> Q.EXISTS_TAC ‘SCdeg’ >> Q.EXISTS_TAC ‘s1’ >> 
Q.EXISTS_TAC ‘<|functionSignature := 6; params := [] |>’ >> 
Q.EXISTS_TAC ‘s1.context.block_timestamp + 86400000’ >>
rw [build_act_def] >>rw [SCdeg_def, get_receive_def, scReceive_def, get_functionSignature_def, execute_def, chooseFunction_def, finishVoting_def, set_state_votingBase_def] >>  
  fs [ml_monadBaseTheory.st_ex_bind_def] >>
  fs [ml_monadBaseTheory.st_ex_return_def] >>
  fs [boolTheory.FUN_EQ_THM] >>
  fs [get_state_def] >>
  fs [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs [assert_def] >>
  fs [raise_Fail_def, check_types_def]>>
  rw []>>EVAL_TAC>>UNDISCH_ALL>>rw[] >> EVAL_TAC >> rw [] >> fs [INDEX_FIND_def] >> EVAL_TAC >> fs [typeOf_def, get_params_def] >> Cases_on ‘s1.votingBase.dateStart’ >> fs[] >> EVAL_TAC) >>
  rw [set_contract_state_def, get_envContractStates_def, UPDATE_def]
QED

Theorem commissionDecryption_isFeasible:
∀ e1 s1. 
  get_envContracts e1 caddr = SOME SCdeg ∧ 
  get_envContractStates e1 caddr = SOME s1 ∧
  (s1.votingBase.status = Completed) ∧
  s1.servers = (h :: t) ∧
  s1.commissionDecryption = 0 ⇒
  ∃ e2.
  ChainStep e1 e2 ∧    
  get_envContracts e2 caddr = SOME SCdeg ∧
  get_envContractStates e2 caddr ≠ NONE ∧  
  ((THE (get_envContractStates e2 caddr)).votingBase.status = Completed) ∧
  ((THE (get_envContractStates e2 caddr)).servers = (h :: t)) ∧
  (THE (get_envContractStates e2 caddr)).commissionDecryption ≠ 0 ∧
  (THE (get_envContractStates e2 caddr)).commissionDecryption = (THE (get_envContractStates e2 caddr)).transactionCount
Proof
  rw [] >> fs [get_envContracts_def, get_envContractStates_def] >>
  rw [ChainStep_cases, ActionEvaluation_cases] >> rw [set_contract_state_def, get_envContractStates_def, get_envContracts_def] >>
  Q.EXISTS_TAC ‘(set_contract_state caddr (s1 with <|context := <|msg_sender:= h; block_number:= s1.context.block_number + 1; block_timestamp:= s1.context.block_timestamp + 1000|>; transactionCount := SUC s1.transactionCount; commissionDecryption := SUC s1.transactionCount |>) e1)’ >> 
  rw [] >- (EXISTS_TAC ``(<| actFrom := h; actType := Call caddr <|functionSignature := 7; params := [SCString s1.commissionKey] |> |>)`` >> rw [get_actType_def] >> DISJ2_TAC >>
Q.EXISTS_TAC ‘h’ >> Q.EXISTS_TAC ‘caddr’ >> Q.EXISTS_TAC ‘SCdeg’ >> Q.EXISTS_TAC ‘s1’ >> 
Q.EXISTS_TAC ‘<|functionSignature := 7; params := [SCString s1.commissionKey] |>’ >> 
Q.EXISTS_TAC ‘s1.context.block_timestamp + 1000’ >>
rw [build_act_def] >>rw [SCdeg_def, get_receive_def, scReceive_def, get_functionSignature_def, execute_def, chooseFunction_def, commissionDecryption_def, set_state_votingBase_def] >>  
  fs [ml_monadBaseTheory.st_ex_bind_def] >>
  fs [ml_monadBaseTheory.st_ex_return_def] >>
  fs [boolTheory.FUN_EQ_THM] >>
  fs [get_state_def] >>
  fs [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs [assert_def] >>
  fs [raise_Fail_def, check_types_def]>>
  rw []>>EVAL_TAC>>UNDISCH_ALL>>rw[] >> EVAL_TAC >> rw [] >> fs [INDEX_FIND_def] >> EVAL_TAC >> fs [typeOf_def, get_params_def]) >>
  rw [set_contract_state_def, get_envContractStates_def, UPDATE_def]
QED

Theorem resultsReceived_isFeasible:
∀ e1 s1. 
  get_envContracts e1 caddr = SOME SCdeg ∧ 
  get_envContractStates e1 caddr = SOME s1 ∧
  (s1.votingBase.status = Completed) ∧
  s1.servers = (h :: t) ∧
  s1.commissionDecryption ≠ 0 ⇒
  ∃ e2.
  ChainStep e1 e2 ∧    
  get_envContracts e2 caddr = SOME SCdeg ∧
  get_envContractStates e2 caddr ≠ NONE ∧ 
  (THE (get_envContractStates e2 caddr)).votingBase.status = ResultsReceived ∧ 
  (THE (get_envContractStates e2 caddr)).commissionDecryption ≠ 0
Proof
  rw [] >> fs [get_envContracts_def, get_envContractStates_def] >>
  rw [ChainStep_cases, ActionEvaluation_cases] >> rw [set_contract_state_def, get_envContractStates_def, get_envContracts_def] >>
  Q.EXISTS_TAC ‘(set_contract_state caddr (s1 with <|context := <|msg_sender:= h; block_number:= s1.context.block_number + 1; block_timestamp:= s1.context.block_timestamp + 1000|>; results := res; votingBase := s1.votingBase with status := ResultsReceived |>) e1)’ >> 
  rw [] >- (EXISTS_TAC ``(<| actFrom := h; actType := Call caddr <|functionSignature := 8; params := [SCNumList res] |> |>)`` >> rw [get_actType_def] >> DISJ2_TAC >>
Q.EXISTS_TAC ‘h’ >> Q.EXISTS_TAC ‘caddr’ >> Q.EXISTS_TAC ‘SCdeg’ >> Q.EXISTS_TAC ‘s1’ >> 
Q.EXISTS_TAC ‘<|functionSignature := 8; params := [SCNumList res] |>’ >> 
Q.EXISTS_TAC ‘s1.context.block_timestamp + 1000’ >>
rw [build_act_def] >>rw [SCdeg_def, get_receive_def, scReceive_def, get_functionSignature_def, execute_def, chooseFunction_def, results_def, set_state_votingBase_def] >>  
  fs [ml_monadBaseTheory.st_ex_bind_def] >>
  fs [ml_monadBaseTheory.st_ex_return_def] >>
  fs [boolTheory.FUN_EQ_THM] >>
  fs [get_state_def] >>
  fs [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs [assert_def] >>
  fs [raise_Fail_def, check_types_def]>>
  rw []>>EVAL_TAC>>UNDISCH_ALL>>rw[] >> EVAL_TAC >> rw [] >> fs [INDEX_FIND_def] >> EVAL_TAC >> fs [typeOf_def, get_params_def]) >>
  rw [set_contract_state_def, get_envContractStates_def, UPDATE_def]
QED

Theorem successful_trace:
∀ e1 s1. 
  get_envContracts e1 caddr = SOME SCdeg ∧ 
  get_envContractStates e1 caddr = SOME s1 ∧
  s1.votingBase.status = Active ∧
  s1.servers = (h :: t) ∧
  s1.commissionDecryption = 0 ∧
  s1.commissionKey = "" ∧
  s1.votingBase.dateStart = NONE ⇒
  ∃ e.
  ChainTrace e1 e ∧    
  get_envContracts e caddr = SOME SCdeg ∧ 
  (THE (get_envContractStates e caddr)).votingBase.status = ResultsReceived ∧ 
  (THE (get_envContractStates e caddr)).commissionDecryption ≠ 0
Proof
  rpt STRIP_TAC >>
  STRIP_ASSUME_TAC commissionKey_isFeasible >> first_x_assum (qspecl_then [‘e1’, ‘s1’] mp_tac) >> fs[] >> rw [] >>
  STRIP_ASSUME_TAC startDate_isFeasible >> first_x_assum (qspecl_then [‘e2’, ‘THE (get_envContractStates e2 caddr)’] mp_tac)  >> fs[] >> rw [] >> 
  STRIP_ASSUME_TAC help1 >> first_x_assum (qspecl_then [‘e2’, ‘caddr’] mp_tac) >> rw [] >> FULL_SIMP_TAC std_ss [] >>
  STRIP_ASSUME_TAC stopDate_isFeasible >> first_x_assum (qspecl_then [‘e2'’, ‘THE (get_envContractStates e2' caddr)’] mp_tac)  >> fs[] >> rw [] >> 
  STRIP_ASSUME_TAC help1 >> first_x_assum (qspecl_then [‘e2'’, ‘caddr’] mp_tac) >> rw [] >> FULL_SIMP_TAC std_ss [] >>
  STRIP_ASSUME_TAC commissionDecryption_isFeasible >> first_x_assum (qspecl_then [‘e2''’, ‘THE (get_envContractStates e2'' caddr)’] mp_tac)  >> fs[] >> rw [] >> 
  STRIP_ASSUME_TAC help1 >> first_x_assum (qspecl_then [‘e2''’, ‘caddr’] mp_tac) >> rw [] >> FULL_SIMP_TAC std_ss [] >>
  STRIP_ASSUME_TAC resultsReceived_isFeasible >> first_x_assum (qspecl_then [‘e2'³'’, ‘THE (get_envContractStates e2'³' caddr)’] mp_tac)  >> fs[] >> rw [] >> 
  STRIP_ASSUME_TAC help1 >> first_x_assum (qspecl_then [‘e2'³'’, ‘caddr’] mp_tac) >> rw [] >> FULL_SIMP_TAC std_ss [] >> 
rw [ChainTrace_cases] >> 
rw [Once ChainedList_cases] >> Q.EXISTS_TAC ‘e2'⁴'’ >> rw [] >> DISJ2_TAC >>
Q.EXISTS_TAC `e2` >> rw [Once ChainedList_cases] >> DISJ2_TAC >> 
Q.EXISTS_TAC `e2'` >> rw [Once ChainedList_cases] >> DISJ2_TAC >> 
Q.EXISTS_TAC `e2''` >> rw [Once ChainedList_cases] >> DISJ2_TAC >>
Q.EXISTS_TAC ‘e2'³'’ >> rw [Once ChainedList_cases] >> DISJ2_TAC >>
Q.EXISTS_TAC ‘e2'⁴'’ >> rw [Once ChainedList_cases] >> DISJ2_TAC
QED


val _ = export_theory();
