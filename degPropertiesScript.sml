(*START ------------------------------------------------------------------------- *)
open preamble
open basis
open ml_monad_translator_interfaceLib

open stringTheory
open wordsTheory
open listTheory
open degTypesTheory
open degTheory

val _ = new_theory "degProperties";
val _ = translation_extends "basisProg";
val _ = ParseExtras.temp_tight_equality ();

(*CONSTS ------------------------------------------------------------------------ *)
val const_defs = [
  (* Errors: *)
  Define `WRN_PARAMS = "Wrong params"`,
  Define `RequiredParamIsMissing = "Monadic_EL extract error, some parameter is missing"`,
  Define `RequiredParamValueMissing = "Type conversion error, some parameter type is incorrect"`,
  Define `ServersDoNotContainSenderPubKey = "Couldn't find the server that contains sender"`,
  Define `ServersListIsEmpty = "Servers list is empty"`,
  Define `VotingIsNotInProgress = "Voting is not in progress (has already finished or not yet started)"`,
  Define `VotingAlreadyStarted = "Voting has already started"`,
  Define `SenderIsNotVotingRegistrator = "Sender is not the voting registrator"`,
  Define `StartDateAlreadyInStateError = "Start date already in state"`,
  Define `SenderIsNotBlindSigIssueRegistrator = "Sender is not the blind sig issue registrator"`,
  Define `EmptyStartDateError = "Start date must be in state before operation starts"`,
  Define `StartDateHasNotComeYet = "Start date has not come yet"`,
  Define `BlindSigIsNotEqual = "Existing 'blindSig' value is not equal to new value"`, 
  Define `RevoteIsBlockedError = "Revote is blocked"`,
  Define `VotingIsNotYetFinished= "Voting is not yet finished (is in progress or not yet started)"`,
  Define `InvalidCommissionSecretKey = "Commission secret key doesn't match with the commission key from the state"`
];

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


Theorem results_status_error:
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

Theorem results_status_error:
∀ state. ∀  params.
(results params state  = fail VotingIsNotYetFinished state) ⇔ 
(check_types params [TypeNumList] ∧
∃ l. params = [SCNumList l] ∧
find_entity state.servers state.context.msg_sender ≠ NONE ∧
¬(state.votingBase.status = Completed))
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

val _ = export_theory();
