open preamble
open basis
open ml_monad_translator_interfaceLib
open stringTheory
open wordsTheory
open listTheory
open pairTheory
open degTypesTheory

val _ = new_theory "deg";
val _ = translation_extends "basisProg";
val _ = ParseExtras.temp_tight_equality ();

val const_defs = [
  (* Errors: *)
  Define `GENERAL_ERROR = (1:num)(*"Type error"*)`,
  Define `BAD_STATUS = (2:num)(*"Status error"*)`,
  Define `EXTRACT_ERROR = (3:num)(*"Monadic_EL extract error"*)`,
  Define `ERR_TYPE_CONV = (4:num)(*"Type conversion error"*)`,
  Define `WRN_PARAMS = (5:num)(*"Wrong params"*)`,
  Define `AUTHENTIFICATION_ERROR = (6:num)(*"Authentification failed"*)`,
  Define `VOTING_NOT_STARTED = (7:num)(*"Voting not started"*)` 
];

Definition monadic_EL_def:
  monadic_EL s m l = if m < LENGTH l then (return (EL m l)) else (failwith s)
End

Definition set_state_votingBase_def:
set_state_votingBase (vb : votingBase): (State, unit, Exn) M
  = λ state. let new_state = state with votingBase := vb in (Success (), new_state)
End

Definition set_state_mainKey_def:
set_state_mainKey (s :  string): (State, unit, Exn) M
  = λ state. let new_state = state with mainKey := s in (Success (), new_state)
End

Definition set_state_comissionKey_def:
set_state_comissionKey (s :  string): (State, unit, Exn) M
  = λ state. let new_state = state with comissionKey := s in (Success (), new_state)
End

Definition set_state_dkgKey_def:
set_state_dkgKey (s :  string): (State, unit, Exn) M
  = λ state. let new_state = state with dkgKey := s in (Success (), new_state)
End

Definition set_state_blindSigIssueRegistrator_def:
set_state_blindSigIssueRegistrator (bir : num): (State, unit, Exn) M
  = λ state. let new_state = state with blindSigIssueRegistrator := bir in (Success (), new_state)
End

Definition set_state_servers_def:
set_state_servers (s : num list): (State, unit, Exn) M
  = λ state. let new_state = state with servers := s in (Success (), new_state)
End

Definition set_state_VotersListRegistrator_def:
set_state_VotersListRegistrator  (vlrs : num list): (State, unit, Exn) M
  = λ state. let new_state = state with VotersListRegistrator := vlrs in (Success (), new_state)
End

Definition set_state_votersList_def:
  set_state_votersList (p : (num # string)): (State, unit, Exn) M
  = λ state. let new_state = state with votersList := p in (Success (), new_state)
End

Definition set_state_removeFromVotersList_def:
  set_state_removeFromVotersList (p : (num # string)): (State, unit, Exn) M
  = λ state. let new_state = state with removeFromVotersList := p in (Success (), new_state)
End

Definition set_state_blindSig_def:
  set_state_blindSig (p : (num # blindSig list)): (State, unit, Exn) M
  = λ state. let new_state = state with blindSig := p in (Success (), new_state)
End

Definition set_state_blindSigFail_def:
  set_state_blindSigFail (p : (num # string)): (State, unit, Exn) M
  = λ state. let new_state = state with blindSigFail := p in (Success (), new_state)
End

Definition set_state_voteFail_def:
  set_state_voteFail (p : (num # (public_key # string))): (State, unit, Exn) M
  = λ state. let new_state = state with voteFail := p in (Success (), new_state)
End

Definition set_state_transactionCount_def:
  set_state_transactionCount (p : num): (State, unit, Exn) M
  = λ state. let new_state = state with transactionCount := p in (Success (), new_state)
End


Definition generate_transaction_id_def:
  generate_transaction_id =
  do
    state <- get_state;
    transaction_id <<- SUC state.transactionCount;
    _ <- set_state_transactionCount transaction_id;
    return transaction_id;
  od
End


(*MIDFUNCS ---------------------------------------------------------------------- *)

Definition scvalue_to_num_def:
scvalue_to_num (sc:SCvalue) : (State, num, Exn) M  =
  (λ (s:State). case sc of
    SCNum v => (Success v, s)  (*Success*)
  | _ => (Failure (CFail ERR_TYPE_CONV), s)) (*Failure*)
End

Definition scvalue_to_bool_def:
scvalue_to_bool (sc:SCvalue) : (State, bool, Exn) M  =
  (λ (s:State). case sc of
    SCBool b => (Success b, s)  (*Success*)
  | _ => (Failure (CFail ERR_TYPE_CONV), s)) (*Failure*)
End

Definition scvalue_to_string_def:
scvalue_to_string (sc:SCvalue) : (State, string, Exn) M  =
  (λ (s:State). case sc of
    SCString stri => (Success stri, s)  (*Success*)
  | _ => (Failure (CFail ERR_TYPE_CONV), s)) (*Failure*)
End

Definition scvalue_to_numlist_def:
scvalue_to_numlist (sc:SCvalue) : (State, num list, Exn) M  =
  (λ (s:State). case sc of
    SCNumList nl => (Success nl, s)  (*Success*)
  | _ => (Failure (CFail ERR_TYPE_CONV), s)) (*Failure*)
End

Definition scvalue_to_numoption_def:
scvalue_to_numoption (sc:SCvalue) : (State, num option, Exn) M  =
  (λ (s:State). case sc of
    SCNumOption no => (Success no, s)  (*Success*)
  | _ => (Failure (CFail ERR_TYPE_CONV), s)) (*Failure*)
End

Definition scvalue_to_numlistlist_def:
scvalue_to_numlistlist (sc:SCvalue) : (State, num list list, Exn) M  =
  (λ (s:State). case sc of
    SCNumListList nll => (Success nll, s)  (*Success*)
  | _ => (Failure (CFail ERR_TYPE_CONV), s)) (*Failure*)
End

Definition find_entity_def:
  find_entity (l : α list) (e:α) =
    FIND (λ (x : α). x = e) l
End


(* 103 *)
Definition initiateVoting_def:
  initiateVoting (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeString; TypeNumListList; TypeString; TypeString; TypeNumOption; TypeNumOption; TypeNumList; TypeNumList; TypeNum; TypeNum; TypeBool]);
    p0 <- monadic_EL EXTRACT_ERROR 0 params;
    p1 <- monadic_EL EXTRACT_ERROR 1 params;
    p2 <- monadic_EL EXTRACT_ERROR 2 params;
    p3 <- monadic_EL EXTRACT_ERROR 3 params;
    p4 <- monadic_EL EXTRACT_ERROR 4 params;
    p5 <- monadic_EL EXTRACT_ERROR 5 params;
    p6 <- monadic_EL EXTRACT_ERROR 6 params;
    p7 <- monadic_EL EXTRACT_ERROR 7 params;
    p8 <- monadic_EL EXTRACT_ERROR 8 params;
    p9 <- monadic_EL EXTRACT_ERROR 9 params;
    p10 <- monadic_EL EXTRACT_ERROR 10 params;(* может вообще не прийти. надо подумать как реализовать *)
    bulletinHash <- (scvalue_to_string p0);
    dimension <- (scvalue_to_numlistlist p1);
    blindSigModulo <- (scvalue_to_string p2);
    blindSigExponent <- (scvalue_to_string p3);
    dateStart <- (scvalue_to_numoption p4);
    dateEnd <- (scvalue_to_numoption p5);
    servers <- (scvalue_to_numlist p6);
    votersListRegistrators <- (scvalue_to_numlist p7);
    blindSigIssueRegistrator <- (scvalue_to_num p8);
    pollId <- (scvalue_to_num p9);
    isRevoteBlocked <- (scvalue_to_bool p10); 
    
    state <- get_state;
    voting_base <<- <|pollId:= pollId; bulletinHash:= bulletinHash; dimension:= dimension; blindSigModulo:= blindSigModulo; blindSigExponent:= blindSigExponent; dateStart:= dateStart; dateEnd:=dateEnd; isRevoteBlocked:=isRevoteBlocked; status:= Active|>; 
    _ <- set_state_votingBase voting_base;
    _ <- set_state_servers servers;
    _ <- set_state_VotersListRegistrator votersListRegistrators;
    _ <- set_state_BlindSigIssueRegistrator blindSigIssueRegistrator;
    return(SCUnit);
  od
End

(* 104 *)
Definition updateServerList_def:
  updateServerList (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeNumList]);
    p0 <- monadic_EL EXTRACT_ERROR 0 params;
    servers <- (scvalue_to_numlist p0);
    
    state <- get_state;
    _ <- set_state_servers servers;
    return(SCUnit);
  od
End

(* 104 *)
Definition addMainKey_def:
  addMainKey (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeString; TypeString; TypeString]);
    p0 <- monadic_EL EXTRACT_ERROR 0 params;
    p1 <- monadic_EL EXTRACT_ERROR 1 params;
    p2 <- monadic_EL EXTRACT_ERROR 2 params;
    
    state <- get_state;    
    server_option <<- (find_entity state.servers state.context.msg_sender);
    assert AUTHENTIFICATION_ERROR (server_option ≠ NONE);
    case (state.votingBase.dateStart) of
      NONE   => assert VOTING_NOT_STARTED (state.votingBase.status = Active) |
      SOME t =>
    assert VOTING_NOT_STARTED ((t > state.context.block_timestamp) /\ (state.votingBase.status = Active));
    
    mainKey <- (scvalue_to_string p0);
    comissionKey <- (scvalue_to_string p1);
    dkgKey <- (scvalue_to_string p2);
    _ <- set_state_mainKey mainKey;
    _ <- set_state_comissionKey comissionKey;
    _ <- set_state_dkgKey dkgKey;
    return(SCUnit);
  od
End

(* 104 *)
Definition addVotersList_def:
  addVotersList (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeString]);
    p0 <- monadic_EL EXTRACT_ERROR 0 params;
    
    state <- get_state;    
    votersListRegistrator_option <<- (find_entity state.VotersListRegistrator state.context.msg_sender);
    assert AUTHENTIFICATION_ERROR (votersListRegistrator_option ≠ NONE);
    
    userIdHashes <- (scvalue_to_string p0);

    transaction_id <- generate_transaction_id;

        _ <- set_state_votersList (transaction_id, userIdHashes);
    return(SCUnit);
  od
End

(* 104 *)
Definition removeFromVotersList_def:
  removeFromVotersList (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeString]);
    p0 <- monadic_EL EXTRACT_ERROR 0 params;
    
    state <- get_state;    
    votersListRegistrator_option <<- (find_entity state.VotersListRegistrator state.context.msg_sender);
    assert AUTHENTIFICATION_ERROR (votersListRegistrator_option ≠ NONE);
    
    userIdHashes <- (scvalue_to_string p0);

    transaction_id <- generate_transaction_id;

        _ <- set_state_removeFromVotersList (transaction_id, userIdHashes);
    return(SCUnit);
  od
End
