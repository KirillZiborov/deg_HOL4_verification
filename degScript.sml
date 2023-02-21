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
  Define `VOTING_NOT_STARTED = (7:num)(*"Voting not started"*)`,
  Define `START_DATE_ALREADY_SET = (8:num)(*"Start date is already set"*)`,
  Define `BLINDSIG_ERROR = (9:num)(*"Bling signature is not correct"*)`, 
  Define `ALREADY_VOTED = (10:num)(*"You have already voted!"*)`,
  Define `VOTING_NOT_FINISHED = (11:num)(*"Voting not finished"*)`,
  Define `COMMISSION_SECRET_KEY_IS_INCORRECT = (12:num)(*"Commission secret key is incorrect"*)`
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

Definition set_state_decryption_def:
set_state_decryption (s : num): (State, unit, Exn) M
  = λ state. let new_state = state with decryption := s in (Success (), new_state)
End

Definition set_state_commission_decryption_def:
set_state_commission_decryption (s : num): (State, unit, Exn) M
  = λ state. let new_state = state with commisionDecryption := s in (Success (), new_state)
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
  set_state_votersList (p : (num # string) list): (State, unit, Exn) M
  = λ state. let new_state = state with votersList := p in (Success (), new_state)
End

Definition set_state_votersListAdd_def:
  set_state_votersListAdd (p : (num # string) list): (State, unit, Exn) M
  = λ state. let new_state = state with votersListAdd := p in (Success (), new_state)
End

Definition set_state_removeFromVotersList_def:
  set_state_removeFromVotersList (p : (num # string) list): (State, unit, Exn) M
  = λ state. let new_state = state with removeFromVotersList := p in (Success (), new_state)
End

Definition set_state_blindSig_def:
  set_state_blindSig (p : (num # blindSig list) list): (State, unit, Exn) M
  = λ state. let new_state = state with blindSig := p in (Success (), new_state)
End

Definition set_state_votes_def:
  set_state_votes (p : vote list): (State, unit, Exn) M
  = λ state. let new_state = state with votes := p in (Success (), new_state)
End


Definition set_state_blindSigFail_def:
  set_state_blindSigFail (p : (num # num)): (State, unit, Exn) M
  = λ state. let new_state = state with blindSigFail := p in (Success (), new_state)
End

Definition set_state_voteFail_def:
  set_state_voteFail (p : (num # (num # num))): (State, unit, Exn) M
  = λ state. let new_state = state with voteFail := p in (Success (), new_state)
End

Definition set_state_transactionCount_def:
  set_state_transactionCount (p : num): (State, unit, Exn) M
  = λ state. let new_state = state with transactionCount := p in (Success (), new_state)
End

Definition set_state_results_def:
  set_state_results (p : num list): (State, unit, Exn) M
  = λ state. let new_state = state with results := p in (Success (), new_state)
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

Definition scvalue_to_word8list_def:
scvalue_to_word8list (sc:SCvalue) : (State, word8 list, Exn) M  =
  (λ (s:State). case sc of
    SCWord8List stri => (Success stri, s)  (*Success*)
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

Definition scvalue_to_numstringlist_def:
scvalue_to_numstringlist (sc:SCvalue) : (State, (num # string) list, Exn) M  =
  (λ (s:State). case sc of
    SCNumStringList nll => (Success nll, s)  (*Success*)
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
    p10 <- monadic_EL EXTRACT_ERROR 10 params;
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
    _ <- set_state_blindSigIssueRegistrator blindSigIssueRegistrator;
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

    updated_voters <<- ((transaction_id, userIdHashes) :: state.votersList);    
        _ <- set_state_votersList updated_voters;
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

    updated_removedVoters <<- ((transaction_id, userIdHashes) :: state.removeFromVotersList);
        _ <- set_state_removeFromVotersList updated_removedVoters;
    return(SCUnit);
  od
End

(* 104 *)
Definition addToVotersList_def:
  addToVotersList (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeString]);
    p0 <- monadic_EL EXTRACT_ERROR 0 params;
    
    state <- get_state;    
    votersListRegistrator_option <<- (find_entity state.VotersListRegistrator state.context.msg_sender);
    assert AUTHENTIFICATION_ERROR (votersListRegistrator_option ≠ NONE);
    
    userIdHashes <- (scvalue_to_string p0);

    transaction_id <- generate_transaction_id;

    updated_addedVoters <<- ((transaction_id, userIdHashes) :: state.votersListAdd);
        _ <- set_state_votersListAdd updated_addedVoters;
    return(SCUnit);
  od
End

(* соответствует github-версии *)
(* 104 *)
Definition startVoting_def:
  startVoting : (State, SCvalue, Exn) M =
  do
    state <- get_state;    
    server_option <<- (find_entity state.servers state.context.msg_sender);
    assert AUTHENTIFICATION_ERROR (server_option ≠ NONE);

    assert START_DATE_ALREADY_SET (state.votingBase.dateStart = NONE);
    
    voting_base <<- state.votingBase with dateStart := SOME state.context.block_timestamp;
    _ <- set_state_votingBase voting_base;

    return(SCUnit);
  od
End

(* 104 *)
Definition blindSigIssue_def:
  blindSigIssue (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeNumStringList]);
    p0 <- monadic_EL EXTRACT_ERROR 0 params;
    data <- (scvalue_to_numstringlist p0);

    state <- get_state;
    transaction_id <- generate_transaction_id;

    if (state.blindSigIssueRegistrator ≠ state.context.msg_sender) 
    then do
        _ <- set_state_blindSigFail (transaction_id, AUTHENTIFICATION_ERROR);
        failwith AUTHENTIFICATION_ERROR;
      od
    else case (state.votingBase.dateStart) of
      NONE   => if (state.votingBase.status = Active) then return ()
                else do
                 _ <- set_state_blindSigFail (transaction_id, VOTING_NOT_STARTED);
                 failwith VOTING_NOT_STARTED;
                     od |
      SOME t => if ((t > state.context.block_timestamp) /\ (state.votingBase.status = Active))
                  then return ()
                  else do 
                 _ <- set_state_blindSigFail (transaction_id, VOTING_NOT_STARTED);
                 failwith VOTING_NOT_STARTED;
                       od;


    blindSigs <<- MAP (\(id:num, ms:string). <| userId:= id; maskedSig:= ms |>) data;

    updated_blindSigs <<- ((transaction_id, blindSigs) :: state.blindSig);
    _ <- set_state_blindSig updated_blindSigs;

    return(SCUnit);
  od
End

(* 104 *)
Definition vote_def:
  vote (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeWord8List; TypeString]);
    p0 <- monadic_EL EXTRACT_ERROR 0 params;
    p1 <- monadic_EL EXTRACT_ERROR 1 params;
    vote <- (scvalue_to_word8list p0);
    sig <- (scvalue_to_string p1);

    state <- get_state;
    transaction_id <- generate_transaction_id;

    case (state.votingBase.dateStart) of
      NONE   => assert VOTING_NOT_STARTED (state.votingBase.status = Active) |
      SOME t =>
    assert VOTING_NOT_STARTED ((t > state.context.block_timestamp) /\ (state.votingBase.status = Active));

    vote_option <<- FIND (λ x. x.userId = state.context.msg_sender) state.votes;

    case (vote_option) of
      NONE   => return () |
      SOME t => do assert ALREADY_VOTED (¬state.votingBase.isRevoteBlocked);
                   assert BLINDSIG_ERROR (t.blindSig.maskedSig = sig);
                od;

    (* Проверка корректности слепой подписи *)
    
    updated_votes <<- ((<| userId := state.context.msg_sender; vote := vote; 
                          blindSig := <| userId:= state.context.msg_sender; maskedSig:= sig |> |>) :: state.votes);

    _ <- set_state_votes updated_votes;

    return(SCUnit);
  od
End

(* 104 *)
Definition finishVoting_def:
  finishVoting : (State, SCvalue, Exn) M =
  do
    state <- get_state;
    vb <<- state.votingBase;

    server_option <<- (find_entity state.servers state.context.msg_sender);
    assert AUTHENTIFICATION_ERROR (server_option ≠ NONE);
    assert VOTING_NOT_STARTED (state.votingBase.status = Active);

    case (state.votingBase.dateStart) of
      NONE   =>  do vb <<- vb with status := Halted; return () od |
      SOME t => if (t > state.context.block_timestamp)
                  then do vb <<- vb with status := Halted; return () od
                  else do vb <<- vb with status := Completed; return () od;

    vb <<- vb with dateEnd := SOME state.context.block_timestamp;

    _ <- set_state_votingBase vb;
    return(SCUnit);
  od
End

(* 104 *)
Definition decryption_def:
  decryption : (State, SCvalue, Exn) M =
  do
    state <- get_state;
    transaction_id <- generate_transaction_id;

    server_option <<- (find_entity state.servers state.context.msg_sender);
    assert AUTHENTIFICATION_ERROR (server_option ≠ NONE);
    assert VOTING_NOT_FINISHED (state.votingBase.status = Completed);

    _ <- set_state_decryption transaction_id;
    return(SCUnit);
  od
End

(* 104 *)
Definition commissionDecryption_def:
  commissionDecryption (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeString]);
    p0 <- monadic_EL EXTRACT_ERROR 0 params;
    key <- (scvalue_to_string p0);

    state <- get_state;
    transaction_id <- generate_transaction_id;

    server_option <<- (find_entity state.servers state.context.msg_sender);
    assert AUTHENTIFICATION_ERROR (server_option ≠ NONE);
    assert VOTING_NOT_FINISHED (state.votingBase.status = Completed);
    assert COMMISSION_SECRET_KEY_IS_INCORRECT (state.comissionKey = key);

    _ <- set_state_commission_decryption transaction_id;
    return(SCUnit);
  od
End

(* 104 *)
Definition results_def:
  results (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeNumList]);
    p0 <- monadic_EL EXTRACT_ERROR 0 params;
    results <- (scvalue_to_numlist p0);

    state <- get_state;

    server_option <<- (find_entity state.servers state.context.msg_sender);
    assert AUTHENTIFICATION_ERROR (server_option ≠ NONE);
    assert VOTING_NOT_FINISHED (state.votingBase.status = Completed);

    _ <- set_state_results results;
    return(SCUnit);
  od
End
