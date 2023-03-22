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
  Define `InvalidCommissionSecretKey = "Commission secret key doesn't match with the commission key from the state"`,
  Define `InvalidBlindSig = "Verification failed for blind signature"`,
  Define `IssueBallotsAlreadyStarted = "Issue ballots are already started"`,
  Define `IssueBallotsAlreadyStopped = "Issue ballots are already stopped"`,
  Define `SenderIsNotIssueBallotsRegistrator = "Sender is not the Issue ballots registrator"`
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

Definition set_state_commissionKey_def:
set_state_commissionKey (s :  string): (State, unit, Exn) M
  = λ state. let new_state = state with commissionKey := s in (Success (), new_state)
End

Definition set_state_dkgKey_def:
set_state_dkgKey (s :  string): (State, unit, Exn) M
  = λ state. let new_state = state with dkgKey := s in (Success (), new_state)
End

Definition set_state_decryption_def:
set_state_decryption (s : (num # num) list): (State, unit, Exn) M
  = λ state. let new_state = state with decryption := s in (Success (), new_state)
End

Definition set_state_commission_decryption_def:
set_state_commission_decryption (s : num): (State, unit, Exn) M
  = λ state. let new_state = state with commissionDecryption := s in (Success (), new_state)
End

Definition set_state_blindSigIssueRegistrator_def:
set_state_blindSigIssueRegistrator (bir : num): (State, unit, Exn) M
  = λ state. let new_state = state with blindSigIssueRegistrator := bir in (Success (), new_state)
End

Definition set_state_IssueBallotsRegistrator_def:
set_state_IssueBallotsRegistrator (ibr : num): (State, unit, Exn) M
  = λ state. let new_state = state with IssueBallotsRegistrator := ibr in (Success (), new_state)
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

Definition set_state_votersListRemove_def:
  set_state_votersListRemove (p : (num # string) list): (State, unit, Exn) M
  = λ state. let new_state = state with votersListRemove := p in (Success (), new_state)
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
  set_state_blindSigFail (p : (num # string) list): (State, unit, Exn) M
  = λ state. let new_state = state with blindSigFail := p in (Success (), new_state)
End

Definition set_state_voteFail_def:
  set_state_voteFail (p : (num # (num # string)) list): (State, unit, Exn) M
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
  | _ => (Failure (Fail RequiredParamValueMissing), s)) (*Failure*)
End

Definition scvalue_to_bool_def:
scvalue_to_bool (sc:SCvalue) : (State, bool, Exn) M  =
  (λ (s:State). case sc of
    SCBool b => (Success b, s)  (*Success*)
  | _ => (Failure (Fail RequiredParamValueMissing), s)) (*Failure*)
End

Definition scvalue_to_string_def:
scvalue_to_string (sc:SCvalue) : (State, string, Exn) M  =
  (λ (s:State). case sc of
    SCString stri => (Success stri, s)  (*Success*)
  | _ => (Failure (Fail RequiredParamValueMissing), s)) (*Failure*)
End

Definition scvalue_to_word8list_def:
scvalue_to_word8list (sc:SCvalue) : (State, word8 list, Exn) M  =
  (λ (s:State). case sc of
    SCWord8List stri => (Success stri, s)  (*Success*)
  | _ => (Failure (Fail RequiredParamValueMissing), s)) (*Failure*)
End

Definition scvalue_to_numlist_def:
scvalue_to_numlist (sc:SCvalue) : (State, num list, Exn) M  =
  (λ (s:State). case sc of
    SCNumList nl => (Success nl, s)  (*Success*)
  | _ => (Failure (Fail RequiredParamValueMissing), s)) (*Failure*)
End

Definition scvalue_to_numoption_def:
scvalue_to_numoption (sc:SCvalue) : (State, num option, Exn) M  =
  (λ (s:State). case sc of
    SCNumOption no => (Success no, s)  (*Success*)
  | _ => (Failure (Fail RequiredParamValueMissing), s)) (*Failure*)
End

Definition scvalue_to_numlistlist_def:
scvalue_to_numlistlist (sc:SCvalue) : (State, num list list, Exn) M  =
  (λ (s:State). case sc of
    SCNumListList nll => (Success nll, s)  (*Success*)
  | _ => (Failure (Fail RequiredParamValueMissing), s)) (*Failure*)
End

Definition scvalue_to_numstringlist_def:
scvalue_to_numstringlist (sc:SCvalue) : (State, (num # string) list, Exn) M  =
  (λ (s:State). case sc of
    SCNumStringList nll => (Success nll, s)  (*Success*)
  | _ => (Failure (Fail RequiredParamValueMissing), s)) (*Failure*)
End

Definition find_entity_def:
  find_entity (l : α list) (e:α) =
    FIND (λ (x : α). x = e) l
End


(* 103 *)
Definition initiateVoting_def:
  initiateVoting (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeNum; TypeString; TypeNumListList; TypeNum; TypeNum; TypeNumOption; TypeNumOption; TypeNumList; TypeNumList; TypeNum; TypeNum; TypeBool]);
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    p1 <- monadic_EL RequiredParamIsMissing 1 params;
    p2 <- monadic_EL RequiredParamIsMissing 2 params;
    p3 <- monadic_EL RequiredParamIsMissing 3 params;
    p4 <- monadic_EL RequiredParamIsMissing 4 params;
    p5 <- monadic_EL RequiredParamIsMissing 5 params;
    p6 <- monadic_EL RequiredParamIsMissing 6 params;
    p7 <- monadic_EL RequiredParamIsMissing 7 params;
    p8 <- monadic_EL RequiredParamIsMissing 8 params;
    p9 <- monadic_EL RequiredParamIsMissing 9 params;
    p10 <- monadic_EL RequiredParamIsMissing 10 params;
    p11 <- monadic_EL RequiredParamIsMissing 11 params;
    pollId <- (scvalue_to_num p0);
    bulletinHash <- (scvalue_to_string p1);
    dimension <- (scvalue_to_numlistlist p2);
    blindSigModulo <- (scvalue_to_num p3);
    blindSigExponent <- (scvalue_to_num p4);
    dateStart <- (scvalue_to_numoption p5);
    dateEnd <- (scvalue_to_numoption p6);
    servers <- (scvalue_to_numlist p7);
    votersListRegistrators <- (scvalue_to_numlist p8);
    blindSigIssueRegistrator <- (scvalue_to_num p9);
    IssueBallotsRegistrator <- (scvalue_to_num p10); 
    isRevoteBlocked <- (scvalue_to_bool p11);

    assert ServersListIsEmpty (servers ≠ []);
    
    state <- get_state;
    voting_base <<- <|pollId:= pollId; bulletinHash:= bulletinHash; dimension:= dimension; blindSigModulo:= blindSigModulo; blindSigExponent:= blindSigExponent; dateStart:= dateStart; dateEnd:= dateEnd; isRevoteBlocked:= isRevoteBlocked; status:= Active; startDateIssueBallots:= NONE;
    stopDateIssueBallots:= NONE|>; 
    _ <- set_state_votingBase voting_base;
    _ <- set_state_servers servers;
    _ <- set_state_VotersListRegistrator votersListRegistrators;
    _ <- set_state_blindSigIssueRegistrator blindSigIssueRegistrator;
    _ <- set_state_IssueBallotsRegistrator IssueBallotsRegistrator;
    return(SCUnit);
  od
End

(* 104 *)
Definition updateServerList_def:
  updateServerList (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeNumList]);
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    servers <- (scvalue_to_numlist p0);
    assert ServersListIsEmpty (servers ≠ []);

    state <- get_state;
    server_option <<- (find_entity state.servers state.context.msg_sender);
    assert ServersDoNotContainSenderPubKey (server_option ≠ NONE);
    
    _ <- set_state_servers servers;
    return(SCUnit);
  od
End

(* 104 *)
Definition addMainKey_def:
  addMainKey (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeString; TypeString; TypeString]);
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    p1 <- monadic_EL RequiredParamIsMissing 1 params;
    p2 <- monadic_EL RequiredParamIsMissing 2 params;
    
    state <- get_state;    
    server_option <<- (find_entity state.servers state.context.msg_sender);
    assert ServersDoNotContainSenderPubKey (server_option ≠ NONE);
    case (state.votingBase.dateStart) of
      NONE   => assert VotingIsNotInProgress (state.votingBase.status = Active) |
      SOME t =>
    assert VotingAlreadyStarted ((t > state.context.block_timestamp) /\ (state.votingBase.status = Active));
    
    mainKey <- (scvalue_to_string p0);
    commissionKey <- (scvalue_to_string p1);
    dkgKey <- (scvalue_to_string p2);
    _ <- set_state_mainKey mainKey;
    _ <- set_state_commissionKey commissionKey;
    _ <- set_state_dkgKey dkgKey;
    return(SCUnit);
  od
End

(* 104 *)
Definition addVotersList_def:
  addVotersList (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeString]);
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    
    state <- get_state;    
    votersListRegistrator_option <<- (find_entity state.VotersListRegistrator state.context.msg_sender);
    assert SenderIsNotVotingRegistrator (votersListRegistrator_option ≠ NONE);
    
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
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    
    state <- get_state;    
    votersListRegistrator_option <<- (find_entity state.VotersListRegistrator state.context.msg_sender);
    assert SenderIsNotVotingRegistrator (votersListRegistrator_option ≠ NONE);
    
    userIdHashes <- (scvalue_to_string p0);

    transaction_id <- generate_transaction_id;

    updated_removedVoters <<- ((transaction_id, userIdHashes) :: state.votersListRemove);
        _ <- set_state_votersListRemove updated_removedVoters;
    return(SCUnit);
  od
End

(* 104 *)
Definition addToVotersList_def:
  addToVotersList (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeString]);
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    
    state <- get_state;    
    votersListRegistrator_option <<- (find_entity state.VotersListRegistrator state.context.msg_sender);
    assert SenderIsNotVotingRegistrator (votersListRegistrator_option ≠ NONE);
    
    userIdHashes <- (scvalue_to_string p0);

    transaction_id <- generate_transaction_id;

    updated_addedVoters <<- ((transaction_id, userIdHashes) :: state.votersListAdd);
        _ <- set_state_votersListAdd updated_addedVoters;
    return(SCUnit);
  od
End

(* 104 *)
Definition startIssueBallots_def:
  startIssueBallots (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeNum]);
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    
    state <- get_state;

    assert SenderIsNotIssueBallotsRegistrator (state.IssueBallotsRegistrator = state.context.msg_sender);
    assert IssueBallotsAlreadyStarted (state.votingBase.startDateIssueBallots = NONE);

    startDateIssueBallots <- (scvalue_to_num p0);

    vb <<- state.votingBase with startDateIssueBallots:= SOME startDateIssueBallots;
        _ <- set_state_votingBase vb;
    return(SCUnit);
  od
End

(* 104 *)
Definition stopIssueBallots_def:
  stopIssueBallots (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeNum]);
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    
    state <- get_state;

    assert SenderIsNotIssueBallotsRegistrator (state.IssueBallotsRegistrator = state.context.msg_sender);
    assert IssueBallotsAlreadyStopped (state.votingBase.stopDateIssueBallots = NONE);

    stopDateIssueBallots <- (scvalue_to_num p0);

    vb <<- state.votingBase with stopDateIssueBallots:= SOME stopDateIssueBallots;
        _ <- set_state_votingBase vb;
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
    assert ServersDoNotContainSenderPubKey (server_option ≠ NONE);

    assert StartDateAlreadyInStateError (state.votingBase.dateStart = NONE);
    
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
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    data <- (scvalue_to_numstringlist p0);

    state <- get_state;
    transaction_id <- generate_transaction_id;

    if (state.blindSigIssueRegistrator ≠ state.context.msg_sender) 
    then do
        updated_blindSigFail <<- ((transaction_id, SenderIsNotBlindSigIssueRegistrator) :: state.blindSigFail);
        _ <- set_state_blindSigFail updated_blindSigFail;
        failwith SenderIsNotBlindSigIssueRegistrator;
      od
    else case (state.votingBase.dateStart) of
      NONE   => do
                updated_blindSigFail <<- ((transaction_id, EmptyStartDateError) :: state.blindSigFail);
                _ <- set_state_blindSigFail updated_blindSigFail;
                 failwith EmptyStartDateError;
                od |
      SOME t => if ((t < state.context.block_timestamp) /\ (state.votingBase.status = Active))
                then return ()
                else do
                 updated_blindSigFail <<- ((transaction_id, StartDateHasNotComeYet) :: state.blindSigFail);
                 _ <- set_state_blindSigFail updated_blindSigFail;
                 failwith StartDateHasNotComeYet;
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
    assert  WRN_PARAMS (check_types params [TypeWord8List; TypeNum; TypeNum]);
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    p1 <- monadic_EL RequiredParamIsMissing 1 params;
    p2 <- monadic_EL RequiredParamIsMissing 2 params;
    vote <- (scvalue_to_word8list p0);
    sig <- (scvalue_to_num p1);
    fdh <- (scvalue_to_num p2);

    state <- get_state;
    transaction_id <- generate_transaction_id;

    case (state.votingBase.dateStart) of
      NONE   => do
                 updated_voteFail <<- ((transaction_id, (state.context.msg_sender, EmptyStartDateError)) :: state.voteFail);
                  _ <- set_state_voteFail updated_voteFail;
                 failwith EmptyStartDateError;
                od |
      SOME t => if ((t < state.context.block_timestamp) /\ (state.votingBase.status = Active)) then return ()
                else do
                 updated_voteFail <<- ((transaction_id, (state.context.msg_sender, StartDateHasNotComeYet)) :: state.voteFail);
                 _ <- set_state_voteFail updated_voteFail;
                 failwith StartDateHasNotComeYet;
                     od;

    vote_option <<- FIND (λ x. x.userId = state.context.msg_sender) state.votes;

    case (vote_option) of
      NONE   => return () |
      SOME t => if (¬state.votingBase.isRevoteBlocked) 
                then if (t.blindSig = sig) then return ()
                     else do
                      updated_voteFail <<- ((transaction_id, (state.context.msg_sender, BlindSigIsNotEqual)) :: state.voteFail);
                      _ <- set_state_voteFail updated_voteFail;
                      failwith BlindSigIsNotEqual;
                          od
                else do
                 updated_voteFail <<- ((transaction_id, (state.context.msg_sender, RevoteIsBlockedError)) :: state.voteFail);
                  _ <- set_state_voteFail updated_voteFail;
                 failwith RevoteIsBlockedError;
                     od;

    (* Проверка корректности слепой подписи *)
    (* В HOL4-модели контракта мы предполагаем, что алгоритм FDH-СТРИБОГ-256 работает корректно и опускаем его реализацию.
    Также мы предполагаем, что на вход функция vote получает помимо слепой подписи sig результат работы хэш-функции fdh 
    и сравниваем его с result: *)

    result <<- ($EXP sig state.votingBase.blindSigExponent) MOD state.votingBase.blindSigModulo; 
    if (result = fdh) then return () 
    else do  
     updated_voteFail <<- ((transaction_id, (state.context.msg_sender, InvalidBlindSig)) :: state.voteFail);
     _ <- set_state_voteFail updated_voteFail;
     failwith RevoteIsBlockedError;
         od;

    
    updated_votes <<- ((<| userId := state.context.msg_sender; vote := vote; blindSig :=  sig |> ) :: state.votes);

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
    assert ServersDoNotContainSenderPubKey (server_option ≠ NONE);

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
    assert ServersDoNotContainSenderPubKey (server_option ≠ NONE);
    assert VotingIsNotYetFinished(state.votingBase.status = Completed);

    updated_decryption <<- ((transaction_id, state.context.msg_sender) :: state.decryption);
    _ <- set_state_decryption updated_decryption;
    return(SCUnit);
  od
End

(* 104 *)
Definition commissionDecryption_def:
  commissionDecryption (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert WRN_PARAMS (check_types params [TypeString]);
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    resolvedPublicKey <- (scvalue_to_string p0);

    state <- get_state;
    transaction_id <- generate_transaction_id;

    server_option <<- (find_entity state.servers state.context.msg_sender);
    assert ServersDoNotContainSenderPubKey (server_option ≠ NONE);
    assert VotingIsNotYetFinished(state.votingBase.status = Completed);

    (* Проверка приватного ключа на публичном ключе state.commissionKey *)
    (* В HOL4-модели контракта мы предполагаем, что алгоритм проверки приватного ключа на публичном ключе работает корректно и 
    опускаем его реализацию.
    Также мы предполагаем, что на вход функция получает сразу resolvedPublicKey, полученный из приватного ключа *)
    assert InvalidCommissionSecretKey (state.commissionKey = resolvedPublicKey);

    _ <- set_state_commission_decryption transaction_id;
    return(SCUnit);
  od
End

(* 104 *)
Definition results_def:
  results (params : SCvalue list) : (State, SCvalue, Exn) M =
  do
    assert  WRN_PARAMS (check_types params [TypeNumList]);
    p0 <- monadic_EL RequiredParamIsMissing 0 params;
    results <- (scvalue_to_numlist p0);

    state <- get_state;
    vb <<- state.votingBase;

    server_option <<- (find_entity state.servers state.context.msg_sender);
    assert ServersDoNotContainSenderPubKey (server_option ≠ NONE);
    assert VotingIsNotYetFinished (state.votingBase.status = Completed);

    vb <<- vb with status := ResultsReceived;
    _ <- set_state_results results;
    _ <- set_state_votingBase vb;
    return(SCUnit);
  od
End

val _ = export_theory();
