open preamble
open basis
open ml_monad_translator_interfaceLib
open stringTheory
open wordsTheory
open listTheory
open pairTheory

val _ = new_theory "degTypes";
val _ = translation_extends "basisProg";
val _ = ParseExtras.temp_tight_equality ();

Datatype:
  VotingStatus = Active | Halted | Completed | ResultsReceived
End

Datatype:
  votingBase = <|
    pollId: num;
    bulletinHash: string; 
    dimension: (num list) list;
    blindSigModulo: num; 
    blindSigExponent: num; 
    dateStart: num option;
    dateEnd: num option; 
    status: VotingStatus;
    isRevoteBlocked: bool;
    startDateIssueBallots: num option;
    stopDateIssueBallots: num option;
    |>
End

Datatype:
  blindSig = <| userId: num; maskedSig: string |>;
End

Datatype:
  vote = <| userId: num; vote: num; blindSig: num |>;
End

Datatype:
  Context = <| msg_sender: num; block_number: num; block_timestamp: num |>
End

Datatype:
  State = <|
    context: Context;    
    transactionCount: num;
    
    votingBase: votingBase;

    servers: num list;
    VotersListRegistrator: num list; 
    blindSigIssueRegistrator: num;
    IssueBallotsRegistrator: num;

    commissionKey: string;
    dkgKey: string;
    mainKey: string;

    votersList: num -> string;
    votersListAdd: num -> string;
    votersListRemove: num -> string;

    blindSig: num -> blindSig list;
    votes: vote list;
    
    decryption: num -> num;
    commissionDecryption: num;
    
    results: num list;    
    
    blindSigFail: num -> string; 
    voteFail: (num # (num # string)) list;
    |>
End

Datatype:
  SCType = TypeUnit
  | TypeNum
  | TypeString
  | TypeBool
  | TypeNumList
  | TypeNumOption
  | TypeNumListList
  | TypeNumStringList
End

Datatype:
  SCvalue = SCUnit
  | SCNum num
  | SCString string
  | SCBool bool
  | SCNumListList ((num list) list)
  | SCNumList (num list)
  | SCNumOption (num option)
  | SCNumStringList ((num # string) list)
End

Definition typeOf_def:
  typeOf (SCUnit) = TypeUnit ∧
  typeOf (SCNum _) = TypeNum ∧
  typeOf (SCString _) = TypeString ∧
  typeOf (SCBool _) = TypeBool ∧
  typeOf (SCNumList _) = TypeNumList ∧
  typeOf (SCNumOption _) = TypeNumOption ∧
  typeOf (SCNumListList _) = TypeNumListList ∧
  typeOf (SCNumStringList _) = TypeNumStringList
End

Definition check_types_def:
  check_types params param_types = (MAP typeOf params = param_types)
End

Type state_references = ``:State``

Datatype:
  Exn = Fail string
End

val config =  global_state_config
              |> with_state ``:state_references``
              |> with_exception ``:Exn``;
Overload failwith = ``raise_Fail``
Overload fail = ``failwith : string -> State -> (α, Exn) exc # State``  (*α = SCvalue*)
val _ = start_translation config;

Definition assert_def:
  assert (errstr:string) (b:bool) : (state_references, unit, Exn) M =
    if b then
      return ()
    else
      failwith errstr
End

Definition get_state_def:
get_state : (State, State, Exn) M =
  λ (s:State). (Success s, s)
End

val _ = export_theory();
