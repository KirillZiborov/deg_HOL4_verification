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
  VotingStatus = Active | Halted | Completed
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
    |>
End

Datatype:
blindSig = <|
    userId: num;
    maskedSig: string;
    |>;
End

Datatype:
  vote = <|
    userId: num;
    vote: word8 list;
    blindSig: blindSig;
    |>;
End

Datatype:
  Context = <|
    msg_sender: num;
    block_number: num;
    block_timestamp: num;
  |>
End

Datatype:
  State = <|
    context: Context;    
    transactionCount: num;

    votes: vote list;
    comissionKey: string;
    commisionDecryption: num;
    dkgKey: string;
    mainKey: string;
    results: num list;
    servers: num list;
    votingBase: votingBase;

    VotersListRegistrator: num list; 
    blindSigIssueRegistrator: num;
    IssueBallotsRegistrator: num;
    decryption: (num # num) list;

    votersList: (num # string) list;
    votersListAdd: (num # string) list;
    votersListRemove: (num # string) list;
    blindSig: (num # blindSig list) list;
    blindSigFail: (num # num); 
    voteFail: (num # (num # num));
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
  | TypeWord8List
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
  | SCWord8List (word8 list)
End

Definition typeOf_def:
  typeOf (SCUnit) = TypeUnit ∧
  typeOf (SCNum _) = TypeNum ∧
  typeOf (SCString _) = TypeString ∧
  typeOf (SCBool _) = TypeBool ∧
  typeOf (SCNumList _) = TypeNumList ∧
  typeOf (SCNumOption _) = TypeNumOption ∧
  typeOf (SCNumListList _) = TypeNumListList ∧
  typeOf (SCNumStringList _) = TypeNumStringList ∧
  typeOf (SCWord8List _) = TypeWord8List
End

Definition check_types_def:
  check_types params param_types = (MAP typeOf params = param_types)
End

Type state_references = ``:State``

Datatype:
  Exn = CFail num
End

val config =  global_state_config
              |> with_state ``:state_references``
              |> with_exception ``:Exn``;
Overload failwith = ``raise_CFail``
Overload fail = ``failwith : num -> State -> (α, Exn) exc # State``  (*α = SCvalue*)
val _ = start_translation config;

Definition assert_def:
  assert (errstr:num) (b:bool) : (state_references, unit, Exn) M =
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
