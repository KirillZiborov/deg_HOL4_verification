(*START ------------------------------------------------------------------------- *)
open preamble
open basis
open ml_monad_translator_interfaceLib

open stringTheory
open wordsTheory
open listTheory
open degTypesTheory
     
val _ = new_theory "degChain";
val _ = translation_extends "basisProg";
val _ = ParseExtras.temp_tight_equality ();

Datatype :
  Data = <|functionSignature: num; params: SCvalue list |>
End

Definition get_functionSignature_def:
  get_functionSignature = Data_functionSignature
End

Definition get_params_def:
  get_params = Data_params
End

Datatype :
  Setup = <|code: word8 list; setupParams: SCvalue list |>
End

Definition get_setupparams_def:
  get_setupparams = Setup_setupParams
End

Datatype : 
  Contract = <| init: (Context -> Setup -> State -> (SCvalue, Exn) exc # State); 
                receive: (Context -> Data -> State -> (SCvalue, Exn) exc # State) |>
End

Definition build_contract_def :  
  build_contract i r = <| init := i; receive := r|>
End

Definition get_init_def:
  get_init = Contract_init
End

Definition get_receive_def:
  get_receive = Contract_receive
End

Datatype:
  ActionBody = Call num Data | Deploy Contract Setup
End

(* сам запрос к контракту *)
Datatype :
  Action = <| actFrom : num; actType : ActionBody |> 
End

Definition get_actFrom_def:
  get_actFrom = Action_actFrom
End

Definition get_actType_def:
  get_actType = Action_actType
End

Datatype:
  Environment = <| envContracts : (num -> Contract option); envContractStates : (num -> State option)|>
End

Definition get_envContracts_def:
  get_envContracts = Environment_envContracts
End

Definition get_envContractStates_def:
  get_envContractStates = Environment_envContractStates
End

Definition add_contract_def :  
  add_contract addr c rec : Environment = 
    rec with envContracts := (get_envContracts rec) (|addr |-> SOME c|) 
End

Definition set_contract_state_def :  
  set_contract_state addr SCstate rec : Environment = 
    rec with envContractStates := (get_envContractStates rec) (|addr |-> SOME SCstate|) 
End

Definition build_act_def :  
  build_act addr body = <| actFrom := addr; actType := body |>
End

Inductive ActionEvaluation:
      (* Constructor *)
      (∀ prevEnv act newEnv from to c setup time s0 state.
      (get_envContracts prevEnv to = NONE) ∧
      (act = build_act from (Deploy c setup)) ∧
      ((SND (get_init c <| msg_sender:= from; block_number:= s0.context.block_number + 1; block_timestamp:= time |> setup s0) = state)) ∧
      (state.context.block_timestamp > s0.context.block_timestamp) ∧
      (state.context.block_number = s0.context.block_number + 1) ∧      
      (newEnv = set_contract_state to state (add_contract to c prevEnv)) ==>
      ActionEvaluation prevEnv act newEnv) ∧
      (* Call *)
      (∀ prevEnv act newEnv from to c prevState data time nextState.
      (get_envContracts prevEnv to = SOME c) ∧
      (get_envContractStates prevEnv to = SOME prevState) ∧
      (act = build_act from (Call to data)) ∧
      (SND (get_receive c <| msg_sender:= from; block_number:= prevState.context.block_number + 1; block_timestamp:= time |> data prevState) = nextState) ∧
      (nextState.context.block_timestamp > prevState.context.block_timestamp) ∧
      (nextState.context.block_number = prevState.context.block_number + 1) ∧
      (newEnv = set_contract_state to nextState prevEnv) ==>
      ActionEvaluation prevEnv act newEnv)
End

Inductive ChainStep:
  (∀prevState nextState act. ActionEvaluation prevState act nextState ==> ChainStep prevState nextState)
End

Inductive ChainedList:
  (∀ p. ChainedList R p p) ∧
  (∀ x z. (?y. R x y ∧ ChainedList R y z) ==> ChainedList R x z)  
End

Inductive ChainTrace :
  (∀ s1 s2. ChainedList ChainStep s1 s2 ==> ChainTrace s1 s2) 
End

Definition empty1_def:
  empty1 _ = NONE
End

Definition empty2_def:
  empty2 _ = NONE
End

Definition emptyState_def:
  emptyState = <| envContracts := empty1;
                  envContractStates := empty2 |>
End

Inductive reachable :
  (∀ s. (ChainTrace emptyState s) ∧ (~ (emptyState = s)) ==> reachable s) 
End

val _ = export_theory();
