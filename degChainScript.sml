(*START ------------------------------------------------------------------------- *)
open preamble
open basis
open ml_monad_translator_interfaceLib

open stringTheory
open wordsTheory
open listTheory
open degTypesTheory
     
val _ = new_theory "monadChain";
val _ = translation_extends "basisProg";
val _ = ParseExtras.temp_tight_equality ();

Datatype:
    Address = Contract_address num | Client_address num
End

Definition take_address_def:
  take_address (Contract_address n) = n ∧
  take_address (Client_address n) = n
End

Definition address_is_contract_def:
  address_is_contract (Contract_address num) = T ∧
  address_is_contract (Client_address num) = F
End

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
  Contract = <| init: (Setup -> State -> (SCvalue, Exn) exc # State); receive: (Data -> State -> (SCvalue, Exn) exc # State) |>
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
  ActionBody = Call Address Data | Deploy Contract Setup
End

(* сам запрос к контракту *)
Datatype :
  Action = <| actFrom : Address; actType : ActionBody |> 
End

Definition get_actFrom_def:
  get_actFrom = Action_actFrom
End

Definition get_actType_def:
  get_actType = Action_actType
End

Definition act_is_from_account_def: 
  act_is_from_account act = (address_is_contract (get_actFrom act) = F)
End

Datatype:
  Environment = <| envContracts : (Address -> Contract option); envContractStates : (Address -> SCState option)|>
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
      (∀ prevEnv act newEnv to c setup s0 state. 
      (address_is_contract to = T) ∧
      (get_envContracts prevEnv to = NONE) ∧
      (act = build_act (Client_address s0.context.msgSender) (Deploy c setup)) ∧
      (get_SCState (SND (get_init c setup s0)) = get_SCState state) ∧
      (setup.code = state.context.storage)∧
      (newEnv = set_contract_state to (get_SCState state) (add_contract to c prevEnv)) ==>
      ActionEvaluation prevEnv act newEnv) ∧
      (∀ prevEnv act newEnv to c prevState data nextState.
      (get_envContracts prevEnv to = SOME c) ∧
      (get_envContractStates prevEnv to = SOME (get_SCState prevState)) ∧
      (act = build_act (Client_address prevState.context.msgSender) (Call to data)) ∧
      (get_SCState (SND (get_receive c data prevState)) = get_SCState nextState) ∧
      (newEnv = set_contract_state to (get_SCState nextState) prevEnv) ==>
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