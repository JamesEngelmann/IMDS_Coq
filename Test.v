Require Import CoRN.reals.CReals.
Require Import CoRN.reals.fast.CRIR.
Require Import CoRN.reals.CauchySeq.
Require Import CoRN.model.reals.Cauchy_IR.
Require Import FlightModes.
Require Import Nat.

Require Import Coq.Lists.List. Import ListNotations.

(* output of stall prediction *)

Inductive StallLevel : Type := 
| NO_WARNING : StallLevel
| MEMO_WARNING : StallLevel
| CAUTION_WARNING : StallLevel.  

(* input to stall prediction *) 

Record StallTestParam : Type := mkSParams {
  mmf_iteration : nat;
  R_Mode : autoflight_modes;
  ias_ref : CR;
  h : CR;
  cas : CR;
  V_stall : CR;
  V_Pred_series : list CR;
}.

Record StallAlertInfo : Set := mkSAlert {
  tau_stall_memo : nat;
  tau_stall_caution : nat;
}.

Fixpoint find_first_stall (i : nat) (V_stall : CR) (l : list CR) : option nat := 
  match l with 
    | nil => None
    | h::t => 
        if h < V_stall then Some i
        else find_first_stall (S i) V_stall t
  end.

Definition stall_predict (info : StallAlertInfo) (p : StallTestParam) : StallLevel := 
  if p.(h) > 500 && p.(cas) < p.(ias_ref) && p.(mmf_iteration) >= 25 
  then 
    match find_first_stall O p.(V_stall) p.(V_Pred_series) with 
      | None => NO_WARNING
      | Some stall_index => 
          if stall_index > info.(tau_stall_caution) && stall_index <= info.(tau_stall_memo) 
          then MEMO_WARNING
          else if stall_index <= info.(tau_stall_caution) then CAUTION_WARNING
          else NO_WARNING
    end
  else NO_WARNING. 



Inductive StallTest : Type := mkStall {
  AlertInfo : StallAlertInfo;
  TestParams : StallTestParam;
}.

Definition AlertTest := mkSAlert 0 0 0 0.

Compute AlertTest.(stall_level).

Check CReals.

Print CReals.

Definition nAlertRule : Type := nat -> nat -> Prop. 

(* Definition V_Pred : nat := 0.  this needs to be changed *)

Record StallTestParam : Type := mkSParams {
  mmf_iteration : nat;
  R_Mode : autoflight_modes;
  ias_ref : IR;
  h_pred : IR;
  cas_pred : IR;
  V_stall : IR;
}.

Search ltb.

Fixpoint V_Pred_compare (V_Pred : list nat) (V_stall : nat) : option nat :=
  match V_Pred with
  | nil => None
  | h :: t => if (Nat.ltb_lt h V_stall) then (Some h) else (V_Pred_compare t V_stall)
  end.



Inductive StallTest : Type := mkStall {
  AlertInfo : StallAlertInfo;
  TestParams : StallTestParam;
  mmfCheck : TestParams.(mmf_iteration) > 25;
  RCheck : nAlertRule;
}.

RE


Definition Stall :=  mkStall AlertTest ParamTest.


Definition ParamTest := mkSParams 0 (roll_mode) (0 = 0) (0 = 0) (0 = 0) (0 = 0).

Check ParamTest.(ias_ref).



Inductive StallTest : Type := mkStall {
  AlertInfo : StallAlertInfo;
  TestParams : StallTestParam;
}.

Definition Stall :=  mkStall AlertTest ParamTest.

Compute Stall.(AlertInfo).(stall_index).

Check CProp.
