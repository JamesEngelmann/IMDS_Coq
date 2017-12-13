Require Import CoRN.reals.CReals.
Require Import CoRN.reals.fast.CRIR.
Require Import CoRN.reals.CauchySeq.
Require Import CoRN.model.reals.Cauchy_IR.
Require Import CoRN.reals.fast.CRFieldOps.
Require Import FlightModes.
Require Import Nat.

Require Import Coq.Lists.List. Import ListNotations.

Local Open Scope CR_scope.

(* output of stall prediction *)

Inductive StallLevel : Type := 
| NO_WARNING : StallLevel
| MEMO_WARNING : StallLevel
| CAUTION_WARNING : StallLevel.  

(* input to stall prediction *) 

Record StallTestParam : Type := 
  mkSParams {
    mmf_iteration : nat;           (* KF iteration *)
    R_Mode : autoflight_modes;     (* Active Roll Mode *)
    ias_ref : CR;                  (* Commanded Airspeed *)
    h : CR;                        (* Current Altitude *)
    cas : CR;                      (* Current Calibrated Airspeed *)
    V_stall : CR;                  (* Airspeed Stall (Lower) Limit *)
    V_Pred_series : list CR;       (* Predicted Airspeed (100s) *)
}.

Record StallAlertInfo : Set := 
  mkSAlert {
    tau_stall_memo : nat;         (* Memo Warning Time Threshold == 45s *)
    tau_stall_caution : nat;      (* Caution Warning Time Threshold == 10s *)
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
