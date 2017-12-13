Require Import FlightModes.
Require Import Nat.
Require Import QArith.
Require Import Coq.Lists.List. Import ListNotations.

(*---------------------- Rule Evaluator Helper Functions --------------------------*)

        (* Q type less than -> bool *)

Definition Qlt (a b : Q) : bool := (Qle_bool a b) &&  negb (Qeq_bool a b).

        (* Q type greater than -> bool *) 

Definition Qgt (a b : Q) : bool := negb (Qle_bool a b) &&  negb (Qeq_bool a b).

        (* nat type greater than -> bool *) 

Definition gtr_nat (a b : nat) : bool := negb (Nat.leb a b) && negb (beq_nat a b). 

(************************************************************************************)

(* input to stall prediction *) 

Record StallTestParam : Type := 
  mkSParams {
    mmf_iteration : nat;           (* KF iteration *)
    R_Mode : autoflight_modes;     (* Active Roll Mode *)
    ias_ref : Q;                  (* Commanded Airspeed *)
    h : Q;                        (* Current Altitude *)
    cas : Q;                      (* Current Calibrated Airspeed *)
    V_stall : Q;                  (* Airspeed Stall (Lower) Limit *)
    V_Pred_series : list Q;       (* Predicted Airspeed (100s) *)
}.

Record StallAlertInfo : Set := 
  mkSAlert {
    tau_stall_memo : nat;         (* Memo Warning Time Threshold == 45s *)
    tau_stall_caution : nat;      (* Caution Warning Time Threshold == 10s *)
}.

(* output of stall prediction *)

Inductive StallLevel : Type := 
| NO_WARNING : StallLevel
| MEMO_WARNING : StallLevel
| CAUTION_WARNING : StallLevel.  


(* 
   Project Notes :

   Get data from project to run sanity check
   Define Inductive Prop for the prediction function and test equality

*) 


Fixpoint find_first_stall (i : nat) (V_stall : Q) (l : list Q) : option nat := 
  match l with 
    | nil => None
    | h::t => 
        if Qlt h V_stall then Some i
        else find_first_stall (S i) V_stall t
  end.

Definition stall_predict (info : StallAlertInfo) (p : StallTestParam) : StallLevel := 
  if (Qgt p.(h) (inject_Z 500)) && (Qlt p.(cas) p.(ias_ref)) && (gtr_nat p.(mmf_iteration) 25)
  then 
    match find_first_stall O p.(V_stall) p.(V_Pred_series) with 
      | None => NO_WARNING
      | Some stall_index => 
          if (Nat.ltb stall_index info.(tau_stall_caution)) && (gtr_nat stall_index info.(tau_stall_memo)) then MEMO_WARNING
          else if (Nat.leb stall_index info.(tau_stall_caution)) then CAUTION_WARNING
          else NO_WARNING
    end
  else NO_WARNING.

 

Inductive StallTest : Type := mkStall {
  AlertInfo : StallAlertInfo;
  TestParams : StallTestParam;
}.





