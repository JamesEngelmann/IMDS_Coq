Require Import FlightModes.
Require Import Nat.
Require Import QArith.
Require Import Coq.Lists.List. Import ListNotations.

(***************************Rule Evaluator Helper Functions**************************)

        (* Q type less than -> bool *)

Definition Qltb (a b : Q) : bool := (Qle_bool a b) &&  negb (Qeq_bool a b).

        (* Q type greater than -> bool *) 

Definition Qgtb (a b : Q) : bool := negb (Qle_bool a b) &&  negb (Qeq_bool a b).

        (* nat type greater than or equals -> bool *) 

Definition geb_nat (a b : nat) : bool := negb (Nat.ltb a b) || (beq_nat a b). 

        (* nat type greater than or equals -> Prop *) 

Definition ge (a b: nat) : Prop := ~ (lt a b ).

        (* nat type greater than -> bool *) 

Definition gtrb_nat (a b : nat) : bool := negb (Nat.leb a b).

        (* nat type greater than -> Prop *) 

Definition gtr (a b : nat) : Prop := ~ (le a b).

        (* Sanity Check Function : Convert list nat -> list Q *)

Fixpoint convertln_2_lQ (lZ : list nat) : list Q :=
  match lZ with
  | [] => []
  | h :: t => (inject_Z (Z.of_nat h)) :: (convertln_2_lQ t)
  end.


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
  mkSInfo {
    tau_stall_memo : nat := 45;         (* Memo Warning Time Threshold == 45s *)
    tau_stall_caution : nat := 10;      (* Caution Warning Time Threshold == 10s *)
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
   
   Prove Theorem
  
*) 

(* Function: Find first index where V_pred is less than stall speed *)

Fixpoint find_first_stall (i : nat) (V_stall : Q) (l : list Q) : option nat := 
  match l with 
    | nil => None
    | h::t => 
        if (Qltb h V_stall) then Some i
        else find_first_stall (S i) V_stall t
  end.

(* Function: If V_pred drops beneath Vstall then True else False *)

Definition check_stall_prop (i : nat) (V_stall : Q) (l : list Q) : Prop := 
  match find_first_stall i V_stall l with
  | None => False
  | Some stall_index => True
  end.

(* Function: Test for Roll Mode - Rollout and low reference speed *)

Definition RM_Turkish_test (R_mode : autoflight_modes) (ias_ref : Q) : option Q :=
  match R_mode with
  | pitch_mode mode => None
  | roll_mode mode => match mode with
                      | None => None
                      | Some n => if (beq_nat n 3) && (Qltb ias_ref (inject_Z 170)) then Some (inject_Z 170) else None
                      end
  | at_mode mode => None
  end.

(* Find Correct Reference Speed *)

Definition get_ias_ref (R_mode : autoflight_modes) (ias_ref : Q) : Q := 
  match RM_Turkish_test (R_mode) (ias_ref) with
  | None => ias_ref
  | Some ias => ias
  end.

(* MAIN : Test for stall, output = StallLevel *)

Definition stall_predict (info : StallAlertInfo) (p : StallTestParam) : StallLevel := 
  if (Qgtb p.(h) (inject_Z 500)) && (Qltb p.(cas) (get_ias_ref p.(R_Mode) p.(ias_ref))) && (geb_nat p.(mmf_iteration) 25)
  then 
    match find_first_stall O p.(V_stall) p.(V_Pred_series) with 
      | None => NO_WARNING
      | Some stall_index => 
          if (gtrb_nat stall_index info.(tau_stall_caution)) && (Nat.leb stall_index info.(tau_stall_memo)) then MEMO_WARNING
          else if (Nat.leb stall_index info.(tau_stall_caution)) then CAUTION_WARNING else NO_WARNING
    end
  else NO_WARNING.

(* Define stall_predict as an inductive prop *)

Inductive stall_predict_prop : StallAlertInfo -> StallTestParam -> StallLevel -> Prop :=
  | NoWarning : forall i p stall_index,
 
    (Qgt p.(h) (inject_Z 500)) ->
    (Qlt p.(cas) (get_ias_ref p.(R_Mode) p.(ias_ref))) ->
    (ge p.(mmf_iteration) 25) ->
    (((find_first_stall 0 p.(V_stall) p.(V_Pred_series) = (Some stall_index))/\(gtr stall_index i.(tau_stall_memo))) 
    \/ (find_first_stall 0 p.(V_stall) p.(V_Pred_series) = None)) ->
    
    stall_predict_prop i p NO_WARNING

  | MemoWarning : forall i p stall_index, 

    (Qgt p.(h) (inject_Z 500)) ->
    (Qlt p.(cas) (get_ias_ref p.(R_Mode) p.(ias_ref))) ->
    (ge p.(mmf_iteration) 25) ->
    ((find_first_stall 0 p.(V_stall) p.(V_Pred_series) = (Some stall_index))
     /\
    (gtr stall_index i.(tau_stall_caution))/\(Nat.le stall_index i.(tau_stall_memo)))  ->

    stall_predict_prop i p MEMO_WARNING

  | CautionWarning : forall i p stall_index,
  
    (Qgt p.(h) (inject_Z 500)) ->
    (Qlt p.(cas) (get_ias_ref p.(R_Mode) p.(ias_ref))) ->
    (ge p.(mmf_iteration) 25) ->
    ((find_first_stall 0 p.(V_stall) p.(V_Pred_series) = (Some stall_index))
     /\
    (Nat.le stall_index i.(tau_stall_caution)))  ->

   stall_predict_prop i p CAUTION_WARNING.


(* Prove prediction equivalence (IndProp vs Function)  *)

Theorem predict_match : forall (info : StallAlertInfo) (p : StallTestParam) (warning : StallLevel),
  stall_predict_prop info p warning <-> (stall_predict info p = warning).
Proof.
  intros info p stall_level. split. 
  - intros H. induction H.
    + admit.
    + admit.
    + admit.
  - intros H. induction H.
    + unfold stall_predict.
Admitted.

(*
Theorem predict_match : forall (info : StallAlertInfo) (p : StallTestParam) (stall_index : nat), 
   stall_predict_prop info p (stall_predict info p). 
Proof.
  intros info p stall_index. induction stall_predict.
  - apply NoWarning with stall_index. 
Admitted.
*)

(**********************************Sanity Check Data*****************************************)

Definition V_stall_samp : Q := inject_Z 144.

Definition R_rollout : autoflight_modes := roll_mode (Some 3).

Definition R_lnav : autoflight_modes := roll_mode None.

Definition cur_h : Q := inject_Z 1000.

Definition cur_cas : Q := inject_Z 169.

Definition com_ias : Q := inject_Z 150.

Definition Vnw_nat : list nat := [337;335;333;331;329;327;325;323;321;319;317;315;313;311;309;
                                  307;305;303;301;299;297;295;293;291;288;286;284;282;280;278;
                                  276;274;272;270;268;266;264;262;260;258;256;254;252;250;248;
                                  246;244;242;240;238;236;234;232;230;228;225;223;221;219;217;
                                  215;213;211;209;207;205;203;201;199;197;195;193;191;189;187;
                                  185;183;181;179;177;175;173;171;169;167;164;162;160;158;156;
                                  154;152;150;148;146;144;142;140;138;136].

Definition Vmw_nat : list nat := [164;163;163;162;162;161;161;160;160;159;159;158;158;157;157;
                                  156;156;155;155;154;154;153;153;152;152;151;151;150;150;149;
                                  149;148;148;147;147;146;146;145;145;144;144;143;143;142;142;
                                  141;141;140;140;139;139;138;138;137;137;136;136;135;135;134;
                                  134;133;133;132;132;131;131;130;130;129;129;128;128;127;127;
                                  126;126;125;125;124;124;123;123;122;122;121;121;120;120;119;
                                  119;118;118;117;117;116;116;115;115;114].

Definition Vcw_nat : list nat := [147;146;146;145;145;144;144;143;142;142;141;141;140;140;139;
                                  139;138;137;137;136;136;135;135;134;134;133;133;132;131;131;
                                  130;130;129;129;128;128;127;126;126;125;125;124;124;123;123;
                                  122;122;121;120;120;119;119;118;118;117;117;116;115;115;114;
                                  114;113;113;112;112;111;111;110;109;109;108;108;107;107;106;
                                  106;105;104;104;103;103;102;102;101;101;100;100;99;98;98;97;
                                  97;96;96;95;95;94;93;93;92].

Definition Vnw := convertln_2_lQ Vnw_nat.
Definition Vmw := convertln_2_lQ Vmw_nat.
Definition Vcw := convertln_2_lQ Vcw_nat.

(**********************************************************************************************)

  (* Define StallAlertInfo test case*)

Definition testInfo : StallAlertInfo := mkSInfo.

  (* Define StallTestParam - No Warning Case *)

Definition testParam_nw : StallTestParam := mkSParams 25 R_rollout com_ias cur_h cur_cas V_stall_samp Vnw.

  (* Define StallTestParam - Memo Warning Case *)

Definition testParam_mw : StallTestParam := mkSParams 25 R_rollout com_ias cur_h cur_cas V_stall_samp Vmw.

  (* Define StallTestParam - Caution Warning Case *)

Definition testParam_cw : StallTestParam := mkSParams 25 R_rollout com_ias cur_h cur_cas V_stall_samp Vcw.

(*-------------------Sanity Test------------------------*)

Compute stall_predict testInfo testParam_nw. (* Expect No Warning *)
Compute stall_predict testInfo testParam_mw. (* Expect Memo Warning *)
Compute stall_predict testInfo testParam_cw. (* Expect Caution Warning *)




