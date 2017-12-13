(* Flight Modes *)

(*
// Active pitch modes
#define  ACTIVE_PM_NONE			       -1  -----> None
#define  ACTIVE_PM_VNAV_PTH		      0  -----> Some 0
#define  ACTIVE_PM_VNAV_SPD		      1  -----> Some 1
#define  ACTIVE_PM_VNAV_ALT		      2  -----> Some 2
#define  ACTIVE_PM_ALT			        3  -----> Some 3
#define  ACTIVE_PM_VS			          4  -----> Some 4
#define  ACTIVE_PM_FLARE		        5  -----> Some 5
#define  ACTIVE_PM_GS			          6  -----> Some 6
#define  ACTIVE_PM_TOGA			        7  -----> Some 7
#define  ACTIVE_PM_FLCH_SPD		      8  -----> Some 8
#define  ACTIVE_PM_SPD			        9  -----> Some 9
#define  ACTIVE_PM_SPEED_LIMIT	    10 -----> Some 10
#define  ACTIVE_PM_ALPHA_LIMIT	    11 -----> Some 11
#define  ACTIVE_PM_FLAP_LIMIT	      12 -----> Some 12

// Armed pitch modes
#define  ARMED_PM_VNAV			0 -----> Some 0
#define  ARMED_PM_FLARE			1 -----> Some 1
#define  ARMED_PM_GS			  2 -----> Some 2

// Active roll modes
#define  ACTIVE_RM_LNAV			  0 -----> Some 0
#define  ACTIVE_RM_LOC			  1 -----> Some 1
#define  ACTIVE_RM_HDG_SEL		2 -----> Some 2
#define  ACTIVE_RM_ROLLOUT		3 -----> Some 3
#define  ACTIVE_RM_TOGA			  4 -----> Some 4
#define  ACTIVE_RM_HDG_HOLD		5 -----> Some 5
#define  ACTIVE_RM_TRK_HOLD		6 -----> Some 6

// Armed roll modes
#define  ARMED_RM_NONE			 -1 -----> None
#define  ARMED_RM_LNAV			  0 -----> Some 0
#define  ARMED_RM_LOC			    1 -----> Some 1
#define  ARMED_RM_ROLLOUT		  2 -----> Some 2

// Active autothrottle modes
#define  ACTIVE_AM_NONE			    -1 -----> None
#define  ACTIVE_AM_THR			     0 -----> Some 0
#define  ACTIVE_AM_IDLE			     1 -----> Some 1
#define  ACTIVE_AM_SPD			     2 -----> Some 2
#define  ACTIVE_AM_THR_HOLD		   3 -----> Some 3
#define  ACTIVE_AM_THR_REF		   4 -----> Some 4
#define  ACTIVE_AM_TNAV			     5 -----> Some 5
#define  ACTIVE_AM_SPD_LIMIT	   6 -----> Some 6
#define  ACTIVE_AM_ALPHA_LIMIT	 7 -----> Some 7
#define  ACTIVE_AM_FLAP_LIMIT	   8 -----> Some 8
#define  ACTIVE_AM_VNAV			     9 -----> Some 9

*)

Inductive autoflight_modes : Type :=
  | pitch_mode : option nat -> autoflight_modes
  | roll_mode : option nat -> autoflight_modes
  | at_mode : option nat -> autoflight_modes.



(*
- Find CCorn Real type boolean comparison operators
- Could use Q.Arith if I can't figure out
- Import Q.Arith use Q type
- 


*)