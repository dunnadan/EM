----------------------------- MODULE CarLights -----------------------------

(*************************************************************************)
(* Useful custom operators.                                              *)
(*************************************************************************)
set ++ x == set \union {x}
set -- x == set \ {x}

(*************************************************************************)
(* Signals with 3 states can be represented with the union of BOLEAN     *)
(* and a VALUE not in BOOLEAN, we need not know what that value is.      *)
(*************************************************************************)
Auto == CHOOSE Auto : Auto \notin BOOLEAN
Neutral == CHOOSE Neutral : Neutral \notin BOOLEAN

(*************************************************************************)
(* Our types, so to speak.                                               *)
(* We have tried to pass some of them as CONSTANTS but since we need     *)
(* to know each value, they can't be passed as modal values sets (to     *)
(* the best of our knowledge of course).                                 *)
(*************************************************************************)
LightState == {"Off", "Half", "Low", "Blinking"}
LightRotarySwitch == BOOLEAN ++ Auto
SteeringWheel == BOOLEAN ++ Neutral
Gear == {"G_Forward", "G_Reverse", "G_Neutral"}
PitmanArm == {"P_Neutral", "P_Up5", "P_Up7", "P_Down5", "P_Down7", "P_Forward", "P_Backward"}
Light == {"FrontLeft", "FrontRight", "MiddleLeft", "MiddleRight", "BackRight", "BackLeft", "Top"}


(*************************************************************************)
(* The variables.                                                        *)
(*************************************************************************)
VARIABLES ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key
vars == << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>

(*************************************************************************)
(* Type safety can be enforced as a simple safety proprety.              *)
(*************************************************************************)
TypeInvariant == /\ ambientLight \in BOOLEAN
                 /\ driver \in BOOLEAN
                 /\ lights \in [Light -> LightState] 
                 /\ gear \in Gear
                 /\ pitmanArm \in PitmanArm
                 /\ key \in BOOLEAN (* True => KeyInserted, False => KeyInIgnitionOnPosition *)
                 /\ lightRotarySwitch \in LightRotarySwitch 
                 /\ steeringWheel \in SteeringWheel 
                 
(*************************************************************************)
(* The inital state.                                                     *)
(* We've tried the maximize the initial states that make sense (to us).  *)
(*************************************************************************)
Init == /\ ambientLight = FALSE
        /\ driver = FALSE
        /\ lights = [l \in Light |-> "Off" ]
        /\ gear = "G_Neutral"
        /\ pitmanArm = "P_Neutral"
        /\ key = TRUE
        /\ lightRotarySwitch \in LightRotarySwitch
        /\ steeringWheel \in SteeringWheel


(*************************************************************************)
(* Environment changes.                                                  *)
(*************************************************************************)
ChangeAmbientLight == /\ driver 
                      /\ ambientLight' \in BOOLEAN -- ambientLight
                      /\ UNCHANGED << driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>

ChangeDriver == /\ key
                /\ driver' \in BOOLEAN -- driver
                /\ UNCHANGED << ambientLight, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>                 

ChangeGear == /\ driver
              /\ key = FALSE (* KeyInIgnitionOnPosition *)
              /\ gear' \in Gear -- gear
              /\ UNCHANGED << ambientLight, driver, lights, pitmanArm, lightRotarySwitch, steeringWheel, key >>

ChangePitmanArm == /\ driver
                   /\ pitmanArm' \in PitmanArm -- pitmanArm
                   /\ UNCHANGED << ambientLight, driver, lights, gear, lightRotarySwitch, steeringWheel, key >>


ChangeLightRotarySwitch == /\ driver
                           /\ key
                           /\ lightRotarySwitch' \in LightRotarySwitch -- lightRotarySwitch
                           /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, steeringWheel, key >>

ChangeSteeringWheel == /\ driver
                       /\ steeringWheel' \in SteeringWheel -- steeringWheel
                       /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, key >>

ChangeKey == /\ driver
             /\ key' \in BOOLEAN -- key
             /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel >>


(*************************************************************************)
(* System changes.                                                       *)
(*************************************************************************)
TmpRightBlinking == /\ key = FALSE (* KeyInIgnitionOnPosition *)
                    /\ driver
                    /\ pitmanArm = "P_Up5"
                    /\
                       \/ (* Off *)
                          /\ pitmanArm' = "P_Neutral"
                          /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["MiddleRight"] = "Off", !["BackRight"] = "Off"]
                          /\ UNCHANGED << ambientLight, driver, gear, lightRotarySwitch, steeringWheel, key >>
                       \/ (* On *) 
                          /\ lights["FrontLeft"] # "Blinking" /\  lights["MiddleLeft"] # "Blinking" /\ lights["BackLeft"] # "Blinking"
                          /\ lights' = [lights EXCEPT !["FrontRight"] = "Blinking", !["MiddleRight"] = "Blinking", !["BackRight"] = "Blinking"]
                          /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>


TmpLeftBlinking == /\ key = FALSE (* KeyInIgnitionOnPosition *)
                   /\ driver
                   /\ pitmanArm = "P_Down5"
                   /\
                      \/ (* Off *) 
                         /\ pitmanArm' = "P_Neutral"
                         /\ lights' = [lights EXCEPT !["FrontLeft"] = "Off", !["MiddleLeft"] = "Off", !["BackLeft"] = "Off"]
                         /\ UNCHANGED << ambientLight, driver, gear, lightRotarySwitch, steeringWheel, key >>
                      \/ (* On *) 
                         /\ lights["FrontRight"] # "Blinking" /\ lights["MiddleRight"] # "Blinking" /\ lights["BackRight"] # "Blinking"
                         /\ lights' = [lights EXCEPT !["FrontLeft"] = "Blinking", !["MiddleLeft"] = "Blinking", !["BackLeft"] = "Blinking"]
                         /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>

TmpRightBlinkWillStop == pitmanArm = "P_Up5" ~> (lights["FrontRight"] # "Blinking" /\ lights["MiddleRight"] # "Blinking" /\ lights["BackRight"] # "Blinking")
TmpLeftBlinkWillStop == pitmanArm = "P_Down5" ~> (lights["FrontLeft"] # "Blinking" /\ lights["MiddleLeft"] # "Blinking" /\ lights["BackLeft"] # "Blinking")
TmpBlinkWillStop == /\ TmpRightBlinkWillStop
                    /\ TmpLeftBlinkWillStop
TmpBlinking == TmpRightBlinking \/ TmpLeftBlinking


RightBlinking == /\ key = FALSE (* KeyInIgnitionOnPosition *)
                 /\ driver
                 /\ pitmanArm = "P_Up7"
                 /\ lights["FrontLeft"] # "Blinking" /\  lights["MiddleLeft"] # "Blinking" /\ lights["BackLeft"] # "Blinking"
                 /\ lights' = [lights EXCEPT !["FrontRight"] = "Blinking", !["MiddleRight"] = "Blinking", !["BackRight"] = "Blinking"]
                 /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>

LeftBlinking == /\ key = FALSE (* KeyInIgnitionOnPosition *)
                /\ driver
                /\ pitmanArm = "P_Down7"
                /\ lights["FrontRight"] # "Blinking" /\ lights["MiddleRight"] # "Blinking" /\ lights["BackRight"] # "Blinking"
                /\ lights' = [lights EXCEPT !["FrontLeft"] = "Blinking", !["MiddleLeft"] = "Blinking", !["BackLeft"] = "Blinking"]
                /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>

AlwaysBlinking == RightBlinking \/ LeftBlinking


DeactivateAllLights == /\ driver
                       /\ lightRotarySwitch = FALSE
                       /\ lights' = [l \in Light |-> "Off"]
                       /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>
  

ActivateAmbientLight == /\ key
                        /\ ambientLight
                        /\ driver = FALSE
                        /\ lights' = [l \in Light |-> "Low" ]
                        /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>
  
  
ActivateLowHeadLights == /\ driver
                         /\ key
                         /\ lightRotarySwitch = TRUE
                         /\ lights' = [lights EXCEPT !["FrontRight"] = "Half", !["FrontLeft"] = "Half", !["BackLeft"] = "Half", !["BackRight"] = "Half"]
                         /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>
                                 

DeactivateLowHeadLights == /\ driver
                           /\ key
                           /\ lightRotarySwitch = Auto
                           /\ \E e \in {"Half", "Low"} : lights["FrontRight"] = e /\ lights["FrontLeft"] = e /\ lights["BackLeft"] = e /\ lights["BackRight"] = e
                           /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["FrontLeft"] = "Off", !["BackLeft"] = "Off", !["BackRight"] = "Off"]
                           /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>
                              
LowHeadLights == ActivateLowHeadLights \/ DeactivateLowHeadLights \/ DeactivateAllLights  

                                                          
SysNext == \/ TmpBlinking
           \/ AlwaysBlinking
           \/ ActivateAmbientLight
           \/ LowHeadLights

EnvNext ==  \/ ChangeAmbientLight
            \/ ChangeDriver
            \/ ChangeGear
            \/ ChangePitmanArm
            \/ ChangeLightRotarySwitch
            \/ ChangeSteeringWheel
            \/ ChangeKey
            
Next ==  SysNext \/  EnvNext   

(*************************************************************************)
(* Since we can't do "prime prime", we can't make TmpBlinking            *)
(* stop in the next two state, so we enforce this temporal proprety.     *)
(*************************************************************************)
Spec == Init /\ [][Next]_vars /\ []TmpBlinkWillStop

THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Tue Jan 14 15:43:56 WET 2020 by herulume
\* Last modified Tue Jan 14 14:14:23 WET 2020 by apollo
\* Created Mon Jan 13 20:57:38 WET 2020 by herulume