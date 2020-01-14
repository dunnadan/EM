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
KeyState == {"KeyInserted", "KeyNotInserted", "KeyInIgnitionOnPosition"}
LightRotarySwitch == BOOLEAN ++ Auto
SteeringWheel == BOOLEAN ++ Neutral
Gear == {"G_Forward", "G_Reverse", "G_Neutral"}
PitmanArm == {"P_Neutral", "P_Up5", "P_Up7", "P_Down5", "P_Down7", "P_Forward", "P_Backward"}
Light == {"FrontLeft", "FrontRight", "MiddleLeft", "MiddleRight", "BackRight", "BackLeft", "Top"}
Cornering == {"C_Left", "C_Right"}

(*************************************************************************)
(* The variables.                                                        *)
(*************************************************************************)
VARIABLES ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering
vars == << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>

(*************************************************************************)
(* Type safety can be enforced as a simple safety proprety.              *)
(*************************************************************************)
TypeInvariant == /\ ambientLight \in BOOLEAN
                 /\ driver \in BOOLEAN
                 /\ lights \in [Light -> LightState] 
                 /\ gear \in Gear
                 /\ pitmanArm \in PitmanArm
                 /\ key \in KeyState (* True => KeyInserted, False => KeyInIgnitionOnPosition *)
                 /\ lightRotarySwitch \in LightRotarySwitch 
                 /\ steeringWheel \in SteeringWheel
                 /\ cornering \in Cornering
                 
(*************************************************************************)
(* The inital state.                                                     *)
(*************************************************************************)
Init == /\ ambientLight = FALSE
        /\ driver = FALSE
        /\ lights = [l \in Light |-> "Off" ]
        /\ gear = "G_Neutral"
        /\ pitmanArm = "P_Neutral"
        /\ key = "KeyNotInserted"
        /\ lightRotarySwitch \in LightRotarySwitch
        /\ steeringWheel \in SteeringWheel
        /\ cornering = {}


(*************************************************************************)
(* Environment changes.                                                  *)
(*************************************************************************)
ChangeAmbientLight == /\ driver 
                      /\ ambientLight' \in BOOLEAN -- ambientLight
                      /\ UNCHANGED << driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>

ChangeDriver == /\ key # "KeyInIgnitionOnPosition"
                /\ driver' \in BOOLEAN -- driver
                /\ UNCHANGED << ambientLight, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>                 

ChangeGear == /\ driver
              /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
              /\ gear' \in Gear -- gear
              /\ UNCHANGED << ambientLight, driver, lights, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>

ChangePitmanArm == /\ driver
                   /\ pitmanArm' \in PitmanArm -- pitmanArm
                   /\ UNCHANGED << ambientLight, driver, lights, gear, lightRotarySwitch, steeringWheel, key, cornering >>


ChangeLightRotarySwitch == /\ driver
                           /\ key = "KeyInserted"
                           /\ lightRotarySwitch' \in LightRotarySwitch -- lightRotarySwitch
                           /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, steeringWheel, key, cornering >>

ChangeSteeringWheel == /\ driver
                       /\ steeringWheel' \in SteeringWheel -- steeringWheel
                       /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, key, cornering >>

ChangeKey == /\ driver
             /\ key = "KeyNotInserted" => key' = "KeyInserted"
             /\ key = "KeyInserted" => key'= "KeyNotInserted" \/ key' = "KeyInIgnitionOnPosition"
             /\ key = "KeyInIgnitionOnPosition" => key' = "KeyInserted"
             /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, cornering >>


(*************************************************************************)
(* System changes.                                                       *)
(*************************************************************************)
TmpRightBlinking == /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
                    /\ driver
                    /\ pitmanArm = "P_Up5"
                    /\
                       \/ (* Off *)
                          /\ pitmanArm' = "P_Neutral"
                          /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["MiddleRight"] = "Off", !["BackRight"] = "Off"]
                          /\ UNCHANGED << ambientLight, driver, gear, lightRotarySwitch, steeringWheel, key, cornering >>
                       \/ (* On *) 
                          /\ lights["FrontLeft"] # "Blinking" /\  lights["MiddleLeft"] # "Blinking" /\ lights["BackLeft"] # "Blinking"
                          /\ lights' = [lights EXCEPT !["FrontRight"] = "Blinking", !["MiddleRight"] = "Blinking", !["BackRight"] = "Blinking"]
                          /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>


TmpLeftBlinking == /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
                   /\ driver
                   /\ pitmanArm = "P_Down5"
                   /\
                      \/ (* Off *) 
                         /\ pitmanArm' = "P_Neutral"
                         /\ lights' = [lights EXCEPT !["FrontLeft"] = "Off", !["MiddleLeft"] = "Off", !["BackLeft"] = "Off"]
                         /\ UNCHANGED << ambientLight, driver, gear, lightRotarySwitch, steeringWheel, key, cornering >>
                      \/ (* On *) 
                         /\ lights["FrontRight"] # "Blinking" /\ lights["MiddleRight"] # "Blinking" /\ lights["BackRight"] # "Blinking"
                         /\ lights' = [lights EXCEPT !["FrontLeft"] = "Blinking", !["MiddleLeft"] = "Blinking", !["BackLeft"] = "Blinking"]
                         /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>

TmpRightBlinkWillStop == pitmanArm = "P_Up5" ~> (lights["FrontRight"] # "Blinking" /\ lights["MiddleRight"] # "Blinking" /\ lights["BackRight"] # "Blinking")
TmpLeftBlinkWillStop == pitmanArm = "P_Down5" ~> (lights["FrontLeft"] # "Blinking" /\ lights["MiddleLeft"] # "Blinking" /\ lights["BackLeft"] # "Blinking")
TmpBlinkWillStop == /\ TmpRightBlinkWillStop
                    /\ TmpLeftBlinkWillStop
TmpBlinking == TmpRightBlinking \/ TmpLeftBlinking


RightBlinking == /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
                 /\ driver
                 /\ pitmanArm = "P_Up7"
                 /\ lights["FrontLeft"] # "Blinking" /\  lights["MiddleLeft"] # "Blinking" /\ lights["BackLeft"] # "Blinking"
                 /\ lights' = [lights EXCEPT !["FrontRight"] = "Blinking", !["MiddleRight"] = "Blinking", !["BackRight"] = "Blinking"]
                 /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>

LeftBlinking == /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
                /\ driver
                /\ pitmanArm = "P_Down7"
                /\ lights["FrontRight"] # "Blinking" /\ lights["MiddleRight"] # "Blinking" /\ lights["BackRight"] # "Blinking"
                /\ lights' = [lights EXCEPT !["FrontLeft"] = "Blinking", !["MiddleLeft"] = "Blinking", !["BackLeft"] = "Blinking"]
                /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>

AlwaysBlinking == RightBlinking \/ LeftBlinking


DeactivateAllLights == /\ driver
                       /\ lightRotarySwitch = FALSE
                       /\ lights' = [l \in Light |-> "Off"]
                       /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>
  
ActivateAmbientLight == /\ key = "KeyInserted"
                        /\ ambientLight
                        /\ driver = FALSE
                        /\ lights' = [l \in Light |-> "Low" ]
                        /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>
  
ActivateLowHeadLights == /\ driver
                         /\ key # "KeyNotInserted"
                         /\ lightRotarySwitch = TRUE
                         /\ lights' = [lights EXCEPT !["FrontRight"] = "Half", !["FrontLeft"] = "Half", !["BackLeft"] = "Half", !["BackRight"] = "Half"]
                         /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>
                                 
DeactivateLowHeadLights == /\ driver
                           /\ key # "KeyNotInserted"
                           /\ lightRotarySwitch = FALSE
                           /\ \E e \in {"Half", "Low"} : lights["FrontRight"] = e /\ lights["FrontLeft"] = e /\ lights["BackLeft"] = e /\ lights["BackRight"] = e
                           /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["FrontLeft"] = "Off", !["BackLeft"] = "Off", !["BackRight"] = "Off"]
                           /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>

DeactivateLowHeadLightsNoKeyAuto == /\ driver
                                    /\ lightRotarySwitch = Auto
                                    /\ key = "KeyNotInserted"
                                    /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["FrontLeft"] = "Off", !["BackLeft"] = "Off", !["BackRight"] = "Off"]
                                    /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>
                                    
                              
LowHeadLights == \/ ActivateLowHeadLights 
                 \/ DeactivateLowHeadLights
                 \/ DeactivateAllLights  
                 \/ DeactivateLowHeadLightsNoKeyAuto

                                                          
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
\* Last modified Tue Jan 14 16:45:08 WET 2020 by herulume
\* Last modified Tue Jan 14 14:14:23 WET 2020 by apollo
\* Created Mon Jan 13 20:57:38 WET 2020 by herulume
