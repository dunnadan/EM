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
Hard == CHOOSE Hard : Hard \notin BOOLEAN

(*************************************************************************)
(* Our types, so to speak.                                               *)
(* We have tried to pass some of them as CONSTANTS but since we need     *)
(* to know each value, they can't be passed as modal values sets (to     *)
(* the best of our knowledge of course).                                 *)
(*************************************************************************)
LightState == {"Off", "Half", "Low", "Blinking", "High"}
KeyState == {"KeyInserted", "KeyNotInserted", "KeyInIgnitionOnPosition"}
LightRotarySwitch == BOOLEAN ++ Auto
Brake == BOOLEAN ++ Hard
SteeringWheel == {"S_Left", "S_Right", "S_Neutral"}
Gear == {"G_Forward", "G_Reverse", "G_Neutral"}
PitmanArm == {"P_Neutral", "P_Up5", "P_Up7", "P_Down5", "P_Down7", "P_Forward", "P_Backward"}
Light == {"FrontLeft", "FrontRight", "BackRight", "BackLeft", "Top"}
Cornering == {"C_Left", "C_Right", "C_Neutral"}
Blinker == {"B_Left", "B_Right", "B_Off"}

(*************************************************************************)
(* The variables.                                                        *)
(*************************************************************************)
VARIABLES ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker
vars == << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker >>
                 
(*************************************************************************)
(* The inital state.                                                     *)
(*************************************************************************)
Init == /\ ambientLight = FALSE
        /\ driver = FALSE
        /\ lights = [l \in Light |-> "Off" ]
        /\ gear = "G_Neutral"
        /\ pitmanArm = "P_Neutral"
        /\ key = "KeyNotInserted"
        /\ lightRotarySwitch = FALSE
        /\ steeringWheel = "S_Neutral"
        /\ cornering = "C_Neutral"
        /\ brake = FALSE
        /\ blinker = "B_Off"


(*************************************************************************)
(* System changes.                                                       *)
(*************************************************************************)
TmpRightBlinkingOn == /\ driver
                      /\ pitmanArm = "P_Up5"
                      /\ key = "KeyInIgnitionOnPosition" 
                      /\ blinker' = "B_Right"
                      /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, lights  >>

TmpLeftBlinkingOn == /\ driver
                     /\ pitmanArm = "P_Down5"
                     /\ key = "KeyInIgnitionOnPosition" 
                     /\ blinker' = "B_Left"
                     /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, lights  >>


TmpBlinking == \/ TmpRightBlinkingOn
               \/ TmpLeftBlinkingOn 


RightBlinking == /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
                 /\ driver
                 /\ pitmanArm = "P_Up7"
                 /\ blinker' = "B_Right"
                 /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, lights  >>
                 
LeftBlinking == /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
                /\ driver
                /\ pitmanArm = "P_Down7"
                /\ blinker' = "B_Left"
                /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, lights  >>
                
AlwaysBlinking == RightBlinking \/ LeftBlinking


DeactivateAllLights == /\ driver
                       /\ lightRotarySwitch = FALSE
                       /\ lights' = [l \in Light |-> "Off"]
                       /\ blinker' = "B_Off"
                       /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>
  
ActivateAmbientLight == /\ key = "KeyInserted"
                        /\ ambientLight
                        /\ driver = FALSE
                        /\ lights' = [l \in Light |-> "Low" ]
                        /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker  >>
  
ActivateLowHeadLights == /\ driver
                         /\ key # "KeyNotInserted"
                         /\ lightRotarySwitch = TRUE
                         /\ lights' = [lights EXCEPT !["FrontRight"] = "Half", !["FrontLeft"] = "Half", !["BackLeft"] = "Half", !["BackRight"] = "Half"]
                         /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker  >>
                                 
DeactivateLowHeadLights == /\ driver
                           /\ key # "KeyNotInserted"
                           /\ lightRotarySwitch = FALSE
                           /\ \E e \in {"Half", "Low"} : lights["FrontRight"] = e /\ lights["FrontLeft"] = e /\ lights["BackLeft"] = e /\ lights["BackRight"] = e
                           /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["FrontLeft"] = "Off", !["BackLeft"] = "Off", !["BackRight"] = "Off"]
                           /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker >>

DeactivateLowHeadLightsNoKeyAuto == /\ driver
                                    /\ lightRotarySwitch = Auto
                                    /\ key = "KeyNotInserted"
                                    /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["FrontLeft"] = "Off", !["BackLeft"] = "Off", !["BackRight"] = "Off"]
                                    /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker  >>
                                    
                              
LowHeadLights == \/ ActivateLowHeadLights 
                 \/ DeactivateLowHeadLights
                 \/ DeactivateAllLights  
                 \/ DeactivateLowHeadLightsNoKeyAuto


ActivateLeftCornering == /\ blinker = "B_Left"
                         /\ steeringWheel = "S_Left"
                         /\ cornering' = "C_Left"
                         /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, brake, blinker  >>

ActivateRightCornering == /\ blinker = "B_Right"
                          /\ steeringWheel = "S_Right"
                          /\ cornering' = "C_Right"
                          /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, brake, blinker  >>

DeactivateCornering == /\ cornering # "C_Neutral"
                       /\ steeringWheel = "S_Neutral"
                       /\ cornering' = "C_Neutral"
                       /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, brake, blinker  >>

ActivateCornering == \/ ActivateRightCornering
                     \/ ActivateLeftCornering

ChangeCornering ==  \/ ActivateCornering  
                    \/ DeactivateCornering           


ActivateHighBeam == /\ key # "KeyNotInserted"
                    /\ driver
                    /\ pitmanArm = "P_Forward"
                    /\ lightRotarySwitch # FALSE
                    /\ lights' = [lights EXCEPT  !["FrontRight"] = "High", !["FrontLeft"] = "High", !["BackRight"] = "Half", !["BackLeft"] = "Half"]
                    /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker  >>

HighBeam == ActivateHighBeam


(*************************************************************************)
(* Environment changes.                                                  *)
(*************************************************************************)
ChangeAmbientLight == /\ driver 
                      /\ ambientLight' \in BOOLEAN -- ambientLight
                      /\ UNCHANGED << driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker  >>

ChangeDriver == /\ key # "KeyInIgnitionOnPosition"
                /\ driver' \in BOOLEAN -- driver
                /\ UNCHANGED << ambientLight, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker  >>                 

ChangeGear == /\ driver
              /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
              /\ gear' \in Gear -- gear
              /\ UNCHANGED << ambientLight, driver, lights, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker  >>

ChangePitmanArm == /\ driver
                   /\ pitmanArm # "P_Neutral" => /\ pitmanArm' = "P_Neutral"
                                                 /\ blinker' = "B_Off"
                                                 /\ IF lights["FrontLeft"] = "Half"
                                                        THEN lights' = [lights EXCEPT !["FrontRight"] = "Half", !["FrontLeft"] = "Half", !["BackRight"] = "Half", !["BackLeft"] = "Half"]
                                                        ELSE lights' = [lights EXCEPT !["FrontRight"] = "Off", !["FrontLeft"] = "Off", !["BackRight"] = "Off", !["BackLeft"] = "Off"]
                                                 /\ UNCHANGED << ambientLight, driver, gear, lightRotarySwitch, steeringWheel, key, cornering, brake >>
                   /\ pitmanArm = "P_Neutral" => /\ pitmanArm' \in PitmanArm -- pitmanArm
                                                 /\ 
                                                    \/ 
                                                       \/ TmpRightBlinkingOn
                                                       \/ TmpLeftBlinkingOn
                                                       \/ RightBlinking
                                                       \/ LeftBlinking
                                                    \/ UNCHANGED << ambientLight, driver, lights, gear, lightRotarySwitch, steeringWheel, key, cornering, brake, blinker >>
                                                 
                                                               
ChangeLightRotarySwitch == /\ driver
                           /\ key = "KeyInserted"
                           /\ lightRotarySwitch' \in LightRotarySwitch -- lightRotarySwitch
                           /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, steeringWheel, key, cornering, brake, blinker  >>

ChangeSteeringWheel == /\ driver
                       /\ steeringWheel' \in SteeringWheel -- steeringWheel
                       /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, key, cornering, brake, blinker  >>

ChangeKey == /\ driver
             /\ key = "KeyNotInserted" => key' = "KeyInserted"
             /\ key = "KeyInserted" => key'= "KeyNotInserted" \/ key' = "KeyInIgnitionOnPosition"
             /\ key = "KeyInIgnitionOnPosition" => key' = "KeyInserted"
             /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, cornering, brake, blinker  >>

ChangeBrake == /\ driver
               /\ brake' \in Brake -- brake
               /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, blinker >>
               
(*************************************************************************)
(* Spec                                                                  *)
(*************************************************************************)                                                        
SysNext == \/ TmpBlinking
           \/ AlwaysBlinking
           \/ ActivateAmbientLight
           \/ LowHeadLights
           \/ ChangeCornering
           \/ HighBeam


EnvNext ==  \/ ChangeAmbientLight 
            \/ ChangeDriver
            \/ ChangeGear
            \/ ChangeLightRotarySwitch
            \/ ChangeSteeringWheel
            \/ ChangeKey
            \/ ChangeBrake
            \/ ChangePitmanArm
            
Next ==  SysNext \/ EnvNext  
 



Spec == Init /\ [][Next]_vars  /\ WF_vars(Next)


(*************************************************************************)
(* Liveness                                                              *)
(*************************************************************************)

(*************************************************************************)
(* Can't be []() Since the steps aren't atomic per se, two situations    *)
(* happen:                                                               *)
(*  1) pitmanArm = "P_Up5" happen when the driver's condition or the     *)
(*                  key's condition doesn't verify. The lights aren't    *)
(*                  suppose to blink. This is by design.                 *)
(*  2) All conditions are met but TmpRightBlinkingOn isn't run.          *)
(*     This may happen because there might be a simpler expression.      *)
(*     This issue SHOULD be addressed in future work.                    *) 
(*************************************************************************)
TmpBlinkLiveness == <>(driver /\ pitmanArm = "P_Up5" /\ key = "KeyInIgnitionOnPosition"  => (blinker = "B_Right"))

(*************************************************************************)
(* The "<>(lights["FrontRight"] = "Low")" <> is needed, check            *)
(* previous comment.                                                     *)
(*************************************************************************)
OutWithLights == []<>(driver = FALSE /\ ambientLight = TRUE => <>(lights["FrontRight"] = "Low"))

(*************************************************************************)
(* Isn't verified.                                                       *)
(*************************************************************************)
TmpBlinkWillStop == (blinker # "B_Off" /\ (pitmanArm \in {"P_Up5", "P_Down5"})) ~> blinker = "B_Off" \/ pitmanArm \in {"P_Up7", "P_Down7"}


(*************************************************************************)
(* Safety                                                                *)
(*************************************************************************)

(*************************************************************************)
(* Type safety can be enforced as a simple safety proprety.              *)
(*************************************************************************)
TypeInvariant == /\ ambientLight \in BOOLEAN
                 /\ driver \in BOOLEAN
                 /\ lights \in [Light -> LightState] 
                 /\ gear \in Gear
                 /\ pitmanArm \in PitmanArm
                 /\ key \in KeyState
                 /\ lightRotarySwitch \in LightRotarySwitch 
                 /\ steeringWheel \in SteeringWheel
                 /\ cornering \in Cornering
                 /\ brake \in Brake
                 /\ blinker \in Blinker
                 
(*************************************************************************)
(* Top light is always off or part of ambient light.                     *)
(*************************************************************************)
TopOffOrAmbient == lights["Top"] \in {"Off", "Low"}

(*************************************************************************)
(* KeyOn means driver MUST be inside.                                    *)
(*************************************************************************)
KeyOnDriverIn == key = "KeyInIgnitionOnPosition" => driver

(*************************************************************************)
(* If the front is on, so is the back.                                   *)
(*************************************************************************)
FrontAndBackOn == lights["FrontRight"] # "Off" => lights["BackRight"] # "Off"

(*************************************************************************)
(* Mirror behaviour.                                                     *)
(*************************************************************************)
MirrorSides == /\ lights["FrontRight"] = lights["FrontLeft"]
               /\ lights["BackRight"] = lights["BackLeft"]
               

THEOREM Spec => []TypeInvariant
=============================================================================
