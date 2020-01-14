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
Light == {"FrontLeft", "FrontRight", "MiddleLeft", "MiddleRight", "BackRight", "BackLeft", "Top"}
Cornering == {"C_Left", "C_Right", "C_Neutral"}

(*************************************************************************)
(* The variables.                                                        *)
(*************************************************************************)
VARIABLES ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake
vars == << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake >>

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
                 /\ brake \in Brake
                 
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


(*************************************************************************)
(* System changes.                                                       *)
(*************************************************************************)
TmpRightBlinking == /\ driver
                    /\ pitmanArm = "P_Up5"
                    /\
                       \/ (* Off *)
                          /\ pitmanArm' = "P_Neutral"
                          /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["MiddleRight"] = "Off", !["BackRight"] = "Off"]
                          /\ UNCHANGED << ambientLight, driver, gear, lightRotarySwitch, steeringWheel, key, cornering, brake  >>
                       \/ (* On *) 
                          /\ key = "KeyInIgnitionOnPosition" 
                          /\ lights["FrontRight"] # "Blinking" /\  lights["MiddleRight"] # "Blinking" /\ lights["BackRight"] # "Blinking"
                          /\ lights' = [lights EXCEPT !["FrontRight"] = "Blinking", !["MiddleRight"] = "Blinking", !["BackRight"] = "Blinking"]
                          /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>


TmpLeftBlinking == /\ driver
                   /\ pitmanArm = "P_Down5"
                   /\
                      \/ (* Off *) 
                         /\ pitmanArm' = "P_Neutral"
                         /\ lights' = [lights EXCEPT !["FrontLeft"] = "Off", !["MiddleLeft"] = "Off", !["BackLeft"] = "Off"]
                         /\ UNCHANGED << ambientLight, driver, gear, lightRotarySwitch, steeringWheel, key, cornering, brake  >>
                      \/ (* On *) 
                         /\ key = "KeyInIgnitionOnPosition"
                         /\ lights["FrontLeft"] # "Blinking" /\ lights["MiddleLeft"] # "Blinking" /\ lights["BackLeft"] # "Blinking"
                         /\ lights' = [lights EXCEPT !["FrontLeft"] = "Blinking", !["MiddleLeft"] = "Blinking", !["BackLeft"] = "Blinking"]
                         /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>

TmpBlinking == TmpRightBlinking \/ TmpLeftBlinking


RightBlinking == /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
                 /\ driver
                 /\ pitmanArm = "P_Up7"
                 /\ lights["FrontRight"] # "Blinking" /\  lights["MiddleRight"] # "Blinking" /\ lights["BackRight"] # "Blinking"
                 /\ lights' = [lights EXCEPT !["FrontRight"] = "Blinking", !["MiddleRight"] = "Blinking", !["BackRight"] = "Blinking"]
                 /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>

LeftBlinking == /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
                /\ driver
                /\ pitmanArm = "P_Down7"
                /\ lights["FrontLeft"] # "Blinking" /\ lights["MiddleLeft"] # "Blinking" /\ lights["BackLeft"] # "Blinking"
                /\ lights' = [lights EXCEPT !["FrontLeft"] = "Blinking", !["MiddleLeft"] = "Blinking", !["BackLeft"] = "Blinking"]
                /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>

AlwaysBlinking == RightBlinking \/ LeftBlinking


DeactivateAllLights == /\ driver
                       /\ lightRotarySwitch = FALSE
                       /\ lights' = [l \in Light |-> "Off"]
                       /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>
  
ActivateAmbientLight == /\ key = "KeyInserted"
                        /\ ambientLight
                        /\ driver = FALSE
                        /\ lights' = [l \in Light |-> "Low" ]
                        /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>
  
ActivateLowHeadLights == /\ driver
                         /\ key # "KeyNotInserted"
                         /\ lightRotarySwitch = TRUE
                         /\ lights' = [lights EXCEPT !["FrontRight"] = "Half", !["FrontLeft"] = "Half", !["BackLeft"] = "Half", !["BackRight"] = "Half"]
                         /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>
                                 
DeactivateLowHeadLights == /\ driver
                           /\ key # "KeyNotInserted"
                           /\ lightRotarySwitch = FALSE
                           /\ \E e \in {"Half", "Low"} : lights["FrontRight"] = e /\ lights["FrontLeft"] = e /\ lights["BackLeft"] = e /\ lights["BackRight"] = e
                           /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["FrontLeft"] = "Off", !["BackLeft"] = "Off", !["BackRight"] = "Off"]
                           /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>

DeactivateLowHeadLightsNoKeyAuto == /\ driver
                                    /\ lightRotarySwitch = Auto
                                    /\ key = "KeyNotInserted"
                                    /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["FrontLeft"] = "Off", !["BackLeft"] = "Off", !["BackRight"] = "Off"]
                                    /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>
                                    
                              
LowHeadLights == \/ ActivateLowHeadLights 
                 \/ DeactivateLowHeadLights
                 \/ DeactivateAllLights  
                 \/ DeactivateLowHeadLightsNoKeyAuto


ActivateLeftCornering == /\ lights["FrontLeft"] = "Blinking"
                         /\ steeringWheel = "S_Left"
                         /\ cornering' = "C_Left"
                         /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, brake  >>

ActivateRightCornering == /\ lights["FrontRight"] = "Blinking"
                          /\ steeringWheel = "S_Right"
                          /\ cornering' = "C_Right"
                          /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, brake  >>

DeactivateCornering == /\ cornering # "C_Neutral"
                       /\ steeringWheel = "S_Neutral"
                       /\ cornering' = "C_Neutral"
                       /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, brake  >>

ActivateCornering == \/ ActivateRightCornering
                     \/ ActivateLeftCornering

ChangeCornering ==  \/ ActivateCornering  
                    \/ DeactivateCornering           


ActivateHighBeam == /\ key # "KeyNotInserted"
                    /\ driver
                    /\ pitmanArm = "P_Forward"
                    /\ lightRotarySwitch # FALSE
                    /\ lights' = [lights EXCEPT !["FrontRight"] = "High", !["FrontLeft"] = "High", !["BackLeft"] = "High", !["BackRight"] = "High"]
                    /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>

DeactivateHighBeam == /\ key # "KeyNotInserted"
                      /\ driver
                      /\ lights["MiddleRight"] # "Blinking"
                      /\ lights["MiddleLeft"] # "Blinking"
                      /\ 
                         \/ pitmanArm # "P_Forward" 
                         \/ lightRotarySwitch = FALSE
                     /\ lights' = [lights EXCEPT !["FrontRight"] = "Off", !["FrontLeft"] = "Off", !["BackLeft"] = "Off", !["BackRight"] = "Off"]
                     /\ UNCHANGED << ambientLight, driver, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>                   

HighBeam == ActivateHighBeam \/ DeactivateHighBeam


(*************************************************************************)
(* Environment changes.                                                  *)
(*************************************************************************)
ChangeAmbientLight == /\ driver 
                      /\ ambientLight' \in BOOLEAN -- ambientLight
                      /\ UNCHANGED << driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>

ChangeDriver == /\ key # "KeyInIgnitionOnPosition"
                /\ driver' \in BOOLEAN -- driver
                /\ UNCHANGED << ambientLight, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>                 

ChangeGear == /\ driver
              /\ key = "KeyInIgnitionOnPosition" (* KeyInIgnitionOnPosition *)
              /\ gear' \in Gear -- gear
              /\ UNCHANGED << ambientLight, driver, lights, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering, brake  >>

ChangePitmanArm == /\ driver
                   /\ 
                      /\ pitmanArm # "P_Neutral"
                      /\ lights["MiddleLeft"] # "Blinking"
                      /\ lights["MiddleRight"] # "Blinking"
                      => pitmanArm' = "P_Neutral" 
                   /\ 
                      /\ pitmanArm = "P_Neutral"
                      /\ lights["MiddleLeft"] # "Blinking"
                      /\ lights["MiddleRight"] # "Blinking"
                      => pitmanArm' \in PitmanArm -- "P_Neutral"
                   /\
                      /\ lights["MiddleLeft"] = "Blinking"
                      /\ lights["MiddleRight"] = "Blinking"
                      => pitmanArm' = pitmanArm
                   /\ UNCHANGED << ambientLight, driver, lights, gear, lightRotarySwitch, steeringWheel, key, cornering, brake  >>


ChangeLightRotarySwitch == /\ driver
                           /\ key = "KeyInserted"
                           /\ lightRotarySwitch' \in LightRotarySwitch -- lightRotarySwitch
                           /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, steeringWheel, key, cornering, brake  >>

ChangeSteeringWheel == /\ driver
                       /\ steeringWheel' \in SteeringWheel -- steeringWheel
                       /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, key, cornering, brake  >>

ChangeKey == /\ driver
             /\ key = "KeyNotInserted" => key' = "KeyInserted"
             /\ key = "KeyInserted" => key'= "KeyNotInserted" \/ key' = "KeyInIgnitionOnPosition"
             /\ key = "KeyInIgnitionOnPosition" => key' = "KeyInserted"
             /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, cornering, brake  >>

ChangeBrake == /\ driver
               /\ brake' \in Brake -- brake
               /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key, cornering >>
               
                                                         
SysNext == \/ TmpBlinking
           \/ AlwaysBlinking
           \/ ActivateAmbientLight
           \/ LowHeadLights
           \/ ChangeCornering
           \/ HighBeam


EnvNext ==  \/ ChangeAmbientLight
            \/ ChangeDriver
            \/ ChangeGear
            \/ ChangePitmanArm
            \/ ChangeLightRotarySwitch
            \/ ChangeSteeringWheel
            \/ ChangeKey
            \/ ChangeBrake
            
Next ==  SysNext \/ EnvNext  
 


(*************************************************************************)
(* Since we can't do "prime prime", we can't make TmpBlinking            *)
(* stop in the next two state, so we enforce this temporal proprety.     *)
(*************************************************************************)
Spec == Init /\ [][Next]_vars  /\ SF_lights(Next)


TmpRightBlinkWillStop == (pitmanArm = "P_Up5" /\ lights["FrontRight"] = "Blinking") ~> \/ (lights["FrontRight"] # "Blinking" /\ lights["MiddleRight"] # "Blinking" /\ lights["BackRight"] # "Blinking")
                                                                                       \/ pitmanArm = "P_Up7"
TmpLeftBlinkWillStop == (pitmanArm = "P_Down5"/\ lights["FrontLeft"] = "Blinking") ~> \/ (lights["FrontLeft"] # "Blinking" /\ lights["MiddleLeft"] # "Blinking" /\ lights["BackLeft"] # "Blinking") 
                                                                                      \/ pitmanArm = "P_Down7" 
TmpBlinkWillStop == /\ TmpRightBlinkWillStop
                    /\ TmpLeftBlinkWillStop

THEOREM Spec => []TypeInvariant
=============================================================================
