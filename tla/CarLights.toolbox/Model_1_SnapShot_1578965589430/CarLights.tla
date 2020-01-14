----------------------------- MODULE CarLights -----------------------------
EXTENDS FiniteSets

set ++ x == set \union {x}
set -- x == set \ {x}

CONSTANT Light
ASSUME IsFiniteSet(Light)

(* Env values types *)
Blinking == CHOOSE Blinking : Blinking \notin BOOLEAN
Auto == CHOOSE Auto : Auto \notin BOOLEAN
Neutral == CHOOSE Neutral : Neutral \notin BOOLEAN

LightState == BOOLEAN ++ Blinking
LightRotarySwitch == BOOLEAN ++ Auto
SteeringWheel == BOOLEAN ++ Neutral
Gear == {"G_Forward", "G_Reverse", "G_Neutal"}
PitmanArm == {"P_Neutral", "P_Up5", "P_Up7", "P_Down5", "P_Down7", "P_Forward", "P_Backward"}


VARIABLES ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key
vars == << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>

TypeInvariant == /\ ambientLight \in BOOLEAN
                 /\ driver \in BOOLEAN
                 /\ lights \in [Light -> LightState] 
                 /\ gear \in Gear
                 /\ pitmanArm \in PitmanArm
                 /\ key \in BOOLEAN (* True => KeyInserted, False => KeyInIgnitionOnPosition *)
                 /\ lightRotarySwitch \in LightRotarySwitch 
                 /\ steeringWheel \in SteeringWheel 

Init == /\ ambientLight = FALSE
        /\ driver = FALSE
        /\ lights = [l \in Light |-> FALSE ]
        /\ gear \in Gear
        /\ pitmanArm \in PitmanArm
        /\ key = TRUE
        /\ lightRotarySwitch \in LightRotarySwitch
        /\ steeringWheel \in SteeringWheel


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
                           /\ lightRotarySwitch' \in LightRotarySwitch -- lightRotarySwitch
                           /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, steeringWheel, key >>

ChangeSteeringWheel == /\ driver
                       /\ steeringWheel' \in SteeringWheel -- steeringWheel
                       /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, key >>

ChangeKey == /\ driver
             /\ key' \in BOOLEAN -- key
             /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel >>

(*
SysNext == key' = "NoKey" 
*)

EnvNext ==  \/ ChangeAmbientLight
            \/ ChangeDriver
            \/ ChangeGear
            \/ ChangePitmanArm
            \/ ChangeLightRotarySwitch
            \/ ChangeSteeringWheel
            \/ ChangeKey
            
Next == (* SysNext \/ *) EnvNext   

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Tue Jan 14 01:33:02 WET 2020 by herulume
\* Created Mon Jan 13 20:57:38 WET 2020 by herulume
