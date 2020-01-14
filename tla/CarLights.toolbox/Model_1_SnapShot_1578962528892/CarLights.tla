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
Key == {"NoKey", "KeyInserted", "KeyInIgnitionOnPosition"}
PitmanArm == {"P_Neutral", "P_Up5", "P_Up7", "P_Down5", "P_Down7", "P_Forward", "P_Backward"}


VARIABLES ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key
vars == << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>

TypeInvariant == /\ ambientLight = FALSE
                 /\ driver \in BOOLEAN
                 /\ lights \in [Light -> LightState]
                 /\ gear \in Gear
                 /\ pitmanArm \in PitmanArm
                 /\ key \in Key
                 /\ lightRotarySwitch \in LightRotarySwitch 
                 /\ steeringWheel \in SteeringWheel 

Init == /\ ambientLight \in BOOLEAN
        /\ driver \in BOOLEAN
        /\ lights = [Light |-> FALSE ]
        /\ gear \in Gear
        /\ pitmanArm \in PitmanArm
        /\ key \in Key
        /\ lightRotarySwitch \in LightRotarySwitch
        /\ steeringWheel \in SteeringWheel


(*
SysNext == key' = "NoKey" 
EnvNext == gear'= "G_Reverse"
Next == SysNext \/ EnvNext
*)
Next == key' \in Key /\ UNCHANGED << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel >>
        
Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Tue Jan 14 00:42:06 WET 2020 by herulume
\* Created Mon Jan 13 20:57:38 WET 2020 by herulume
