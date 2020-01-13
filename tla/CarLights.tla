----------------------------- MODULE CarLights -----------------------------
EXTENDS FiniteSets

set ++ x == set \union {x}
set -- x == set \ {x}

CONSTANT Light
ASSUME IsFiniteSet(Light)

(* Env values types *)
Blinking_Auto_Neutral == CHOOSE Blinking_Auto_Neutral : Blinking_Auto_Neutral \notin BOOLEAN

LRS_State == BOOLEAN ++ Blinking_Auto_Neutral

Gear == {"G_Forward", "G_Reverse", "G_Neutal"}
Key == {"NoKey", "KeyInserted", "KeyInIgnitionOnPosition"}
PitmanArm == {"P_Neutral", "P_Up5", "P_Up7", "P_Down5", "P_Down7", "P_Forward", "P_Backward"}


VARIABLES ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key
vars == << ambientLight, driver, lights, gear, pitmanArm, lightRotarySwitch, steeringWheel, key >>

TypeInvariant == /\ ambientLight = FALSE
                 /\ driver \in BOOLEAN
                 /\ lights \in [Light -> LRS_State] (* Blinking *)
                 /\ gear \in Gear
                 /\ pitmanArm \in PitmanArm
                 /\ key \in Key
                 /\ lightRotarySwitch \in LRS_State (* Auto *)
                 /\ steeringWheel \in LRS_State (* Neutral *)

Init == /\ ambientLight \in BOOLEAN
        /\ driver \in BOOLEAN
        /\ lights = [ Light |-> FALSE ]
        /\ gear \in Gear
        /\ pitmanArm \in PitmanArm
        /\ key \in Key
        /\ lightRotarySwitch \in LRS_State
        /\ steeringWheel \in LRS_State
        
SysNext == UNCHANGED vars   (* \/ A  lights change *)
EnvNext == UNCHANGED vars   (* \/ B  vars minus lights change *)
Next == SysNext \/ EnvNext
        
Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Mon Jan 13 23:06:07 WET 2020 by herulume
\* Created Mon Jan 13 20:57:38 WET 2020 by herulume
